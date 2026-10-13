import Alexander313.Alexander.WeakSemantics
import Mathlib.ModelTheory.Satisfiability

/-!
# The first-order Δ language and its base-logic schemata

This is an actual translation into mathlib first-order syntax. Each pair
(owner, modal argument) has a predicate symbol of arity exactly the number
of free variables of the argument. Its argument tuple is sorted increasingly,
as in Alexander Definitions 1.3.1--1.3.7. Modal heads become atomic
first-order relations; their arguments are not recursively translated.

`SatisfiesBL` expresses truth of the universal closures of BL1 and BL2 by
requiring every assignment to satisfy their matrices. The forward model
construction and the reverse admissible modal construction are explicit.
The effective first-order proof calculus needed for the r.e. claim is a
separate obligation; no completeness or enumeration assumption is introduced.
-/

namespace Alexander313

namespace Delta

inductive ArithmeticSymbol : Nat → Type
  | zero : ArithmeticSymbol 0
  | succ : ArithmeticSymbol 1
  | add : ArithmeticSymbol 2
  | mul : ArithmeticSymbol 2
  deriving DecidableEq

def Relation (Owner : Type) (n : Nat) :=
  {q : Owner × Formula Owner // q.2.freeVars.card = n}

def language (Owner : Type) : FirstOrder.Language where
  Functions := ArithmeticSymbol
  Relations := Relation Owner

instance languageFunctionsDecidableEq (Owner : Type) (n : Nat) :
    DecidableEq ((language Owner).Functions n) :=
  inferInstanceAs (DecidableEq (ArithmeticSymbol n))

instance languageRelationsDecidableEq (Owner : Type) [DecidableEq Owner] (n : Nat) :
    DecidableEq ((language Owner).Relations n) :=
  inferInstanceAs (DecidableEq {q : Owner × Formula Owner // q.2.freeVars.card = n})

def modalSymbol {Owner : Type} (a : Owner) (φ : Formula Owner) :
    (language Owner).Relations φ.freeVars.card := ⟨(a, φ), rfl⟩

def freeTuple {Owner : Type} (φ : Formula Owner) : Fin φ.freeVars.card → Nat :=
  φ.freeVars.orderEmbOfFin rfl

@[simp] theorem freeTuple_mem {Owner : Type} (φ : Formula Owner)
    (i : Fin φ.freeVars.card) : freeTuple φ i ∈ φ.freeVars :=
  Finset.orderEmbOfFin_mem _ rfl i

def tupleAssignment {Owner D : Type} (zero : D) (φ : Formula Owner)
    (values : Fin φ.freeVars.card → D) : Nat → D :=
  fun x => if hx : x ∈ φ.freeVars then
    values ((φ.freeVars.orderIsoOfFin rfl).symm ⟨x, hx⟩) else zero

@[simp] theorem tupleAssignment_freeTuple {Owner D : Type} (zero : D)
    (φ : Formula Owner) (values : Fin φ.freeVars.card → D)
    (i : Fin φ.freeVars.card) :
    tupleAssignment zero φ values (freeTuple φ i) = values i := by
  unfold tupleAssignment
  rw [dif_pos (freeTuple_mem φ i)]
  have hi : (⟨freeTuple φ i, freeTuple_mem φ i⟩ : φ.freeVars) =
      φ.freeVars.orderIsoOfFin rfl i := by
    apply Subtype.ext
    rfl
  rw [hi, OrderIso.symm_apply_apply]

theorem tupleAssignment_agrees {Owner D : Type} (zero : D) (φ : Formula Owner)
    (s : Nat → D) :
    ∀ x ∈ φ.freeVars,
      tupleAssignment zero φ (fun i => s (freeTuple φ i)) x = s x := by
  intro x hx
  unfold tupleAssignment
  rw [dif_pos hx]
  change s (↑(φ.freeVars.orderIsoOfFin rfl
    ((φ.freeVars.orderIsoOfFin rfl).symm ⟨x, hx⟩))) = s x
  rw [OrderIso.apply_symm_apply]

def arithmeticMap {Owner D : Type} (M : ModalModel Owner D) :
    {n : Nat} → ArithmeticSymbol n → (Fin n → D) → D
  | _, .zero, _ => M.zero
  | _, .succ, v => M.succ (v 0)
  | _, .add, v => M.add (v 0) (v 1)
  | _, .mul, v => M.mul (v 0) (v 1)

/-- Alexander's ΔM from Proposition 1.3.10. Values at variables outside
    the relation tuple are filled with zero; free independence proves this
    choice does not affect the relation interpretation. -/
def structureOfModal {Owner D : Type} (M : ModalModel Owner D) :
    (language Owner).Structure D where
  funMap := arithmeticMap M
  RelMap := fun {n} r values => M.modal r.val.1 r.val.2
    (tupleAssignment M.zero r.val.2 (fun i => values (Fin.cast r.property i)))

theorem structure_modal_iff {Owner D : Type} (M : ModalModel Owner D)
    (a : Owner) (φ : Formula Owner) (s : Nat → D) :
    (structureOfModal M).RelMap (modalSymbol a φ)
      (fun i => s (freeTuple φ i)) ↔ M.modal a φ s := by
  change M.modal a φ (tupleAssignment M.zero φ (fun i => s (freeTuple φ i))) ↔
    M.modal a φ s
  exact M.free_independence a φ _ s (tupleAssignment_agrees M.zero φ s)

def term {Owner α : Type} (ρ : Nat → α) : Term → (language Owner).Term α
  | .var x => .var (ρ x)
  | .zero => .func .zero Fin.elim0
  | .succ t => FirstOrder.Language.Functions.apply₁ (L := language Owner)
      ArithmeticSymbol.succ (term ρ t)
  | .add t u => FirstOrder.Language.Functions.apply₂ (L := language Owner)
      ArithmeticSymbol.add (term ρ t) (term ρ u)
  | .mul t u => FirstOrder.Language.Functions.apply₂ (L := language Owner)
      ArithmeticSymbol.mul (term ρ t) (term ρ u)

/-- Allocate the new bound variable at the last de Bruijn level. Previously
    bound variables retain their levels, including through shadowing. -/
def bind {n : Nat} (ρ : Nat → Nat ⊕ Fin n) (x : Nat) : Nat → Nat ⊕ Fin (n + 1) :=
  Function.update (fun z => Sum.map id Fin.castSucc (ρ z)) x (.inr (Fin.last n))

def formulaAux {Owner : Type} {n : Nat} (ρ : Nat → Nat ⊕ Fin n) :
    Formula Owner → (language Owner).BoundedFormula Nat n
  | .falsum => .falsum
  | .equal t u => .equal (term ρ t) (term ρ u)
  | .imp φ ψ => (formulaAux ρ φ).imp (formulaAux ρ ψ)
  | .conj φ ψ => formulaAux ρ φ ⊓ formulaAux ρ ψ
  | .disj φ ψ => formulaAux ρ φ ⊔ formulaAux ρ ψ
  | .neg φ => (formulaAux ρ φ).not
  | .all x φ => (formulaAux (bind ρ x) φ).all
  | .ex x φ => (formulaAux (bind ρ x) φ).ex
  | .know a φ => .rel (modalSymbol a φ) (fun i => .var (ρ (freeTuple φ i)))

def formula {Owner : Type} (φ : Formula Owner) : (language Owner).Formula Nat :=
  formulaAux Sum.inl φ

theorem term_realize {Owner D α : Type} (M : ModalModel Owner D) (t : Term)
    (ρ : Nat → α) (s : α → D) :
    letI : (language Owner).Structure D := structureOfModal M
    (term (Owner := Owner) ρ t).realize s = generalTermEval M (s ∘ ρ) t := by
  letI : (language Owner).Structure D := structureOfModal M
  induction t with
  | var x => rfl
  | zero => rfl
  | succ t ih => exact congrArg M.succ ih
  | add t u iht ihu => exact congrArg₂ M.add iht ihu
  | mul t u iht ihu => exact congrArg₂ M.mul iht ihu

theorem bind_assignment {D : Type} {n : Nat} (ρ : Nat → Nat ⊕ Fin n)
    (s : Nat → D) (v : Fin n → D) (x : Nat) (d : D) :
    (Sum.elim s (Fin.snoc v d)) ∘ bind ρ x =
      Function.update ((Sum.elim s v) ∘ ρ) x d := by
  funext z
  by_cases hzx : z = x
  · subst z
    simp [bind, Function.comp_def]
  · cases hρ : ρ z <;> simp [bind, Function.comp_def, hzx, hρ]

theorem formulaAux_realize {Owner D : Type} (M : ModalModel Owner D)
    (φ : Formula Owner) {n : Nat} (ρ : Nat → Nat ⊕ Fin n)
    (s : Nat → D) (v : Fin n → D) :
    letI : (language Owner).Structure D := structureOfModal M
    (formulaAux ρ φ).Realize s v ↔ generalTruth M φ ((Sum.elim s v) ∘ ρ) := by
  letI : (language Owner).Structure D := structureOfModal M
  induction φ generalizing n ρ s v with
  | falsum => rfl
  | equal t u =>
    simp only [formulaAux, FirstOrder.Language.BoundedFormula.Realize,
      term_realize, generalTruth]
  | imp φ ψ ihφ ihψ =>
    simp only [formulaAux, FirstOrder.Language.BoundedFormula.realize_imp,
      generalTruth, ihφ, ihψ]
  | conj φ ψ ihφ ihψ =>
    simp only [formulaAux, FirstOrder.Language.BoundedFormula.realize_inf,
      generalTruth, ihφ, ihψ]
  | disj φ ψ ihφ ihψ =>
    simp only [formulaAux, FirstOrder.Language.BoundedFormula.realize_sup,
      generalTruth, ihφ, ihψ]
  | neg φ ih => exact not_congr (ih ρ s v)
  | all x φ ih =>
    simp only [formulaAux, FirstOrder.Language.BoundedFormula.realize_all, generalTruth]
    apply forall_congr'
    intro d
    simpa only [bind_assignment] using ih (bind ρ x) s (Fin.snoc v d)
  | ex x φ ih =>
    simp only [formulaAux, FirstOrder.Language.BoundedFormula.realize_ex, generalTruth]
    apply exists_congr
    intro d
    simpa only [bind_assignment] using ih (bind ρ x) s (Fin.snoc v d)
  | know a φ _ =>
    exact structure_modal_iff M a φ ((Sum.elim s v) ∘ ρ)

/-- Proposition 1.3.11's induction on satisfaction, in the forward direction. -/
theorem formula_realize {Owner D : Type} (M : ModalModel Owner D)
    (φ : Formula Owner) (s : Nat → D) :
    letI : (language Owner).Structure D := structureOfModal M
    (formula φ).Realize s ↔ generalTruth M φ s := by
  letI : (language Owner).Structure D := structureOfModal M
  simpa only [formula, FirstOrder.Language.Formula.Realize, Function.comp_def,
    Sum.elim_inl] using formulaAux_realize M φ Sum.inl s (default : Fin 0 → D)

def replaceVar (x y : Nat) : Nat → Nat := fun z => if z = x then y else z

theorem replaceVar_assignment {D : Type} (s : Nat → D) (x y : Nat) :
    s ∘ replaceVar x y = Function.update s x (s y) := by
  funext z
  by_cases hzx : z = x <;> simp [Function.comp_def, replaceVar, hzx]

def BL1 {Owner : Type} (a : Owner) (φ ψ : Formula Owner) :
    (language Owner).Formula Nat :=
  (formula (.know a φ)).iff (formula (.know a ψ))

def BL2 {Owner : Type} (a : Owner) (φ : Formula Owner) (x y : Nat) :
    (language Owner).Formula Nat :=
  (formula (.know a (φ.substVar x y))).iff
    ((formula (.know a φ)).relabel (replaceVar x y))

def baseLogicMatrices (Owner : Type) : Set ((language Owner).Formula Nat) :=
  {σ | (∃ a φ ψ, φ.AlphaEquivalent ψ ∧ σ = BL1 a φ ψ) ∨
       (∃ a φ x y, φ.VarSubstitutable x y ∧ σ = BL2 a φ x y)}

/-- Satisfaction of the universal closures in Definition 1.3.7. -/
def SatisfiesBL {Owner D : Type} (N : (language Owner).Structure D) : Prop :=
  letI : (language Owner).Structure D := N
  ∀ σ ∈ baseLogicMatrices Owner, ∀ s : Nat → D, σ.Realize s

theorem structureOfModal_BL1 {Owner D : Type} (M : ModalModel Owner D)
    (a : Owner) (φ ψ : Formula Owner) (h : φ.AlphaEquivalent ψ) (s : Nat → D) :
    letI : (language Owner).Structure D := structureOfModal M
    (BL1 a φ ψ).Realize s := by
  letI : (language Owner).Structure D := structureOfModal M
  simpa only [BL1, FirstOrder.Language.Formula.realize_iff, formula_realize,
    generalTruth] using M.alphabetic a φ ψ s h

theorem structureOfModal_BL2 {Owner D : Type} (M : ModalModel Owner D)
    (a : Owner) (φ : Formula Owner) (x y : Nat) (h : φ.VarSubstitutable x y)
    (s : Nat → D) :
    letI : (language Owner).Structure D := structureOfModal M
    (BL2 a φ x y).Realize s := by
  letI : (language Owner).Structure D := structureOfModal M
  simpa only [BL2, FirstOrder.Language.Formula.realize_iff,
    FirstOrder.Language.Formula.realize_relabel, formula_realize,
    replaceVar_assignment, generalTruth] using M.weak_substitution a φ x y s h

theorem structureOfModal_satisfiesBL {Owner D : Type} (M : ModalModel Owner D) :
    SatisfiesBL (structureOfModal M) := by
  intro σ hσ s
  rcases hσ with ⟨a, φ, ψ, h, rfl⟩ | ⟨a, φ, x, y, h, rfl⟩
  · exact structureOfModal_BL1 M a φ ψ h s
  · exact structureOfModal_BL2 M a φ x y h s

/-- The converse construction of Proposition 1.3.10. Its only premise is
    that the given first-order structure satisfies the explicitly constructed
    BL1/BL2 schemata; the admissibility fields are proved from them. -/
def modalOfStructure {Owner D : Type} (N : (language Owner).Structure D)
    (hN : SatisfiesBL N) : ModalModel Owner D := by
  letI : (language Owner).Structure D := N
  refine {
    zero := N.funMap .zero Fin.elim0
    succ := fun d => N.funMap .succ ![d]
    add := fun d e => N.funMap .add ![d, e]
    mul := fun d e => N.funMap .mul ![d, e]
    modal := fun a φ s => (formula (.know a φ)).Realize s
    free_independence := ?_
    alphabetic := ?_
    weak_substitution := ?_
  }
  · intro a φ s t h
    change N.RelMap (modalSymbol a φ) (fun i => s (freeTuple φ i)) ↔
      N.RelMap (modalSymbol a φ) (fun i => t (freeTuple φ i))
    have ht : (fun i => s (freeTuple φ i)) = (fun i => t (freeTuple φ i)) :=
      funext fun i => h _ (freeTuple_mem φ i)
    rw [ht]
  · intro a φ ψ s h
    exact FirstOrder.Language.Formula.realize_iff.mp
      (hN (BL1 a φ ψ) (Or.inl ⟨a, φ, ψ, h, rfl⟩) s)
  · intro a φ x y s h
    have hs := FirstOrder.Language.Formula.realize_iff.mp
      (hN (BL2 a φ x y) (Or.inr ⟨a, φ, x, y, h, rfl⟩) s)
    simpa only [FirstOrder.Language.Formula.realize_relabel,
      replaceVar_assignment] using hs

theorem term_realize_modalOfStructure {Owner D α : Type}
    (N : (language Owner).Structure D) (hN : SatisfiesBL N)
    (t : Term) (ρ : Nat → α) (s : α → D) :
    letI : (language Owner).Structure D := N
    (term (Owner := Owner) ρ t).realize s =
      generalTermEval (modalOfStructure N hN) (s ∘ ρ) t := by
  letI : (language Owner).Structure D := N
  induction t with
  | var x => rfl
  | zero =>
    change N.funMap .zero _ = N.funMap .zero _
    congr 1
    funext i
    exact Fin.elim0 i
  | succ t ih =>
    simpa only [term, FirstOrder.Language.Term.realize_functions_apply₁,
      generalTermEval, modalOfStructure] using
      congrArg (fun d => N.funMap .succ ![d]) ih
  | add t u iht ihu =>
    simpa only [term, FirstOrder.Language.Term.realize_functions_apply₂,
      generalTermEval, modalOfStructure] using
      congrArg₂ (fun d e => N.funMap .add ![d, e]) iht ihu
  | mul t u iht ihu =>
    simpa only [term, FirstOrder.Language.Term.realize_functions_apply₂,
      generalTermEval, modalOfStructure] using
      congrArg₂ (fun d e => N.funMap .mul ![d, e]) iht ihu

theorem formulaAux_realize_modalOfStructure {Owner D : Type}
    (N : (language Owner).Structure D) (hN : SatisfiesBL N)
    (φ : Formula Owner) {n : Nat} (ρ : Nat → Nat ⊕ Fin n)
    (s : Nat → D) (v : Fin n → D) :
    letI : (language Owner).Structure D := N
    (formulaAux ρ φ).Realize s v ↔
      generalTruth (modalOfStructure N hN) φ ((Sum.elim s v) ∘ ρ) := by
  letI : (language Owner).Structure D := N
  induction φ generalizing n ρ s v with
  | falsum => rfl
  | equal t u =>
    simp only [formulaAux, FirstOrder.Language.BoundedFormula.Realize,
      term_realize_modalOfStructure N hN, generalTruth]
  | imp φ ψ ihφ ihψ =>
    simp only [formulaAux, FirstOrder.Language.BoundedFormula.realize_imp,
      generalTruth, ihφ, ihψ]
  | conj φ ψ ihφ ihψ =>
    simp only [formulaAux, FirstOrder.Language.BoundedFormula.realize_inf,
      generalTruth, ihφ, ihψ]
  | disj φ ψ ihφ ihψ =>
    simp only [formulaAux, FirstOrder.Language.BoundedFormula.realize_sup,
      generalTruth, ihφ, ihψ]
  | neg φ ih => exact not_congr (ih ρ s v)
  | all x φ ih =>
    simp only [formulaAux, FirstOrder.Language.BoundedFormula.realize_all, generalTruth]
    apply forall_congr'
    intro d
    simpa only [bind_assignment] using ih (bind ρ x) s (Fin.snoc v d)
  | ex x φ ih =>
    simp only [formulaAux, FirstOrder.Language.BoundedFormula.realize_ex, generalTruth]
    apply exists_congr
    intro d
    simpa only [bind_assignment] using ih (bind ρ x) s (Fin.snoc v d)
  | know a φ _ => rfl

/-- Proposition 1.3.11's satisfaction induction in the reverse direction. -/
theorem formula_realize_modalOfStructure {Owner D : Type}
    (N : (language Owner).Structure D) (hN : SatisfiesBL N)
    (φ : Formula Owner) (s : Nat → D) :
    letI : (language Owner).Structure D := N
    (formula φ).Realize s ↔ generalTruth (modalOfStructure N hN) φ s := by
  letI : (language Owner).Structure D := N
  simpa only [formula, FirstOrder.Language.Formula.Realize, Function.comp_def,
    Sum.elim_inl] using formulaAux_realize_modalOfStructure N hN φ Sum.inl s
      (default : Fin 0 → D)

/-- Base validity is exactly first-order consequence of BL. This does not
    yet assert that such first-order consequences have an effective proof
    enumerator; that theorem requires a constructed proof calculus. -/
theorem valid_iff_firstOrder_BL {Owner : Type} (φ : Formula Owner) :
    Valid φ ↔ ∀ (D : Type) (_ : Nonempty D) (N : (language Owner).Structure D),
      SatisfiesBL N → ∀ s : Nat → D,
        letI : (language Owner).Structure D := N
        (formula φ).Realize s := by
  constructor
  · intro hφ D hD N hN s
    exact (formula_realize_modalOfStructure N hN φ s).mpr
      (hφ D hD (modalOfStructure N hN) s)
  · intro hφ D hD M s
    exact (formula_realize M φ s).mp
      (hφ D hD (structureOfModal M) (structureOfModal_satisfiesBL M) s)

end Delta

end Alexander313
