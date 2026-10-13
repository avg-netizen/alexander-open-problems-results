import Alexander313.ArithmeticCoding
import Alexander313.Alexander.WeakSemantics

/-!
# Hygienic instantiation of a two-variable arithmetic formula

The finite arithmetic template has ports 0 and 1. Instantiation first moves
every template variable above every free variable of the two argument terms,
then binds the two port values by equations. Its meaning in an arbitrary
first-order structure consequently depends only on the values of the two
arguments. This is an arithmetic construction; no substitution law for an
arbitrary term under a modal head is used.

Constructing the particular template representing `W` remains a separate
arithmetization obligation. `ArithmeticTemplate.coding` requires that precise
standard-number correctness proof and does not provide it by choice.
-/

namespace Alexander313

namespace Term

/-- A strict upper bound on the free-variable names of a term. -/
def variableBound : Term → Nat
  | .var x => x + 1
  | .zero => 0
  | .succ t => t.variableBound
  | .add t u => max t.variableBound u.variableBound
  | .mul t u => max t.variableBound u.variableBound

theorem lt_variableBound (t : Term) {v : Nat} (hv : v ∈ t.freeVars) :
    v < t.variableBound := by
  induction t with
  | var x =>
    have h : v = x := Finset.mem_singleton.mp hv
    subst v
    exact Nat.lt_succ_self x
  | zero => simp [freeVars] at hv
  | succ t ih => exact ih hv
  | add t u iht ihu =>
    rcases Finset.mem_union.mp hv with h | h
    · exact lt_of_lt_of_le (iht h) (le_max_left _ _)
    · exact lt_of_lt_of_le (ihu h) (le_max_right _ _)
  | mul t u iht ihu =>
    rcases Finset.mem_union.mp hv with h | h
    · exact lt_of_lt_of_le (iht h) (le_max_left _ _)
    · exact lt_of_lt_of_le (ihu h) (le_max_right _ _)

def renameVariables (f : Nat → Nat) : Term → Term
  | .var x => .var (f x)
  | .zero => .zero
  | .succ t => .succ (t.renameVariables f)
  | .add t u => .add (t.renameVariables f) (u.renameVariables f)
  | .mul t u => .mul (t.renameVariables f) (u.renameVariables f)

@[simp] theorem freeVars_renameVariables (t : Term) (f : Nat → Nat) :
    (t.renameVariables f).freeVars = t.freeVars.image f := by
  induction t <;> simp_all [renameVariables, freeVars, Finset.image_union]

theorem generalEval_renameVariables {Owner D : Type} (M : ModalModel Owner D)
    (t : Term) (f : Nat → Nat) (s : Nat → D) :
    generalTermEval M s (t.renameVariables f) = generalTermEval M (s ∘ f) t := by
  induction t <;> simp_all [renameVariables, generalTermEval, Function.comp_def]

end Term

namespace Formula

def renameVariables {Owner : Type} (f : Nat → Nat) : Formula Owner → Formula Owner
  | .falsum => .falsum
  | .equal t u => .equal (t.renameVariables f) (u.renameVariables f)
  | .imp φ ψ => .imp (φ.renameVariables f) (ψ.renameVariables f)
  | .conj φ ψ => .conj (φ.renameVariables f) (ψ.renameVariables f)
  | .disj φ ψ => .disj (φ.renameVariables f) (ψ.renameVariables f)
  | .neg φ => .neg (φ.renameVariables f)
  | .all x φ => .all (f x) (φ.renameVariables f)
  | .ex x φ => .ex (f x) (φ.renameVariables f)
  | .know a φ => .know a (φ.renameVariables f)

@[simp] theorem freeVars_renameVariables {Owner : Type} (φ : Formula Owner)
    (f : Nat → Nat) (hf : Function.Injective f) :
    (φ.renameVariables f).freeVars = φ.freeVars.image f := by
  induction φ <;>
    simp_all [renameVariables, freeVars, Finset.image_union, Finset.image_erase hf]

theorem arithmetic_renameVariables {Owner : Type} (φ : Formula Owner)
    (hφ : φ.Arithmetic) (f : Nat → Nat) : (φ.renameVariables f).Arithmetic := by
  induction φ <;> simp_all [renameVariables, Arithmetic]

/-- Variable renaming is proved here only for arithmetic formulas. -/
theorem generalTruth_renameVariables {Owner D : Type} (M : ModalModel Owner D)
    (φ : Formula Owner) (hφ : φ.Arithmetic) (f : Nat → Nat)
    (hf : Function.Injective f) (s : Nat → D) :
    generalTruth M (φ.renameVariables f) s ↔ generalTruth M φ (s ∘ f) := by
  induction φ generalizing s with
  | falsum => rfl
  | equal t u => simp [renameVariables, generalTruth, Term.generalEval_renameVariables]
  | imp φ ψ ihφ ihψ =>
    simp only [Arithmetic] at hφ
    simp [renameVariables, generalTruth, ihφ hφ.1 s, ihψ hφ.2 s]
  | conj φ ψ ihφ ihψ =>
    simp only [Arithmetic] at hφ
    simp [renameVariables, generalTruth, ihφ hφ.1 s, ihψ hφ.2 s]
  | disj φ ψ ihφ ihψ =>
    simp only [Arithmetic] at hφ
    simp [renameVariables, generalTruth, ihφ hφ.1 s, ihψ hφ.2 s]
  | neg φ ih => simp [renameVariables, generalTruth, ih hφ s]
  | all x φ ih =>
    simp only [renameVariables, generalTruth]
    exact forall_congr' fun n => by
      simpa only [Function.update_comp_eq_of_injective s hf x n] using
        ih hφ (Function.update s (f x) n)
  | ex x φ ih =>
    simp only [renameVariables, generalTruth]
    exact exists_congr fun n => by
      simpa only [Function.update_comp_eq_of_injective s hf x n] using
        ih hφ (Function.update s (f x) n)
  | know a φ ih => exact False.elim hφ

end Formula

structure ArithmeticTemplate (Owner : Type) where
  body : Formula Owner
  arithmetic : body.Arithmetic
  «variables» : body.freeVars ⊆ {0, 1}

namespace ArithmeticTemplate

variable {Owner : Type}

def base (e x : Term) : Nat := max e.variableBound x.variableBound

def member (T : ArithmeticTemplate Owner) (e x : Term) : Formula Owner :=
  let k := base e x
  .ex k (.conj (.equal (.var k) e)
    (.ex (k + 1) (.conj (.equal (.var (k + 1)) x)
      (T.body.renameVariables (fun v => k + v)))))

def relation {D : Type} (T : ArithmeticTemplate Owner) (M : ModalModel Owner D)
    (e x : D) : Prop :=
  generalTruth M T.body (fun v => if v = 0 then e else if v = 1 then x else M.zero)

theorem member_arithmetic (T : ArithmeticTemplate Owner) (e x : Term) :
    (T.member e x).Arithmetic := by
  simp only [member, Formula.Arithmetic]
  exact ⟨trivial, trivial, T.body.arithmetic_renameVariables T.arithmetic _⟩

theorem lt_base_left (e x : Term) {v : Nat} (hv : v ∈ e.freeVars) :
    v < base e x :=
  lt_of_lt_of_le (e.lt_variableBound hv) (le_max_left _ _)

theorem lt_base_right (e x : Term) {v : Nat} (hv : v ∈ x.freeVars) :
    v < base e x :=
  lt_of_lt_of_le (x.lt_variableBound hv) (le_max_right _ _)

theorem member_variables (T : ArithmeticTemplate Owner) (e x : Term) :
    (T.member e x).freeVars ⊆ e.freeVars ∪ x.freeVars := by
  intro v hv
  have hinj : Function.Injective (fun u => base e x + u) := by
    intro u w h
    exact Nat.add_left_cancel h
  simp only [member, Formula.freeVars, Formula.freeVars_renameVariables _ _ hinj,
    Term.freeVars] at hv
  obtain ⟨hvk, hv⟩ := Finset.mem_erase.mp hv
  rcases Finset.mem_union.mp hv with heq | hinner
  · rcases Finset.mem_union.mp heq with hk | he
    · exact False.elim (hvk (Finset.mem_singleton.mp hk))
    · exact Finset.mem_union_left _ he
  · obtain ⟨hvnext, hinner⟩ := Finset.mem_erase.mp hinner
    rcases Finset.mem_union.mp hinner with heq | hbody
    · rcases Finset.mem_union.mp heq with hnext | hx
      · exact False.elim (hvnext (Finset.mem_singleton.mp hnext))
      · exact Finset.mem_union_right _ hx
    · obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp hbody
      have hu01 := T.variables hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu01
      rcases hu01 with rfl | rfl
      · simp only [Nat.add_zero] at huv
        exact False.elim (hvk huv.symm)
      · exact False.elim (hvnext huv.symm)

theorem member_coherent {D : Type} (T : ArithmeticTemplate Owner)
    (M : ModalModel Owner D) (e x : Term) (s : Nat → D) :
    generalTruth M (T.member e x) s ↔
      T.relation M (generalTermEval M s e) (generalTermEval M s x) := by
  let k := base e x
  have he (a : D) : generalTermEval M (Function.update s k a) e =
      generalTermEval M s e := by
    apply generalTermEval_eq_of_agree
    intro v hv
    have hlt := lt_base_left e x hv
    have hne : v ≠ k := by omega
    simp [Function.update_of_ne hne]
  have hx (a b : D) :
      generalTermEval M (Function.update (Function.update s k a) (k + 1) b) x =
      generalTermEval M s x := by
    apply generalTermEval_eq_of_agree
    intro v hv
    have hlt := lt_base_right e x hv
    have hne : v ≠ k := by omega
    have hnext : v ≠ k + 1 := by omega
    simp [Function.update_of_ne hne, Function.update_of_ne hnext]
  have hinj : Function.Injective (fun v => k + v) := by
    intro v w h
    exact Nat.add_left_cancel h
  have hkne : k ≠ k + 1 := by omega
  have hb (a b : D) :
      generalTruth M (T.body.renameVariables (fun v => k + v))
        (Function.update (Function.update s k a) (k + 1) b) ↔ T.relation M a b := by
    rw [Formula.generalTruth_renameVariables M T.body T.arithmetic _ hinj]
    apply generalTruth_eq_of_agree
    intro v hv
    have hv01 := T.variables hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv01
    rcases hv01 with rfl | rfl <;>
      simp [Function.comp_def, relation, hkne]
  simp only [member, generalTruth, generalTermEval, Function.update_self]
  change (∃ a, a = generalTermEval M (Function.update s k a) e ∧
      ∃ b, b = generalTermEval M
        (Function.update (Function.update s k a) (k + 1) b) x ∧
        generalTruth M (T.body.renameVariables (fun v => k + v))
          (Function.update (Function.update s k a) (k + 1) b)) ↔ _
  simp only [he, hx, hb]
  constructor
  · rintro ⟨a, rfl, b, rfl, h⟩
    exact h
  · intro h
    exact ⟨_, rfl, _, rfl, h⟩

end ArithmeticTemplate

/-- Coherence is proved separately, so the comparator's `ArithmeticCoding`
    contract and target types retain their original meaning. -/
structure CoherentArithmeticCoding {Owner : Type} (A : ArithmeticCoding Owner) where
  relation : {D : Type} → ModalModel Owner D → D → D → Prop
  coherent : ∀ {D : Type} (M : ModalModel Owner D) (e x : Term) (s : Nat → D),
    generalTruth M (A.member e x) s ↔
      relation M (generalTermEval M s e) (generalTermEval M s x)

/-- A standard arithmetic structure with the constantly false modal
    interpretation, used only to evaluate arithmetic templates. -/
def arithmeticStandardModel (Owner : Type) : ModalModel Owner Nat where
  zero := 0
  succ := fun n => n + 1
  add := Nat.add
  mul := Nat.mul
  modal := fun _ _ _ => False
  free_independence := fun _ _ _ _ _ => Iff.rfl
  alphabetic := fun _ _ _ _ _ => Iff.rfl
  weak_substitution := fun _ _ _ _ _ _ => Iff.rfl

theorem generalTermEval_arithmeticStandardModel {Owner : Type}
    (t : Term) (s : Assignment) :
    generalTermEval (arithmeticStandardModel Owner) s t = t.eval s := by
  induction t <;> simp_all [generalTermEval, arithmeticStandardModel, Term.eval]

theorem generalTruth_arithmeticStandardModel {Owner : Type}
    (φ : Formula Owner) (hφ : φ.Arithmetic) (P : RawPredicates Owner)
    (filtered : Bool) (s : Assignment) :
    generalTruth (arithmeticStandardModel Owner) φ s ↔ truth filtered P φ s := by
  induction φ generalizing s with
  | falsum => rfl
  | equal t u => simp [generalTruth, truth, generalTermEval_arithmeticStandardModel]
  | imp φ ψ ihφ ihψ =>
    simp only [Formula.Arithmetic] at hφ
    simp [generalTruth, truth, ihφ hφ.1 s, ihψ hφ.2 s]
  | conj φ ψ ihφ ihψ =>
    simp only [Formula.Arithmetic] at hφ
    simp [generalTruth, truth, ihφ hφ.1 s, ihψ hφ.2 s]
  | disj φ ψ ihφ ihψ =>
    simp only [Formula.Arithmetic] at hφ
    simp [generalTruth, truth, ihφ hφ.1 s, ihψ hφ.2 s]
  | neg φ ih => simp [generalTruth, truth, ih hφ s]
  | all x φ ih => exact forall_congr' fun n => ih hφ (Function.update s x n)
  | ex x φ ih => exact exists_congr fun n => ih hφ (Function.update s x n)
  | know a φ ih => exact False.elim hφ

namespace ArithmeticTemplate

variable {Owner : Type}

/-- The actual `W` template and its standard-number correctness proof are
    the remaining inputs here. Hygiene/coherence are constructed above. -/
def coding (T : ArithmeticTemplate Owner)
    (hW : ∀ e x, T.relation (arithmeticStandardModel Owner) e x ↔ W e x) :
    ArithmeticCoding Owner where
  member := T.member
  arithmetic := T.member_arithmetic
  «variables» := T.member_variables
  correct := by
    intro e x P filtered s
    rw [← generalTruth_arithmeticStandardModel (T.member e x)
      (T.member_arithmetic e x) P filtered s]
    rw [T.member_coherent, generalTermEval_arithmeticStandardModel,
      generalTermEval_arithmeticStandardModel]
    exact hW _ _

def codingCoherent (T : ArithmeticTemplate Owner)
    (hW : ∀ e x, T.relation (arithmeticStandardModel Owner) e x ↔ W e x) :
    CoherentArithmeticCoding (T.coding hW) where
  relation := T.relation
  coherent := T.member_coherent

end ArithmeticTemplate

end Alexander313
