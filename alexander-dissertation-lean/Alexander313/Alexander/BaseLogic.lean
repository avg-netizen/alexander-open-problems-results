import Alexander313.Semantics

/-!
# Alexander's weak modal structures and finite certificates

This is the definition of the base logic, not normal modal logic. In
particular no arbitrary-term substitution or global necessitation rule
is added to validity. The completeness/r.e. theorem is proved separately by
`Delta.BLProofProgram.valid_program_exists`; validity is defined semantically here.
-/

namespace Alexander313

namespace Formula

variable {Owner : Type}

def substVar (x y : Nat) (φ : Formula Owner) : Formula Owner :=
  φ.substTerm x (.var y)

/-- The usual no-capture condition for substitution of a variable. -/
def VarSubstitutable (x y : Nat) : Formula Owner → Prop
  | .falsum => True
  | .equal _ _ => True
  | .imp φ ψ => φ.VarSubstitutable x y ∧ ψ.VarSubstitutable x y
  | .conj φ ψ => φ.VarSubstitutable x y ∧ ψ.VarSubstitutable x y
  | .disj φ ψ => φ.VarSubstitutable x y ∧ ψ.VarSubstitutable x y
  | .neg φ => φ.VarSubstitutable x y
  | .all z φ => z = x ∨ ((z ≠ y ∨ x ∉ φ.freeVars) ∧ φ.VarSubstitutable x y)
  | .ex z φ => z = x ∨ ((z ≠ y ∨ x ∉ φ.freeVars) ∧ φ.VarSubstitutable x y)
  | .know _ φ => φ.VarSubstitutable x y

end Formula

inductive AlphaTerm where
  | free : Nat → AlphaTerm
  | bound : Nat → AlphaTerm
  | zero : AlphaTerm
  | succ : AlphaTerm → AlphaTerm
  | add : AlphaTerm → AlphaTerm → AlphaTerm
  | mul : AlphaTerm → AlphaTerm → AlphaTerm
  deriving DecidableEq, Repr

inductive AlphaFormula (Owner : Type) where
  | falsum : AlphaFormula Owner
  | equal : AlphaTerm → AlphaTerm → AlphaFormula Owner
  | imp : AlphaFormula Owner → AlphaFormula Owner → AlphaFormula Owner
  | conj : AlphaFormula Owner → AlphaFormula Owner → AlphaFormula Owner
  | disj : AlphaFormula Owner → AlphaFormula Owner → AlphaFormula Owner
  | neg : AlphaFormula Owner → AlphaFormula Owner
  | all : AlphaFormula Owner → AlphaFormula Owner
  | ex : AlphaFormula Owner → AlphaFormula Owner
  | know : Owner → AlphaFormula Owner → AlphaFormula Owner
  deriving DecidableEq, Repr

def Term.alpha (bound : List Nat) : Term → AlphaTerm
  | .var x => if x ∈ bound then .bound (bound.idxOf x) else .free x
  | .zero => .zero
  | .succ t => .succ (t.alpha bound)
  | .add t u => .add (t.alpha bound) (u.alpha bound)
  | .mul t u => .mul (t.alpha bound) (u.alpha bound)

def Formula.alpha {Owner : Type} (bound : List Nat) : Formula Owner → AlphaFormula Owner
  | .falsum => .falsum
  | .equal t u => .equal (t.alpha bound) (u.alpha bound)
  | .imp φ ψ => .imp (φ.alpha bound) (ψ.alpha bound)
  | .conj φ ψ => .conj (φ.alpha bound) (ψ.alpha bound)
  | .disj φ ψ => .disj (φ.alpha bound) (ψ.alpha bound)
  | .neg φ => .neg (φ.alpha bound)
  | .all x φ => .all (φ.alpha (x :: bound))
  | .ex x φ => .ex (φ.alpha (x :: bound))
  | .know a φ => .know a (φ.alpha bound)

def Formula.AlphaEquivalent {Owner : Type} (φ ψ : Formula Owner) : Prop :=
  φ.alpha [] = ψ.alpha []

structure ModalModel (Owner D : Type) where
  zero : D
  succ : D → D
  add : D → D → D
  mul : D → D → D
  modal : Owner → Formula Owner → (Nat → D) → Prop
  free_independence : ∀ a φ s t,
    (∀ x ∈ φ.freeVars, s x = t x) → (modal a φ s ↔ modal a φ t)
  alphabetic : ∀ a φ ψ s, φ.AlphaEquivalent ψ → (modal a φ s ↔ modal a ψ s)
  weak_substitution : ∀ a φ x y s, φ.VarSubstitutable x y →
    (modal a (φ.substVar x y) s ↔ modal a φ (Function.update s x (s y)))

def generalTermEval {Owner D : Type} (M : ModalModel Owner D) (s : Nat → D) : Term → D
  | .var x => s x
  | .zero => M.zero
  | .succ t => M.succ (generalTermEval M s t)
  | .add t u => M.add (generalTermEval M s t) (generalTermEval M s u)
  | .mul t u => M.mul (generalTermEval M s t) (generalTermEval M s u)

def generalTruth {Owner D : Type} (M : ModalModel Owner D) :
    Formula Owner → (Nat → D) → Prop
  | .falsum, _ => False
  | .equal t u, s => generalTermEval M s t = generalTermEval M s u
  | .imp φ ψ, s => generalTruth M φ s → generalTruth M ψ s
  | .conj φ ψ, s => generalTruth M φ s ∧ generalTruth M ψ s
  | .disj φ ψ, s => generalTruth M φ s ∨ generalTruth M ψ s
  | .neg φ, s => ¬ generalTruth M φ s
  | .all x φ, s => ∀ n, generalTruth M φ (Function.update s x n)
  | .ex x φ, s => ∃ n, generalTruth M φ (Function.update s x n)
  | .know a φ, s => M.modal a φ s

/-- The standard-natural-number interpretation is required to be an
    admissible Alexander structure, not merely a recursive evaluator. -/
structure ActualRealization {Owner : Type} (P : RawPredicates Owner) where
  model : ModalModel Owner Nat
  zero_correct : model.zero = 0
  succ_correct : ∀ n, model.succ n = n + 1
  add_correct : ∀ m n, model.add m n = m + n
  mul_correct : ∀ m n, model.mul m n = m * n
  modal_correct : ∀ a φ s, model.modal a φ s ↔ actualTruth P (.know a φ) s

def Valid {Owner : Type} (φ : Formula Owner) : Prop :=
  ∀ (D : Type) (_ : Nonempty D) (M : ModalModel Owner D) (s : Nat → D),
    generalTruth M φ s

def Formula.chain {Owner : Type} : List (Formula Owner) → Formula Owner → Formula Owner
  | [], φ => φ
  | θ :: Γ, φ => .imp θ (chain Γ φ)

structure Certificate {Owner : Type} (axioms : Formula Owner → Prop)
    (conclusion : Formula Owner) where
  premises : List (Formula Owner)
  admitted : ∀ θ ∈ premises, axioms θ
  validity : Valid (Formula.chain premises conclusion)

def Provable {Owner : Type} (axioms : Formula Owner → Prop) (φ : Formula Owner) : Prop :=
  Nonempty (Certificate axioms φ)

theorem chain_elim {Owner D : Type} (M : ModalModel Owner D)
    (Γ : List (Formula Owner)) (φ : Formula Owner) (s : Nat → D)
    (hΓ : ∀ θ ∈ Γ, generalTruth M θ s)
    (h : generalTruth M (Formula.chain Γ φ) s) : generalTruth M φ s := by
  induction Γ with
  | nil => exact h
  | cons θ Γ ih =>
    apply ih (fun η hm => hΓ η (List.mem_cons_of_mem _ hm))
    exact h (hΓ θ List.mem_cons_self)

theorem certificate_sound {Owner D : Type} [Nonempty D]
    (M : ModalModel Owner D) {axioms : Formula Owner → Prop}
    {φ : Formula Owner} (c : Certificate axioms φ)
    (hax : ∀ θ, axioms θ → ∀ s, generalTruth M θ s) (s : Nat → D) :
    generalTruth M φ s :=
  chain_elim M c.premises φ s
    (fun θ hm => hax θ (c.admitted θ hm) s) (c.validity D inferInstance M s)

theorem provable_sound {Owner D : Type} [Nonempty D]
    (M : ModalModel Owner D) {axioms : Formula Owner → Prop}
    {φ : Formula Owner} (h : Provable axioms φ)
    (hax : ∀ θ, axioms θ → ∀ s, generalTruth M θ s) (s : Nat → D) :
    generalTruth M φ s := by
  rcases h with ⟨c⟩
  exact certificate_sound M c hax s

end Alexander313
