import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Common

/-!
# Actual simultaneous semantics of the pure order-two relations

Wilken's pure structure has the relational signature (<=, <=1, <=2), with
equality and ordinary first-order quantification. The two relations are
defined simultaneously by recursion on the upper ordinal, using Sigma1
and Sigma2 elementarity of initial segments. There is no bounded-quantifier
syntax here: the tuples below are finite blocks of ordinary quantifiers.

The matrices explicitly contain every Boolean combination of atomic formulas
in that signature. Sigma1 and Sigma2 are their respective existential and
existential-universal prenex forms, with any finite parameter tuple. This
module constructs the recursive relations and their literal equations;
conversion of arbitrary first-order formulas to these prenex forms, finite
expanded-pattern reflection, separated room, cofinality and public-code
decision algorithms are separate proofs. No relation or elementarity
contract is an input to the constructed R1/R2. Uncompiled proof candidates.
-/

noncomputable section

namespace Alexander313.Wilken.PureRelations

/-- Quantifier-free matrices in precisely the pure relational signature. -/
inductive Matrix (n : Nat) where
  | falsum
  | equal (i j : Fin n)
  | lessEqual (i j : Fin n)
  | first (i j : Fin n)
  | second (i j : Fin n)
  | neg (φ : Matrix n)
  | conj (φ ψ : Matrix n)
  | disj (φ ψ : Matrix n)

def Matrix.realize {n : Nat} (R₁ R₂ : Ordinal.{0} → Ordinal.{0} → Prop)
    (v : Fin n → Ordinal.{0}) : Matrix n → Prop
  | .falsum => False
  | .equal i j => v i = v j
  | .lessEqual i j => v i ≤ v j
  | .first i j => R₁ (v i) (v j)
  | .second i j => R₂ (v i) (v j)
  | .neg φ => ¬ φ.realize R₁ R₂ v
  | .conj φ ψ => φ.realize R₁ R₂ v ∧ ψ.realize R₁ R₂ v
  | .disj φ ψ => φ.realize R₁ R₂ v ∨ ψ.realize R₁ R₂ v

def TupleBelow {n : Nat} (α : Ordinal.{0}) (v : Fin n → Ordinal.{0}) : Prop :=
  ∀ i, v i < α

def sigma1Truth (R₁ R₂ : Ordinal.{0} → Ordinal.{0} → Prop) (α : Ordinal.{0})
    (p m : Nat) (φ : Matrix (p + m)) (v : Fin p → Ordinal.{0}) : Prop :=
  ∃ w : Fin m → Ordinal.{0}, TupleBelow α w ∧ φ.realize R₁ R₂ (Fin.append v w)

def sigma2Truth (R₁ R₂ : Ordinal.{0} → Ordinal.{0} → Prop) (α : Ordinal.{0})
    (p m n : Nat) (φ : Matrix ((p + m) + n)) (v : Fin p → Ordinal.{0}) : Prop :=
  ∃ w : Fin m → Ordinal.{0}, TupleBelow α w ∧
    ∀ z : Fin n → Ordinal.{0}, TupleBelow α z →
      φ.realize R₁ R₂ (Fin.append (Fin.append v w) z)

def Sigma1Elementary (R₁ R₂ : Ordinal.{0} → Ordinal.{0} → Prop) (α β : Ordinal.{0}) : Prop :=
  ∀ (p m : Nat) (φ : Matrix (p + m)) (v : Fin p → Ordinal.{0}),
    TupleBelow α v → (sigma1Truth R₁ R₂ α p m φ v ↔ sigma1Truth R₁ R₂ β p m φ v)

def Sigma2Elementary (R₁ R₂ : Ordinal.{0} → Ordinal.{0} → Prop) (α β : Ordinal.{0}) : Prop :=
  ∀ (p m n : Nat) (φ : Matrix ((p + m) + n)) (v : Fin p → Ordinal.{0}),
    TupleBelow α v → (sigma2Truth R₁ R₂ α p m n φ v ↔ sigma2Truth R₁ R₂ β p m n φ v)

theorem sigma1Elementary_refl (R₁ R₂ : Ordinal.{0} → Ordinal.{0} → Prop) (α : Ordinal.{0}) :
    Sigma1Elementary R₁ R₂ α α := fun _ _ _ _ _ => Iff.rfl

theorem sigma2Elementary_refl (R₁ R₂ : Ordinal.{0} → Ordinal.{0} → Prop) (α : Ordinal.{0}) :
    Sigma2Elementary R₁ R₂ α α := fun _ _ _ _ _ _ => Iff.rfl

theorem sigma2Truth_zero_universal (R₁ R₂ : Ordinal.{0} → Ordinal.{0} → Prop)
    (α : Ordinal.{0}) (p m : Nat) (φ : Matrix (p + m)) (v : Fin p → Ordinal.{0}) :
    sigma2Truth R₁ R₂ α p m 0 φ v ↔ sigma1Truth R₁ R₂ α p m φ v := by
  have append_empty (w : Fin (p + m) → Ordinal.{0}) : Fin.append w Fin.elim0 = w := by
    simpa only [Fin.append_elim0, Fin.cast_refl, Function.comp_id]
  constructor
  · rintro ⟨w, hw, h⟩
    refine ⟨w, hw, ?_⟩
    simpa only [append_empty] using h Fin.elim0 (fun i => Fin.elim0 i)
  · rintro ⟨w, hw, h⟩
    refine ⟨w, hw, ?_⟩
    intro z _
    have he : z = Fin.elim0 := funext (fun i => Fin.elim0 i)
    simpa only [he, append_empty] using h

theorem sigma2Elementary_sigma1 (R₁ R₂ : Ordinal.{0} → Ordinal.{0} → Prop)
    (α β : Ordinal.{0}) (h : Sigma2Elementary R₁ R₂ α β) : Sigma1Elementary R₁ R₂ α β := by
  intro p m φ v hv
  exact (sigma2Truth_zero_universal R₁ R₂ α p m φ v).symm.trans
    ((h p m 0 φ v hv).trans (sigma2Truth_zero_universal R₁ R₂ β p m φ v))

abbrev Level := Ordinal.{0} → Prop × Prop

def previousFirst (β : Ordinal.{0}) (previous : ∀ γ : Ordinal.{0}, γ < β → Level)
    (x y : Ordinal.{0}) : Prop :=
  if hy : y < β then (previous y hy x).1 else False

def previousSecond (β : Ordinal.{0}) (previous : ∀ γ : Ordinal.{0}, γ < β → Level)
    (x y : Ordinal.{0}) : Prop :=
  if hy : y < β then (previous y hy x).2 else False

/-- Both source relations at upper bound beta use only values at STRICTLY
smaller upper ordinals. Equality of endpoints is handled by elementarity. -/
def step (β : Ordinal.{0}) (previous : ∀ γ : Ordinal.{0}, γ < β → Level) : Level :=
  fun α => (α ≤ β ∧ Sigma1Elementary (previousFirst β previous) (previousSecond β previous) α β,
    α ≤ β ∧ Sigma2Elementary (previousFirst β previous) (previousSecond β previous) α β)

def family (β : Ordinal.{0}) : Level := Ordinal.lt_wf.fix step β

def R1 (α β : Ordinal.{0}) : Prop := (family β α).1

def R2 (α β : Ordinal.{0}) : Prop := (family β α).2

def prefixFirst (β x y : Ordinal.{0}) : Prop := y < β ∧ R1 x y

def prefixSecond (β x y : Ordinal.{0}) : Prop := y < β ∧ R2 x y

theorem previousFirst_family (β : Ordinal.{0}) :
    previousFirst β (fun γ _ => family γ) = prefixFirst β := by
  funext x y
  apply propext
  by_cases h : y < β <;> simp only [previousFirst, prefixFirst, R1, h, ↓reduceDIte,
    true_and, false_and]

theorem previousSecond_family (β : Ordinal.{0}) :
    previousSecond β (fun γ _ => family γ) = prefixSecond β := by
  funext x y
  apply propext
  by_cases h : y < β <;> simp only [previousSecond, prefixSecond, R2, h, ↓reduceDIte,
    true_and, false_and]

theorem family_eq (β : Ordinal.{0}) : family β = step β (fun γ _ => family γ) :=
  WellFounded.fix_eq Ordinal.lt_wf step β

/-- The actual first relation satisfies the source simultaneous initial-
segment Sigma1 equation, with no supplied relation or reflection witness. -/
theorem R1_iff (α β : Ordinal.{0}) : R1 α β ↔
    α ≤ β ∧ Sigma1Elementary (prefixFirst β) (prefixSecond β) α β := by
  unfold R1
  rw [family_eq, step, previousFirst_family, previousSecond_family]

/-- The actual second relation satisfies the source simultaneous initial-
segment Sigma2 equation, using the very same previously constructed pair. -/
theorem R2_iff (α β : Ordinal.{0}) : R2 α β ↔
    α ≤ β ∧ Sigma2Elementary (prefixFirst β) (prefixSecond β) α β := by
  unfold R2
  rw [family_eq, step, previousFirst_family, previousSecond_family]

theorem R1_le {α β : Ordinal.{0}} (h : R1 α β) : α ≤ β := (R1_iff α β).mp h |>.1

theorem R2_le {α β : Ordinal.{0}} (h : R2 α β) : α ≤ β := (R2_iff α β).mp h |>.1

theorem R1_refl (α : Ordinal.{0}) : R1 α α :=
  (R1_iff α α).mpr ⟨le_rfl, sigma1Elementary_refl _ _ α⟩

theorem R2_refl (α : Ordinal.{0}) : R2 α α :=
  (R2_iff α α).mpr ⟨le_rfl, sigma2Elementary_refl _ _ α⟩

theorem R2_R1 {α β : Ordinal.{0}} (h : R2 α β) : R1 α β := by
  have hs := (R2_iff α β).mp h
  exact (R1_iff α β).mpr ⟨hs.1, sigma2Elementary_sigma1 _ _ α β hs.2⟩

theorem prefixFirst_below {β x y : Ordinal.{0}} (hy : y < β) : prefixFirst β x y ↔ R1 x y :=
  and_iff_right hy

theorem prefixSecond_below {β x y : Ordinal.{0}} (hy : y < β) : prefixSecond β x y ↔ R2 x y :=
  and_iff_right hy

end Alexander313.Wilken.PureRelations
