import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Common

/-!
# Carlson's covering relations of order two, pure case

T. J. Carlson, *Patterns of resemblance of order 2*, Ann. Pure Appl. Logic 158
(2009), Definitions 5.2–5.4, for the base structure `R₀ = (ORD, ≤)`. Here every
ordinal is indecomposable and every subset is closed (Carlson §3–§4 treat this
pure case as the motivating example), so a covering is an order embedding that
carries both relations forward.

`a ≤₁ b` holds when `a ≤ b` and every finite set `F` of points below `b` has a
copy map `f` that fixes `F ∩ [0, a)`, moves `F ∩ [a, b)` below `a`, is strictly
increasing on `F`, and carries the first and second relations forward. With
`X = F ∩ [0, a)`, `Y = F ∩ [a, b)` and `Ỹ = f[Y]` this is Carlson's condition:
`X < Ỹ` follows from monotonicity, and `X ∪ Ỹ` is a covering of `X ∪ Y`.

`a ≤₂ b` adds, in clause 1, that a copied point of `Y` which is `≤₁ b` lands
`≤₁ a`, and, in clause 2, that whenever finite coverings of a finite structure
`P` over a finite `X < a` occur cofinally below `a`, they occur cofinally below
`b`.

Both relations at upper point `b` read only the relations among points below
`b`, together with the first relation at `b` itself for clause 1 of `≤₂`. They
are therefore defined by well-founded recursion on `b`. No relation, copy or
elementarity hypothesis is an input.

The conditions are stated for an arbitrary linear order: Carlson also reads
Definition 5.3 inside abstract countable unions of patterns (Lemma 14.8).
-/

noncomputable section

namespace Alexander313.Carlson

/-- A copy map for the finite set `F` into the points below `a`: it fixes the
points of `F` below `a`, is strictly increasing on `F`, and carries both
relations forward. -/
def CoveringCopy {α : Type*} [LinearOrder α] (S₁ S₂ : α → α → Prop) (F : Finset α)
    (f : α → α) (a : α) : Prop :=
  (∀ z ∈ F, f z < a) ∧ (∀ z ∈ F, z < a → f z = z) ∧
  (∀ z ∈ F, ∀ w ∈ F, z < w → f z < f w) ∧
  (∀ z ∈ F, ∀ w ∈ F, S₁ z w → S₁ (f z) (f w)) ∧
  (∀ z ∈ F, ∀ w ∈ F, S₂ z w → S₂ (f z) (f w))

/-- Definition 5.3, first relation, read in the structure with relations
`S₁`, `S₂`. -/
def FirstCondition {α : Type*} [LinearOrder α] (S₁ S₂ : α → α → Prop) (a b : α) : Prop :=
  ∀ F : Finset α, (∀ z ∈ F, z < b) → ∃ f, CoveringCopy S₁ S₂ F f a

/-- Definition 5.3, clause 1 of the second relation: a copy which also sends
every point of `F ∩ [a, b)` satisfying `upper` to a point satisfying `lower`.
In use, `upper y` is `y ≤₁ b` and `lower y'` is `y' ≤₁ a`. -/
def LinkedCondition {α : Type*} [LinearOrder α] (S₁ S₂ : α → α → Prop)
    (upper lower : α → Prop) (a b : α) : Prop :=
  ∀ F : Finset α, (∀ z ∈ F, z < b) →
    ∃ f, CoveringCopy S₁ S₂ F f a ∧ ∀ z ∈ F, a ≤ z → upper z → lower (f z)

/-- The finite set `S` is a covering of the abstract finite structure `P` on
`Fin n`: its increasing enumeration carries both relations of `P` forward. -/
def CoversStructure {α : Type*} [LinearOrder α] (S₁ S₂ : α → α → Prop) (S : Finset α)
    {n : ℕ} (P₁ P₂ : Fin n → Fin n → Prop) : Prop :=
  ∃ h : S.card = n, ∀ i j,
    (P₁ i j → S₁ (S.orderEmbOfFin h i) (S.orderEmbOfFin h j)) ∧
    (P₂ i j → S₂ (S.orderEmbOfFin h i) (S.orderEmbOfFin h j))

/-- Cofinally many finite `Y` below `c` make `X ∪ Y` a covering of `P`. -/
def CofinalCopies {α : Type*} [LinearOrder α] (S₁ S₂ : α → α → Prop) (X : Finset α)
    {n : ℕ} (P₁ P₂ : Fin n → Fin n → Prop) (c : α) : Prop :=
  ∀ ξ, ξ < c → ∃ Y : Finset α, (∀ y ∈ Y, ξ < y ∧ y < c) ∧
    CoversStructure S₁ S₂ (X ∪ Y) P₁ P₂

/-- Definition 5.3, clause 2 of the second relation. -/
def CofinalCondition {α : Type*} [LinearOrder α] (S₁ S₂ : α → α → Prop) (a b : α) : Prop :=
  ∀ X : Finset α, (∀ x ∈ X, x < a) →
    ∀ (n : ℕ) (P₁ P₂ : Fin n → Fin n → Prop),
      CofinalCopies S₁ S₂ X P₁ P₂ a → CofinalCopies S₁ S₂ X P₁ P₂ b

/-- The first and second relation of every lower point to one upper point. -/
abbrev Level := Ordinal.{0} → Prop × Prop

def previousFirst (b : Ordinal.{0}) (previous : ∀ c : Ordinal.{0}, c < b → Level)
    (x y : Ordinal.{0}) : Prop :=
  if hy : y < b then (previous y hy x).1 else False

def previousSecond (b : Ordinal.{0}) (previous : ∀ c : Ordinal.{0}, c < b → Level)
    (x y : Ordinal.{0}) : Prop :=
  if hy : y < b then (previous y hy x).2 else False

/-- Both relations at upper point `b`, from the relations at smaller upper
points. Clause 1 of the second relation also reads the first relation at `b`,
which is computed in the same step. -/
def step (b : Ordinal.{0}) (previous : ∀ c : Ordinal.{0}, c < b → Level) : Level :=
  fun a =>
    (a ≤ b ∧ FirstCondition (previousFirst b previous) (previousSecond b previous) a b,
     a ≤ b ∧
      LinkedCondition (previousFirst b previous) (previousSecond b previous)
        (fun y => y ≤ b ∧
          FirstCondition (previousFirst b previous) (previousSecond b previous) y b)
        (fun y' => previousFirst b previous y' a) a b ∧
      CofinalCondition (previousFirst b previous) (previousSecond b previous) a b)

def family (b : Ordinal.{0}) : Level := Ordinal.lt_wf.fix step b

/-- Carlson's `≤₁` (Definition 5.4), pure case. -/
def R1 (a b : Ordinal.{0}) : Prop := (family b a).1

/-- Carlson's `≤₂` (Definition 5.4), pure case. -/
def R2 (a b : Ordinal.{0}) : Prop := (family b a).2

def prefixFirst (b x y : Ordinal.{0}) : Prop := y < b ∧ R1 x y

def prefixSecond (b x y : Ordinal.{0}) : Prop := y < b ∧ R2 x y

theorem previousFirst_family (b : Ordinal.{0}) :
    previousFirst b (fun c _ => family c) = prefixFirst b := by
  funext x y
  apply propext
  by_cases h : y < b <;> simp only [previousFirst, prefixFirst, R1, h, ↓reduceDIte,
    true_and, false_and]

theorem previousSecond_family (b : Ordinal.{0}) :
    previousSecond b (fun c _ => family c) = prefixSecond b := by
  funext x y
  apply propext
  by_cases h : y < b <;> simp only [previousSecond, prefixSecond, R2, h, ↓reduceDIte,
    true_and, false_and]

theorem family_eq (b : Ordinal.{0}) : family b = step b (fun c _ => family c) :=
  WellFounded.fix_eq Ordinal.lt_wf step b

/-- The defining equation of the first relation. -/
theorem R1_iff (a b : Ordinal.{0}) :
    R1 a b ↔ a ≤ b ∧ FirstCondition (prefixFirst b) (prefixSecond b) a b := by
  unfold R1
  rw [family_eq, step, previousFirst_family, previousSecond_family]

/-- The defining equation of the second relation. -/
theorem R2_iff (a b : Ordinal.{0}) :
    R2 a b ↔ a ≤ b ∧
      LinkedCondition (prefixFirst b) (prefixSecond b) (fun y => R1 y b)
        (fun y' => prefixFirst b y' a) a b ∧
      CofinalCondition (prefixFirst b) (prefixSecond b) a b := by
  have hfirst : (fun y => R1 y b) =
      fun y => y ≤ b ∧ FirstCondition (prefixFirst b) (prefixSecond b) y b :=
    funext fun y => propext (R1_iff y b)
  rw [hfirst]
  unfold R2
  rw [family_eq, step, previousFirst_family, previousSecond_family]

theorem prefixFirst_below {b x y : Ordinal.{0}} (hy : y < b) : prefixFirst b x y ↔ R1 x y :=
  and_iff_right hy

theorem prefixSecond_below {b x y : Ordinal.{0}} (hy : y < b) : prefixSecond b x y ↔ R2 x y :=
  and_iff_right hy

end Alexander313.Carlson
