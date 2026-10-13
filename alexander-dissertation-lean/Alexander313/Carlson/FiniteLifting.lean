import Alexander313.Carlson.FinitePatterns
import Alexander313.Carlson.PatternLifting
import Alexander313.Carlson.PatternTransport

/-!
# Executable finite lifting and minimality checks

Arithmetic liftings, pattern liftings and continuous embeddings have
computable decision procedures over finite ambient orders with decidable
relation tables. These procedures check the fields of the existing
Carlson predicates directly.

Minimality quantifies over arbitrary propositional structures in its
original definition. On `Fin m`, every such competitor has an exact
Boolean-table presentation. `PatternCode.MinimalCriterion` consequently
replaces that quantifier with exhaustive finite enumeration of table
codes and total maps. Its equivalence with the original `IsMinimal` is
used only to justify the computable decision procedure: the executable
check never calls the proof-side classical encoding operation.

The target carrier is fixed exactly as in `PatternLifting.IsMinimal`.
These checks decide lifting and minimality inside the supplied finite
ambient orders; they do not assert that a lifting exists on an arbitrary
finite carrier.
-/

namespace Alexander313.Carlson

variable {α β : Type*} [LinearOrder α] [LinearOrder β]

namespace ArithmeticLifting

/-- The arithmetic lifting fields are a finite conjunction of decidable
conditions when both ambient orders are finite. -/
theorem iff_conditions (A Aplus : Finset α) (B Bplus : Finset β) (h f : α → β) :
    ArithmeticLifting A Aplus B Bplus h f ↔
    (A ⊆ Aplus) ∧
    (∀ x ∈ Aplus, ∃ a ∈ A, x ≤ a) ∧
    (∀ x ∈ A, ∀ y ∈ A, x < y → h x < h y) ∧
    (∀ x ∈ A, h x ∈ B) ∧
    (B ⊆ Bplus) ∧
    (∀ x ∈ Aplus, ∀ y ∈ Aplus, x < y → f x < f y) ∧
    (∀ x ∈ Aplus, f x ∈ Bplus) ∧
    (∀ x ∈ A, f x = h x) ∧
    (Bplus = B ∪ Aplus.image f) ∧
    (∀ a x, x ∈ Aplus → Str.JustBelow A a x → Str.JustBelow B (h a) (f x)) := by
  constructor
  · intro D
    exact ⟨D.source_sub, D.source_bounded, D.base_mono, D.base_mem, D.target_sub,
      D.mono, D.mem, D.agrees, D.carrier_eq, D.justBelow⟩
  · rintro ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀⟩
    exact ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀⟩

set_option synthInstance.maxSize 2048 in
instance instDecidable [Fintype α] [Fintype β]
    (A Aplus : Finset α) (B Bplus : Finset β) (h f : α → β) :
    Decidable (ArithmeticLifting A Aplus B Bplus h f) :=
  decidable_of_iff _ (iff_conditions A Aplus B Bplus h f).symm

end ArithmeticLifting

namespace PatternLifting

/-- Unpack pattern lifting into the original finite structural conditions. -/
theorem iff_conditions (P Pplus : Str α) (Q Qplus : Str β) (h f : α → β) :
    PatternLifting P Pplus Q Qplus h f ↔
    Pplus.IsPattern ∧ Qplus.IsPattern ∧
    Str.IsSub P Pplus ∧ Str.IsSub Q Qplus ∧
    ArithmeticLifting P.U Pplus.U Q.U Qplus.U h f ∧
    (∀ x ∈ Pplus.U, ∀ y ∈ Pplus.U,
      (Pplus.r₁ x y ↔ Qplus.r₁ (f x) (f y)) ∧
      (Pplus.r₂ x y ↔ Qplus.r₂ (f x) (f y))) := by
  constructor
  · intro D
    exact ⟨D.source_pattern, D.target_pattern, D.source_sub, D.target_sub,
      D.arithmetic, D.relations⟩
  · rintro ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩
    exact ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩

set_option synthInstance.maxSize 2048 in
instance instDecidable [Fintype α] [Fintype β]
    (P Pplus : Str α) (Q Qplus : Str β) (h f : α → β)
    [DecidableRel P.r₁] [DecidableRel P.r₂]
    [DecidableRel Pplus.r₁] [DecidableRel Pplus.r₂]
    [DecidableRel Q.r₁] [DecidableRel Q.r₂]
    [DecidableRel Qplus.r₁] [DecidableRel Qplus.r₂] :
    Decidable (PatternLifting P Pplus Q Qplus h f) :=
  decidable_of_iff _ (iff_conditions P Pplus Q Qplus h f).symm

end PatternLifting

namespace Str

instance instDecidableContinuousEmbedding [Fintype α] [Fintype β]
    (P : Str α) (Q : Str β) (h : α → β)
    [DecidableRel P.r₁] [DecidableRel P.r₂] [DecidableRel Q.r₁] [DecidableRel Q.r₂] :
    Decidable (ContinuousEmbedding P Q h) := by
  unfold ContinuousEmbedding
  dsimp only [restrict]
  infer_instance

end Str

namespace Finite.PatternCode

variable {n m : ℕ}

/-- Exhaustive finite criterion for minimality on the supplied target
carrier. Both relation tables and all total competitor maps are checked. -/
def MinimalCriterion (P Pplus : PatternCode n) (Q Qplus : PatternCode m)
    (h : Fin n → Fin m) : Prop :=
  ∀ (S : PatternCode m) (g : Fin n → Fin m), S.U = Qplus.U →
    PatternLifting P.toStr Pplus.toStr Q.toStr S.toStr h g →
    Str.CoversInto Qplus.toStr S.toStr id

instance instDecidableMinimalCriterion
    (P Pplus : PatternCode n) (Q Qplus : PatternCode m) (h : Fin n → Fin m) :
    Decidable (MinimalCriterion P Pplus Q Qplus h) := by
  unfold MinimalCriterion
  infer_instance

/-- Every arbitrary propositional competitor has an exact finite code,
so finite enumeration is both sound and complete for original minimality. -/
theorem minimalCriterion_iff
    (P Pplus : PatternCode n) (Q Qplus : PatternCode m) (h : Fin n → Fin m) :
    MinimalCriterion P Pplus Q Qplus h ↔
      PatternLifting.IsMinimal P.toStr Pplus.toStr Q.toStr Qplus.toStr h := by
  constructor
  · intro hmin S g hS E
    have hU : (encode S).U = Qplus.U := by
      change (encode S).toStr.U = Qplus.toStr.U
      simpa only [toStr_encode] using hS
    have hE : PatternLifting P.toStr Pplus.toStr Q.toStr (encode S).toStr h g := by
      simpa only [toStr_encode] using E
    have hc := hmin (encode S) g hU hE
    simpa only [toStr_encode] using hc
  · intro hmin S g hS E
    exact hmin S.toStr g hS E

/-- This decision procedure enumerates finite Boolean tables. The
classical presentation in `minimalCriterion_iff` occurs only in its proof. -/
instance instDecidableIsMinimal
    (P Pplus : PatternCode n) (Q Qplus : PatternCode m) (h : Fin n → Fin m) :
    Decidable (PatternLifting.IsMinimal P.toStr Pplus.toStr Q.toStr Qplus.toStr h) :=
  decidable_of_iff _ (minimalCriterion_iff P Pplus Q Qplus h)

/-- Check all arithmetic lifting, patternhood and exact relation conditions. -/
def checkLifting (P Pplus : PatternCode n) (Q Qplus : PatternCode m)
    (h f : Fin n → Fin m) : Bool :=
  decide (PatternLifting P.toStr Pplus.toStr Q.toStr Qplus.toStr h f)

@[simp] theorem checkLifting_eq_true
    (P Pplus : PatternCode n) (Q Qplus : PatternCode m) (h f : Fin n → Fin m) :
    checkLifting P Pplus Q Qplus h f = true ↔
      PatternLifting P.toStr Pplus.toStr Q.toStr Qplus.toStr h f := by
  simp [checkLifting]

/-- Check exact embedding into the target and continuity of its image. -/
def checkEmbedding (P : PatternCode n) (Q : PatternCode m) (h : Fin n → Fin m) : Bool :=
  decide (Str.ContinuousEmbedding P.toStr Q.toStr h)

@[simp] theorem checkEmbedding_eq_true
    (P : PatternCode n) (Q : PatternCode m) (h : Fin n → Fin m) :
    checkEmbedding P Q h = true ↔ Str.ContinuousEmbedding P.toStr Q.toStr h := by
  simp [checkEmbedding]

/-- Check original fixed-carrier minimality by exhaustive finite comparison.
As in `IsMinimal`, whether the supplied candidate is itself a lifting is
the separate condition checked by `checkLifting`. -/
def checkMinimal (P Pplus : PatternCode n) (Q Qplus : PatternCode m)
    (h : Fin n → Fin m) : Bool :=
  decide (PatternLifting.IsMinimal P.toStr Pplus.toStr Q.toStr Qplus.toStr h)

@[simp] theorem checkMinimal_eq_true
    (P Pplus : PatternCode n) (Q Qplus : PatternCode m) (h : Fin n → Fin m) :
    checkMinimal P Pplus Q Qplus h = true ↔
      PatternLifting.IsMinimal P.toStr Pplus.toStr Q.toStr Qplus.toStr h := by
  simp [checkMinimal]

end Finite.PatternCode

end Alexander313.Carlson
