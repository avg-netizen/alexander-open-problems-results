import Alexander313.Carlson.FinitePatterns
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Equiv.Finset

/-!
# Executable finite presentations on rational labels

A `RationalPresentation` consists of a finite rational carrier and two
finite sets of relation edges. Its interpretation has executable relation
deciders, even though the ambient type `ℚ` is infinite. No pattern axioms
are built into the presentation format.

`ofDecidable` records a structure's relations on its carrier. It discards
off-carrier relation values and therefore recovers the structure up to an
identity isomorphism, rather than equality of structure records. The
classical `encode` convenience operation has the same specification and
is kept separate from the executable checking operations.

`checkIso` checks a supplied map from a finite Boolean pattern code into a
rational presentation. All quantifiers in `Str.IsIso` range over the
finite source type or finite carriers; no decision procedure on arbitrary
propositions over all rational numbers is required.
-/

namespace Alexander313.Carlson.Finite

/-- Finite rational labels and finite edge sets for the two relations. -/
structure RationalPresentation where
  U : Finset ℚ
  r₁ : Finset (ℚ × ℚ)
  r₂ : Finset (ℚ × ℚ)
  deriving DecidableEq, Encodable

namespace RationalPresentation

/-- Interpret a stored relation edge by finite-set membership. -/
def toStr (P : RationalPresentation) : Str ℚ where
  U := P.U
  r₁ x y := (x, y) ∈ P.r₁
  r₂ x y := (x, y) ∈ P.r₂

@[simp] theorem toStr_U (P : RationalPresentation) : P.toStr.U = P.U := rfl

@[simp] theorem toStr_r₁ (P : RationalPresentation) (x y : ℚ) :
    P.toStr.r₁ x y ↔ (x, y) ∈ P.r₁ := Iff.rfl

@[simp] theorem toStr_r₂ (P : RationalPresentation) (x y : ℚ) :
    P.toStr.r₂ x y ↔ (x, y) ∈ P.r₂ := Iff.rfl

instance instDecidableRelToStrOne (P : RationalPresentation) :
    DecidableRel P.toStr.r₁ :=
  fun x y => inferInstanceAs (Decidable ((x, y) ∈ P.r₁))

instance instDecidableRelToStrTwo (P : RationalPresentation) :
    DecidableRel P.toStr.r₂ :=
  fun x y => inferInstanceAs (Decidable ((x, y) ∈ P.r₂))

/-- Record exactly the relation edges whose endpoints lie in the carrier,
using the supplied executable relation deciders. -/
def ofDecidable (P : Str ℚ) [DecidableRel P.r₁] [DecidableRel P.r₂] :
    RationalPresentation where
  U := P.U
  r₁ := (P.U ×ˢ P.U).filter (fun xy => P.r₁ xy.1 xy.2)
  r₂ := (P.U ×ˢ P.U).filter (fun xy => P.r₂ xy.1 xy.2)

@[simp] theorem ofDecidable_U (P : Str ℚ) [DecidableRel P.r₁] [DecidableRel P.r₂] :
    (ofDecidable P).U = P.U := rfl

/-- The presented relation agrees on the carrier and is false outside it. -/
@[simp] theorem toStr_ofDecidable_r₁ (P : Str ℚ)
    [DecidableRel P.r₁] [DecidableRel P.r₂] (x y : ℚ) :
    (ofDecidable P).toStr.r₁ x y ↔ x ∈ P.U ∧ y ∈ P.U ∧ P.r₁ x y := by
  simp [toStr, ofDecidable, and_assoc]

/-- The presented relation agrees on the carrier and is false outside it. -/
@[simp] theorem toStr_ofDecidable_r₂ (P : Str ℚ)
    [DecidableRel P.r₁] [DecidableRel P.r₂] (x y : ℚ) :
    (ofDecidable P).toStr.r₂ x y ↔ x ∈ P.U ∧ y ∈ P.U ∧ P.r₂ x y := by
  simp [toStr, ofDecidable, and_assoc]

/-- Removing off-carrier relation values preserves the finite structure
along the identity map. -/
theorem ofDecidable_iso (P : Str ℚ) [DecidableRel P.r₁] [DecidableRel P.r₂] :
    Str.IsIso P (ofDecidable P).toStr id := by
  refine ⟨Finset.image_id, fun _ _ _ _ h => h, ?_⟩
  intro x hx y hy
  simp only [toStr, ofDecidable, id_eq, Finset.mem_filter, Finset.mem_product,
    hx, hy, true_and]

/-- Classical presentation of an arbitrary rational structure. This is
used only in completeness arguments; executable checks use stored edges. -/
noncomputable def encode (P : Str ℚ) : RationalPresentation := by
  classical
  exact ofDecidable P

@[simp] theorem encode_U (P : Str ℚ) : (encode P).U = P.U := rfl

/-- Every rational structure has a finite-edge presentation with the
same carrier and the same induced relations on that carrier. -/
theorem presentation_iso (P : Str ℚ) : Str.IsIso P (encode P).toStr id := by
  classical
  exact ofDecidable_iso P

/-- Check a supplied finite labeling against the claimed rational
carrier, order, and both relation tables. -/
def checkIso {n : ℕ} (C : PatternCode n) (labels : Fin n → ℚ)
    (P : RationalPresentation) : Bool :=
  decide (Str.IsIso C.toStr P.toStr labels)

@[simp] theorem checkIso_eq_true {n : ℕ} (C : PatternCode n)
    (labels : Fin n → ℚ) (P : RationalPresentation) :
    checkIso C labels P = true ↔ Str.IsIso C.toStr P.toStr labels := by
  simp [checkIso]

end RationalPresentation
end Alexander313.Carlson.Finite
