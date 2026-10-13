import Alexander313.Carlson.PrimitiveFiniteExtrema
import Alexander313.Carlson.PrimitiveFiniteDataExamples
import Alexander313.Carlson.PrimitivePatternLifting
import Alexander313.Carlson.ComputableLiftingExamples

/-!
# Checks of the certified rational lifting computations

The affine parameters remain part of the machine input. The same family
therefore includes translations, order-reversing maps, and constant maps.
The construction is total on its finite data; pattern hypotheses govern
the separate semantic correctness statements.
-/

namespace Alexander313.Carlson.PrimitiveLiftingExamples

open Encodable Finite PrimitiveFiniteOperations PrimitiveRationalData
open Finite.RationalPresentation
open PrimitiveFiniteExtrema

/-- Defaults apply only to empty sets, and extrema use rational order. -/
theorem extrema_regression :
    minD (∅ : Finset ℚ) (7 / 3) = 7 / 3 ∧
    maxD (∅ : Finset ℚ) (7 / 3) = 7 / 3 ∧
    minD ({2} : Finset ℚ) 0 = 2 ∧ maxD ({-2} : Finset ℚ) 0 = -2 ∧
    minD ({-1, 0} : Finset ℚ) 5 = -1 ∧ maxD ({-1, 0} : Finset ℚ) 5 = 0 := by
  decide +kernel

/-- The stored first element need not be the finite minimum. -/
theorem extrema_code_order_regression :
    PrimitiveFiniteData.finsetView ({-1, 0} : Finset ℚ) = [0, -1] ∧
    minD ({-1, 0} : Finset ℚ) 5 = -1 :=
  ⟨PrimitiveFiniteDataExamples.encoded_order_regression.1, extrema_regression.2.2.2.2.1⟩

/-- One machine computes both extrema with the supplied default on every
typed input, including the empty set and sets ordered differently by codes. -/
theorem extrema_program_answers : ∃ c : Nat.Partrec.Code,
    c.eval (encode ((∅ : Finset ℚ), (7 / 3 : ℚ))) =
      Part.some (encode ((7 / 3 : ℚ), (7 / 3 : ℚ))) ∧
    c.eval (encode (({2} : Finset ℚ), (0 : ℚ))) =
      Part.some (encode ((2 : ℚ), (2 : ℚ))) ∧
    c.eval (encode (({-2} : Finset ℚ), (0 : ℚ))) =
      Part.some (encode ((-2 : ℚ), (-2 : ℚ))) ∧
    c.eval (encode (({-1, 0} : Finset ℚ), (5 : ℚ))) =
      Part.some (encode ((-1 : ℚ), (0 : ℚ))) := by
  have hp : Primrec (fun p : Finset ℚ × ℚ => (minD p.1 p.2, maxD p.1 p.2)) :=
    Primrec.pair (minD_primrec rat_le) (maxD_primrec rat_le)
  obtain ⟨c, hc⟩ := exists_program hp
  refine ⟨c, ?_, ?_, ?_, ?_⟩
  · simpa only [minD_empty, maxD_empty] using hc (∅, 7 / 3)
  · simpa only [minD_singleton, maxD_singleton] using hc ({2}, 0)
  · simpa only [minD_singleton, maxD_singleton] using hc ({-2}, 0)
  · simpa only [extrema_regression.2.2.2.2.1, extrema_regression.2.2.2.2.2]
      using hc ({-1, 0}, 5)

/-- A first-order family containing both injective and constant maps. -/
def affine (p : ℚ × ℚ) (x : ℚ) : ℚ := p.1 * x + p.2

theorem affine_primrec : Primrec₂ affine :=
  rat_add.comp (rat_mul.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
    (Primrec.snd.comp Primrec.fst)

/-- Both affine parameters are data, without an order-preservation assumption. -/
theorem affine_regression :
    affine (1, 1) (-1) = 0 ∧ affine (-2, 3) 2 = -1 ∧ affine (0, 3) (-99) = 3 := by
  decide +kernel

/-- Mapping removes off-carrier edges before translation or collapse. -/
theorem mapped_tables_regression :
    (ComputablePatternCandidateExamples.source.map (affine (1, 1))) =
      ⟨{0, 1}, {(0, 0), (0, 1), (1, 1)}, {(0, 0), (0, 1), (1, 1)}⟩ ∧
    (ComputablePatternCandidateExamples.source.map (affine (0, 3))) =
      ⟨{3}, {(3, 3)}, {(3, 3)}⟩ := by
  decide +kernel

/-- A single affine-map machine accepts translations and constant maps. -/
theorem mapped_tables_program : ∃ c : Nat.Partrec.Code,
    c.eval (encode ((1 : ℚ), (1 : ℚ))) = Part.some
      (encode (⟨{0, 1}, {(0, 0), (0, 1), (1, 1)},
        {(0, 0), (0, 1), (1, 1)}⟩ : RationalPresentation)) ∧
    c.eval (encode ((0 : ℚ), (3 : ℚ))) = Part.some
      (encode (⟨{3}, {(3, 3)}, {(3, 3)}⟩ : RationalPresentation)) := by
  obtain ⟨c, hc⟩ := PrimitivePatternLifting.map_program
    (Primrec.const ComputablePatternCandidateExamples.source) affine_primrec
  refine ⟨c, ?_, ?_⟩
  · simpa only [mapped_tables_regression.1] using hc (1, 1)
  · simpa only [mapped_tables_regression.2] using hc (0, 3)

/-- Query the candidate's incoming second relation while varying its source. -/
def incomingAnswer (S : RationalPresentation) : Bool :=
  decide ((liftingCandidate {0} S ComputablePatternCandidateExamples.target
    {-2, -3 / 2, -1, 0}).toStr.r₂ (-2) (-1))

theorem incomingAnswer_primrec : Primrec incomingAnswer := by
  have hC : Primrec (fun S : RationalPresentation =>
      liftingCandidate {0} S ComputablePatternCandidateExamples.target
        {-2, -3 / 2, -1, 0}) :=
    PrimitivePatternLifting.liftingCandidate_primrec (Primrec.const {0}) Primrec.id
      (Primrec.const ComputablePatternCandidateExamples.target)
      (Primrec.const {-2, -3 / 2, -1, 0})
  exact (PrimitiveRationalPresentation.relation₂_mem.comp hC
    (Primrec.const (-2, -1))).decide

/-- The intermediate witness may differ from the query but must be in the source. -/
theorem incoming_search_regression :
    incomingAnswer ComputablePatternCandidateExamples.incomingSource = true ∧
    incomingAnswer ComputablePatternCandidateExamples.outsiderSource = false := by
  decide +kernel

/-- The same machine accepts an in-carrier witness and rejects an outside witness. -/
theorem incoming_search_program : ∃ c : Nat.Partrec.Code,
    c.eval (encode ComputablePatternCandidateExamples.incomingSource) =
      Part.some (encode true) ∧
    c.eval (encode ComputablePatternCandidateExamples.outsiderSource) =
      Part.some (encode false) := by
  obtain ⟨c, hc⟩ := exists_program incomingAnswer_primrec
  refine ⟨c, ?_, ?_⟩
  · simpa only [incoming_search_regression.1]
      using hc ComputablePatternCandidateExamples.incomingSource
  · simpa only [incoming_search_regression.2]
      using hc ComputablePatternCandidateExamples.outsiderSource

/-- All finite presentations and both affine coefficients are coded inputs. -/
abbrev LiftInput := (ℚ × ℚ) × RationalPresentation × RationalPresentation ×
  RationalPresentation

def liftValue (p : LiftInput) : RationalPresentation :=
  liftTarget p.2.1 p.2.2.1 p.2.2.2 (affine p.1)

/-- The entire input tuple, including its affine coefficients, is uniform. -/
theorem liftValue_primrec : Primrec liftValue :=
  PrimitivePatternLifting.liftTarget_primrec
    (Primrec.fst.comp Primrec.snd)
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    (affine_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)

def translatedInput : LiftInput :=
  ((1, 1), ComputableLiftingExamples.base, ComputableLiftingExamples.extended,
    ComputableLiftingExamples.target)

def stationaryInput : LiftInput :=
  ((1, 1), ComputableLiftingExamples.base, ComputableLiftingExamples.base,
    ComputableLiftingExamples.target)

def emptyInput : LiftInput :=
  ((1, 0), ComputableLiftingExamples.empty, ComputableLiftingExamples.empty,
    ComputableLiftingExamples.empty)

/-- These data fail the reflexivity condition for a pattern. -/
def nonpattern : RationalPresentation := ⟨{0, 1}, ∅, ∅⟩

theorem nonpattern_not_pattern : ¬ nonpattern.toStr.IsPattern := by
  intro h
  exact (show ¬ nonpattern.toStr.r₁ 0 0 by decide +kernel)
    (h.refl₁ 0 (by decide +kernel))

def nonpatternInput : LiftInput :=
  ((0, 3), ComputableLiftingExamples.empty, ComputableLiftingExamples.empty, nonpattern)

/-- Exact target tables include a new rational point and discard outside edges. -/
theorem translated_lifting_regression :
    liftValue translatedInput =
      ⟨{0, 1 / 3, 1}, ComputableLiftingExamples.expectedEdges,
        ComputableLiftingExamples.expectedEdges⟩ := by
  decide +kernel

/-- Total computation includes stationary, empty, and nonpattern inputs. -/
theorem boundary_lifting_regression :
    liftValue stationaryInput =
      ⟨{0, 1}, {(0, 0), (0, 1), (1, 1)}, {(0, 0), (0, 1), (1, 1)}⟩ ∧
    liftValue emptyInput = ComputableLiftingExamples.empty ∧
    liftValue nonpatternInput = nonpattern := by
  decide +kernel

/-- One certified machine produces each full target under the unchanged
presentation encoding; its inputs include the varying affine coefficients. -/
theorem lifting_program_answers : ∃ c : Nat.Partrec.Code,
    c.eval (encode translatedInput) = Part.some
      (encode (⟨{0, 1 / 3, 1}, ComputableLiftingExamples.expectedEdges,
        ComputableLiftingExamples.expectedEdges⟩ : RationalPresentation)) ∧
    c.eval (encode stationaryInput) = Part.some
      (encode (⟨{0, 1}, {(0, 0), (0, 1), (1, 1)},
        {(0, 0), (0, 1), (1, 1)}⟩ : RationalPresentation)) ∧
    c.eval (encode emptyInput) = Part.some (encode ComputableLiftingExamples.empty) ∧
    c.eval (encode nonpatternInput) = Part.some (encode nonpattern) := by
  obtain ⟨c, hc⟩ := exists_program liftValue_primrec
  refine ⟨c, ?_, ?_, ?_, ?_⟩
  · simpa only [translated_lifting_regression] using hc translatedInput
  · simpa only [boundary_lifting_regression.1] using hc stationaryInput
  · simpa only [boundary_lifting_regression.2.1] using hc emptyInput
  · simpa only [boundary_lifting_regression.2.2] using hc nonpatternInput

end Alexander313.Carlson.PrimitiveLiftingExamples
