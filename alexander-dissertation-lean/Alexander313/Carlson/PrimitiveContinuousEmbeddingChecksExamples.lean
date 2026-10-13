import Alexander313.Carlson.PrimitiveContinuousEmbeddingChecks

/-!
# Continuous embedding checker regressions

These kernel computations distinguish a continuous embedding from both a
covering and an isomorphism onto the whole target. They separately test exact
relation agreement, target-carrier inclusion, order, boundedness, and the two
correctness levels. Every encoded computation uses the original codec equations
before reducing its finite structural check.
-/

namespace Alexander313.Carlson.PrimitiveContinuousEmbeddingChecksExamples

open Encodable Finite PrimitivePatternCode PrimitiveEmbeddingChecks
open PrimitiveContinuousEmbeddingChecks

def one : PatternCode 1 where
  U := {0}
  r₁ i j := decide (i = j)
  r₂ i j := decide (i = j)

def two : PatternCode 2 where
  U := Finset.univ
  r₁ i j := decide (i = j)
  r₂ i j := decide (i = j)

def three : PatternCode 3 where
  U := Finset.univ
  r₁ i j := decide (i = j)
  r₂ i j := decide (i = j)

def five : PatternCode 5 where
  U := Finset.univ
  r₁ i j := decide (i = j)
  r₂ i j := decide (i = j)

/-- The image leaves an interior target point and contains the target maximum. -/
def spacedMap : Fin 2 → Fin 3 := fun i => if i = 0 then 0 else 2

/-- This image omits the target maximum. -/
def lowMap : Fin 2 → Fin 3 := fun i => if i = 0 then 0 else 1

def reverseMap : Fin 2 → Fin 2 := fun i => if i = 0 then 1 else 0

def sparse : PatternCode 2 := { two with U := {0} }

def trimmedSparse : PatternCode 2 where
  U := {0}
  r₁ i j := decide (i = 0 ∧ j = 0)
  r₂ i j := decide (i = 0 ∧ j = 0)

def sparseMap : Fin 2 → Fin 1 := fun _ => 0

def missingFirst : PatternCode 1 := { one with r₁ := fun _ _ => false }

def missingSecond : PatternCode 1 := { one with r₂ := fun _ _ => false }

def absentImageTarget : PatternCode 3 := { three with U := {0, 1} }

def absentImageMap : Fin 1 → Fin 3 := fun _ => 2

/-- The image consists of the old anchors 0, 2 and 4. -/
def anchorMap : Fin 3 → Fin 5 := fun i => if i = 0 then 0 else if i = 1 then 2 else 4

def firstViolation : PatternCode 5 :=
  { five with r₁ := fun i j => decide (i = j ∨ (i = 1 ∧ j = 3)) }

def secondViolation : PatternCode 5 :=
  { five with r₂ := fun i j => decide (i = j ∨ (i = 1 ∧ j = 3)) }

def crossingSource : PatternCode 3 where
  U := Finset.univ
  r₁ i j := decide (i = j ∨ (i = 1 ∧ j = 2))
  r₂ i j := decide (i = j ∨ (i = 1 ∧ j = 2))

/-- The old edge from 2 to 4 supplies both witnesses required by the
new edge from 1 to 3 crossing between image-anchor blocks. -/
def crossingTarget : PatternCode 5 where
  U := Finset.univ
  r₁ i j := decide (i = j ∨ (i = 2 ∧ j = 4) ∨ (i = 1 ∧ j = 3))
  r₂ i j := decide (i = j ∨ (i = 2 ∧ j = 4) ∨ (i = 1 ∧ j = 3))

def empty : PatternCode 0 where
  U := ∅
  r₁ i := Fin.elim0 i
  r₂ i := Fin.elim0 i

def emptyThree : PatternCode 3 := { three with U := ∅ }

def emptyMap (m : ℕ) : Fin 0 → Fin m := Fin.elim0

/-- An interior target point may be omitted by a continuous embedding. -/
theorem interior_point_regression :
    two.checkCoversInto three spacedMap = true ∧
      two.checkIso three spacedMap = false ∧
      two.checkEmbedding three spacedMap = true := by
  decide +kernel

/-- A covering with exact image relations can still fail continuity when
the target has a point above every image point. -/
theorem new_maximum_regression :
    two.checkCoversInto three lowMap = true ∧
      two.checkIso (imageCode two three lowMap) lowMap = true ∧
      two.checkEmbedding three lowMap = false := by
  decide +kernel

/-- Forming a restriction to the image cannot create a missing target point. -/
theorem image_membership_regression :
    one.checkIso (imageCode one absentImageTarget absentImageMap) absentImageMap = true ∧
      one.checkEmbedding absentImageTarget absentImageMap = false := by
  decide +kernel

/-- Exactness checks the reverse implication for each relation separately. -/
theorem relation_reflection_regression :
    missingFirst.checkCoversInto one id = true ∧
      missingFirst.checkEmbedding one id = false ∧
      missingSecond.checkCoversInto one id = true ∧
      missingSecond.checkEmbedding one id = false := by
  decide +kernel

theorem relation_preservation_regression :
    one.checkEmbedding missingFirst id = false ∧
      one.checkEmbedding missingSecond id = false := by
  decide +kernel

/-- The target image is the whole target, and its relations agree exactly;
reversing the two source points still fails the strict order condition. -/
theorem reversed_order_regression :
    (imageCode two two reverseMap).checkContinuous two = true ∧
      two.checkEmbedding two reverseMap = false := by
  decide +kernel

/-- Both source tables and injectivity matter only on the actual source
carrier. The total map may identify a carrier point with an off-carrier point. -/
theorem off_carrier_regression :
    sparse.checkEmbedding one sparseMap = true ∧
      trimmedSparse.checkEmbedding one sparseMap = true := by
  decide +kernel

/-- Exact image embedding succeeds here. Only first-level correctness
of the image's inclusion in the target fails. -/
theorem first_correctness_regression :
    three.checkIso (imageCode three firstViolation anchorMap) anchorMap = true ∧
      (imageCode three firstViolation anchorMap).checkKCorrect firstViolation .one = false ∧
      (imageCode three firstViolation anchorMap).checkKCorrect firstViolation .two = true ∧
      three.checkEmbedding firstViolation anchorMap = false := by
  decide +kernel

theorem second_correctness_regression :
    three.checkIso (imageCode three secondViolation anchorMap) anchorMap = true ∧
      (imageCode three secondViolation anchorMap).checkKCorrect secondViolation .one = true ∧
      (imageCode three secondViolation anchorMap).checkKCorrect secondViolation .two = false ∧
      three.checkEmbedding secondViolation anchorMap = false := by
  decide +kernel

/-- Both nonvacuous correctness checks accept when the old image edge is present. -/
theorem crossing_witness_regression :
    crossingSource.checkEmbedding crossingTarget anchorMap = true ∧
      (imageCode crossingSource crossingTarget anchorMap).checkKCorrect crossingTarget .one = true ∧
      (imageCode crossingSource crossingTarget anchorMap).checkKCorrect crossingTarget .two = true := by
  decide +kernel

theorem image_data_regression :
    (imageData (dataView two) (dataView three) (mapView spacedMap)).1 = {0, 2} ∧
      (imageData (dataView two) (dataView three) (mapView spacedMap)).2 = (dataView three).2 ∧
      decide (ContinuousEmbeddingData (dataView two) (dataView three) (mapView spacedMap)) = true ∧
      decide (ContinuousEmbeddingData (dataView two) (dataView three) (mapView lowMap)) = false := by
  decide +kernel

theorem encoded_regression :
    checkEmbedding 2 3 (encode two) (encode three) (encode spacedMap) = true ∧
      checkEmbedding 2 3 (encode two) (encode three) (encode lowMap) = false ∧
      checkEmbedding 2 1 (encode sparse) (encode one) (encode sparseMap) = true ∧
      checkEmbedding 3 5 (encode crossingSource) (encode crossingTarget) (encode anchorMap) = true ∧
      checkEmbedding 3 5 (encode three) (encode firstViolation) (encode anchorMap) = false ∧
      checkEmbedding 3 5 (encode three) (encode secondViolation) (encode anchorMap) = false := by
  simp only [checkEmbedding_encode]
  decide +kernel

/-- An empty image can be continuous only when the target carrier is empty. -/
theorem empty_regression :
    empty.checkEmbedding empty (emptyMap 0) = true ∧
      empty.checkEmbedding emptyThree (emptyMap 3) = true ∧
      empty.checkEmbedding three (emptyMap 3) = false := by
  decide +kernel

theorem encoded_empty_regression :
    checkEmbedding 0 0 (encode empty) (encode empty) (encode (emptyMap 0)) = true ∧
      checkEmbedding 0 3 (encode empty) (encode emptyThree) (encode (emptyMap 3)) = true ∧
      checkEmbedding 0 3 (encode empty) (encode three) (encode (emptyMap 3)) = false := by
  simp only [checkEmbedding_encode]
  decide +kernel

theorem malformed_source_rejects (n m d f : ℕ) :
    checkEmbedding n m 0 d f = false := by
  simp [checkEmbedding, checkWith, decodeData,
    PrimitiveRationalPresentation.decodeFields, PrimitiveRationalPresentation.decodeField]

theorem malformed_target_rejects :
    checkEmbedding 2 3 (encode two) 0 (encode spacedMap) = false := by
  have hzero : decodeData 3 0 = none := by
    simp [decodeData, PrimitiveRationalPresentation.decodeFields,
      PrimitiveRationalPresentation.decodeField]
  simp [checkEmbedding, checkWith, decodeData_encode, hzero]

/-- The list must have the correct dimension and its tags must appear
in the original position order. -/
theorem malformed_map_rejects :
    checkEmbedding 2 3 (encode two) (encode three) 0 = false ∧
      checkEmbedding 2 3 (encode two) (encode three)
        (encode ([Nat.pair 1 0, Nat.pair 0 2] : List ℕ)) = false := by
  simp only [checkEmbedding, checkWith, decodeData_encode]
  decide +kernel

/-- Even the value at source label 1, outside `sparse.U`, must decode
inside the target type before the structural test is allowed to run. -/
theorem off_carrier_map_bound_rejects :
    checkEmbedding 2 1 (encode sparse) (encode one)
        (encode ([Nat.pair 0 0, Nat.pair 1 1] : List ℕ)) = false := by
  simp only [checkEmbedding, checkWith, decodeData_encode]
  decide +kernel

theorem impossible_codomain_rejects :
    checkEmbedding 1 0 (encode one) (encode empty)
        (encode ([Nat.pair 0 0] : List ℕ)) = false := by
  simp only [checkEmbedding, checkWith, decodeData_encode]
  decide +kernel

/-- The same total machine returns the structural positive and negative
answers and rejects a malformed source without a decoding hypothesis. -/
theorem machine_regression : ∃ machine : Nat.Partrec.Code,
    machine.eval (Nat.pair 2 (Nat.pair 3 (Nat.pair (encode two)
      (Nat.pair (encode three) (encode spacedMap))))) = Part.some (encode true) ∧
    machine.eval (Nat.pair 2 (Nat.pair 3 (Nat.pair (encode two)
      (Nat.pair (encode three) (encode lowMap))))) = Part.some (encode false) ∧
    machine.eval (Nat.pair 2 (Nat.pair 3 (Nat.pair 0 (Nat.pair 0 0)))) =
      Part.some (encode false) := by
  obtain ⟨machine, hm⟩ := checkEmbedding_program
  refine ⟨machine, ?_, ?_, ?_⟩
  · simpa only [checkEmbedding_encode, interior_point_regression.2.2] using
      hm 2 3 (encode two) (encode three) (encode spacedMap)
  · simpa only [checkEmbedding_encode, new_maximum_regression.2.2] using
      hm 2 3 (encode two) (encode three) (encode lowMap)
  · simpa only [malformed_source_rejects 2 3 0 0] using hm 2 3 0 0 0

end Alexander313.Carlson.PrimitiveContinuousEmbeddingChecksExamples
