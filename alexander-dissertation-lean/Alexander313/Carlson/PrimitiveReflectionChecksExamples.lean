import Alexander313.Carlson.PrimitiveReflectionChecks

/-!
# Kernel regressions for reflection hypothesis checking

The positive examples copy a point down from 2 to 1, or up from 1 to 3.
Negative examples exercise the original pattern requirement, the two relation
levels, interval endpoints, nonempty blocks, placement below an anchor,
matching, and the nontrivial extension requirement. Raw tests retain the
original codecs and reject malformed records, carriers, anchors and maps.
-/

namespace Alexander313.Carlson.PrimitiveReflectionChecksExamples

open Encodable Finite PrimitivePatternCode PrimitiveEmbeddingChecks PrimitiveReflectionChecks

def base : PatternCode 5 where
  U := {0, 2, 4}
  r₁ i j := decide (i ≤ j)
  r₂ i j := decide (i ≤ j)

def inserted : PatternCode 5 := { base with U := {0, 1, 2, 4} }

def firstOnly : PatternCode 5 := { base with r₂ := fun i j => decide (i = j) }

def badPattern : PatternCode 5 := { base with r₁ := fun _ _ => false }

def downMap : Fin 5 → Fin 5 := fun _ => 2

def upMap : Fin 5 → Fin 5 := fun i => if i = 3 then 1 else i

/-- Values outside the one-point copied carrier need not preserve order. -/
def offCarrierMap : Fin 5 → Fin 5 := fun i => if i = 3 then 1 else 4

def toTop : Fin 5 → Fin 5 := fun _ => 4

def toZero : Fin 5 → Fin 5 := fun _ => 0

theorem downward_positive :
    base.checkDownward .one 2 4 {2} {1} downMap = true ∧
      base.checkDownward .two 2 4 {2} {1} downMap = true := by
  decide +kernel

/-- A first-level edge does not suffice for second-level downward reflection. -/
theorem downward_level_regression :
    firstOnly.checkDownward .one 2 4 {2} {1} downMap = true ∧
      firstOnly.checkDownward .two 2 4 {2} {1} downMap = false := by
  decide +kernel

/-- These failures retain the claimed matching, isolating the block restrictions. -/
theorem downward_block_regression :
    base.checkDownward .one 2 4 ∅ ∅ downMap = false ∧
      base.checkDownward .one 2 4 {4} {1} toTop = false ∧
      base.checkDownward .one 2 4 {0} {1} toZero = false := by
  decide +kernel

theorem downward_hypotheses_regression :
    badPattern.checkDownward .two 2 4 {2} {1} downMap = false ∧
      base.checkDownward .one 2 4 {2} {3} downMap = false ∧
      base.checkDownward .one 2 4 {2} {1} toTop = false ∧
      base.checkDownward .one 2 2 {2} {1} downMap = false := by
  decide +kernel

theorem upward_positive :
    base.checkUpward inserted 2 4 {3} upMap = true ∧
      base.checkUpward inserted 2 4 {3} offCarrierMap = true := by
  decide +kernel

/-- An empty extension, an incorrect gap, an incorrect image and a missing
second-level anchor edge each cause rejection. -/
theorem upward_hypotheses_regression :
    base.checkUpward base 2 4 ∅ upMap = false ∧
      base.checkUpward inserted 2 4 {1} id = false ∧
      base.checkUpward inserted 2 4 {3} id = false ∧
      firstOnly.checkUpward { inserted with r₂ := fun i j => decide (i = j) }
        2 4 {3} upMap = false ∧
      base.checkUpward badPattern 2 4 {3} upMap = false := by
  decide +kernel

theorem matching_order_regression :
    decide (MapMonoData {0, 1} [2, 3]) = true ∧
      decide (MapMonoData {0, 1} [3, 2]) = false ∧
      decide (MapMonoData {1} [4, 2, 0]) = true := by
  decide +kernel

theorem placement_regression :
    decide (PlacementData (dataView base) {1} 2) = true ∧
      decide (PlacementData (dataView base) {3} 4) = true ∧
      decide (PlacementData (dataView base) {1} 4) = false ∧
      decide (PlacementData (dataView base) {2} 4) = false := by
  decide +kernel

theorem data_regression :
    decide (DownwardData (dataView base) false 2 4 {2} {1} (mapView downMap)) = true ∧
      decide (DownwardData (dataView firstOnly) true 2 4 {2} {1} (mapView downMap)) = false ∧
      decide (UpwardData (dataView base) (dataView inserted) 2 4 {3} (mapView upMap)) = true := by
  decide +kernel

theorem encoded_downward_regression :
    checkDownward false 5 (encode base) (encode (2 : Fin 5)) (encode (4 : Fin 5))
      (encode ({2} : Finset (Fin 5))) (encode ({1} : Finset (Fin 5))) (encode downMap) = true ∧
    checkDownward true 5 (encode firstOnly) (encode (2 : Fin 5)) (encode (4 : Fin 5))
      (encode ({2} : Finset (Fin 5))) (encode ({1} : Finset (Fin 5))) (encode downMap) = false := by
  simp only [checkDownward_encode, PrimitiveContinuityChecks.level]
  decide +kernel

theorem encoded_upward_regression :
    checkUpward 5 (encode base) (encode inserted) (encode (2 : Fin 5)) (encode (4 : Fin 5))
      (encode ({3} : Finset (Fin 5))) (encode upMap) = true ∧
    checkUpward 5 (encode base) (encode base) (encode (2 : Fin 5)) (encode (4 : Fin 5))
      (encode (∅ : Finset (Fin 5))) (encode upMap) = false := by
  simp only [checkUpward_encode]
  decide +kernel

/-- Constructor rejection is independent of every other raw parameter. -/
theorem malformed_source_rejects (k : Bool) (n a b x s f d : ℕ) :
    checkDownward k n 0 a b x s f = false ∧ checkUpward n 0 d a b s f = false := by
  simp [checkDownward, checkUpward, decodeData, PrimitiveRationalPresentation.decodeFields,
    PrimitiveRationalPresentation.decodeField]

theorem malformed_target_rejects (n c a b s f : ℕ) :
    checkUpward n c 0 a b s f = false := by
  simp [checkUpward, decodeData, PrimitiveRationalPresentation.decodeFields,
    PrimitiveRationalPresentation.decodeField]

/-- An out-of-range anchor rejects before the structural predicates are tested. -/
theorem out_of_range_anchor_rejects (k : Bool) (n c d a b x s f : ℕ) (ha : n ≤ a) :
    checkDownward k n c a b x s f = false ∧ checkUpward n c d a b s f = false := by
  have hP : decodeParameters n a b s f = none := by
    simp [decodeParameters, decodeLabel, Nat.not_lt.mpr ha]
  simp [checkDownward, checkUpward, hP]

/-- Duplicate source-block labels cannot be silently turned into a valid set. -/
theorem duplicate_block_rejects :
    checkDownward false 5 (encode base) 2 4 (encode ([2, 2] : List (Fin 5)))
      (encode ({1} : Finset (Fin 5))) (encode downMap) = false := by
  have hX : decodeCarrier 5 (encode ([2, 2] : List (Fin 5))) = none := by
    decide +kernel
  unfold checkDownward
  rw [hX]
  simp

/-- An empty function code is malformed at nonzero dimension, including at
labels the reflection predicate itself would never inspect. -/
theorem malformed_map_rejects :
    checkDownward false 5 (encode base) 2 4 (encode ({2} : Finset (Fin 5)))
      (encode ({1} : Finset (Fin 5))) 0 = false ∧
    checkUpward 5 (encode base) (encode inserted) 2 4
      (encode ({3} : Finset (Fin 5))) 0 = false := by
  have hF : decodeMap 5 5 0 = none := by decide +kernel
  simp [checkDownward, checkUpward, decodeParameters, hF]

def empty : PatternCode 0 where
  U := ∅
  r₁ i := Fin.elim0 i
  r₂ i := Fin.elim0 i

def emptyMap : Fin 0 → Fin 0 := Fin.elim0

/-- Empty pattern and map codes are valid, but there is no anchor in `Fin 0`. -/
theorem empty_regression :
    checkDownward false 0 (encode empty) 0 0 (encode (∅ : Finset (Fin 0)))
      (encode (∅ : Finset (Fin 0))) (encode emptyMap) = false ∧
    checkUpward 0 (encode empty) (encode empty) 0 0
      (encode (∅ : Finset (Fin 0))) (encode emptyMap) = false := by
  exact out_of_range_anchor_rejects false 0 (encode empty) (encode empty) 0 0
    (encode (∅ : Finset (Fin 0))) (encode (∅ : Finset (Fin 0))) (encode emptyMap) le_rfl

theorem downward_machine_regression : ∃ machine : Nat.Partrec.Code,
    machine.eval (encode ((5, encode base, encode (2 : Fin 5), encode (4 : Fin 5),
      encode ({2} : Finset (Fin 5)), encode ({1} : Finset (Fin 5)), encode downMap) : RawInputs)) =
        Part.some (encode true) ∧
    machine.eval (encode ((5, 0, 0, 0, 0, 0, 0) : RawInputs)) = Part.some (encode false) := by
  simp only [Encodable.encode_prod_val, Encodable.encode_nat]
  obtain ⟨machine, hm⟩ := checkDownward_program false
  refine ⟨machine, ?_, ?_⟩
  · simpa only [encoded_downward_regression.1] using
      hm 5 (encode base) (encode (2 : Fin 5)) (encode (4 : Fin 5))
        (encode ({2} : Finset (Fin 5))) (encode ({1} : Finset (Fin 5))) (encode downMap)
  · simpa only [(malformed_source_rejects false 5 0 0 0 0 0 0).1] using hm 5 0 0 0 0 0 0

theorem upward_machine_regression : ∃ machine : Nat.Partrec.Code,
    machine.eval (encode ((5, encode base, encode inserted, encode (2 : Fin 5),
      encode (4 : Fin 5), encode ({3} : Finset (Fin 5)), encode upMap) : RawInputs)) =
        Part.some (encode true) ∧
    machine.eval (encode ((5, 0, 0, 0, 0, 0, 0) : RawInputs)) = Part.some (encode false) := by
  simp only [Encodable.encode_prod_val, Encodable.encode_nat]
  obtain ⟨machine, hm⟩ := checkUpward_program
  refine ⟨machine, ?_, ?_⟩
  · simpa only [encoded_upward_regression.1] using
      hm 5 (encode base) (encode inserted) (encode (2 : Fin 5)) (encode (4 : Fin 5))
        (encode ({3} : Finset (Fin 5))) (encode upMap)
  · simpa only [(malformed_source_rejects false 5 0 0 0 0 0 0).2] using hm 5 0 0 0 0 0 0

end Alexander313.Carlson.PrimitiveReflectionChecksExamples
