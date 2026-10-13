import Alexander313.Carlson.PrimitiveContinuityChecks

/-!
# Regressions for finite continuity and extension checking

These kernel computations exercise added points, old anchors, least-point
witnesses, no-new-maximum requirements, and independent failures of the
two relation levels. Encoded tests use the proved codec equations to
avoid expanding unnecessarily large natural-number table encodings.
-/

namespace Alexander313.Carlson.PrimitiveContinuityChecksExamples

open Encodable Finite PrimitivePatternCode PrimitiveContinuityChecks

def old : PatternCode 5 where
  U := {0, 2, 4}
  r₁ i j := decide (i = j)
  r₂ i j := decide (i = j)

def inserted : PatternCode 5 := { old with U := {0, 1, 2, 4} }

def twoGaps : PatternCode 5 := { old with U := {0, 1, 2, 3, 4} }

def lowOld : PatternCode 5 := { old with U := {0, 2} }

def highNew : PatternCode 5 := { old with U := {0, 2, 4} }

def missingFirst : PatternCode 5 := { inserted with r₁ := fun _ _ => false }

def missingSecond : PatternCode 5 := { inserted with r₂ := fun _ _ => false }

/-- The old edge from 2 to 4 witnesses correctness of a new edge from
1 to 3, whose least old upper bounds are 2 and 4. -/
def crossingOld : PatternCode 5 where
  U := {0, 2, 4}
  r₁ i j := decide (i = j ∨ (i = 2 ∧ j = 4))
  r₂ i j := decide (i = j ∨ (i = 2 ∧ j = 4))

def crossingNew : PatternCode 5 where
  U := {0, 1, 2, 3, 4}
  r₁ i j := decide (i = j ∨ (i = 2 ∧ j = 4) ∨ (i = 1 ∧ j = 3))
  r₂ i j := decide (i = j ∨ (i = 2 ∧ j = 4) ∨ (i = 1 ∧ j = 3))

/-- Removing the old first-level witness preserves substructure when
the same old edge is removed from both stored first tables. -/
def firstBadOld : PatternCode 5 :=
  { crossingOld with r₁ := fun i j => decide (i = j) }

def firstBadNew : PatternCode 5 :=
  { crossingNew with r₁ := fun i j => decide (i = j ∨ (i = 1 ∧ j = 3)) }

def secondBadOld : PatternCode 5 :=
  { crossingOld with r₂ := fun i j => decide (i = j) }

def secondBadNew : PatternCode 5 :=
  { crossingNew with r₂ := fun i j => decide (i = j ∨ (i = 1 ∧ j = 3)) }

def empty : PatternCode 0 where
  U := ∅
  r₁ i := Fin.elim0 i
  r₂ i := Fin.elim0 i

theorem least_point_regression :
    decide (LeastGEData {0, 2, 4} 1 2) = true ∧
      decide (LeastGEData {0, 2, 4} 1 4) = false ∧
      decide (LeastGEData {0, 2, 4} 5 4) = false ∧
      decide (LeastGEData {0, 2, 4} 1 1) = false := by
  decide +kernel

theorem just_below_regression :
    decide (JustBelowData {0, 2, 4} 2 1) = true ∧
      decide (JustBelowData {0, 2, 4} 4 1) = false ∧
      decide (JustBelowData {0, 2, 4} 3 1) = false ∧
      decide (JustBelowData {0, 2, 4} 2 0) = false := by
  decide +kernel

/-- No-new-point, missing-anchor, wrong-anchor and separated-gap cases
all reject, despite the unchanged old relation tables. -/
theorem extension_at_regression :
    old.checkExtensionAt inserted 2 = true ∧
      old.checkExtensionAt old 2 = false ∧
      old.checkExtensionAt inserted 0 = false ∧
      old.checkExtensionAt inserted 3 = false ∧
      old.checkExtensionAt inserted 4 = false ∧
      old.checkExtensionAt twoGaps 2 = false := by
  decide +kernel

theorem substructure_regression :
    old.checkExtensionAt missingFirst 2 = false ∧
      old.checkExtensionAt missingSecond 2 = false ∧
      old.checkContinuous missingFirst = false ∧
      old.checkContinuous missingSecond = false := by
  decide +kernel

theorem continuity_regression :
    old.checkContinuous inserted = true ∧
      old.checkContinuous old = true ∧
      lowOld.checkContinuous highNew = false := by
  decide +kernel

/-- The correctness premise is active at both levels, with its witness
in the old carrier strictly above the old source anchor. -/
theorem crossing_regression :
    crossingOld.checkKCorrect crossingNew .one = true ∧
      crossingOld.checkKCorrect crossingNew .two = true ∧
      crossingOld.checkContinuous crossingNew = true ∧
      decide (LeastGEData (dataView crossingOld).1 1 2) = true ∧
      decide (LeastGEData (dataView crossingOld).1 3 4) = true ∧
      entryLevel (dataView crossingNew) false (1, 3) = true ∧
      entryLevel (dataView crossingNew) true (1, 3) = true := by
  decide +kernel

theorem first_relation_regression :
    firstBadOld.checkSub firstBadNew = true ∧
      firstBadOld.checkKCorrect firstBadNew .one = false ∧
      firstBadOld.checkKCorrect firstBadNew .two = true ∧
      firstBadOld.checkContinuous firstBadNew = false := by
  decide +kernel

theorem second_relation_regression :
    secondBadOld.checkSub secondBadNew = true ∧
      secondBadOld.checkKCorrect secondBadNew .one = true ∧
      secondBadOld.checkKCorrect secondBadNew .two = false ∧
      secondBadOld.checkContinuous secondBadNew = false := by
  decide +kernel

theorem data_regression :
    decide (ExtensionAtData (dataView old) (dataView inserted) 2) = true ∧
      decide (ContinuousData (dataView old) (dataView inserted)) = true ∧
      decide (KCorrectData (dataView firstBadOld) (dataView firstBadNew) false) = false ∧
      decide (KCorrectData (dataView secondBadOld) (dataView secondBadNew) true) = false := by
  decide +kernel

theorem encoded_regression :
    checkExtensionAt 5 (encode old) (encode inserted) (encode (2 : Fin 5)) = true ∧
      checkExtensionAt 5 (encode old) (encode old) (encode (2 : Fin 5)) = false ∧
      checkContinuous 5 (encode crossingOld) (encode crossingNew) = true ∧
      checkKCorrect false 5 (encode firstBadOld) (encode firstBadNew) = false ∧
      checkKCorrect true 5 (encode secondBadOld) (encode secondBadNew) = false := by
  simp only [checkExtensionAt_encode, checkContinuous_encode, checkKCorrect_encode, level]
  decide +kernel

theorem empty_regression :
    empty.checkContinuous empty = true ∧
      empty.checkKCorrect empty .one = true ∧
      empty.checkKCorrect empty .two = true ∧
      checkExtensionAt 0 (encode empty) (encode empty) 0 = false := by
  simp only [checkExtensionAt, decodeData_encode]
  decide +kernel

/-- The raw pattern constructor tag is checked before any structural test. -/
theorem malformed_left_rejects (k : Bool) (n d a : ℕ) :
    checkKCorrect k n 0 d = false ∧ checkContinuous n 0 d = false ∧
      checkExtensionAt n 0 d a = false := by
  simp [checkKCorrect, checkContinuous, checkExtensionAt, decodeData,
    PrimitiveRationalPresentation.decodeFields, PrimitiveRationalPresentation.decodeField]

theorem malformed_right_rejects :
    checkKCorrect false 5 (encode old) 0 = false ∧
      checkContinuous 5 (encode old) 0 = false ∧
      checkExtensionAt 5 (encode old) 0 2 = false := by
  have hzero : decodeData 5 0 = none := by
    simp [decodeData, PrimitiveRationalPresentation.decodeFields,
      PrimitiveRationalPresentation.decodeField]
  simp [checkKCorrect, checkContinuous, checkExtensionAt, decodeData_encode, hzero]

/-- Point-code rejection is uniform, even when a malformed point would
otherwise be hidden by default table entries. -/
theorem out_of_range_anchor_rejects (n c d a : ℕ) (ha : n ≤ a) :
    checkExtensionAt n c d a = false := by
  cases hC : decodeData n c <;> cases hD : decodeData n d <;>
    simp [checkExtensionAt, decodeLabel, Nat.not_lt.mpr ha, hC, hD]

theorem extension_machine_regression : ∃ machine : Nat.Partrec.Code,
    machine.eval (Nat.pair 5 (Nat.pair (encode old)
      (Nat.pair (encode inserted) (encode (2 : Fin 5))))) = Part.some (encode true) ∧
    machine.eval (Nat.pair 5 (Nat.pair (encode old)
      (Nat.pair (encode old) (encode (2 : Fin 5))))) = Part.some (encode false) ∧
    machine.eval (Nat.pair 5 (Nat.pair (encode old)
      (Nat.pair (encode inserted) 5))) = Part.some (encode false) := by
  obtain ⟨machine, hm⟩ := checkExtensionAt_program
  refine ⟨machine, ?_, ?_, ?_⟩
  · simpa only [checkExtensionAt_encode, extension_at_regression.1] using
      hm 5 (encode old) (encode inserted) (encode (2 : Fin 5))
  · simpa only [checkExtensionAt_encode, extension_at_regression.2.1] using
      hm 5 (encode old) (encode old) (encode (2 : Fin 5))
  · simpa only [out_of_range_anchor_rejects 5 (encode old) (encode inserted) 5 le_rfl] using
      hm 5 (encode old) (encode inserted) 5

/-- Changing only the encoded Boolean selector changes the answer of
the same machine when exactly one original relation is correct. -/
theorem level_machine_regression : ∃ machine : Nat.Partrec.Code,
    machine.eval (Nat.pair (encode false) (Nat.pair 5
      (Nat.pair (encode firstBadOld) (encode firstBadNew)))) = Part.some (encode false) ∧
    machine.eval (Nat.pair (encode true) (Nat.pair 5
      (Nat.pair (encode firstBadOld) (encode firstBadNew)))) = Part.some (encode true) := by
  obtain ⟨machine, hm⟩ := checkKCorrect_uniform_program
  refine ⟨machine, ?_, ?_⟩
  · simpa only [checkKCorrect_encode, level, Bool.false_eq_true, ↓reduceIte,
      first_relation_regression.2.1] using
      hm false 5 (encode firstBadOld) (encode firstBadNew)
  · simpa only [checkKCorrect_encode, level, ↓reduceIte,
      first_relation_regression.2.2.1] using
      hm true 5 (encode firstBadOld) (encode firstBadNew)

end Alexander313.Carlson.PrimitiveContinuityChecksExamples
