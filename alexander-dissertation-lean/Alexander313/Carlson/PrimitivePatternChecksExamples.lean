import Alexander313.Carlson.PrimitivePatternChecks

/-!
# Kernel regressions for uniform finite patternhood

The eight Boolean fields appear in the original `IsPattern` order. The
counterexamples isolate each independent field, including the two
transitivity tests, convexity and respect. First reflexivity follows from
second reflexivity and inclusion, so its counterexample necessarily fails
another field as well. Every concrete answer is proved with kernel reduction.
-/

namespace Alexander313.Carlson.PrimitivePatternChecksExamples

open Encodable Finite PrimitivePatternCode PrimitivePatternChecks

def fieldChecks {n : ℕ} (C : PatternCode n) : List Bool :=
  [decide (Le₁Data (dataView C)), decide (Sub₂Data (dataView C)),
    decide (Refl₁Data (dataView C)), decide (Refl₂Data (dataView C)),
    decide (Trans₁Data (dataView C)), decide (Trans₂Data (dataView C)),
    decide (Convex₁Data (dataView C)), decide (Respect₂Data (dataView C))]

def diagonal : PatternCode 3 where
  U := Finset.univ
  r₁ i j := decide (i = j)
  r₂ i j := decide (i = j)

def reverse : PatternCode 2 where
  U := Finset.univ
  r₁ i j := decide (i = j ∨ (i = 1 ∧ j = 0))
  r₂ i j := decide (i = j ∨ (i = 1 ∧ j = 0))

def outsideFirst : PatternCode 2 where
  U := Finset.univ
  r₁ i j := decide (i = j)
  r₂ i j := decide (i ≤ j)

def missingFirst : PatternCode 1 where
  U := Finset.univ
  r₁ _ _ := false
  r₂ _ _ := true

def missingSecond : PatternCode 1 where
  U := Finset.univ
  r₁ _ _ := true
  r₂ _ _ := false

/-- Adjacent first edges without their composite. -/
def firstGap : PatternCode 3 where
  U := Finset.univ
  r₁ i j := decide (i = j ∨ j.val = i.val + 1)
  r₂ i j := decide (i = j)

/-- Adjacent second edges without their composite; the first table is complete. -/
def secondGap : PatternCode 3 where
  U := Finset.univ
  r₁ i j := decide (i ≤ j)
  r₂ i j := decide (i = j ∨ j.val = i.val + 1)

def nonconvex : PatternCode 3 where
  U := Finset.univ
  r₁ i j := decide (i = j ∨ (i = 0 ∧ j = 2))
  r₂ i j := decide (i = j)

def disrespect : PatternCode 3 where
  U := Finset.univ
  r₁ i j := decide (i ≤ j)
  r₂ i j := decide (i = j ∨ (i = 0 ∧ j = 2))

theorem valid_fields_regression :
    fieldChecks diagonal = [true, true, true, true, true, true, true, true] := by
  decide +kernel

theorem le₁_regression :
    fieldChecks reverse = [false, true, true, true, true, true, true, true] := by
  decide +kernel

theorem sub₂_regression :
    fieldChecks outsideFirst = [true, false, true, true, true, true, true, true] := by
  decide +kernel

/-- Retaining second reflexivity while losing first reflexivity also violates inclusion. -/
theorem refl₁_regression :
    fieldChecks missingFirst = [true, false, false, true, true, true, true, true] := by
  decide +kernel

theorem refl₂_regression :
    fieldChecks missingSecond = [true, true, true, false, true, true, true, true] := by
  decide +kernel

theorem trans₁_regression :
    fieldChecks firstGap = [true, true, true, true, false, true, true, true] := by
  decide +kernel

theorem trans₂_regression :
    fieldChecks secondGap = [true, true, true, true, true, false, true, true] := by
  decide +kernel

theorem convex₁_regression :
    fieldChecks nonconvex = [true, true, true, true, true, true, false, true] := by
  decide +kernel

theorem respect₂_regression :
    fieldChecks disrespect = [true, true, true, true, true, true, true, false] := by
  decide +kernel

theorem original_regression :
    diagonal.checkPattern = true ∧ reverse.checkPattern = false ∧
      outsideFirst.checkPattern = false ∧ missingFirst.checkPattern = false ∧
      missingSecond.checkPattern = false ∧ firstGap.checkPattern = false ∧
      secondGap.checkPattern = false ∧ nonconvex.checkPattern = false ∧
      disrespect.checkPattern = false := by
  decide +kernel

def empty : PatternCode 0 where
  U := ∅
  r₁ i := Fin.elim0 i
  r₂ i := Fin.elim0 i

/-- The one carrier point is reflexive; every other table entry is unrestricted. -/
def offCarrier : PatternCode 3 where
  U := {1}
  r₁ i j := decide ((i = 1 ∧ j = 1) ∨ (i = 2 ∧ j = 0))
  r₂ _ _ := true

def expandedCarrier : PatternCode 3 := { offCarrier with U := Finset.univ }

def emptyCarrier : PatternCode 3 := { expandedCarrier with U := ∅ }

theorem off_carrier_regression :
    offCarrier.checkPattern = true ∧ expandedCarrier.checkPattern = false ∧
      emptyCarrier.checkPattern = true := by
  decide +kernel

theorem empty_regression :
    empty.checkPattern = true ∧
      decide (PatternData (∅, [], [])) = true ∧
      decide (PatternData ({0}, [], [])) = false := by
  decide +kernel

/-- Public raw-code checking agrees with the original finite answers. -/
theorem encoded_regression :
    checkPattern 3 (encode diagonal) = true ∧
      checkPattern 2 (encode reverse) = false ∧
      checkPattern 3 (encode firstGap) = false ∧
      checkPattern 3 (encode secondGap) = false ∧
      checkPattern 3 (encode nonconvex) = false ∧
      checkPattern 3 (encode disrespect) = false := by
  simp only [checkPattern_encode]
  decide +kernel

theorem encoded_carrier_regression :
    checkPattern 0 (encode empty) = true ∧
      checkPattern 3 (encode offCarrier) = true ∧
      checkPattern 3 (encode expandedCarrier) = false ∧
      checkPattern 3 (encode emptyCarrier) = true := by
  simp only [checkPattern_encode]
  decide +kernel

/-- Zero is a malformed constructor record at every finite bound. -/
theorem malformed_rejects (n : ℕ) : checkPattern n 0 = false := by
  simp [checkPattern, decodeData, PrimitiveRationalPresentation.decodeFields,
    PrimitiveRationalPresentation.decodeField]

/-- Empty carrier semantics do not bypass decoding of either complete table.
The same empty-table encoding has valid dimensions exactly at bound zero. -/
theorem table_dimensions_regression :
    checkPattern 0 (encodeData (∅, [], [])) = true ∧
      checkPattern 1 (encodeData (∅, [], [])) = false := by
  decide +kernel

/-- One machine returns the expected encoded Booleans for valid, invalid and
malformed inputs, and for the empty ambient type. -/
theorem machine_regression : ∃ machine : Nat.Partrec.Code,
    machine.eval (Nat.pair 3 (encode diagonal)) = Part.some (encode true) ∧
    machine.eval (Nat.pair 3 (encode disrespect)) = Part.some (encode false) ∧
    machine.eval (Nat.pair 3 0) = Part.some (encode false) ∧
    machine.eval (Nat.pair 0 (encode empty)) = Part.some (encode true) := by
  obtain ⟨machine, hm⟩ := checkPattern_program
  refine ⟨machine, ?_, ?_, ?_, ?_⟩
  · simpa only [encoded_regression.1] using hm 3 (encode diagonal)
  · simpa only [encoded_regression.2.2.2.2.2] using hm 3 (encode disrespect)
  · simpa only [malformed_rejects] using hm 3 0
  · simpa only [encoded_carrier_regression.1] using hm 0 (encode empty)

end Alexander313.Carlson.PrimitivePatternChecksExamples
