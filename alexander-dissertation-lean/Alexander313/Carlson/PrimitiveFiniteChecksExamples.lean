import Alexander313.Carlson.PrimitiveFiniteChecks

/-!
# Regressions for the partial primitive-recursive finite checker

The tests distinguish carrier-sensitive substructure checks from agreement
on an explicitly supplied set. Encoded tests use the proved codec equations
rather than reducing unnecessarily large natural encodings. Concrete Boolean
answers are checked by the kernel, not by `native_decide`.
-/

namespace Alexander313.Carlson.PrimitiveFiniteChecksExamples

open Encodable Finite PrimitivePatternCode PrimitiveFiniteChecks

def base : PatternCode 3 where
  U := {0}
  r₁ i j := decide (i = j)
  r₂ i j := decide (i = j)

def extension : PatternCode 3 := { base with U := {0, 2} }

/-- The first table changes away from the one-point carrier only. -/
def trimmed : PatternCode 3 :=
  { base with r₁ := fun i j => decide (i = 0 ∧ j = 0) }

/-- A first-relation disagreement on the source carrier must reject. -/
def missingFirst : PatternCode 3 := { extension with r₁ := fun _ _ => false }

/-- The second relation is checked independently of the first. -/
def missingSecond : PatternCode 3 := { extension with r₂ := fun _ _ => false }

def empty : PatternCode 0 where
  U := ∅
  r₁ i := Fin.elim0 i
  r₂ i := Fin.elim0 i

theorem substructure_regression :
    base.checkSub extension = true ∧ extension.checkSub base = false ∧
      base.checkSub missingFirst = false ∧ base.checkSub missingSecond = false := by
  decide +kernel

theorem off_carrier_regression :
    base.checkSub trimmed = true ∧ trimmed.checkSub base = true ∧
      base.checkAgree trimmed {0} = true ∧ base.checkAgree trimmed {1} = false := by
  decide +kernel

theorem empty_regression :
    empty.checkSub empty = true ∧ empty.checkAgree empty ∅ = true ∧
      base.checkAgree missingFirst ∅ = true := by
  decide +kernel

theorem data_regression :
    decide (SubData (dataView base) (dataView extension)) = true ∧
      decide (AgreeData (dataView base) (dataView trimmed) {1}) = false := by
  decide +kernel

/-- The public raw-code algorithms inherit the exact finite answers. -/
theorem encoded_regression :
    checkSub 3 (encode base) (encode extension) = true ∧
      checkSub 3 (encode extension) (encode base) = false ∧
      checkAgree 3 (encode base) (encode trimmed) (encode ({1} : Finset (Fin 3))) = false := by
  simp only [checkSub_encode, checkAgree_encode]
  decide +kernel

theorem encoded_empty_regression :
    checkSub 0 (encode empty) (encode empty) = true ∧
      checkAgree 0 (encode empty) (encode empty) (encode (∅ : Finset (Fin 0))) = true := by
  simp only [checkSub_encode, checkAgree_encode]
  decide +kernel

/-- Zero is not a tagged pattern record, for any ambient size. -/
theorem malformed_left_rejects (n d s : ℕ) :
    checkSub n 0 d = false ∧ checkAgree n 0 d s = false := by
  simp [checkSub, checkAgree, decodeData, PrimitiveRationalPresentation.decodeFields,
    PrimitiveRationalPresentation.decodeField]

theorem malformed_right_rejects :
    checkSub 3 (encode base) 0 = false ∧
      checkAgree 3 (encode base) 0 (encode ({0} : Finset (Fin 3))) = false := by
  have hzero : decodeData 3 0 = none := by
    simp [decodeData, PrimitiveRationalPresentation.decodeFields,
      PrimitiveRationalPresentation.decodeField]
  simp [checkSub, checkAgree, decodeData_encode, hzero]

/-- A carrier list with duplicates fails even when both pattern codes are valid. -/
theorem duplicate_test_set_rejects :
    checkAgree 3 (encode base) (encode base) (encode ([0, 0] : List (Fin 3))) = false := by
  simp only [checkAgree, decodeData_encode]
  decide +kernel

/-- Out-of-range labels are rejected instead of using a missing-entry default. -/
theorem out_of_range_test_set_rejects :
    checkAgree 3 (encode base) (encode base) (encode ([3] : List ℕ)) = false := by
  simp only [checkAgree, decodeData_encode]
  decide +kernel

/-- Unsorted distinct lists retain the existing decoder's permissive behavior. -/
theorem unsorted_test_set_accepts :
    checkAgree 3 (encode base) (encode base) (encode ([2, 0] : List (Fin 3))) = true := by
  simp only [checkAgree, decodeData_encode]
  decide +kernel

/-- Machine answers use the existing Boolean encoding, for the same total checker. -/
theorem machine_regression : ∃ machine : Nat.Partrec.Code,
    machine.eval (Nat.pair 3 (Nat.pair (encode base) (encode extension))) =
      Part.some (encode true) ∧
    machine.eval (Nat.pair 3 (Nat.pair (encode extension) (encode base))) =
      Part.some (encode false) ∧
    machine.eval (Nat.pair 3 (Nat.pair 0 0)) = Part.some (encode false) := by
  obtain ⟨machine, hm⟩ := checkSub_program
  refine ⟨machine, ?_, ?_, ?_⟩
  · simpa only [checkSub_encode, substructure_regression.1] using
      hm 3 (encode base) (encode extension)
  · simpa only [checkSub_encode, substructure_regression.2.1] using
      hm 3 (encode extension) (encode base)
  · simpa only [(malformed_left_rejects 3 0 0).1] using hm 3 0 0

end Alexander313.Carlson.PrimitiveFiniteChecksExamples
