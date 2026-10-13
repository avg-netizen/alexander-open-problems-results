import Alexander313.Carlson.PrimitiveRequests

/-!
# Regression checks for the existing rational-presentation format

These checks exercise the derived constructor tag, the exact field count,
component normalization, and rejection of malformed finite data. The decoder
continues to accept structurally valid presentations without imposing pattern
axioms on their carriers or edge tables.
-/

namespace Alexander313.Carlson.PrimitivePresentationExamples

open Encodable Finite PrimitiveRationalPresentation
open PrimitiveFiniteData

def empty : RationalPresentation := ⟨∅, ∅, ∅⟩

/-- The empty presentation retains its original tagged code. -/
theorem empty_code_regression :
    encode empty = packCode 0 0 0 ∧
    decode (α := RationalPresentation) (packCode 0 0 0) = some empty := by
  decide +kernel

/-- A decoded noncanonical carrier is accepted and re-encoded canonically. -/
theorem noncanonical_carrier_regression :
    decode (α := RationalPresentation)
      (packCode (encode ([-1, 0] : List ℚ)) 0 0) = some ⟨{-1, 0}, ∅, ∅⟩ ∧
    encode (⟨{-1, 0}, ∅, ∅⟩ : RationalPresentation) ≠
      packCode (encode ([-1, 0] : List ℚ)) 0 0 := by
  have hU : decode (α := Finset ℚ) (encode ([-1, 0] : List ℚ)) = some {-1, 0} := by
    rw [decode_finset_encode_list, dif_pos (show ([-1, 0] : List ℚ).Nodup by decide +kernel)]
    congr 1
  have hz : encode (∅ : Finset (ℚ × ℚ)) = 0 := by
    rw [encode_finset]
    change encode (sortCodes ([] : List (ℚ × ℚ))) = 0
    simp [sortCodes]
  have hd0 : decode (α := Finset (ℚ × ℚ)) 0 = some ∅ := by
    rw [← hz, Encodable.encodek]
  have hparse (a b c : ℕ) : decodeFields (packCode a b c) = some (a, b, c) := by
    simp [decodeFields, decodeField, packCode]
  constructor
  · rw [decode_presentation]
    simp only [decodeData, hparse, Option.bind_some, hU, hd0, Option.map_some, ofFields]
  · rw [encode_presentation]
    change packCode (encode ({-1, 0} : Finset ℚ))
      (encode (∅ : Finset (ℚ × ℚ))) (encode (∅ : Finset (ℚ × ℚ))) ≠ _
    rw [hz]
    rw [show ({-1, 0} : Finset ℚ) = ([-1, 0] : List ℚ).toFinset by decide +kernel,
      encode_finset, finsetView_ofList]
    simp only [sortCodes, List.mergeSort_eq_insertionSort]
    decide +kernel

/-- Every component decoder rejects a list containing the invalid element code zero. -/
theorem malformed_components_regression :
    decode (α := RationalPresentation)
      (packCode (encode ([0] : List ℕ)) 0 0) = none ∧
    decode (α := RationalPresentation)
      (packCode 0 (encode ([0] : List ℕ)) 0) = none ∧
    decode (α := RationalPresentation)
      (packCode 0 0 (encode ([0] : List ℕ))) = none := by
  decide +kernel

/-- Duplicate entries in the carrier remain invalid inside the tagged record. -/
theorem duplicate_carrier_regression :
    decode (α := RationalPresentation)
      (packCode (encode ([0, 0] : List ℚ)) 0 0) = none := by
  decide +kernel

/-- Encode a raw S-expression cell for testing malformed record shapes. -/
private def rawCons (head tail : ℕ) : ℕ := Nat.pair (head + 1) tail

/-- The natural atom used by the existing deriving handler. -/
private def rawAtom (n : ℕ) : ℕ := Nat.pair 0 n

/-- Reject a wrong constructor tag, an omitted field, an extra field,
and an invalid nonzero terminating atom. -/
theorem malformed_shape_regression :
    decode (α := RationalPresentation)
      (rawCons (rawAtom 1)
        (rawCons (rawAtom 0) (rawCons (rawAtom 0) (rawCons (rawAtom 0) (rawAtom 0))))) = none ∧
    decode (α := RationalPresentation)
      (rawCons (rawAtom 0) (rawCons (rawAtom 0) (rawCons (rawAtom 0) (rawAtom 0)))) = none ∧
    decode (α := RationalPresentation)
      (rawCons (rawAtom 0) (rawCons (rawAtom 0)
        (rawCons (rawAtom 0) (rawCons (rawAtom 0) (rawCons (rawAtom 0) (rawAtom 0)))))) = none ∧
    decode (α := RationalPresentation)
      (rawCons (rawAtom 0)
        (rawCons (rawAtom 0) (rawCons (rawAtom 0) (rawCons (rawAtom 0) (rawAtom 1))))) = none := by
  decide +kernel

/-- Request decoding preserves the stored certificate value without checking it. -/
theorem request_data_regression :
    decode (α := ComputableRequests.Request)
      (PrimitiveRequests.packCode (encode empty) 7) = some ⟨empty, 7⟩ ∧
    decode (α := ComputableRequests.Request)
      (PrimitiveRequests.packCode 0 7) = none := by
  decide +kernel

/-- A malformed request has the actual scheduler's empty fallback. -/
theorem invalid_schedule_regression :
    ComputableRequests.sourceIndex 0 = 0 ∧
    ComputableRequests.decode 0 = none ∧
    ComputableRequests.target 0 = empty := by
  decide +kernel

/-- The certified target machine returns that same fallback on the malformed input. -/
theorem invalid_schedule_program : ∃ c : Nat.Partrec.Code,
    c.eval 0 = Part.some (encode empty) := by
  obtain ⟨c, hc⟩ := PrimitiveRequests.schedule_target_program
  exact ⟨c, by simpa only [invalid_schedule_regression.2.2] using hc 0⟩

end Alexander313.Carlson.PrimitivePresentationExamples
