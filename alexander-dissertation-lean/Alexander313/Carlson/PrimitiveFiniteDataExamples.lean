import Alexander313.Carlson.PrimitiveFiniteOperations

/-!
# Regression checks for the unchanged finite-data encodings

The standard finite-set decoder accepts unsorted lists without duplicates.
Re-encoding sorts their element codes. Duplicate lists remain valid
multisets but are rejected as finite sets, and malformed rational elements
are rejected instead of becoming the empty carrier. These distinctions are
part of the certificate format. The checks combine proved normalization
equations with ordinary kernel reduction.
-/

namespace Alexander313.Carlson.PrimitiveFiniteDataExamples

open Encodable PrimitiveFiniteData PrimitiveFiniteOperations

/-- The rational finite-set instance retains the precise original encoding. -/
theorem rational_encoding_unchanged :
    (inferInstance : Encodable (Finset ℚ)) = @Finset.encodable ℚ Rat.instEncodable := rfl

/-- A noncanonical order is accepted, then canonicalized on re-encoding. -/
theorem unsorted_code_regression :
    decode (α := Finset ℕ) (encode ([1, 0] : List ℕ)) = some {0, 1} ∧
    encode ({0, 1} : Finset ℕ) = encode ([0, 1] : List ℕ) ∧
    encode ({0, 1} : Finset ℕ) ≠ encode ([1, 0] : List ℕ) := by
  constructor
  · rw [decode_finset_encode_list, dif_pos (show ([1, 0] : List ℕ).Nodup by decide +kernel)]
    congr 1
    ext a
    simp [or_comm]
  · rw [show ({0, 1} : Finset ℕ) = ([0, 1] : List ℕ).toFinset by decide +kernel,
      encode_finset, finsetView_ofList]
    simp only [sortCodes, List.mergeSort_eq_insertionSort]
    decide +kernel

/-- Duplicate entries are meaningful for multisets and invalid for finite sets. -/
theorem duplicate_code_regression :
    decode (α := Multiset ℕ) (encode ([1, 1] : List ℕ)) = some (↑([1, 1] : List ℕ)) ∧
    decode (α := Finset ℕ) (encode ([1, 1] : List ℕ)) = none := by
  decide +kernel

/-- An invalid rational element code is rejected; the empty list remains valid. -/
theorem malformed_element_regression :
    decode (α := Finset ℚ) (encode ([0] : List ℕ)) = none ∧
    decode (α := Finset ℚ) (encode ([] : List ℕ)) = some ∅ := by
  decide +kernel

/-- The canonical list orders element codes, independently of rational order. -/
theorem encoded_order_regression :
    finsetView ({-1, 0} : Finset ℚ) = [0, -1] ∧ (-1 : ℚ) < 0 := by
  rw [show ({-1, 0} : Finset ℚ) = ([-1, 0] : List ℚ).toFinset by decide +kernel,
    finsetView_ofList]
  simp only [sortCodes, List.mergeSort_eq_insertionSort]
  decide +kernel

def sample : Finset ℚ := {-1, 0, 3 / 2, 2}

/-- Strict boundary filtering and finite arithmetic use the represented values. -/
theorem finite_operations_regression :
    sample.filter (fun x => x < 2) = {-1, 0, 3 / 2} ∧
    sample.filter (fun x => x < 0) = {-1} ∧
    sample ∩ {0, 3 / 2, 99} = {0, 3 / 2} ∧
    sample \ {0, 2} = {-1, 3 / 2} ∧
    sample.image (fun x => x + 1) = {0, 1, 5 / 2, 3} ∧
    (sample ×ˢ ({0, 1} : Finset ℚ)).card = 8 := by
  decide +kernel

/-- The certified membership operation has one total Boolean answer on every
pair of canonical rational and finite-set codes. -/
theorem membership_answers : ∃ c : Nat.Partrec.Code,
    c.eval (Nat.pair (encode (3 / 2 : ℚ)) (encode sample)) = Part.some (encode true) ∧
    c.eval (Nat.pair (encode (3 : ℚ)) (encode sample)) = Part.some (encode false) := by
  obtain ⟨c, hc⟩ := rational_membership_program
  refine ⟨c, ?_, ?_⟩
  · simpa only [show decide ((3 / 2 : ℚ) ∈ sample) = true by decide +kernel]
      using hc (3 / 2) sample
  · simpa only [show decide ((3 : ℚ) ∈ sample) = false by decide +kernel]
      using hc 3 sample

end Alexander313.Carlson.PrimitiveFiniteDataExamples
