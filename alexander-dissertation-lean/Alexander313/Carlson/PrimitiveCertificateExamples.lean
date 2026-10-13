import Alexander313.Carlson.PrimitiveRationalCertificate

/-!
# Regression checks for uniform finite certificate coding

These checks cover arbitrary raw component codes, both table dimensions,
carrier normalization, complete off-carrier tables, and the dependent
certificate's exact record shape. Symbolic encoder and decoder equations
avoid reducing the large natural numbers used by tagged records.

The machine regressions instantiate the proved uniform specifications.
Grid checking remains separate from decoding and tests every grid label,
including labels unused by either endpoint carrier.
-/

namespace Alexander313.Carlson.PrimitiveCertificateExamples

open Encodable Finite PrimitiveFiniteFunctions

@[simp] private theorem decodeListWith_pair {α : Type*}
    (d : ℕ → Option α) (head tail : ℕ) :
    decodeListWith d (Nat.pair head tail + 1) =
      (d head).bind fun a => (decodeListWith d tail).map (List.cons a) := by
  rw [decodeListWith_succ, Nat.unpair_pair]

private theorem pattern_fields (a b c : ℕ) :
    PrimitiveRationalPresentation.decodeFields
      (PrimitiveRationalPresentation.packCode a b c) = some (a, b, c) := by
  simp [PrimitiveRationalPresentation.decodeFields,
    PrimitiveRationalPresentation.decodeField, PrimitiveRationalPresentation.packCode]

private theorem witness_fields (a b c d : ℕ) :
    PrimitiveRationalCertificate.decodeFields
      (PrimitiveRationalCertificate.packCode a b c d) = some (a, b, c, d) := by
  simp [PrimitiveRationalCertificate.decodeFields,
    PrimitiveRationalPresentation.decodeField, PrimitiveRationalCertificate.packCode]

/-- Finite-function decoding checks the supplied length, and lookup checks its index. -/
theorem finite_function_regression :
    decodeArrowWith (decode (α := Bool)) 2 (encodeArrowData [0, 1]) = some [false, true] ∧
    decodeArrowWith (decode (α := Bool)) 1 (encodeArrowData [0, 1]) = none ∧
    lookup (α := Bool) 2 (encodeArrowData [0, 1]) 1 = some true ∧
    lookup (α := Bool) 2 (encodeArrowData [0, 1]) 2 = none := by
  simp [decodeArrowWith, decodeVectorWith, decodeTaggedWith,
    encodeArrowData, List.range_succ, lookup]

/-- The original inferred codec stores index tags; the vector codec has a different format. -/
theorem original_arrow_encoding_regression :
    @encode (Fin 2 → Bool) (Encodable.finPi 2 (fun _ => Bool))
      (fun i => decide (i = 1)) = encodeArrowData [0, 1] ∧
    @encode (Fin 2 → Bool) Encodable.finArrow
      (fun i => decide (i = 1)) = encode [false, true] := by
  constructor
  · rw [encode_arrow]
    congr 1
  · rw [encode_vector]
    congr 1

/-- Valid but misplaced tags, out-of-bounds tags, and omitted tags are all rejected. -/
theorem arrow_index_regression :
    decodeArrowWith (decode (α := Bool)) 2
      (encode ([Nat.pair 1 0, Nat.pair 0 1] : List ℕ)) = none ∧
    decodeArrowWith (decode (α := Bool)) 2
      (encode ([Nat.pair 0 0, Nat.pair 2 1] : List ℕ)) = none ∧
    decodeArrowWith (decode (α := Bool)) 2 (encode [false, true]) = none := by
  simp [decodeArrowWith, decodeVectorWith, decodeTaggedWith,
    List.range_succ, show Nat.unpair 1 = (0, 1) by decide +kernel]

def table : List (List Bool) := [[false, true], [true, false]]

theorem table_decode : decodeTable 2 (encodeTableData table) = some table := by
  simp [decodeTable, decodeArrowWith, decodeVectorWith, decodeTaggedWith,
    encodeArrowData, encodeTableData, List.range_succ, table]

/-- Both the number of rows and the length of each row are checked. -/
theorem table_dimensions_regression :
    decodeTable 1 (encodeTableData []) = none ∧
    decodeTable 1 (encodeTableData [[]]) = none ∧
    decodeTable 1 (encodeTableData [[false, true]]) = none ∧
    decodeTable 2 (encodeTableData [[false, true]]) = none := by
  simp [decodeTable, decodeArrowWith, decodeVectorWith, decodeTaggedWith,
    encodeArrowData, encodeTableData, List.range_succ]

private theorem malformed_bool : (decode 2 : Option Bool) = none :=
  Encodable.decode_ge_two 2 (by decide +kernel)

private theorem malformed_rational : (decode 0 : Option ℚ) = none := by
  decide +kernel

/-- Lists retain their original component codec, including malformed-component rejection. -/
theorem list_components_regression :
    decodeListWith (decode (α := Bool)) (encode [false, true]) = some [false, true] ∧
    decodeListWith (decode (α := Bool)) (encode ([2] : List ℕ)) = none := by
  simp [malformed_bool]

/-- A malformed Boolean cell rejects its whole table. -/
theorem malformed_boolean_regression :
    decodeTable 1 (encodeArrowData [encodeArrowData [2]]) = none := by
  simp [decodeTable, decodeArrowWith, decodeVectorWith, decodeTaggedWith,
    encodeArrowData, List.range_succ, malformed_bool]

/-- A malformed rational label rejects its whole finite function. -/
theorem malformed_rational_regression :
    normalizeArrow (α := ℚ) 1 (encodeArrowData [0]) = none := by
  simp [normalizeArrow, normalizeArrowWith, decodeArrowWith, decodeVectorWith,
    decodeTaggedWith, encodeArrowData, List.range_succ, malformed_rational]

private theorem carrier_unsorted :
    PrimitivePatternCode.decodeCarrier 2 (encode ([1, 0] : List ℕ)) = some {0, 1} := by
  simp [PrimitivePatternCode.decodeCarrier, PrimitivePatternCode.decodeLabel,
    Finset.pair_comm]

/-- An unsorted carrier is valid; duplicate and out-of-bound labels are rejected. -/
theorem carrier_regression :
    PrimitivePatternCode.decodeCarrier 2 (encode ([1, 0] : List ℕ)) = some {0, 1} ∧
    PrimitivePatternCode.decodeCarrier 2 (encode ([0, 0] : List ℕ)) = none ∧
    PrimitivePatternCode.decodeCarrier 2 (encode ([2] : List ℕ)) = none := by
  refine ⟨carrier_unsorted, ?_⟩
  simp [PrimitivePatternCode.decodeCarrier, PrimitivePatternCode.decodeLabel]

/-- Carrier normalization preserves both complete stored tables. -/
theorem unsorted_pattern_regression :
    PrimitivePatternCode.decodeData 2
      (PrimitiveRationalPresentation.packCode
        (encode ([1, 0] : List ℕ)) (encodeTableData table) (encodeTableData table)) =
      some ({0, 1}, table, table) ∧
    PrimitivePatternCode.normalize 2
      (PrimitiveRationalPresentation.packCode
        (encode ([1, 0] : List ℕ)) (encodeTableData table) (encodeTableData table)) =
      some (PrimitiveRationalPresentation.packCode
        (encode ({0, 1} : Finset ℕ)) (encodeTableData table) (encodeTableData table)) := by
  have hd : PrimitivePatternCode.decodeData 2
      (PrimitiveRationalPresentation.packCode
        (encode ([1, 0] : List ℕ)) (encodeTableData table) (encodeTableData table)) =
      some ({0, 1}, table, table) := by
    simp only [PrimitivePatternCode.decodeData, pattern_fields,
      Option.bind_some, carrier_unsorted, table_decode, Option.map_some]
  exact ⟨hd, by simp only [PrimitivePatternCode.normalize, hd,
    Option.map_some, PrimitivePatternCode.encodeData]⟩

/-- Component rejection survives the surrounding tagged pattern record. -/
theorem malformed_pattern_regression :
    PrimitivePatternCode.decodeData 2
      (PrimitiveRationalPresentation.packCode
        (encode ([0, 0] : List ℕ)) (encodeTableData table) (encodeTableData table)) = none ∧
    PrimitivePatternCode.decodeData 2
      (PrimitiveRationalPresentation.packCode
        (encode ([2] : List ℕ)) (encodeTableData table) (encodeTableData table)) = none ∧
    PrimitivePatternCode.decodeData 2
      (PrimitiveRationalPresentation.packCode 0 0 (encodeTableData table)) = none ∧
    PrimitivePatternCode.decodeData 2
      (PrimitiveRationalPresentation.packCode 0 (encodeTableData table) 0) = none := by
  simp [PrimitivePatternCode.decodeData, pattern_fields,
    PrimitivePatternCode.decodeCarrier, PrimitivePatternCode.decodeLabel,
    decodeTable, decodeArrowWith, decodeVectorWith, decodeTaggedWith,
    encodeArrowData, encodeTableData, List.range_succ, table]

def offCarrierPattern : PatternCode 2 :=
  ⟨{0}, fun i j => decide (i = 1 ∧ j = 1), fun _ _ => true⟩

/-- Decoding retains true entries even when neither index is in the carrier. -/
theorem off_carrier_regression :
    (1 : Fin 2) ∉ offCarrierPattern.U ∧
    ((PrimitivePatternCode.decodeData 2 (encode offCarrierPattern)).bind
      fun d => PrimitivePatternCode.relation₁ d (1, 1)) = some true ∧
    ((PrimitivePatternCode.decodeData 2 (encode offCarrierPattern)).bind
      fun d => PrimitivePatternCode.relation₂ d (1, 1)) = some true := by
  refine ⟨by decide +kernel, ?_, ?_⟩
  · rw [PrimitivePatternCode.decodeData_encode]
    exact PrimitivePatternCode.relation₁_dataView offCarrierPattern (1 : Fin 2) (1 : Fin 2)
  · rw [PrimitivePatternCode.decodeData_encode]
    exact PrimitivePatternCode.relation₂_dataView offCarrierPattern (1 : Fin 2) (1 : Fin 2)

def blankPattern (n : ℕ) : PatternCode n :=
  ⟨∅, fun _ _ => false, fun _ _ => false⟩

def emptyWitness (d : ℕ) : RationalWitness 0 :=
  ⟨fun _ => 0, blankPattern 0, blankPattern 0, d⟩

def emptyCertificate (d : ℕ) : RationalCertificate := ⟨0, emptyWitness d⟩

def emptyRaw (d : ℕ) : ℕ :=
  Nat.pair 0 (PrimitiveRationalCertificate.packCode
    0 (encode (blankPattern 0)) (encode (blankPattern 0)) d)

theorem encode_emptyCertificate (d : ℕ) : encode (emptyCertificate d) = emptyRaw d := by
  change Nat.pair 0 (encode (emptyWitness d)) = _
  rw [PrimitiveRationalCertificate.encode_witness]
  rfl

theorem decode_emptyRaw (d : ℕ) :
    decode (α := RationalCertificate) (emptyRaw d) = some (emptyCertificate d) := by
  rw [← encode_emptyCertificate, Encodable.encodek]

/-- Size zero decodes as data, while the actual grid check rejects it. -/
theorem empty_certificate_regression (d : ℕ) :
    decode (α := RationalCertificate) (emptyRaw d) = some (emptyCertificate d) ∧
    PrimitiveRationalCertificate.normalizeCertificate (emptyRaw d) = some (emptyRaw d) ∧
    PrimitiveRationalCertificate.checkGrid (emptyCertificate d) = false := by
  refine ⟨decode_emptyRaw d, ?_, rfl⟩
  rw [PrimitiveRationalCertificate.normalizeCertificate_eq, decode_emptyRaw,
    Option.map_some, encode_emptyCertificate]

/-- Every natural derivation field survives decoding without validation or truncation. -/
theorem derivation_regression (d : ℕ) :
    (decode (α := RationalCertificate) (emptyRaw d)).map
      (fun c => c.2.derivation) = some d := by
  rw [decode_emptyRaw]
  rfl

/-- An empty label function cannot be decoded at a positive grid size. -/
theorem wrong_grid_size_regression (n a b d : ℕ) :
    PrimitiveRationalCertificate.normalizeWitness (n + 1)
      (PrimitiveRationalCertificate.packCode 0 a b d) = none := by
  simp [PrimitiveRationalCertificate.normalizeWitness,
    PrimitiveRationalCertificate.decodeData, witness_fields,
    normalizeArrow, normalizeArrowWith, decodeArrowWith, decodeVectorWith]

/-- An invalid rational component is rejected before either endpoint is used. -/
theorem malformed_witness_regression (a b d : ℕ) :
    PrimitiveRationalCertificate.normalizeWitness 1
      (PrimitiveRationalCertificate.packCode (encodeArrowData [0]) a b d) = none := by
  simp only [PrimitiveRationalCertificate.normalizeWitness,
    PrimitiveRationalCertificate.decodeData, witness_fields, Option.bind_some,
    malformed_rational_regression, Option.bind_none, Option.map_none]

private def field (a rest : ℕ) : ℕ := Nat.pair (Nat.pair 0 a + 1) rest

@[simp] private theorem decode_field (a rest : ℕ) :
    PrimitiveRationalPresentation.decodeField (field a rest) = some (a, rest) := by
  simp [field, PrimitiveRationalPresentation.decodeField]

@[simp] private theorem decode_field_zero :
    PrimitiveRationalPresentation.decodeField 0 = none := by
  decide +kernel

private theorem field_ne_zero (a rest : ℕ) : field a rest ≠ 0 :=
  Nat.ne_of_gt ((Nat.succ_pos _).trans_le (Nat.left_le_pair _ _))

private theorem witness_rejects_fields (n raw : ℕ)
    (h : PrimitiveRationalCertificate.decodeFields raw = none) :
    decode (α := RationalWitness n) raw = none := by
  rw [PrimitiveRationalCertificate.decode_witness]
  simp [PrimitiveRationalCertificate.decodeTypedFields, h]

/-- Reject the wrong constructor, three or five fields, and a nonzero terminator. -/
theorem malformed_shape_regression (n a b c d e : ℕ) :
    decode (α := RationalWitness n)
      (field 1 (field a (field b (field c (field d 0))))) = none ∧
    decode (α := RationalWitness n)
      (field 0 (field a (field b (field c 0)))) = none ∧
    decode (α := RationalWitness n)
      (field 0 (field a (field b (field c (field d (field e 0)))))) = none ∧
    decode (α := RationalWitness n)
      (field 0 (field a (field b (field c (field d (Nat.pair 0 1)))))) = none := by
  refine ⟨witness_rejects_fields n _ ?_, witness_rejects_fields n _ ?_,
    witness_rejects_fields n _ ?_, witness_rejects_fields n _ ?_⟩
  · simp [PrimitiveRationalCertificate.decodeFields]
  · simp [PrimitiveRationalCertificate.decodeFields]
  · simp [PrimitiveRationalCertificate.decodeFields, field_ne_zero]
  · simp [PrimitiveRationalCertificate.decodeFields,
      show Nat.pair 0 1 ≠ 0 by decide +kernel]

private theorem certificate_decode_zero :
    decode (α := RationalCertificate) 0 = none := by
  change (decode (α := RationalWitness 0) 0).map (Sigma.mk 0) = none
  rw [witness_rejects_fields 0 0 (by
    simp [PrimitiveRationalCertificate.decodeFields,
      PrimitiveRationalPresentation.decodeField])]
  rfl

/-- One actual table machine accepts a full square and rejects a malformed Boolean cell. -/
theorem table_machine_regression : ∃ c : Nat.Partrec.Code,
    c.eval (Nat.pair 2 (encodeTableData table)) = Part.some (encode (some table)) ∧
    c.eval (Nat.pair 1 (encodeArrowData [encodeArrowData [2]])) =
      Part.some (encode (none : Option (List (List Bool)))) := by
  obtain ⟨c, hc⟩ := decodeTable_program
  refine ⟨c, ?_, ?_⟩
  · simpa only [table_decode] using hc 2 (encodeTableData table)
  · simpa only [malformed_boolean_regression] using
      hc 1 (encodeArrowData [encodeArrowData [2]])

/-- The same certificate-decoding machine accepts every stored derivation and rejects raw zero. -/
theorem certificate_machine_regression : ∃ c : Nat.Partrec.Code,
    (∀ d : ℕ, c.eval (emptyRaw d) =
      Part.some (encode (some (emptyCertificate d)))) ∧
    c.eval 0 = Part.some (encode (none : Option RationalCertificate)) := by
  obtain ⟨c, hc⟩ := PrimitiveRationalCertificate.certificate_decode_program
  refine ⟨c, fun d => ?_, ?_⟩
  · simpa only [decode_emptyRaw] using hc (emptyRaw d)
  · simpa only [certificate_decode_zero] using hc 0

def gridCertificate (labels : Fin 2 → ℚ) : RationalCertificate :=
  ⟨2, ⟨labels, blankPattern 2, blankPattern 2, 37⟩⟩

def ascendingGrid : RationalCertificate :=
  gridCertificate (fun i => if i = 0 then 0 else 1)

def repeatedGrid : RationalCertificate := gridCertificate (fun _ => 0)

def reversedGrid : RationalCertificate :=
  gridCertificate (fun i => if i = 0 then 1 else 0)

/-- Strict increase is checked on unused labels, even when both carriers are empty. -/
theorem grid_regression :
    ascendingGrid.2.source.U = ∅ ∧ ascendingGrid.2.target.U = ∅ ∧
    PrimitiveRationalCertificate.checkGrid ascendingGrid = true ∧
    PrimitiveRationalCertificate.checkGrid repeatedGrid = false ∧
    PrimitiveRationalCertificate.checkGrid reversedGrid = false := by
  decide +kernel

/-- Non-increasing grids remain decodable untrusted data. -/
theorem invalid_grid_data_regression :
    decode (α := RationalCertificate) (encode repeatedGrid) = some repeatedGrid ∧
    decode (α := RationalCertificate) (encode reversedGrid) = some reversedGrid := by
  exact ⟨Encodable.encodek _, Encodable.encodek _⟩

/-- The certified grid machine returns both its accepting and rejecting Boolean answers. -/
theorem grid_machine_regression : ∃ p : Nat.Partrec.Code,
    p.eval (encode ascendingGrid) = Part.some (encode true) ∧
    p.eval (encode repeatedGrid) = Part.some (encode false) ∧
    p.eval (encode reversedGrid) = Part.some (encode false) ∧
    p.eval (encode (emptyCertificate 37)) = Part.some (encode false) := by
  obtain ⟨p, hp⟩ := PrimitiveRationalCertificate.grid_check_program
  refine ⟨p, ?_, ?_, ?_, ?_⟩
  · simpa only [grid_regression.2.2.1] using hp ascendingGrid
  · simpa only [grid_regression.2.2.2.1] using hp repeatedGrid
  · simpa only [grid_regression.2.2.2.2] using hp reversedGrid
  · simpa only [(empty_certificate_regression 37).2.2] using hp (emptyCertificate 37)

end Alexander313.Carlson.PrimitiveCertificateExamples
