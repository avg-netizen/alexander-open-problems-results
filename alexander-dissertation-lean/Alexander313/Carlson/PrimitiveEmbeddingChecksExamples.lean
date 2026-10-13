import Alexander313.Carlson.PrimitiveEmbeddingChecks

/-!
# Finite-map checker regressions

These kernel-checked examples separate forward preservation, strict order,
exact image equality, and reflection of both relations. Encoded tests use
the proved compatibility equations before reducing finite Boolean checks.
Malformed-map tests exercise the original index tags and codomain bounds.
-/

namespace Alexander313.Carlson.PrimitiveEmbeddingChecksExamples

open Encodable Finite PrimitivePatternCode PrimitiveEmbeddingChecks

def one : PatternCode 1 where
  U := {0}
  r₁ i j := decide (i = j)
  r₂ i j := decide (i = j)

def two : PatternCode 2 where
  U := Finset.univ
  r₁ i j := decide (i = j)
  r₂ i j := decide (i = j)

def inclusionMap : Fin 1 → Fin 2 := fun _ => 0

def collapse : Fin 2 → Fin 2 := fun _ => 0

def missingFirst : PatternCode 2 := { two with r₁ := fun _ _ => false }

def missingSecond : PatternCode 2 := { two with r₂ := fun _ _ => false }

def outside : PatternCode 2 := { two with U := {1} }

def noRelations : PatternCode 1 where
  U := {0}
  r₁ _ _ := false
  r₂ _ _ := false

def oneInTwo : PatternCode 2 := { two with U := {0} }

/-- Only entries away from the sole carrier point change. -/
def offCarrier : PatternCode 2 where
  U := {0}
  r₁ i j := decide (i = 0 ∧ j = 0)
  r₂ i j := decide (i = 0 ∧ j = 0)

def empty : PatternCode 0 where
  U := ∅
  r₁ i := Fin.elim0 i
  r₂ i := Fin.elim0 i

def emptyTwo : PatternCode 2 := { two with U := ∅ }

def emptyMap (m : ℕ) : Fin 0 → Fin m := Fin.elim0

/-- A covering may omit target points; an isomorphism must hit all of them. -/
theorem nonsurjective_regression :
    one.checkCoversInto two inclusionMap = true ∧ one.checkIso two inclusionMap = false := by
  decide +kernel

/-- Forward preservation alone does not require reflection of target edges. -/
theorem reflection_regression :
    noRelations.checkCoversInto one id = true ∧ noRelations.checkIso one id = false := by
  decide +kernel

/-- Collapsing two ordered carrier points violates strict order preservation. -/
theorem collapsed_order_regression :
    two.checkCoversInto oneInTwo collapse = false ∧
      two.checkIso oneInTwo collapse = false := by
  decide +kernel

/-- Either missing source edge causes both checks to fail independently. -/
theorem missing_edges_regression :
    two.checkCoversInto missingFirst id = false ∧
      two.checkCoversInto missingSecond id = false ∧
      two.checkIso missingFirst id = false ∧ two.checkIso missingSecond id = false := by
  decide +kernel

/-- A label inside the ambient target type may still lie outside its carrier. -/
theorem outside_carrier_regression :
    one.checkCoversInto outside inclusionMap = false ∧ one.checkIso outside inclusionMap = false := by
  decide +kernel

/-- Ambient table entries outside the source carrier do not affect either check. -/
theorem off_carrier_regression :
    oneInTwo.checkCoversInto offCarrier id = true ∧
      oneInTwo.checkIso offCarrier id = true := by
  decide +kernel

theorem empty_regression :
    empty.checkCoversInto empty (emptyMap 0) = true ∧
      empty.checkIso empty (emptyMap 0) = true ∧
      empty.checkCoversInto two (emptyMap 2) = true ∧
      empty.checkIso two (emptyMap 2) = false ∧
      empty.checkIso emptyTwo (emptyMap 2) = true := by
  decide +kernel

theorem data_regression :
    decide (CoversIntoData (dataView one) (dataView two) (mapView inclusionMap)) = true ∧
      decide (IsoData (dataView one) (dataView two) (mapView inclusionMap)) = false ∧
      decide (CoversIntoData (dataView two) (dataView oneInTwo) (mapView collapse)) = false := by
  decide +kernel

/-- Both bounds are ordinary varying inputs to the raw checkers. -/
theorem encoded_regression :
    checkCoversInto 1 2 (encode one) (encode two) (encode inclusionMap) = true ∧
      checkIso 1 2 (encode one) (encode two) (encode inclusionMap) = false ∧
      checkCoversInto 2 2 (encode two) (encode oneInTwo) (encode collapse) = false ∧
      checkIso 2 2 (encode oneInTwo) (encode offCarrier) (encode (id : Fin 2 → Fin 2)) = true := by
  simp only [checkCoversInto_encode, checkIso_encode]
  decide +kernel

theorem encoded_empty_regression :
    checkCoversInto 0 0 (encode empty) (encode empty) (encode (emptyMap 0)) = true ∧
      checkIso 0 0 (encode empty) (encode empty) (encode (emptyMap 0)) = true ∧
      checkIso 0 2 (encode empty) (encode emptyTwo) (encode (emptyMap 2)) = true ∧
      checkIso 0 2 (encode empty) (encode two) (encode (emptyMap 2)) = false := by
  simp only [checkCoversInto_encode, checkIso_encode]
  decide +kernel

/-- Wrong length, an out-of-range source tag, incorrect in-range tags,
and an out-of-range output are all rejected by the original map decoder. -/
theorem malformed_map_decoder :
    decodeMap 1 1 0 = none ∧
      decodeMap 1 1 (encode ([Nat.pair 1 0] : List ℕ)) = none ∧
      decodeMap 2 1 (encode ([Nat.pair 1 0, Nat.pair 0 0] : List ℕ)) = none ∧
      decodeMap 1 1 (encode ([Nat.pair 0 1] : List ℕ)) = none := by
  decide +kernel

/-- The unique empty map is accepted even when the target type is empty;
nonempty source dimensions have no map into an empty target type. -/
theorem empty_map_decoder :
    decodeMap 0 0 0 = some [] ∧ decodeMap 0 2 0 = some [] ∧
      decodeMap 1 0 0 = none ∧
      decodeMap 1 0 (encode ([Nat.pair 0 0] : List ℕ)) = none := by
  decide +kernel

theorem valid_map_decoder :
    decodeMap 1 2 (encode ([Nat.pair 0 1] : List ℕ)) = some [1] := by
  decide +kernel

theorem malformed_source_rejects (n m d f : ℕ) :
    checkCoversInto n m 0 d f = false ∧ checkIso n m 0 d f = false := by
  simp [checkCoversInto, checkIso, checkWith, decodeData,
    PrimitiveRationalPresentation.decodeFields, PrimitiveRationalPresentation.decodeField]

theorem malformed_target_rejects :
    checkCoversInto 1 2 (encode one) 0 (encode inclusionMap) = false ∧
      checkIso 1 2 (encode one) 0 (encode inclusionMap) = false := by
  have hzero : decodeData 2 0 = none := by
    simp [decodeData, PrimitiveRationalPresentation.decodeFields,
      PrimitiveRationalPresentation.decodeField]
  simp [checkCoversInto, checkIso, checkWith, decodeData_encode, hzero]

theorem malformed_map_rejects :
    checkCoversInto 1 1 (encode one) (encode one) 0 = false ∧
      checkIso 1 1 (encode one) (encode one) 0 = false := by
  simp [checkCoversInto, checkIso, checkWith, decodeData_encode, malformed_map_decoder.1]

theorem out_of_bound_map_rejects :
    checkCoversInto 1 1 (encode one) (encode one)
        (encode ([Nat.pair 0 1] : List ℕ)) = false ∧
      checkIso 1 1 (encode one) (encode one)
        (encode ([Nat.pair 0 1] : List ℕ)) = false := by
  simp only [checkCoversInto, checkIso, checkWith, decodeData_encode,
    malformed_map_decoder.2.2.2, Option.bind_some, Option.map_none,
    Option.getD_none, and_self]

/-- The map is total on the ambient source type: an invalid value at the
off-carrier source label `1` rejects even though the carrier label `0`
has a valid image in the target carrier. -/
theorem off_carrier_map_bound_rejects :
    checkCoversInto 2 1 (encode oneInTwo) (encode one)
        (encode ([Nat.pair 0 0, Nat.pair 1 1] : List ℕ)) = false ∧
      checkIso 2 1 (encode oneInTwo) (encode one)
        (encode ([Nat.pair 0 0, Nat.pair 1 1] : List ℕ)) = false := by
  have hmap : decodeMap 2 1 (encode ([Nat.pair 0 0, Nat.pair 1 1] : List ℕ)) = none := by
    decide +kernel
  simp only [checkCoversInto, checkIso, checkWith, decodeData_encode, hmap,
    Option.bind_some, Option.map_none, Option.getD_none, and_self]

theorem impossible_codomain_rejects :
    checkCoversInto 1 0 (encode one) (encode empty) 0 = false ∧
      checkIso 1 0 (encode one) (encode empty) 0 = false := by
  simp [checkCoversInto, checkIso, checkWith, decodeData_encode, empty_map_decoder.2.2.1]

/-- One covering machine gives the same positive, negative, and malformed answers. -/
theorem covering_machine_regression : ∃ machine : Nat.Partrec.Code,
    machine.eval (Nat.pair 1 (Nat.pair 2 (Nat.pair (encode one)
      (Nat.pair (encode two) (encode inclusionMap))))) = Part.some (encode true) ∧
    machine.eval (Nat.pair 2 (Nat.pair 2 (Nat.pair (encode two)
      (Nat.pair (encode oneInTwo) (encode collapse))))) = Part.some (encode false) ∧
    machine.eval (Nat.pair 1 (Nat.pair 2 (Nat.pair 0 (Nat.pair 0 0)))) =
      Part.some (encode false) := by
  obtain ⟨machine, hm⟩ := checkCoversInto_program
  refine ⟨machine, ?_, ?_, ?_⟩
  · simpa only [checkCoversInto_encode, nonsurjective_regression.1] using
      hm 1 2 (encode one) (encode two) (encode inclusionMap)
  · simpa only [checkCoversInto_encode, collapsed_order_regression.1] using
      hm 2 2 (encode two) (encode oneInTwo) (encode collapse)
  · simpa only [(malformed_source_rejects 1 2 0 0).1] using hm 1 2 0 0 0

theorem iso_machine_regression : ∃ machine : Nat.Partrec.Code,
    machine.eval (Nat.pair 1 (Nat.pair 2 (Nat.pair (encode one)
      (Nat.pair (encode two) (encode inclusionMap))))) = Part.some (encode false) ∧
    machine.eval (Nat.pair 0 (Nat.pair 0 (Nat.pair (encode empty)
      (Nat.pair (encode empty) (encode (emptyMap 0)))))) = Part.some (encode true) := by
  obtain ⟨machine, hm⟩ := checkIso_program
  refine ⟨machine, ?_, ?_⟩
  · simpa only [checkIso_encode, nonsurjective_regression.2] using
      hm 1 2 (encode one) (encode two) (encode inclusionMap)
  · simpa only [checkIso_encode, empty_regression.2.1] using
      hm 0 0 (encode empty) (encode empty) (encode (emptyMap 0))

end Alexander313.Carlson.PrimitiveEmbeddingChecksExamples
