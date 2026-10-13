import Alexander313.Carlson.PrimitiveMinimalityChecks

/-!
# Exhaustive minimality regressions

Small kernel computations check the explicit enumerations and one-point
minimality searches. A two-point counterexample uses an explicit competitor,
avoiding exhaustive reduction of the larger finite search. The examples also
separate fixed-carrier minimality from the candidate's being a lifting, and
distinguish skipped malformed competitor codes from rejected external inputs.
-/

namespace Alexander313.Carlson.PrimitiveMinimalityChecksExamples

open Encodable Finite PrimitivePatternCode PrimitiveEmbeddingChecks
open PrimitiveFiniteEnumeration PrimitiveMinimalityChecks
open PrimitiveLiftingChecks (pairDecoded)

def empty : PatternCode 0 where
  U := ∅
  r₁ i := Fin.elim0 i
  r₂ i := Fin.elim0 i

def one : PatternCode 1 where
  U := {0}
  r₁ i j := decide (i = j)
  r₂ i j := decide (i = j)

def emptyOne : PatternCode 1 := { one with U := ∅ }

def missingFirst : PatternCode 1 := { one with r₁ := fun _ _ => false }

def missingSecond : PatternCode 1 := { one with r₂ := fun _ _ => false }

def missingBoth : PatternCode 1 :=
  { one with r₁ := fun _ _ => false, r₂ := fun _ _ => false }

def two : PatternCode 2 where
  U := {0, 1}
  r₁ i j := decide (i = j)
  r₂ i j := decide (i = j)

/-- A proposed target with a first-level edge absent from the diagonal competitor. -/
def extraFirst : PatternCode 2 :=
  { two with r₁ := fun i j => decide (i = j ∨ (i = 0 ∧ j = 1)) }

def emptyMap (m : ℕ) : Fin 0 → Fin m := Fin.elim0

def singletonInput : SearchInput :=
  ((1, 1), (dataView one, dataView one), (dataView one, dataView one),
    mapView (id : Fin 1 → Fin 1))

def weakenedInput : SearchInput :=
  ((1, 1), (dataView one, dataView one), (dataView one, dataView missingFirst),
    mapView (id : Fin 1 → Fin 1))

def fixedCarrierInput : SearchInput :=
  ((0, 1), (dataView empty, dataView empty), (dataView emptyOne, dataView one),
    mapView (emptyMap 1))

def nonminimalInput : SearchInput :=
  ((0, 2), (dataView empty, dataView empty), (dataView two, dataView extraFirst),
    mapView (emptyMap 2))

/-- The list enumeration has the specified order and exact length; shorter
lists and entries outside the alphabet do not occur. -/
theorem list_enumeration_regression :
    listsOfLength [false, true] 0 = [[]] ∧
      listsOfLength [false, true] 2 =
        [[false, false], [false, true], [true, false], [true, true]] ∧
      ([false] : List Bool) ∉ listsOfLength [false, true] 2 ∧
      ([0, 2] : List ℕ) ∉ listsOfLength [0, 1] 2 ∧
      ([1, 0] : List ℕ) ∈ listsOfLength [0, 1] 2 := by
  decide +kernel

/-- Both complete relation tables are varied even when the carrier is empty. -/
theorem table_enumeration_regression :
    tables 0 = [[]] ∧ tables 1 = [[[false]], [[true]]] ∧
      (patternCodes 0 ∅).length = 1 ∧
      (patternCodes 1 {0}).length = 4 ∧ (patternCodes 1 ∅).length = 4 := by
  decide +kernel

/-- All four original one-point Boolean-table codes occur on the fixed carrier. -/
theorem pattern_completeness_regression :
    encode one ∈ patternCodes 1 {0} ∧
      encode missingFirst ∈ patternCodes 1 {0} ∧
      encode missingSecond ∈ patternCodes 1 {0} ∧
      encode missingBoth ∈ patternCodes 1 {0} := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [one, carrierView] using encode_mem_patternCodes one
  · simpa [missingFirst, one, carrierView] using encode_mem_patternCodes missingFirst
  · simpa [missingSecond, one, carrierView] using encode_mem_patternCodes missingSecond
  · simpa [missingBoth, one, carrierView] using encode_mem_patternCodes missingBoth

/-- The total-map enumeration uses the original position-tagged code. -/
theorem map_enumeration_regression :
    mapCodes 0 0 = [0] ∧ mapCodes 0 1 = [0] ∧ mapCodes 1 0 = [] ∧
      mapCodes 1 1 = [encode ([Nat.pair 0 0] : List ℕ)] ∧
      mapCodes 1 2 = [encode ([Nat.pair 0 0] : List ℕ),
        encode ([Nat.pair 0 1] : List ℕ)] ∧
      encode ([Nat.pair 0 2] : List ℕ) ∉ mapCodes 1 2 := by
  decide +kernel

theorem map_completeness_regression :
    encode (emptyMap 0) ∈ mapCodes 0 0 ∧
      encode (emptyMap 1) ∈ mapCodes 0 1 ∧
      encode (id : Fin 1 → Fin 1) ∈ mapCodes 1 1 :=
  ⟨encode_mem_mapCodes (emptyMap 0), encode_mem_mapCodes (emptyMap 1),
    encode_mem_mapCodes (id : Fin 1 → Fin 1)⟩

theorem singleton_minimality_regression :
    one.checkLifting one one one id id = true ∧
      one.checkMinimal one one one id = true := by
  decide +kernel

/-- The competitor set is nonempty, but minimality alone still accepts a
candidate whose first relation is not reflexive and which is not a lifting. -/
theorem minimality_is_separate_regression :
    one.checkLifting one one one id id = true ∧
      one.checkMinimal one one missingFirst id = true ∧
      one.checkLifting one one missingFirst id id = false ∧
      missingFirst.checkPattern = false := by
  decide +kernel

/-- An impossible source inclusion makes every lifting antecedent false. -/
theorem vacuous_source_regression :
    one.checkLifting emptyOne one one id id = false ∧
      one.checkMinimal emptyOne one one id = true := by
  decide +kernel

/-- This different-carrier competitor is a genuine lifting and fails the
candidate's covering conclusion. The fixed-carrier guard must skip it. -/
theorem fixed_carrier_competitor_regression :
    empty.checkLifting empty emptyOne emptyOne (emptyMap 1) (emptyMap 1) = true ∧
      one.checkCoversInto emptyOne id = false ∧
      checkCompetitor fixedCarrierInput (encode emptyOne) (encode (emptyMap 1)) = true := by
  simp only [fixedCarrierInput, checkCompetitor_eq, Encodable.encodek]
  decide +kernel

theorem fixed_carrier_minimality_regression :
    empty.checkMinimal empty emptyOne one (emptyMap 1) = true ∧
      empty.checkLifting empty emptyOne one (emptyMap 1) (emptyMap 1) = false := by
  decide +kernel

/-- A successfully decoded competitor which is not a lifting imposes no obligation. -/
theorem nonlifting_competitor_skipped :
    checkCompetitor singletonInput (encode missingFirst) (encode (id : Fin 1 → Fin 1)) = true := by
  simp only [singletonInput, checkCompetitor_eq, Encodable.encodek]
  decide +kernel

/-- The two-point negative case requires only this explicit small competitor. -/
theorem nonminimal_competitor_regression :
    empty.checkLifting empty two two (emptyMap 2) (emptyMap 2) = true ∧
      extraFirst.checkCoversInto two id = false ∧
      checkCompetitor nonminimalInput (encode two) (encode (emptyMap 2)) = false := by
  simp only [nonminimalInput, checkCompetitor_eq, Encodable.encodek]
  decide +kernel

/-- No enumeration of the two-point table space is reduced in this proof. -/
theorem nonminimal_candidate_regression :
    empty.checkMinimal empty two extraFirst (emptyMap 2) = false := by
  apply Bool.eq_false_iff.mpr
  intro hc
  have hmin := (PatternCode.checkMinimal_eq_true empty empty two extraFirst (emptyMap 2)).mp hc
  have hL := (PatternCode.checkLifting_eq_true empty empty two two
    (emptyMap 2) (emptyMap 2)).mp nonminimal_competitor_regression.1
  have hcover := hmin two.toStr (emptyMap 2) rfl hL
  have hc' := (PatternCode.checkCoversInto_eq_true extraFirst two
    (id : Fin 2 → Fin 2)).mpr hcover
  rw [nonminimal_competitor_regression.2.1] at hc'
  cases hc'

/-- Execute the new four-competitor data search at the one-point bound. -/
theorem exhaustive_data_regression :
    decide (MinimalData singletonInput) = true ∧ decide (MinimalData weakenedInput) = true := by
  decide +kernel

theorem encoded_regression :
    checkMinimal 1 1 (encode one) (encode one) (encode one) (encode one)
        (encode (id : Fin 1 → Fin 1)) = true ∧
      checkMinimal 1 1 (encode one) (encode one) (encode one) (encode missingFirst)
        (encode (id : Fin 1 → Fin 1)) = true ∧
      checkMinimal 0 1 (encode empty) (encode empty) (encode emptyOne) (encode one)
        (encode (emptyMap 1)) = true ∧
      checkMinimal 0 2 (encode empty) (encode empty) (encode two) (encode extraFirst)
        (encode (emptyMap 2)) = false := by
  simp only [checkMinimal_encode]
  exact ⟨singleton_minimality_regression.2, minimality_is_separate_regression.2.1,
    fixed_carrier_minimality_regression.1, nonminimal_candidate_regression⟩

theorem empty_regression :
    empty.checkMinimal empty empty empty (emptyMap 0) = true ∧
      empty.checkMinimal empty emptyOne emptyOne (emptyMap 1) = true ∧
      checkMinimal 0 0 (encode empty) (encode empty) (encode empty) (encode empty)
        (encode (emptyMap 0)) = true := by
  simp only [checkMinimal_encode]
  decide +kernel

/-- Malformed competitor records are ignored for every supplied competitor-map code. -/
theorem malformed_competitor_pattern_skipped (g : ℕ) :
    checkCompetitor singletonInput 0 g = true := by
  simp [checkCompetitor, singletonInput, decodeData,
    PrimitiveRationalPresentation.decodeFields, PrimitiveRationalPresentation.decodeField]

theorem malformed_competitor_map_skipped :
    checkCompetitor singletonInput (encode one) 0 = true ∧
      checkCompetitor singletonInput (encode one)
        (encode ([Nat.pair 1 0] : List ℕ)) = true := by
  simp only [checkCompetitor, singletonInput, decodeData_encode]
  decide +kernel

/-- Every external pattern slot must decode; none receives the competitor default. -/
theorem malformed_external_patterns_reject :
    checkMinimal 1 1 0 (encode one) (encode one) (encode one)
        (encode (id : Fin 1 → Fin 1)) = false ∧
      checkMinimal 1 1 (encode one) 0 (encode one) (encode one)
        (encode (id : Fin 1 → Fin 1)) = false ∧
      checkMinimal 1 1 (encode one) (encode one) 0 (encode one)
        (encode (id : Fin 1 → Fin 1)) = false ∧
      checkMinimal 1 1 (encode one) (encode one) (encode one) 0
        (encode (id : Fin 1 → Fin 1)) = false := by
  have hzero : decodeData 1 0 = none := by
    simp [decodeData, PrimitiveRationalPresentation.decodeFields,
      PrimitiveRationalPresentation.decodeField]
  simp [checkMinimal, decodeInput, pairDecoded, decodeData_encode, decodeMap_encode, hzero]

theorem malformed_external_map_rejects :
    checkMinimal 1 1 (encode one) (encode one) (encode one) (encode one) 0 = false := by
  simp only [checkMinimal, decodeInput, pairDecoded, decodeData_encode]
  decide +kernel

/-- The internal map enumeration is empty, but an impossible external base
map must reject before a vacuous data-level answer can be returned. -/
theorem empty_codomain_regression :
    decide (MinimalData ((1, 0), (dataView one, dataView one),
      (dataView empty, dataView empty), [])) = true ∧
      checkMinimal 1 0 (encode one) (encode one) (encode empty) (encode empty) 0 = false := by
  constructor
  · simp [MinimalData, mapCodes_succ_zero]
  · simp only [checkMinimal, decodeInput, pairDecoded, decodeData_encode]
    decide +kernel

/-- The same extracted machine accepts, rejects an explicit nonminimal
candidate, and rejects malformed external codes. -/
theorem machine_regression : ∃ machine : Nat.Partrec.Code,
    machine.eval (Nat.pair (Nat.pair 1 1)
      (Nat.pair (Nat.pair (encode one) (encode one))
        (Nat.pair (Nat.pair (encode one) (encode one)) (encode (id : Fin 1 → Fin 1))))) =
      Part.some (encode true) ∧
    machine.eval (Nat.pair (Nat.pair 0 2)
      (Nat.pair (Nat.pair (encode empty) (encode empty))
        (Nat.pair (Nat.pair (encode two) (encode extraFirst)) (encode (emptyMap 2))))) =
      Part.some (encode false) ∧
    machine.eval (Nat.pair (Nat.pair 1 1)
      (Nat.pair (Nat.pair 0 (encode one))
        (Nat.pair (Nat.pair (encode one) (encode one)) (encode (id : Fin 1 → Fin 1))))) =
      Part.some (encode false) := by
  obtain ⟨machine, hm⟩ := checkMinimal_program
  refine ⟨machine, ?_, ?_, ?_⟩
  · simpa only [checkMinimal_encode, singleton_minimality_regression.2] using
      hm 1 1 (encode one) (encode one) (encode one) (encode one) (encode (id : Fin 1 → Fin 1))
  · simpa only [checkMinimal_encode, nonminimal_candidate_regression] using
      hm 0 2 (encode empty) (encode empty) (encode two) (encode extraFirst) (encode (emptyMap 2))
  · simpa only [malformed_external_patterns_reject.1] using
      hm 1 1 0 (encode one) (encode one) (encode one) (encode (id : Fin 1 → Fin 1))

end Alexander313.Carlson.PrimitiveMinimalityChecksExamples
