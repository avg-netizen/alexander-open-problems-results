import Alexander313.Carlson.PrimitiveLiftingChecks

/-!
# Kernel regressions for finite lifting checks

The main positive example inserts a source point below an old anchor and
lifts it between different finite ambient orders. Separate counterexamples
isolate source boundedness, agreement with the base map, exact target carrier,
and placement relative to every old target point. Both relation tables and
both total-map decoder boundaries are exercised independently.
-/

namespace Alexander313.Carlson.PrimitiveLiftingChecksExamples

open Encodable Finite PrimitivePatternCode PrimitiveEmbeddingChecks
open PrimitiveContinuityChecks PrimitiveLiftingChecks

def sourceBase : PatternCode 3 where
  U := {2}
  r₁ i j := decide (i = j)
  r₂ i j := decide (i = j)

def sourcePlus : PatternCode 3 := { sourceBase with U := {0, 2} }

def targetBase : PatternCode 4 where
  U := {3}
  r₁ i j := decide (i = j)
  r₂ i j := decide (i = j)

def targetPlus : PatternCode 4 := { targetBase with U := {1, 3} }

def baseMap : Fin 3 → Fin 4 := fun _ => 3

def liftMap (i : Fin 3) : Fin 4 := ⟨i.val + 1, Nat.add_lt_add_right i.isLt 1⟩

/-- The ten values use exactly the order in `ArithmeticLifting.iff_conditions`. -/
def arithmeticFields {n m : ℕ} (P Pplus : PatternCode n) (Q Qplus : PatternCode m)
    (h f : Fin n → Fin m) : List Bool :=
  let A := (dataView P).1
  let Aplus := (dataView Pplus).1
  let B := (dataView Q).1
  let Bplus := (dataView Qplus).1
  let H := mapView h
  let F := mapView f
  [decide (A ⊆ Aplus), decide (BoundedData (dataView P) (dataView Pplus)),
    decide (IncreasingData A H), decide (LandsData A B H), decide (B ⊆ Bplus),
    decide (IncreasingData Aplus F), decide (LandsData Aplus Bplus F),
    decide (AgreesData A H F), decide (Bplus = B ∪ Aplus.image (mapAt F)),
    decide (PlacementData A Aplus B H F)]

theorem positive_arithmetic_regression :
    arithmeticFields sourceBase sourcePlus targetBase targetPlus baseMap liftMap =
      [true, true, true, true, true, true, true, true, true, true] := by
  decide +kernel

theorem positive_lifting_regression :
    sourceBase.checkLifting sourcePlus targetBase targetPlus baseMap liftMap = true ∧
      decide (LiftingData (dataView sourceBase) (dataView sourcePlus)
        (dataView targetBase) (dataView targetPlus) (mapView baseMap) (mapView liftMap)) = true := by
  decide +kernel

def unboundedSource : PatternCode 3 := { sourceBase with U := {0} }

def lowerTarget : PatternCode 4 := { targetBase with U := {1} }

/-- The added source maximum is unanchored; the other nine arithmetic fields hold. -/
theorem boundedness_regression :
    arithmeticFields unboundedSource sourcePlus lowerTarget targetPlus liftMap liftMap =
      [true, false, true, true, true, true, true, true, true, true] ∧
      unboundedSource.checkLifting sourcePlus lowerTarget targetPlus liftMap liftMap = false := by
  decide +kernel

def agreementBase : PatternCode 4 := { targetBase with U := {2, 3} }

def agreementPlus : PatternCode 4 := { targetBase with U := {1, 2, 3} }

def wrongBaseMap : Fin 3 → Fin 4 := fun _ => 2

/-- Both maps land correctly, but the extended map changes the old-source image. -/
theorem agreement_regression :
    arithmeticFields sourceBase sourcePlus agreementBase agreementPlus wrongBaseMap liftMap =
      [true, true, true, true, true, true, true, false, true, true] ∧
      sourceBase.checkLifting sourcePlus agreementBase agreementPlus wrongBaseMap liftMap = false := by
  decide +kernel

def extraTarget : PatternCode 4 := { targetPlus with U := {0, 1, 3} }

/-- The target must be exactly the old target union the extended source image. -/
theorem carrier_regression :
    arithmeticFields sourceBase sourcePlus targetBase extraTarget baseMap liftMap =
      [true, true, true, true, true, true, true, true, false, true] ∧
      sourceBase.checkLifting sourcePlus targetBase extraTarget baseMap liftMap = false := by
  decide +kernel

def interposedBase : PatternCode 4 := { targetBase with U := {1, 3} }

def misplacedMap (i : Fin 3) : Fin 4 := if i = 0 then 0 else 3

/-- The old target point `1` lies between the proposed new image and its anchor. -/
theorem placement_regression :
    arithmeticFields sourceBase sourcePlus interposedBase extraTarget baseMap misplacedMap =
      [true, true, true, true, true, true, true, true, true, false] ∧
      sourceBase.checkLifting sourcePlus interposedBase extraTarget baseMap misplacedMap = false := by
  decide +kernel

def firstEdge : PatternCode 3 := { sourcePlus with r₁ := fun i j => decide (i ≤ j) }

def bothEdges : PatternCode 3 := { firstEdge with r₂ := fun i j => decide (i ≤ j) }

def targetFirstEdge : PatternCode 4 := { targetPlus with r₁ := fun i j => decide (i ≤ j) }

/-- Patternhood and all arithmetic fields hold; exact table agreement still matters. -/
theorem relation_regression :
    firstEdge.checkPattern = true ∧ bothEdges.checkPattern = true ∧
      targetFirstEdge.checkPattern = true ∧
      sourceBase.checkLifting firstEdge targetBase targetPlus baseMap liftMap = false ∧
      sourceBase.checkLifting bothEdges targetBase targetFirstEdge baseMap liftMap = false ∧
      sourceBase.checkLifting firstEdge targetBase targetFirstEdge baseMap liftMap = true := by
  decide +kernel

def changedOldSource : PatternCode 3 := { sourceBase with r₁ := fun _ _ => false }

def changedOldTarget : PatternCode 4 := { targetBase with r₂ := fun _ _ => false }

theorem substructure_regression :
    changedOldSource.checkLifting sourcePlus targetBase targetPlus baseMap liftMap = false ∧
      sourceBase.checkLifting sourcePlus changedOldTarget targetPlus baseMap liftMap = false := by
  decide +kernel

def empty : PatternCode 0 where
  U := ∅
  r₁ i := Fin.elim0 i
  r₂ i := Fin.elim0 i

def point : PatternCode 1 where
  U := {0}
  r₁ _ _ := true
  r₂ _ _ := true

def emptyMap (m : ℕ) : Fin 0 → Fin m := Fin.elim0

theorem empty_regression :
    empty.checkLifting empty empty empty (emptyMap 0) (emptyMap 0) = true ∧
      empty.checkLifting empty point point (emptyMap 1) (emptyMap 1) = true := by
  decide +kernel

theorem encoded_regression :
    checkLifting 3 4 (encode sourceBase) (encode sourcePlus) (encode targetBase)
      (encode targetPlus) (encode baseMap) (encode liftMap) = true ∧
    checkLifting 3 4 (encode sourceBase) (encode sourcePlus) (encode interposedBase)
      (encode extraTarget) (encode baseMap) (encode misplacedMap) = false ∧
    checkLifting 3 4 (encode sourceBase) (encode bothEdges) (encode targetBase)
      (encode targetFirstEdge) (encode baseMap) (encode liftMap) = false := by
  simp only [checkLifting_encode]
  decide +kernel

theorem encoded_empty_regression :
    checkLifting 0 0 (encode empty) (encode empty) (encode empty) (encode empty)
      (encode (emptyMap 0)) (encode (emptyMap 0)) = true ∧
    checkLifting 0 1 (encode empty) (encode empty) (encode point) (encode point)
      (encode (emptyMap 1)) (encode (emptyMap 1)) = true := by
  simp only [checkLifting_encode]
  decide +kernel

theorem malformed_source_rejects (n m pplus q qplus h f : ℕ) :
    checkLifting n m 0 pplus q qplus h f = false := by
  have hz : decodeData n 0 = none := by
    simp [decodeData, PrimitiveRationalPresentation.decodeFields,
      PrimitiveRationalPresentation.decodeField]
  simp [checkLifting, decodeInput, pairDecoded, hz]

theorem malformed_target_rejects :
    checkLifting 3 4 (encode sourceBase) (encode sourcePlus) (encode targetBase)
      0 (encode baseMap) (encode liftMap) = false := by
  have hz : decodeData 4 0 = none := by
    simp [decodeData, PrimitiveRationalPresentation.decodeFields,
      PrimitiveRationalPresentation.decodeField]
  simp only [checkLifting, decodeInput, pairDecoded, decodeData_encode, decodeMap_encode, hz,
    Option.bind_some, Option.bind_none, Option.map_some, Option.map_none, Option.getD_none]

def narrowSource : PatternCode 2 where
  U := {0}
  r₁ i j := decide (i = j)
  r₂ i j := decide (i = j)

def narrowMap : Fin 2 → Fin 1 := fun _ => 0

/-- Both decoders enforce total-map bounds even at source label `1`, which
belongs to neither the old nor extended source carrier. -/
theorem off_carrier_map_bounds_reject :
    checkLifting 2 1 (encode narrowSource) (encode narrowSource) (encode point) (encode point)
      (encode ([Nat.pair 0 0, Nat.pair 1 1] : List ℕ)) (encode narrowMap) = false ∧
    checkLifting 2 1 (encode narrowSource) (encode narrowSource) (encode point) (encode point)
      (encode narrowMap) (encode ([Nat.pair 0 0, Nat.pair 1 1] : List ℕ)) = false := by
  have hm : decodeMap 2 1 (encode ([Nat.pair 0 0, Nat.pair 1 1] : List ℕ)) = none := by
    decide +kernel
  simp only [checkLifting, decodeInput, pairDecoded, decodeData_encode, decodeMap_encode, hm,
    Option.bind_some, Option.bind_none, Option.map_some, Option.map_none, Option.getD_none, and_self]

theorem malformed_map_lengths_reject :
    checkLifting 2 1 (encode narrowSource) (encode narrowSource) (encode point) (encode point)
      0 (encode narrowMap) = false ∧
    checkLifting 2 1 (encode narrowSource) (encode narrowSource) (encode point) (encode point)
      (encode narrowMap) 0 = false := by
  have hm : decodeMap 2 1 0 = none := by decide +kernel
  simp only [checkLifting, decodeInput, pairDecoded, decodeData_encode, decodeMap_encode, hm,
    Option.bind_some, Option.bind_none, Option.map_some, Option.map_none, Option.getD_none, and_self]

/-- The same machine recognizes a lifting, rejects misplaced points, and rejects malformed records. -/
theorem machine_regression : ∃ machine : Nat.Partrec.Code,
    machine.eval (Nat.pair (Nat.pair 3 4)
      (Nat.pair (Nat.pair (encode sourceBase) (encode sourcePlus))
        (Nat.pair (Nat.pair (encode targetBase) (encode targetPlus))
          (Nat.pair (encode baseMap) (encode liftMap))))) = Part.some (encode true) ∧
    machine.eval (Nat.pair (Nat.pair 3 4)
      (Nat.pair (Nat.pair (encode sourceBase) (encode sourcePlus))
        (Nat.pair (Nat.pair (encode interposedBase) (encode extraTarget))
          (Nat.pair (encode baseMap) (encode misplacedMap))))) = Part.some (encode false) ∧
    machine.eval (Nat.pair (Nat.pair 3 4)
      (Nat.pair (Nat.pair 0 0) (Nat.pair (Nat.pair 0 0) (Nat.pair 0 0)))) =
        Part.some (encode false) := by
  obtain ⟨machine, hm⟩ := checkLifting_program
  refine ⟨machine, ?_, ?_, ?_⟩
  · simpa only [encoded_regression.1] using hm 3 4 (encode sourceBase) (encode sourcePlus)
      (encode targetBase) (encode targetPlus) (encode baseMap) (encode liftMap)
  · simpa only [encoded_regression.2.1] using hm 3 4 (encode sourceBase) (encode sourcePlus)
      (encode interposedBase) (encode extraTarget) (encode baseMap) (encode misplacedMap)
  · simpa only [malformed_source_rejects] using hm 3 4 0 0 0 0 0 0

end Alexander313.Carlson.PrimitiveLiftingChecksExamples
