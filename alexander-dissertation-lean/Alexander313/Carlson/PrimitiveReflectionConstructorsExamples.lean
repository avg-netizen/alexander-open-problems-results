import Alexander313.Carlson.PrimitiveReflectionConstructors
import Alexander313.Carlson.PrimitiveReflectionChecksExamples
import Alexander313.Carlson.PrimitiveSExpression

/-!
# Kernel regressions for reflection targets and derived-code recursion

The controls separate first-level bridges from second-relation edges, retain
off-carrier table behavior, accept noncanonical original carrier codes, reject
invalid total maps, and construct targets even when reflection hypotheses
fail. Recursion controls use the exact atom and cons pairing format.
-/

namespace Alexander313.Carlson.PrimitiveReflectionConstructorsExamples

open Encodable Finite PrimitivePatternCode PrimitiveContinuityChecks
open PrimitiveEmbeddingChecks PrimitiveReflectionChecks PrimitiveReflectionConstructors
open PrimitiveReflectionChecksExamples (base inserted downMap upMap badPattern)
open PrimitiveEndpointIso (entry₁ entry₂)

private theorem encode_fin {n : ℕ} (i : Fin n) : encode i = i.val := rfl

theorem downward_bridge_regression :
    entry₁ (downwardData 5 (dataView base) false 2 4 {1} (mapView downMap)) (1, 4) = false ∧
    entry₁ (downwardData 5 (dataView base) true 2 4 {1} (mapView downMap)) (1, 4) = true ∧
    entry₂ (downwardData 5 (dataView base) true 2 4 {1} (mapView downMap)) (1, 4) = false ∧
    entry₁ (downwardData 5 (dataView base) false 2 4 {1} (mapView downMap)) (0, 1) = true := by
  decide +kernel

theorem upward_cross_regression :
    entry₁ (upwardData 5 (dataView base) (dataView inserted) 2 4 {3} (mapView upMap)) (2, 3) = true ∧
    entry₂ (upwardData 5 (dataView base) (dataView inserted) 2 4 {3} (mapView upMap)) (2, 3) = false ∧
    entry₂ (upwardData 5 (dataView base) (dataView inserted) 2 4 {3} (mapView upMap)) (0, 3) = true ∧
    entry₂ (upwardData 5 (dataView base) (dataView inserted) 2 4 {3} (mapView upMap)) (3, 3) = true := by
  decide +kernel

/-- Old off-carrier edges are not silently retained in either target. -/
theorem off_carrier_regression :
    base.r₁ 3 3 = true ∧
    entry₁ (downwardData 5 (dataView base) true 2 4 {1} (mapView downMap)) (3, 3) = false ∧
    inserted.r₂ 1 1 = true ∧
    entry₂ (upwardData 5 (dataView base) (dataView inserted) 2 4 {3} (mapView upMap)) (1, 1) = false := by
  decide +kernel

theorem raw_targets_regression :
    constructDownward false 5 (encode base) 2 4 (encode ({1} : Finset (Fin 5)))
      (encode downMap) = some (encode (base.downward .one 2 4 {1} downMap)) ∧
    constructDownward true 5 (encode base) 2 4 (encode ({1} : Finset (Fin 5)))
      (encode downMap) = some (encode (base.downward .two 2 4 {1} downMap)) ∧
    constructUpward 5 (encode base) (encode inserted) 2 4 (encode ({3} : Finset (Fin 5)))
      (encode upMap) = some (encode (base.upward inserted 2 4 {3} upMap)) := by
  simpa [encode_fin, level]
    using And.intro (constructDownward_encode false base 2 4 {1} downMap)
      (And.intro (constructDownward_encode true base 2 4 {1} downMap)
        (constructUpward_encode base inserted 2 4 {3} upMap))

/-- Construction and validity checking have different obligations. -/
theorem invalid_pattern_still_constructs :
    badPattern.checkDownward .one 2 4 {2} {1} downMap = false ∧
    constructDownward false 5 (encode badPattern) 2 4 (encode ({1} : Finset (Fin 5)))
      (encode downMap) = some (encode (badPattern.downward .one 2 4 {1} downMap)) := by
  constructor
  · decide +kernel
  · simpa [encode_fin, level]
      using constructDownward_encode false badPattern 2 4 {1} downMap

/-- The original carrier decoder accepts unsorted duplicate-free lists. -/
theorem unsorted_carrier_regression :
    constructDownward true 5 (encode base) 2 4 (encode ([3, 1] : List (Fin 5)))
      (encode downMap) = some (encode (base.downward .two 2 4 {1, 3} downMap)) := by
  have hN : decodeCarrier 5 (encode ([3, 1] : List (Fin 5))) = some {1, 3} := by
    decide +kernel
  have heN : decodeCarrier 5 (encode ({1, 3} : Finset (Fin 5))) = some {1, 3} := by
    simp [decodeCarrier_eq, carrierView]
  have heq : constructDownward true 5 (encode base) 2 4
      (encode ([3, 1] : List (Fin 5))) (encode downMap) =
      constructDownward true 5 (encode base) 2 4
        (encode ({1, 3} : Finset (Fin 5))) (encode downMap) := by
    simp only [constructDownward, decodeParameters, hN, heN]
  rw [heq]
  simpa [encode_fin, level]
    using constructDownward_encode true base 2 4 {1, 3} downMap

theorem malformed_pattern_rejects (k : Bool) (n a b s f d : ℕ) :
    constructDownward k n 0 a b s f = none ∧
    constructUpward n 0 d a b s f = none ∧ constructUpward n d 0 a b s f = none := by
  simp [constructDownward, constructUpward, decodeData,
    PrimitiveRationalPresentation.decodeFields, PrimitiveRationalPresentation.decodeField]

theorem out_of_range_anchor_rejects (k : Bool) (n c d a b s f : ℕ) (ha : n ≤ a) :
    constructDownward k n c a b s f = none ∧ constructUpward n c d a b s f = none := by
  have hP : decodeParameters n a b s f = none := by
    simp [decodeParameters, decodeLabel, Nat.not_lt.mpr ha]
  simp [constructDownward, constructUpward, hP]

theorem duplicate_carrier_rejects :
    constructDownward true 5 (encode base) 2 4 (encode ([1, 1] : List (Fin 5)))
      (encode downMap) = none := by
  have hN : decodeCarrier 5 (encode ([1, 1] : List (Fin 5))) = none := by
    decide +kernel
  simp only [constructDownward, decodeParameters, hN, Option.bind_none]
  simp

/-- Every map entry must decode, including unused off-carrier positions. -/
theorem malformed_total_map_rejects :
    constructDownward false 5 (encode base) 2 4 (encode ({1} : Finset (Fin 5))) 0 = none ∧
    constructUpward 5 (encode base) (encode inserted) 2 4 (encode ({3} : Finset (Fin 5))) 0 = none := by
  have hF : decodeMap 5 5 0 = none := by decide +kernel
  simp [constructDownward, constructUpward, decodeParameters, hF]

theorem empty_dimension_rejects (k : Bool) (c d a b s f : ℕ) :
    constructDownward k 0 c a b s f = none ∧ constructUpward 0 c d a b s f = none :=
  out_of_range_anchor_rejects k 0 c d a b s f (Nat.zero_le a)

def nodeCount (code : ℕ) : ℕ :=
  PrimitiveSExpression.fold (fun (_ : Unit) _ => 1) (fun _ h t => 1 + h + t) () code

theorem nodeCount_primrec : Primrec nodeCount := by
  have ha : Primrec₂ (fun (_ : Unit) (_ : ℕ) => (1 : ℕ)) := Primrec₂.const 1
  have hc : Primrec (fun p : Unit × ℕ × ℕ => 1 + p.2.1 + p.2.2) :=
    Primrec.nat_add.comp
      (Primrec.nat_add.comp (Primrec.const 1) (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  exact (PrimitiveSExpression.fold_primrec ha hc).comp (Primrec.const ()) Primrec.id

/-- Both children, including a nonzero atom, use the original derived codes. -/
theorem nested_recursion_regression :
    nodeCount (Nat.pair (Nat.pair 1 0 + 1) (Nat.pair 0 7)) = 5 ∧ nodeCount 0 = 1 := by
  have hz : PrimitiveSExpression.fold (fun (_ : Unit) _ => (1 : ℕ))
      (fun _ h t => 1 + h + t) () 0 = 1 :=
    PrimitiveSExpression.fold_atom _ _ () 0
  simp only [nodeCount, PrimitiveSExpression.fold_cons, PrimitiveSExpression.fold_atom, hz]
  norm_num

theorem downward_machine_regression : ∃ machine : Nat.Partrec.Code,
    machine.eval (encode ((5, encode base, 2, 4, encode ({1} : Finset (Fin 5)),
      encode downMap) : RawDownward)) =
      Part.some (encode (some (encode (base.downward .one 2 4 {1} downMap)))) ∧
    machine.eval (encode ((5, 0, 0, 0, 0, 0) : RawDownward)) = Part.some (encode (none : Option ℕ)) := by
  obtain ⟨machine, hm⟩ := constructDownward_program false
  refine ⟨machine, ?_, ?_⟩
  · simpa only [raw_targets_regression.1] using
      hm 5 (encode base) 2 4 (encode ({1} : Finset (Fin 5))) (encode downMap)
  · simpa only [(malformed_pattern_rejects false 5 0 0 0 0 0).1] using hm 5 0 0 0 0 0

end Alexander313.Carlson.PrimitiveReflectionConstructorsExamples
