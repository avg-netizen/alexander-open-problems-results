import Alexander313.Carlson.TallnessExamples

open Alexander313.Carlson
open Ordinal Cardinal

example : ∀ γ : Ordinal.{0}, γ < ω₁ → ∃ a, γ < a ∧ ReflectionPoint a :=
  fun _ h => exists_reflectionPoint_above h

example : ∀ a b : Ordinal.{0}, ReflectionPoint a → ReflectionPoint b → a ≤ b → R2 a b :=
  fun _ _ ha hb hab => ha.second hb hab

example : ∀ n : ℕ, ∃ xs : List Ordinal.{0},
    xs.length = n ∧ xs.Pairwise (· < ·) ∧ xs.Pairwise R2 := exists_finite_second_chain

example {α : Type*} [LinearOrder α] (P : Str α) : P.IsPattern → P.Covered :=
  every_pattern_covered P

#print axioms WitnessRequest.chosen_realizes
#print axioms WitnessRequest.bound_lt_omega_one
#print axioms WitnessRequest.exists_below_bound
#print axioms countable_Iic_of_lt_omega_one
#print axioms countable_witnessRequest
#print axioms witnessBound_lt_omega_one
#print axioms reflect_request
#print axioms CofinalRequest.exists_blocker
#print axioms CofinalRequest.blocker_lt
#print axioms CofinalRequest.blocker_blocks
#print axioms countable_cofinalRequest
#print axioms obstructionBound_lt_omega_one
#print axioms closureStep_lt_omega_one
#print axioms lt_closureStep
#print axioms witnessBound_lt_closureStep
#print axioms obstructionBound_lt_closureStep
#print axioms exists_reflectionPoint_above
#print axioms ReflectionPoint.finite_copy
#print axioms ReflectionPoint.first
#print axioms ReflectionPoint.cofinal_down
#print axioms ReflectionPoint.cofinal_up
#print axioms ReflectionPoint.second
#print axioms nextReflectionPoint_spec
#print axioms lt_advanceReflectionOrdinal
#print axioms reflectionSequence_point
#print axioms reflectionSequence_strictMono
#print axioms reflectionSequence_second
#print axioms exists_finite_second_chain
#print axioms exists_ordinal_guard
#print axioms exists_covering_below_omega_one
#print axioms every_pattern_covered
#print axioms completeFiniteChain_isPattern
#print axioms completeFiniteChain_covered
#print axioms empty_second_chain
#print axioms zero_rank_ordinal_guard
#print axioms reversedFirstStructure_not_covered
