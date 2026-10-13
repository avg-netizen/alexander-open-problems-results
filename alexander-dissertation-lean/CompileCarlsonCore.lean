import Alexander313.Carlson.CoreExamples

open Alexander313 Alexander313.Carlson
open Ordinal Cardinal

example : coreBound < ω₁ := coreBound_lt_omega_one

example (a : Ordinal.{0}) :
    (∃ U : Finset Ordinal.{0}, a ∈ U ∧ IsominimalOrdinalSet U) ↔ a < coreBound :=
  isominimal_core_iff_lt a

example : ∀ k : ℕ, ∃ top : Ordinal.{0}, ∃ tail : List Ordinal.{0},
    tail.length = k ∧ (top :: tail).Pairwise (· < ·) ∧
      (top :: tail).Pairwise R2 ∧ ∀ z ∈ top :: tail, z < coreBound :=
  exists_guard_in_core

example {Label : Type} [LinearOrder Label] (P : OrdinalPresentation Label)
    (hbound : P.bound = coreBound) : ∀ k, ∃ top : Label, GuardHead P.second k top :=
  P.tall_of_core hbound

example : Nonempty (ℕ ≃ Set.Iio coreBound) := exists_core_nat_equiv

#print axioms exists_fair_ordinalRealization_of_pattern
#print axioms exists_minimal_ordinal_copy_of_pattern
#print axioms exists_patternRealization
#print axioms PatternRealization.seed_isIso
#print axioms PatternRealization.seed_covering
#print axioms PatternRealization.seed_minimal
#print axioms PatternRealization.seed_label_lt_bound
#print axioms PatternRealization.bound_lt_omega_one
#print axioms coreBound_lt_omega_one
#print axioms core_label_lt
#print axioms stage_label_corePoint
#print axioms corePoint_iff_lt_coreBound
#print axioms core_lt_of_R1
#print axioms core_lt_of_R2
#print axioms corePoint_of_R1
#print axioms corePoint_of_R2
#print axioms exists_minimal_copy_in_core
#print axioms corePoint_iff_isominimal
#print axioms isominimal_core_iff_lt
#print axioms rationalFullChain_isPattern
#print axioms rationalFullChain_mem
#print axioms exists_guard_in_core
#print axioms exists_finite_second_chain_in_core
#print axioms coreBound_pos
#print axioms corePoint_zero
#print axioms countable_core
#print axioms infinite_core
#print axioms exists_core_nat_equiv
#print axioms OrdinalPresentation.tall_of_core
#print axioms OrdinalPackage.ofCarlsonCore
#print axioms empty_pattern_realization_bound
#print axioms core_boundary_not_corePoint
#print axioms no_first_edge_to_core_boundary
#print axioms no_second_edge_to_core_boundary
#print axioms two_point_least_copy_in_core
