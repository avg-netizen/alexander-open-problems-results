import Alexander313.Carlson.CoreIsominimal
import Alexander313.Carlson.CorePackageInputs

/-! Boundary checks for the common core and its inherited guard domain. -/

noncomputable section

namespace Alexander313.Carlson

theorem empty_pattern_realization_bound (P : Str ℚ) (hP : P.IsPattern)
    (hU : P.U = ∅) : (PatternRealization.ofPattern P hP).bound = 0 := by
  let A := PatternRealization.ofPattern P hP
  apply (A.ordinal.bound_eq_zero_iff 0).mpr
  simpa only [A.seed] using hU

theorem core_boundary_not_corePoint : ¬CorePoint coreBound := by
  rw [corePoint_iff_lt_coreBound]
  exact lt_irrefl _

theorem no_first_edge_to_core_boundary {a : Ordinal.{0}} (ha : a < coreBound) :
    ¬R1 a coreBound := fun h => (lt_irrefl coreBound) (core_lt_of_R1 ha h)

theorem no_second_edge_to_core_boundary {a : Ordinal.{0}} (ha : a < coreBound) :
    ¬R2 a coreBound := fun h => (lt_irrefl coreBound) (core_lt_of_R2 ha h)

theorem two_point_least_copy_in_core :
    ∃ h : ℚ → Ordinal.{0},
      Str.IsIso (rationalFullChain 2)
        (Str.ofOrdinals ((rationalFullChain 2).U.image h)) h ∧
      (∀ x ∈ (rationalFullChain 2).U, h x < coreBound) ∧
      ∀ g : ℚ → Ordinal.{0}, (rationalFullChain 2).CoveringR g →
        ∀ x ∈ (rationalFullChain 2).U, h x ≤ g x :=
  exists_minimal_copy_in_core _ (rationalFullChain_isPattern 2)

end Alexander313.Carlson
