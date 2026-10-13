import Alexander313.Wilken.HereditaryNativeRelativeCollapseMonotonicity
import Alexander313.Wilken.HereditaryNativeHeightBoundary
import Alexander313.Wilken.SuccessorEpsilonBases

/-!
# Actual finite endpoint comparison at larger public bases

Every finite public base lies below the first positive cardinal at one.
On an interval of bases the genuine positive collapse families agree,
so the actual positive descending towers agree. The two actual zero-family
minima then give monotonicity of the finite LOW endpoints. These are
semantic source lemmas and do not invoke a native parser at base one.
No tower, endpoint, height or public-return oracle is supplied. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.LowPublicCoverage.Support

theorem finiteBase_one_le (r : Nat) : 1 ≤ finiteBase r := by
  simpa only [finiteBase_zero] using
    finiteBase_strictMono.monotone (Nat.zero_le r)

theorem finiteBase_lt_first_cardinal (r : Nat) :
    finiteBase r < omegaSequence 1 1 := by
  induction r with
  | zero => simpa only [finiteBase_zero] using omegaSequence_base_lt 1
  | succ r ih =>
    have hω := Iota.AlphaPlus.omega_succ 1 (finiteBase r)
      (finiteBase_one_le r) ih 0
    simpa only [hω] using finiteBase_lt_cardinal r

theorem terminalApproximant_base_eq (τ α : Ordinal.{0})
    (hle : τ ≤ α) (hlt : α < omegaSequence τ 1)
    (top : Nat) (htop : 0 < top) (k : Nat) :
    terminalApproximant τ top k = terminalApproximant α top k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [terminalApproximant_succ, terminalApproximant_succ,
      Iota.AlphaPlus.positive_collapse τ α hle hlt (top + 1) top htop
        (Nat.lt_succ_self top), ih]

theorem descendingApproximant_base_eq (τ α : Ordinal.{0})
    (hle : τ ≤ α) (hlt : α < omegaSequence τ 1)
    (top d k : Nat) (hd : d < top) :
    descendingApproximant τ top d k = descendingApproximant α top d k := by
  revert hd
  induction d with
  | zero =>
    intro hd
    exact terminalApproximant_base_eq τ α hle hlt top hd k
  | succ d ih =>
    intro hd
    change sourceFiniteCollapse τ (top + 1) (top - (d + 1))
        (descendingApproximant τ top d k) =
      sourceFiniteCollapse α (top + 1) (top - (d + 1))
        (descendingApproximant α top d k)
    rw [Iota.AlphaPlus.positive_collapse τ α hle hlt (top + 1)
      (top - (d + 1)) (by omega) (by omega), ih (by omega)]

theorem finiteApproximant_positive_base_eq (τ α : Ordinal.{0})
    (hle : τ ≤ α) (hlt : α < omegaSequence τ 1)
    (n m k : Nat) (hm : 0 < m) (hmn : m < n) :
    finiteApproximant τ n m k = finiteApproximant α n m k := by
  exact descendingApproximant_base_eq τ α hle hlt (n - 1)
    (n - (m + 1)) k (by omega)

/-- The common positive tower is an actual argument in the larger base's
next-level grammar. Zero-family monotonicity uses the two genuine minima. -/
theorem finiteBoundary_mono_base (τ α : Ordinal.{0}) (hτ : 0 < τ)
    (hle : τ ≤ α) (hlt : α < omegaSequence τ 1)
    (n : Nat) (hn : 0 < n) :
    finiteBoundary τ n 0 ≤ finiteBoundary α n 0 := by
  have hα : 0 < α := hτ.trans_le hle
  rw [finiteBoundary_eq_next_firstApproximant τ hτ n 0 hn,
    finiteBoundary_eq_next_firstApproximant α hα n 0 hn,
    finiteApproximant_next τ (n + 1) 0 1 (by omega),
    finiteApproximant_next α (n + 1) 0 1 (by omega),
    finiteApproximant_positive_base_eq τ α hle hlt (n + 1) 1 1
      (by omega) (by omega)]
  apply RelativeCollapseMonotonicity.finite_collapse_mono_base τ α hτ hle hlt
    (n + 1) (by omega)
  · exact finiteApproximant_lower_notation α hα (n + 1) 1 (by omega) 1 le_rfl 1
  · have hs := finiteApproximant_lt_cardinal α hα (n + 1) 1 (by omega) 1
    simpa only [Iota.AlphaPlus.omega_succ τ α hle hlt 1] using hs

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.LowPublicCoverage.Support
