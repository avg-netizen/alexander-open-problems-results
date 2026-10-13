import Alexander313.Wilken.HereditaryNativeSourceRho
import Alexander313.Wilken.HereditaryNativeHeightBoundary
import Alexander313.Wilken.HighCollapseEpsilon

/-!
# Genuine epsilon closure of the positive native height endpoints

The endpoint of fragment n>0 is the next fragment's first descending
approximant. Its outer theta-zero has an actual level-one argument. The
existing high-collapse proof therefore makes the literal endpoint an epsilon;
the pinned ordinal multiplication-principal theorem gives its actual product
closure. Strict endpoint growth supplies the original base's strict bound.

No endpoint equation, epsilon predicate, closure or height oracle is an input.
The auxiliary finite argument proof uses the constructed finite collapses on
their genuine domains. All proof candidates remain uncompiled.
-/

namespace Alexander313.Wilken

private theorem firstApproximant_base_le (τ : Ordinal.{0}) (n m : Nat)
    (hm : m < n) : omegaSequence τ m ≤ finiteApproximant τ n m 1 := by
  by_cases hnext : m + 1 < n
  · rw [finiteApproximant_next τ n m 1 hnext]
    exact (sourceFiniteCollapse_bounds τ n m hm _).1
  · have hn : n = m + 1 := by omega
    subst n
    rw [finiteApproximant_top, terminalApproximant_succ, terminalApproximant_zero]
    exact (sourceFiniteCollapse_bounds τ (m + 1) m (Nat.lt_succ_self m) 0).1

namespace RelativeTerm.Hereditary.NativeContext.HeightBoundary

/-- Every positive literal height endpoint is a genuine epsilon fixed
point, derived from its actual high finite-collapse argument. -/
theorem endpoint_epsilon (q n : Nat) (hq : baseCheck q = true) (hn : 0 < n) :
    Ordinal.omega0 ^ endpoint q n = endpoint q n := by
  have hp := base_pos q hq
  have hlevel : 1 < n + 1 := by omega
  let α := finiteApproximant (base q) (n + 1) 1 1
  have hs : α < omegaSequence (base q) 2 :=
    finiteApproximant_lt_cardinal (base q) hp (n + 1) 1 hlevel 1
  have ha : sourceNotation (base q) (n + 1) 1 α :=
    finiteApproximant_lower_notation (base q) hp (n + 1) 1 hlevel 1 le_rfl 1
  have hh : omegaSequence (base q) 1 ≤ α :=
    firstApproximant_base_le (base q) (n + 1) 1 hlevel
  have he : endpoint q n = sourceFiniteCollapse (base q) (n + 1) 0 α := by
    rw [endpoint_eq_finiteBoundary q n hq hn,
      finiteBoundary_eq_next_firstApproximant (base q) hp n 0 hn,
      finiteApproximant_next (base q) (n + 1) 0 1 (by omega)]
  rw [he]
  exact ((sourceFiniteCollapse_epsilon_above_base_iff (base q)
    (Or.inr (SourceChi.epsilon_base q hq)) (n + 1) 0 (by omega) α hs ha).mpr hh).1

/-- Literal epsilon equality derives closure under real ordinal
multiplication; it is not an extra arithmetic premise. -/
theorem endpoint_mul_closed (q n : Nat) (hq : baseCheck q = true) (hn : 0 < n) :
    Ordinal.IsPrincipal (· * ·) (endpoint q n) := by
  have he := endpoint_epsilon q n hq hn
  simpa only [he] using Ordinal.isPrincipal_mul_omega0_opow_opow (endpoint q n)

/-- The base is strictly below every positive height endpoint. -/
theorem base_lt_endpoint (q n : Nat) (hq : baseCheck q = true) (hn : 0 < n) :
    base q < endpoint q n := by
  simpa only [endpoint_zero q hq] using endpoint_strictMono q hq hn

end RelativeTerm.Hereditary.NativeContext.HeightBoundary

end Alexander313.Wilken
