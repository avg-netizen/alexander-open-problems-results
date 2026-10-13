import Alexander313.Wilken.MultiplicativeFactorRemoval

/-!
# Genuine principal quotients in a factor interval

Positive additive principals have a real left quotient whenever the
divisor is no greater than the dividend. The quotient is the omega power
of the genuine ordinal difference of their exponents. Thus an additive
principal strictly between a prefix and its product with a final factor
has a smaller positive additive quotient. A descending final factor also
excludes multiplicative principality of that intervening input. No
quotient equation, factorization, or tracking comparison is assumed.
Source-only uncompiled; source coding and subsidiary tracking order remain
separate consumers.
-/

namespace Alexander313.Wilken.MultiplicativePrincipalInterval

universe u

open MultiplicativePrincipalArithmetic

theorem omega_power_quotient (x y : Ordinal.{u}) (hxy : x ≤ y) :
    Ordinal.omega0 ^ y / Ordinal.omega0 ^ x = Ordinal.omega0 ^ (y - x) := by
  have he : Ordinal.omega0 ^ y =
      Ordinal.omega0 ^ x * Ordinal.omega0 ^ (y - x) := by
    rw [← Ordinal.opow_add, Ordinal.add_sub_cancel_of_le hxy]
  rw [he, Ordinal.mul_div_cancel _
    (Ordinal.opow_ne_zero x Ordinal.omega0_ne_zero)]

/-- The actual left quotient, including the equal-input quotient one,
is a positive additive principal and genuinely cancels its divisor. -/
theorem principal_quotient_spec {eta alpha : Ordinal.{u}}
    (heta : 0 < eta) (he : Ordinal.IsPrincipal (· + ·) eta)
    (ha : Ordinal.IsPrincipal (· + ·) alpha) (hle : eta ≤ alpha) :
    0 < alpha / eta ∧ Ordinal.IsPrincipal (· + ·) (alpha / eta) ∧
      eta * (alpha / eta) = alpha := by
  rcases Ordinal.isPrincipal_add_iff_zero_or_omega0_opow.mp he with hz | ⟨x, hx⟩
  · exact False.elim ((ne_of_gt heta) hz)
  rcases Ordinal.isPrincipal_add_iff_zero_or_omega0_opow.mp ha with hz | ⟨y, hy⟩
  · exact False.elim ((ne_of_gt (heta.trans_le hle)) hz)
  have hxy : x ≤ y := (Ordinal.opow_le_opow_iff_right Ordinal.one_lt_omega0).mp
    (by simpa only [← hx, ← hy] using hle)
  have hq : alpha / eta = Ordinal.omega0 ^ (y - x) := by
    rw [← hx, ← hy]
    exact omega_power_quotient x y hxy
  refine ⟨by rw [hq]; exact Ordinal.opow_pos _ Ordinal.omega0_pos,
    by rw [hq]; exact Ordinal.isPrincipal_add_omega0_opow _, ?_⟩
  rw [hq, ← hx, ← hy, ← Ordinal.opow_add, Ordinal.add_sub_cancel_of_le hxy]

/-- Strict interval bounds derive strict bounds on the actual quotient,
rather than supplying a smaller factor as a premise. -/
theorem strict_quotient_bounds {eta alpha factor : Ordinal.{u}}
    (heta : 0 < eta) (he : Ordinal.IsPrincipal (· + ·) eta)
    (ha : Ordinal.IsPrincipal (· + ·) alpha)
    (hl : eta < alpha) (hr : alpha < eta * factor) :
    1 < alpha / eta ∧ alpha / eta < factor ∧
      Ordinal.IsPrincipal (· + ·) (alpha / eta) ∧ eta * (alpha / eta) = alpha := by
  have hs := principal_quotient_spec heta he ha hl.le
  have hleft : 1 < alpha / eta := by
    apply (Ordinal.isNormal_mul_right heta).strictMono.lt_iff_lt.mp
    simpa only [mul_one, hs.2.2] using hl
  have hright : alpha / eta < factor :=
    (Ordinal.lt_mul_iff_div_lt (ne_of_gt heta)).mp hr
  exact ⟨hleft, hright, hs.2.1, hs.2.2⟩

/-- A genuine descending final factor forces every intervening input to
be nonmultiplicative, by its actual multiplicative closure predicate. -/
theorem intervening_not_multiplicative {eta alpha factor : Ordinal.{u}}
    (hf : factor ≤ eta) (hl : eta < alpha) (hr : alpha < eta * factor) :
    ¬ IsMultiplicativePrincipal alpha := by
  intro hm
  exact (hm.2.2 hl (hf.trans_lt hl)).not_ge hr.le

/-- The original difficult interval yields a true smaller principal
quotient below both the original prefix and intervening input. This is an
arithmetic subsidiary caller, not a tracking-word comparison theorem. -/
theorem descending_interval_spec {eta alpha factor : Ordinal.{u}}
    (heta : 0 < eta) (he : Ordinal.IsPrincipal (· + ·) eta)
    (ha : Ordinal.IsPrincipal (· + ·) alpha) (hf : factor ≤ eta)
    (hl : eta < alpha) (hr : alpha < eta * factor) :
    ¬ IsMultiplicativePrincipal alpha ∧ 1 < alpha / eta ∧
      alpha / eta < factor ∧ alpha / eta < eta ∧ alpha / eta < alpha ∧
        Ordinal.IsPrincipal (· + ·) (alpha / eta) ∧ eta * (alpha / eta) = alpha := by
  have hs := strict_quotient_bounds heta he ha hl hr
  have hsmall : alpha / eta < eta := hs.2.1.trans_le hf
  exact ⟨intervening_not_multiplicative hf hl hr, hs.1, hs.2.1, hsmall,
    hsmall.trans hl, hs.2.2.1, hs.2.2.2⟩

end Alexander313.Wilken.MultiplicativePrincipalInterval
