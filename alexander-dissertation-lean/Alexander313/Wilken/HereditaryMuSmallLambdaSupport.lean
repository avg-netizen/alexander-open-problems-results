import Alexander313.Wilken.HereditaryLambdaEpsilonMuSupport

/-!
# The genuine small-mu half of source3.14(c)

The actual corrected omega power below epsilon alpha forces the total
uncorrected coefficient below alpha. A positive total coefficient gives
the lower product bound alpha. The genuine ordinal principal-power
remainder inequality bounds alpha*coefficient+zeta strictly below alpha^2.
The operator adapters derive positivity from original Delta. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.MuSmallLambda

theorem corrected_coefficient_le (coefficient : Ordinal.{0}) (k : Nat) (bit : Bool) :
    coefficient + (k : Ordinal.{0}) ≤ coefficient + cond bit (1 : Ordinal.{0}) 0 +
      (k : Ordinal.{0}) := by
  cases bit with
  | false => simpa only [Bool.cond_false, add_zero] using le_refl (coefficient + (k : Ordinal.{0}))
  | true =>
    exact add_le_add_left
      (show coefficient ≤ coefficient + (1 : Ordinal.{0}) from le_self_add) (k : Ordinal.{0})

theorem small_power_lambda_bounds (alpha coefficient lambda zeta : Ordinal.{0})
    (k : Nat) (bit : Bool) (he : Ordinal.omega0 ^ alpha = alpha)
    (hpositive : 0 < coefficient + (k : Ordinal.{0})) (hz : zeta < alpha)
    (hsmall : Ordinal.omega0 ^ (coefficient + cond bit (1 : Ordinal.{0}) 0 +
      (k : Ordinal.{0})) < alpha)
    (hl : lambda = alpha * (coefficient + (k : Ordinal.{0})) + zeta) :
    alpha ≤ lambda ∧ lambda < alpha * alpha := by
  have hexponent := (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mp
    (hsmall.trans_eq he.symm)
  have htotal := (corrected_coefficient_le coefficient k bit).trans_lt hexponent
  have hlower : alpha ≤ alpha * (coefficient + (k : Ordinal.{0})) := by
    simpa only [mul_one] using mul_le_mul_right (Order.one_le_iff_pos.mpr hpositive) alpha
  refine ⟨hlower.trans (by rw [hl]; exact le_self_add), ?_⟩
  rw [hl]
  have htail : zeta < Ordinal.omega0 ^ alpha := hz.trans_eq he.symm
  simpa only [he] using Ordinal.opow_mul_add_lt_opow_mul htail htotal

end Alexander313.Wilken.RelativeTerm.Hereditary.MuSmallLambda
