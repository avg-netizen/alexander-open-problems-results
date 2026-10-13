import Alexander313.Wilken.LimitFiniteDecomposition
import Alexander313.Wilken.HereditaryEpsilonOffsets

/-!
# Actual epsilon lambda determines its coefficient and finite offset

For an epsilon lambda strictly above alpha, multiplication by positive
alpha fixes lambda. Actual ordinal division of alpha*(coefficient+k)+zeta,
with zeta<alpha, determines coefficient+k=lambda. Genuine limit-plus-finite
uniqueness then determines coefficient=lambda and k=0. No coefficient,
offset or epsilon classification oracle is assumed. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.LambdaEpsilonMu

theorem epsilon_mul_absorb {alpha lambda : Ordinal.{0}} (ha : 0 < alpha)
    (he : Ordinal.omega0 ^ lambda = lambda) (hal : alpha < lambda) :
    alpha * lambda = lambda := by
  have hb : alpha < Ordinal.omega0 ^ Ordinal.omega0 ^ lambda := by
    simpa only [he] using hal
  simpa only [he] using Ordinal.mul_omega0_opow_opow ha hb

theorem epsilon_product_coefficient (alpha coefficient lambda zeta : Ordinal.{0}) (k : Nat)
    (ha : 0 < alpha) (he : Ordinal.omega0 ^ lambda = lambda) (hal : alpha < lambda)
    (hc : coefficient = 0 ∨ Order.IsSuccLimit coefficient) (hz : zeta < alpha)
    (hl : lambda = alpha * (coefficient + (k : Ordinal.{0})) + zeta) :
    coefficient = lambda ∧ k = 0 ∧ zeta = 0 := by
  have hm := epsilon_mul_absorb ha he hal
  have hq : coefficient + (k : Ordinal.{0}) = lambda := by
    calc
      coefficient + (k : Ordinal.{0}) =
          (alpha * (coefficient + (k : Ordinal.{0})) + zeta) / alpha := by
        rw [Ordinal.mul_add_div _ (ne_of_gt ha), Ordinal.div_eq_zero_of_lt hz, add_zero]
      _ = lambda / alpha := congrArg (fun x => x / alpha) hl.symm
      _ = (alpha * lambda) / alpha := congrArg (fun x => x / alpha) hm.symm
      _ = lambda := Ordinal.mul_div_cancel _ (ne_of_gt ha)
  have hprincipal := (EpsilonOffsets.epsilon_pos_principal he).2
  have hlimit := Ordinal.isSuccLimit_of_isPrincipal_add (EpsilonOffsets.epsilon_one_lt he) hprincipal
  have hcf := LimitFiniteDecomposition.coefficient_unique coefficient lambda k 0 hc (Or.inr hlimit)
    (by simpa only [Nat.cast_zero, add_zero] using hq)
  refine ⟨hcf.1, hcf.2, ?_⟩
  have hadd : lambda + zeta = lambda := by
    simpa only [hq, hm] using hl.symm
  exact add_left_cancel (show lambda + zeta = lambda + 0 from by
    simpa only [add_zero] using hadd)

theorem corrected_power_at_epsilon (coefficient lambda : Ordinal.{0}) (k : Nat) (bit : Bool)
    (he : Ordinal.omega0 ^ lambda = lambda) (hc : coefficient = lambda) (hk : k = 0) :
    Ordinal.omega0 ^ (coefficient + cond bit (1 : Ordinal.{0}) 0 + (k : Ordinal.{0})) =
      cond bit (lambda * Ordinal.omega0) lambda := by
  subst coefficient
  subst k
  cases bit with
  | false => simp only [Bool.cond_false, Nat.cast_zero, add_zero, he]
  | true =>
    simp only [Bool.cond_true, Nat.cast_zero, add_zero]
    rw [Ordinal.opow_add, Ordinal.opow_one, he]

end Alexander313.Wilken.RelativeTerm.Hereditary.LambdaEpsilonMu
