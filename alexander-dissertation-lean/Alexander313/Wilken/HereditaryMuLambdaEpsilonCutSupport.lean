import Alexander313.Wilken.HereditaryLambdaEpsilonMuSupport
import Alexander313.Wilken.HereditaryNativeRhoPowerBoundSupport

/-!
# Genuine greatest-epsilon arithmetic for the computed mu and lambda

The epsilon cut is the actual set of omega-power fixed points below an
ordinal. Its bounded nonempty supremum is proved to be its greatest
member. Corrected powers and actual product-plus-tail values have equal
cuts above the base; positivity and the mu-at-least-base hypothesis cover
the remaining epsilons. No greatest-epsilon or operator oracle. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.MuLambdaEpsilonCut

noncomputable def epsilonCut (x : Ordinal.{0}) : Set Ordinal.{0} :=
  {e | Ordinal.omega0 ^ e = e ∧ e ≤ x}

noncomputable def maxE (x : Ordinal.{0}) : Ordinal.{0} := sSup (epsilonCut x)

theorem epsilonCut_bddAbove (x : Ordinal.{0}) : BddAbove (epsilonCut x) :=
  ⟨x, fun e he => he.2⟩

theorem epsilonCut_image (x : Ordinal.{0}) :
    (fun e : Ordinal.{0} => Ordinal.omega0 ^ e) '' epsilonCut x = epsilonCut x := by
  ext e
  constructor
  · rintro ⟨d, hd, rfl⟩
    rw [hd.1]
    exact hd
  · intro he
    exact ⟨e, he, he.1⟩

/-- The bounded nonempty supremum is actually a greatest epsilon, rather
than an assumed maximum. -/
theorem maxE_isGreatest (x : Ordinal.{0}) (hn : (epsilonCut x).Nonempty) :
    IsGreatest (epsilonCut x) (maxE x) := by
  have hb := epsilonCut_bddAbove x
  have hfix : Ordinal.omega0 ^ maxE x = maxE x := by
    change Ordinal.omega0 ^ sSup (epsilonCut x) = sSup (epsilonCut x)
    rw [Order.IsNormal.map_sSup (Ordinal.isNormal_opow Ordinal.one_lt_omega0) hn hb,
      epsilonCut_image x]
  exact ⟨⟨hfix, csSup_le hn (fun e he => he.2)⟩, fun e he => le_csSup hb he⟩

theorem epsilon_mul_principal (e : Ordinal.{0})
    (he : Ordinal.omega0 ^ e = e) : Ordinal.IsPrincipal (· * ·) e := by
  simpa only [he] using Ordinal.isPrincipal_mul_omega0_opow_opow e

/-- Adding the real zero-or-one chi correction cannot cross an epsilon. -/
theorem epsilon_le_corrected_power_iff (m e : Ordinal.{0}) (k : Nat) (bit : Bool)
    (he : Ordinal.omega0 ^ e = e) :
    e ≤ Ordinal.omega0 ^ (m + cond bit (1 : Ordinal.{0}) 0 + (k : Ordinal.{0})) ↔
      e ≤ m + (k : Ordinal.{0}) := by
  constructor
  · intro h
    apply le_of_not_gt
    intro ht
    have hL : m + cond bit (1 : Ordinal.{0}) 0 + (k : Ordinal.{0}) < e := by
      cases bit with
      | false => simpa only [Bool.cond_false, add_zero] using ht
      | true =>
        simp only [Bool.cond_true,
          NativeContext.SourceRho.Uniform.PowerBoundSupport.finite_one_swap]
        exact (EpsilonOffsets.epsilon_pos_principal he).2 ht
          (EpsilonOffsets.epsilon_one_lt he)
    have hp := omegaPower_strictMono hL
    rw [he] at hp
    exact hp.not_ge h
  · intro h
    have hL : m + (k : Ordinal.{0}) ≤
        m + cond bit (1 : Ordinal.{0}) 0 + (k : Ordinal.{0}) := by
      cases bit with
      | false => simp only [Bool.cond_false, add_zero]
      | true =>
        simp only [Bool.cond_true,
          NativeContext.SourceRho.Uniform.PowerBoundSupport.finite_one_swap]
        exact le_self_add
    have hp := omegaPower_strictMono.monotone (h.trans hL)
    rwa [he] at hp

/-- Above the base epsilon, multiplication by that smaller positive base
and addition of the genuine smaller tail cannot cross an epsilon. -/
theorem epsilon_le_product_tail_iff (alpha a zeta e : Ordinal.{0})
    (ha : 0 < alpha) (he : Ordinal.omega0 ^ e = e)
    (hal : alpha < e) (hz : zeta < alpha) :
    e ≤ alpha * a + zeta ↔ e ≤ a := by
  constructor
  · intro h
    apply le_of_not_gt
    intro ht
    have hp := epsilon_mul_principal e he hal ht
    exact ((EpsilonOffsets.epsilon_pos_principal he).2 hp (hz.trans hal)).not_ge h
  · intro h
    have hp := mul_le_mul_right h alpha
    rw [LambdaEpsilonMu.epsilon_mul_absorb ha he hal] at hp
    exact hp.trans le_self_add

/-- Actual corrected omega-power and actual divided-head product-plus-tail
have exactly the same epsilon cut whenever mu is at least the base. -/
theorem epsilonCut_eq (alpha m zeta : Ordinal.{0}) (k : Nat) (bit : Bool)
    (ha : 0 < alpha) (hA : 0 < m + (k : Ordinal.{0})) (hz : zeta < alpha)
    (hmu : alpha ≤ Ordinal.omega0 ^
      (m + cond bit (1 : Ordinal.{0}) 0 + (k : Ordinal.{0}))) :
    epsilonCut (Ordinal.omega0 ^
      (m + cond bit (1 : Ordinal.{0}) 0 + (k : Ordinal.{0}))) =
    epsilonCut (alpha * (m + (k : Ordinal.{0})) + zeta) := by
  have hlambda : alpha ≤ alpha * (m + (k : Ordinal.{0})) + zeta := by
    have hp := mul_le_mul_right (Order.one_le_iff_pos.mpr hA) alpha
    simp only [mul_one] at hp
    exact hp.trans le_self_add
  ext e
  change (Ordinal.omega0 ^ e = e ∧ e ≤ Ordinal.omega0 ^
      (m + cond bit (1 : Ordinal.{0}) 0 + (k : Ordinal.{0}))) ↔
    (Ordinal.omega0 ^ e = e ∧ e ≤ alpha * (m + (k : Ordinal.{0})) + zeta)
  by_cases he : Ordinal.omega0 ^ e = e
  · simp only [he, true_and]
    by_cases hlow : e ≤ alpha
    · exact ⟨fun _ => hlow.trans hlambda, fun _ => hlow.trans hmu⟩
    · exact (epsilon_le_corrected_power_iff m e k bit he).trans
        (epsilon_le_product_tail_iff alpha _ zeta e ha he (lt_of_not_ge hlow) hz).symm
  · simp only [he, false_and]

/-- The printed maxima exist and agree; their existence and equality are
both consequences of the real arithmetic cut, not extra premises. -/
theorem maxE_eq_and_greatest (alpha m zeta : Ordinal.{0}) (k : Nat) (bit : Bool)
    (he : Ordinal.omega0 ^ alpha = alpha) (hA : 0 < m + (k : Ordinal.{0}))
    (hz : zeta < alpha) (hmu : alpha ≤ Ordinal.omega0 ^
      (m + cond bit (1 : Ordinal.{0}) 0 + (k : Ordinal.{0}))) :
    maxE (Ordinal.omega0 ^ (m + cond bit (1 : Ordinal.{0}) 0 + (k : Ordinal.{0}))) =
      maxE (alpha * (m + (k : Ordinal.{0})) + zeta) ∧
    IsGreatest (epsilonCut (Ordinal.omega0 ^
      (m + cond bit (1 : Ordinal.{0}) 0 + (k : Ordinal.{0}))))
      (maxE (Ordinal.omega0 ^ (m + cond bit (1 : Ordinal.{0}) 0 + (k : Ordinal.{0})))) := by
  have hs := epsilonCut_eq alpha m zeta k bit
    (EpsilonOffsets.epsilon_pos_principal he).1 hA hz hmu
  refine ⟨congrArg sSup hs, maxE_isGreatest _ ⟨alpha, he, hmu⟩⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.MuLambdaEpsilonCut
