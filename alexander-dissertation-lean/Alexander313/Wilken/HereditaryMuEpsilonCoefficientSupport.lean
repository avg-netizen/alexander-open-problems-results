import Alexander313.Wilken.HereditaryLambdaEpsilonMuSupport
import Alexander313.Wilken.HereditaryLogEnd

/-!
# An epsilon mu determines its actual finite-corrected coefficient

Power injectivity identifies the corrected exponent with epsilon mu.
Actual zero-or-limit plus finite uniqueness forces the coefficient to
mu and both the indicator and finite offset to zero. The actual ANF
first-component definition then identifies mc(mu+zeta) with mu whenever
zeta<mu. These are ordinal identities, with no operator oracle. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.MuEpsilonCoefficient

theorem epsilon_power_coefficient (coefficient mu : Ordinal.{0}) (k : Nat) (bit : Bool)
    (hc : coefficient = 0 ∨ Order.IsSuccLimit coefficient)
    (he : Ordinal.omega0 ^ mu = mu)
    (hp : Ordinal.omega0 ^ (coefficient + cond bit (1 : Ordinal.{0}) 0 +
      (k : Ordinal.{0})) = mu) :
    coefficient = mu ∧ bit = false ∧ k = 0 := by
  have hexponent := (Ordinal.opow_right_inj Ordinal.one_lt_omega0).mp (hp.trans he.symm)
  have hprincipal := (EpsilonOffsets.epsilon_pos_principal he).2
  have hlimit := Ordinal.isSuccLimit_of_isPrincipal_add
    (EpsilonOffsets.epsilon_one_lt he) hprincipal
  have hfinite : coefficient + ((cond bit 1 0 + k : Nat) : Ordinal.{0}) = mu := by
    rw [Nat.cast_add, ← add_assoc]
    cases bit <;> simpa only [Bool.cond_false, Bool.cond_true, Nat.cast_zero, Nat.cast_one]
      using hexponent
  have hcf := LimitFiniteDecomposition.coefficient_unique coefficient mu
    (cond bit 1 0 + k) 0 hc (Or.inr hlimit)
    (by simpa only [Nat.cast_zero, add_zero] using hfinite)
  have hn := Nat.eq_zero_of_add_eq_zero hcf.2
  have hb : bit = false := by
    cases hbit : bit with
    | false => rfl
    | true =>
      have h10 : (1 : Nat) = 0 := by simpa only [hbit, Bool.cond_true] using hn.1
      exact False.elim (Nat.one_ne_zero h10)
  exact ⟨hcf.1, hb, hn.2⟩

theorem epsilon_mc_add (mu zeta : Ordinal.{0})
    (he : Ordinal.omega0 ^ mu = mu) (hz : zeta < mu) :
    LogEnd.mc (mu + zeta) = mu := by
  have hm := EpsilonOffsets.epsilon_pos_principal he
  have hn : IsAdditiveNormalForm (mu :: canonicalANF zeta) := by
    refine ⟨?_, List.pairwise_cons.mpr ⟨?_, (canonicalANF_normal zeta).2⟩⟩
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hm
      · exact (canonicalANF_normal zeta).1 p hp
    · intro p hp
      exact (canonicalANF_mem_le hp).trans hz.le
  exact (LogEnd.mc_of_anf (mu + zeta) (mu :: canonicalANF zeta) hn (by
    rw [principalSum, principalSum_canonicalANF])).trans (by rfl)

end Alexander313.Wilken.RelativeTerm.Hereditary.MuEpsilonCoefficient
