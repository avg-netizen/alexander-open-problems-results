import Alexander313.Wilken.PublicEpsilonNativeUnboundedLambda
import Alexander313.Wilken.HereditaryMuEpsilonCoefficientSupport

/-!
# The source3.14 note for the actual full-domain beta-context mu

An actual computed epsilon mu strictly above beta has coefficient equal
to mu, false indicator and zero offset. The genuine mapped product and
actual lambda execution therefore give mu=iotaDelta and lambda=mu+zeta.
The derived zeta<beta<mu supplies the actual greatest-component identity.
Every operator caller comes from the original ANY-q high-root guard.
No coefficient, product, indicator or component oracle is used. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.Mu

theorem epsilon_coefficient (q root : Nat) (ha : inputCheck q root = true)
    (he : Ordinal.omega0 ^ interpretation (betaCode q root) (muCode q root) =
      interpretation (betaCode q root) (muCode q root)) :
    interpretation (betaCode q root) (mappedCoefficient q root) =
        interpretation (betaCode q root) (muCode q root) ∧
      chi q root = false ∧ OmegaQuotient.coefficientOffset q root = 0 := by
  apply MuEpsilonCoefficient.epsilon_power_coefficient _ _ _ _
    (RhoMuSupport.mappedCoefficient_zero_or_limit q root ha) he
  rw [(muCode_spec q root ha).2.2, sourceValue, ← chi_correct q root ha]

theorem epsilon_delta_value (q root : Nat) (ha : inputCheck q root = true)
    (he : Ordinal.omega0 ^ interpretation (betaCode q root) (muCode q root) =
      interpretation (betaCode q root) (muCode q root))
    (hlarge : base (betaCode q root) < interpretation (betaCode q root) (muCode q root)) :
    interpretation (betaCode q root) (literalCode q root (OmegaQuotient.deltaCode root)) =
      interpretation (betaCode q root) (muCode q root) := by
  have hc := epsilon_coefficient q root ha he
  rw [MappedOmegaQuotient.literal_delta_coefficient_product q root ha]
  change base (betaCode q root) *
    (interpretation (betaCode q root) (mappedCoefficient q root) +
      (OmegaQuotient.coefficientOffset q root : Ordinal.{0})) = _
  rw [hc.1, hc.2.2, Nat.cast_zero, add_zero]
  exact LambdaEpsilonMu.epsilon_mul_absorb
    (base_pos _ (betaCode_baseCheck q root ha)) he hlarge

theorem epsilon_lambda_value (q root out : Nat) (ho : out ∈ Lambda.execute q root)
    (he : Ordinal.omega0 ^ interpretation (betaCode q root) (muCode q root) =
      interpretation (betaCode q root) (muCode q root))
    (hlarge : base (betaCode q root) < interpretation (betaCode q root) (muCode q root)) :
    interpretation (betaCode q root) out = interpretation (betaCode q root) (muCode q root) +
      DirectZeta.sourceValue q root := by
  have hs := Lambda.execute_spec q root out ho
  rw [hs.2.2.2, Lambda.sourceValue, epsilon_delta_value q root hs.1 he hlarge]

/-- The complete source3.14 note uses the actual mc definition. -/
theorem source_lemma_3_14_note (q root out : Nat) (ho : out ∈ Lambda.execute q root)
    (he : Ordinal.omega0 ^ interpretation (betaCode q root) (muCode q root) =
      interpretation (betaCode q root) (muCode q root))
    (hlarge : base (betaCode q root) < interpretation (betaCode q root) (muCode q root)) :
    interpretation (betaCode q root) (muCode q root) =
        interpretation (betaCode q root) (literalCode q root (OmegaQuotient.deltaCode root)) ∧
      interpretation (betaCode q root) (muCode q root) =
        Hereditary.LogEnd.mc (interpretation (betaCode q root) out) := by
  have ha := (Lambda.execute_spec q root out ho).1
  have hz : DirectZeta.sourceValue q root < base (betaCode q root) := by
    simpa only [beta_base q root ha] using Lambda.zeta_value_lt_root q root ha
  refine ⟨(epsilon_delta_value q root ha he hlarge).symm, ?_⟩
  rw [epsilon_lambda_value q root out ho he hlarge]
  exact (MuEpsilonCoefficient.epsilon_mc_add _ _ he (hz.trans hlarge)).symm

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.Mu
