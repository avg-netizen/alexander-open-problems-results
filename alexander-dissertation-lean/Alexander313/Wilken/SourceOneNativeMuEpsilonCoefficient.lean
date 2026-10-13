import Alexander313.Wilken.SourceOneNativeLambdaRhoMu
import Alexander313.Wilken.HereditaryMuEpsilonCoefficientSupport

/-!
# The source3.14 epsilon-mu note in the original source-one dictionary

Original source-zero admission and actual source-one quotient/iota/mu
give the coefficient and indicator identities. Only the actual target
alpha uses the native epsilon dictionary. The original lambda execution
then has greatest component equal to actual epsilon mu above alpha.
No native base-one source parser or operator oracle is used. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.Mu

theorem epsilon_coefficient (a : Nat) (ha : inputCheck a = true)
    (he : Ordinal.omega0 ^ NativeContext.interpretation (alphaCode a) (muCode a) =
      NativeContext.interpretation (alphaCode a) (muCode a)) :
    NativeContext.interpretation (alphaCode a) (mappedCoefficient a) =
        NativeContext.interpretation (alphaCode a) (muCode a) ∧
      chi a = false ∧ OmegaQuotient.coefficientOffset a = 0 := by
  apply MuEpsilonCoefficient.epsilon_power_coefficient _ _ _ _
    (RhoMuSupport.mappedCoefficient_zero_or_limit a ha) he
  rw [(muCode_spec a ha).2.2, sourceValue, ← chi_correct a ha]

theorem epsilon_delta_value (a : Nat) (ha : inputCheck a = true)
    (he : Ordinal.omega0 ^ NativeContext.interpretation (alphaCode a) (muCode a) =
      NativeContext.interpretation (alphaCode a) (muCode a))
    (hlarge : NativeContext.base (alphaCode a) < NativeContext.interpretation (alphaCode a) (muCode a)) :
    NativeContext.interpretation (alphaCode a) (literalCode a (OmegaQuotient.deltaCode a)) =
      NativeContext.interpretation (alphaCode a) (muCode a) := by
  have hc := epsilon_coefficient a ha he
  rw [MappedOmegaQuotient.literal_delta_coefficient_product a ha]
  change NativeContext.base (alphaCode a) *
    (NativeContext.interpretation (alphaCode a) (mappedCoefficient a) +
      (OmegaQuotient.coefficientOffset a : Ordinal.{0})) = _
  rw [hc.1, hc.2.2, Nat.cast_zero, add_zero]
  exact LambdaEpsilonMu.epsilon_mul_absorb
    (NativeContext.base_pos _ (alphaCode_baseCheck a ha)) he hlarge

theorem epsilon_lambda_value (a out : Nat) (ho : out ∈ Lambda.execute a)
    (he : Ordinal.omega0 ^ NativeContext.interpretation (alphaCode a) (muCode a) =
      NativeContext.interpretation (alphaCode a) (muCode a))
    (hlarge : NativeContext.base (alphaCode a) < NativeContext.interpretation (alphaCode a) (muCode a)) :
    NativeContext.interpretation (alphaCode a) out =
      NativeContext.interpretation (alphaCode a) (muCode a) + SourceZeta.sourceValue 0 a := by
  have hs := Lambda.execute_spec a out ho
  rw [hs.2.2, epsilon_delta_value a hs.1 he hlarge]

theorem source_lemma_3_14_note (a out : Nat) (ho : out ∈ Lambda.execute a)
    (he : Ordinal.omega0 ^ NativeContext.interpretation (alphaCode a) (muCode a) =
      NativeContext.interpretation (alphaCode a) (muCode a))
    (hlarge : NativeContext.base (alphaCode a) < NativeContext.interpretation (alphaCode a) (muCode a)) :
    NativeContext.interpretation (alphaCode a) (muCode a) =
        NativeContext.interpretation (alphaCode a) (literalCode a (OmegaQuotient.deltaCode a)) ∧
      NativeContext.interpretation (alphaCode a) (muCode a) =
        LogEnd.mc (NativeContext.interpretation (alphaCode a) out) := by
  have ha := (Lambda.execute_spec a out ho).1
  have hz : SourceZeta.sourceValue 0 a < NativeContext.base (alphaCode a) := by
    simpa only [alpha_base a ha] using Lambda.zeta_value_lt_root a ha
  refine ⟨(epsilon_delta_value a ha he hlarge).symm, ?_⟩
  rw [epsilon_lambda_value a out ho he hlarge]
  exact (MuEpsilonCoefficient.epsilon_mc_add _ _ he (hz.trans hlarge)).symm

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.Mu
