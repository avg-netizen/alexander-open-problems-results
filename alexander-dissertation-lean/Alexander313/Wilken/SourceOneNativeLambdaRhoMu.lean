import Alexander313.Wilken.SourceOneNativeRhoMu
import Alexander313.Wilken.SourceOneNativeLambda
import Alexander313.Wilken.HereditaryLambdaEpsilonMuSupport

/-!
# Complete source3.14(a) and epsilon clause(d) at original source one

The original source-one lambda execution already constructs iotaDelta
plus the actual source-zero zeta. The genuine rho(mu) identity completes
the printed hence equation. When this actual lambda is epsilon above
alpha, division and true limit-plus-finite uniqueness force its computed
coefficient to lambda and its offset/zeta to zero. SAME-alpha indicator
invariance and the real mu formula give the printed two cases. No native
base-one source parser or coefficient/indicator oracle occurs. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.Lambda

theorem execute_product (a out : Nat) (ho : out ∈ execute a) :
    NativeContext.interpretation (alphaCode a) out = NativeContext.base (alphaCode a) *
      (NativeContext.interpretation (alphaCode a) (Mu.mappedCoefficient a) +
        (OmegaQuotient.coefficientOffset a : Ordinal.{0})) + SourceZeta.sourceValue 0 a := by
  have hs := execute_spec a out ho
  rw [hs.2.2, MappedOmegaQuotient.literal_delta_coefficient_product a hs.1]
  rfl

theorem source_lemma_3_14_a_lambda (a lambdaOut rhoOut : Nat) (hl : lambdaOut ∈ execute a)
    (hr : rhoOut ∈ NativeContext.SourceRho.Uniform.execute (alphaCode a) (Mu.muCode a)) :
    NativeContext.interpretation (alphaCode a) lambdaOut =
      NativeContext.interpretation (alphaCode a) rhoOut + SourceZeta.sourceValue 0 a := by
  have hs := execute_spec a lambdaOut hl
  rw [hs.2.2, RhoMu.source_lemma_3_14_a a rhoOut hs.1 hr]

theorem zeta_value_lt_root (a : Nat) (ha : inputCheck a = true) :
    SourceZeta.sourceValue 0 a < interpretation 0 a := by
  obtain ⟨out, ho⟩ := SourceZeta.zeta_returns 0 a (Bool.and_eq_true.mp ha).1
  rw [← (SourceZeta.zeta_value 0 a out ho).2.2]
  exact SourceZeta.zeta_bound 0 a out ho

theorem epsilon_coefficient (a out : Nat) (ho : out ∈ execute a)
    (he : Ordinal.omega0 ^ NativeContext.interpretation (alphaCode a) out =
      NativeContext.interpretation (alphaCode a) out)
    (hlarge : NativeContext.base (alphaCode a) < NativeContext.interpretation (alphaCode a) out) :
    NativeContext.interpretation (alphaCode a) (Mu.mappedCoefficient a) =
        NativeContext.interpretation (alphaCode a) out ∧
      OmegaQuotient.coefficientOffset a = 0 ∧ SourceZeta.sourceValue 0 a = 0 := by
  have hs := execute_spec a out ho
  exact LambdaEpsilonMu.epsilon_product_coefficient _ _ _ _ _
    (NativeContext.base_pos _ (alphaCode_baseCheck a hs.1)) he hlarge
    (RhoMuSupport.mappedCoefficient_zero_or_limit a hs.1)
    (by simpa only [alpha_base a hs.1] using zeta_value_lt_root a hs.1)
    (execute_product a out ho)

theorem source_lemma_3_14_d (a lambdaOut : Nat) (hl : lambdaOut ∈ execute a)
    (he : Ordinal.omega0 ^ NativeContext.interpretation (alphaCode a) lambdaOut =
      NativeContext.interpretation (alphaCode a) lambdaOut)
    (hlarge : NativeContext.base (alphaCode a) < NativeContext.interpretation (alphaCode a) lambdaOut) :
    NativeContext.interpretation (alphaCode a) (Mu.muCode a) =
      cond (NativeContext.SourceChi.chiCode (alphaCode a) lambdaOut)
        (NativeContext.interpretation (alphaCode a) lambdaOut * Ordinal.omega0)
        (NativeContext.interpretation (alphaCode a) lambdaOut) := by
  have hs := execute_spec a lambdaOut hl
  have hc := epsilon_coefficient a lambdaOut hl he hlarge
  have hchi := NativeContext.SourceChi.Invariance.chiCode_invariant (alphaCode a)
    (Mu.mappedCoefficient a) lambdaOut (Mu.mappedCoefficient_spec a hs.1).2 hs.2.1 hc.1
  rw [(Mu.muCode_spec a hs.1).2.2, Mu.sourceValue, ← Mu.chi_correct a hs.1]
  exact (LambdaEpsilonMu.corrected_power_at_epsilon _ _ _ _ he hc.1 hc.2.1).trans
    (by rw [Mu.chi, hchi])

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.Lambda
