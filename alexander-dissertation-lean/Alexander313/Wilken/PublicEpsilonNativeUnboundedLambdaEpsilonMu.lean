import Alexander313.Wilken.PublicEpsilonNativeUnboundedLambda
import Alexander313.Wilken.HereditaryLambdaEpsilonMuSupport

/-!
# Source3.14(d) for the actual full-domain beta-context lambda and mu

The original ANY-q high root constructs actual lambda and mu. If that
actual lambda value is epsilon and strictly above the actual beta, its
computed coefficient equals lambda, its computed finite offset is zero
and its actual zeta value is zero. Actual SAME-beta chi value invariance
identifies the indicator used by mu with the indicator of the actual
lambda output. The genuine omega-power formula gives the printed two
cases, with no coefficient/offset/indicator premise. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.Lambda

theorem epsilon_coefficient (q root out : Nat) (ho : out ∈ execute q root)
    (he : Ordinal.omega0 ^ interpretation (betaCode q root) out =
      interpretation (betaCode q root) out)
    (hlarge : base (betaCode q root) < interpretation (betaCode q root) out) :
    interpretation (betaCode q root) (Mu.mappedCoefficient q root) =
        interpretation (betaCode q root) out ∧
      OmegaQuotient.coefficientOffset q root = 0 ∧ DirectZeta.sourceValue q root = 0 := by
  have hs := execute_spec q root out ho
  exact LambdaEpsilonMu.epsilon_product_coefficient _ _ _ _ _
    (base_pos _ (betaCode_baseCheck q root hs.1)) he hlarge
    (RhoMuSupport.mappedCoefficient_zero_or_limit q root hs.1)
    (by simpa only [beta_base q root hs.1] using zeta_value_lt_root q root hs.1)
    (execute_product q root out ho)

theorem source_lemma_3_14_d (q root lambdaOut : Nat) (hl : lambdaOut ∈ execute q root)
    (he : Ordinal.omega0 ^ interpretation (betaCode q root) lambdaOut =
      interpretation (betaCode q root) lambdaOut)
    (hlarge : base (betaCode q root) < interpretation (betaCode q root) lambdaOut) :
    interpretation (betaCode q root) (Mu.muCode q root) =
      cond (SourceChi.chiCode (betaCode q root) lambdaOut)
        (interpretation (betaCode q root) lambdaOut * Ordinal.omega0)
        (interpretation (betaCode q root) lambdaOut) := by
  have hs := execute_spec q root lambdaOut hl
  have hc := epsilon_coefficient q root lambdaOut hl he hlarge
  have hchi := SourceChi.Invariance.chiCode_invariant (betaCode q root)
    (Mu.mappedCoefficient q root) lambdaOut (Mu.mappedCoefficient_spec q root hs.1).2 hs.2.2.1 hc.1
  rw [(Mu.muCode_spec q root hs.1).2.2, Mu.sourceValue, ← Mu.chi_correct q root hs.1]
  exact (LambdaEpsilonMu.corrected_power_at_epsilon _ _ _ _ he hc.1 hc.2.1).trans
    (by rw [Mu.chi, hchi])

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.Lambda
