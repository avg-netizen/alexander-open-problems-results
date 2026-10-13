import Alexander313.Wilken.PublicEpsilonNativeUnboundedMuSmallLambda
import Alexander313.Wilken.HereditaryNativeRhoPowerBoundRaw
import Alexander313.Wilken.HereditaryMuLambdaEpsilonCutSupport

/-!
# Full actual source3.14(b,c) at every original coded epsilon

Every coefficient, zero-or-limit and positive-total premise is derived
from the genuine original high root and actual producer. The rho query
retains the entire original raw LOW domain, including zero and arbitrary
spellings. Actual normalization computes its indicator for the stronger
clause. Genuine corrected-power/product arithmetic proves epsilon-cut
and greatest-epsilon equality in the nonsmall branch. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.Lambda

theorem mu_corrected_value (q root : Nat) (ha : inputCheck q root = true) :
    interpretation (betaCode q root) (Mu.muCode q root) = Ordinal.omega0 ^
      (interpretation (betaCode q root) (Mu.mappedCoefficient q root) +
        cond (SourceChi.chiCode (betaCode q root) (Mu.mappedCoefficient q root))
          (1 : Ordinal.{0}) 0 + (OmegaQuotient.coefficientOffset q root : Ordinal.{0})) := by
  rw [(Mu.muCode_spec q root ha).2.2, Mu.sourceValue, ← Mu.chi_correct q root ha]
  rfl

/-- Every genuine rho query beta<=mu has the printed lambda bound. -/
theorem source_lemma_3_14_b (q root lambdaOut query rhoOut : Nat)
    (hl : lambdaOut ∈ execute q root)
    (hr : rhoOut ∈ SourceRho.Uniform.execute (betaCode q root) query)
    (hb : interpretation (betaCode q root) query ≤
      interpretation (betaCode q root) (Mu.muCode q root)) :
    interpretation (betaCode q root) rhoOut ≤ interpretation (betaCode q root) lambdaOut := by
  have ha := (execute_spec q root lambdaOut hl).1
  have hc := Mu.mappedCoefficient_spec q root ha
  have hbound := SourceRho.Uniform.PowerBound.rho_le_corrected_power
    (betaCode q root) (Mu.mappedCoefficient q root) (OmegaQuotient.coefficientOffset q root)
    query rhoOut hc.1 hc.2 (RhoMuSupport.mappedCoefficient_zero_or_limit q root ha) hr
    (by rw [← mu_corrected_value q root ha]; exact hb)
  exact hbound.trans (by rw [execute_product q root lambdaOut hl]; exact le_self_add)

/-- The printed strict false-indicator clause on EVERY original raw query.
Its coefficient positivity is a consequence of the actual high root. -/
theorem source_lemma_3_14_b_strict (q root lambdaOut query rhoOut : Nat)
    (hl : lambdaOut ∈ execute q root)
    (hr : rhoOut ∈ SourceRho.Uniform.execute (betaCode q root) query)
    (hb : interpretation (betaCode q root) query <
      interpretation (betaCode q root) (Mu.muCode q root))
    (hχ : SourceChi.rawChiCode (betaCode q root) query = false) :
    interpretation (betaCode q root) rhoOut + base (betaCode q root) ≤
      interpretation (betaCode q root) lambdaOut := by
  have ha := (execute_spec q root lambdaOut hl).1
  have hc := Mu.mappedCoefficient_spec q root ha
  have hbound := SourceRho.Uniform.PowerBound.rho_add_base_le_corrected_power_raw
    (betaCode q root) (Mu.mappedCoefficient q root) (OmegaQuotient.coefficientOffset q root)
    query rhoOut hc.1 hc.2 (RhoMuSupport.mappedCoefficient_zero_or_limit q root ha)
    (coefficient_total_positive q root ha) hχ hr
    (by rw [← mu_corrected_value q root ha]; exact hb)
  exact hbound.trans (by rw [execute_product q root lambdaOut hl]; exact le_self_add)

/-- The actual nonsmall branch has identical epsilon cuts. -/
theorem source_lemma_3_14_c_epsilonCut (q root out : Nat) (ho : out ∈ execute q root)
    (hlarge : base (betaCode q root) ≤ interpretation (betaCode q root) (Mu.muCode q root)) :
    MuLambdaEpsilonCut.epsilonCut (interpretation (betaCode q root) (Mu.muCode q root)) =
      MuLambdaEpsilonCut.epsilonCut (interpretation (betaCode q root) out) := by
  have ha := (execute_spec q root out ho).1
  rw [mu_corrected_value q root ha, execute_product q root out ho]
  exact MuLambdaEpsilonCut.epsilonCut_eq _ _ _ _ _
    (base_pos _ (betaCode_baseCheck q root ha)) (coefficient_total_positive q root ha)
    (by simpa only [beta_base q root ha] using zeta_value_lt_root q root ha)
    (by rw [← mu_corrected_value q root ha]; exact hlarge)

/-- Both printed maxima genuinely exist and are greatest members. -/
theorem source_lemma_3_14_c_large (q root out : Nat) (ho : out ∈ execute q root)
    (hlarge : base (betaCode q root) ≤ interpretation (betaCode q root) (Mu.muCode q root)) :
    MuLambdaEpsilonCut.maxE (interpretation (betaCode q root) (Mu.muCode q root)) =
        MuLambdaEpsilonCut.maxE (interpretation (betaCode q root) out) ∧
      IsGreatest (MuLambdaEpsilonCut.epsilonCut
        (interpretation (betaCode q root) (Mu.muCode q root)))
        (MuLambdaEpsilonCut.maxE (interpretation (betaCode q root) (Mu.muCode q root))) ∧
      IsGreatest (MuLambdaEpsilonCut.epsilonCut (interpretation (betaCode q root) out))
        (MuLambdaEpsilonCut.maxE (interpretation (betaCode q root) out)) := by
  have ha := (execute_spec q root out ho).1
  have hs := source_lemma_3_14_c_epsilonCut q root out ho hlarge
  have hn : (MuLambdaEpsilonCut.epsilonCut
      (interpretation (betaCode q root) (Mu.muCode q root))).Nonempty :=
    ⟨base (betaCode q root), SourceChi.epsilon_base _ (betaCode_baseCheck q root ha), hlarge⟩
  refine ⟨congrArg sSup hs, MuLambdaEpsilonCut.maxE_isGreatest _ hn, ?_⟩
  exact MuLambdaEpsilonCut.maxE_isGreatest _ (by rw [← hs]; exact hn)

/-- The complete small/nonsmall alternative has only an actual source
lambda execution as premise; no coefficient, bound or maximum is supplied. -/
theorem source_lemma_3_14_c (q root out : Nat) (ho : out ∈ execute q root) :
    (interpretation (betaCode q root) (Mu.muCode q root) < base (betaCode q root) ∧
      base (betaCode q root) ≤ interpretation (betaCode q root) out ∧
      interpretation (betaCode q root) out < base (betaCode q root) * base (betaCode q root)) ∨
    (base (betaCode q root) ≤ interpretation (betaCode q root) (Mu.muCode q root) ∧
      MuLambdaEpsilonCut.maxE (interpretation (betaCode q root) (Mu.muCode q root)) =
        MuLambdaEpsilonCut.maxE (interpretation (betaCode q root) out)) := by
  by_cases hs : interpretation (betaCode q root) (Mu.muCode q root) < base (betaCode q root)
  · exact Or.inl ⟨hs, source_lemma_3_14_c_small q root out ho hs⟩
  · have hlarge := le_of_not_gt hs
    exact Or.inr ⟨hlarge, (source_lemma_3_14_c_large q root out ho hlarge).1⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.Lambda
