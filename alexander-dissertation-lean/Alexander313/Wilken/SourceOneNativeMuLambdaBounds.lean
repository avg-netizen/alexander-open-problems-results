import Alexander313.Wilken.SourceOneNativeMuSmallLambda
import Alexander313.Wilken.HereditaryNativeRhoPowerBoundRaw
import Alexander313.Wilken.HereditaryMuLambdaEpsilonCutSupport

/-!
# Full actual source3.14(b,c) in the original source-one dictionary

Every coefficient, zero-or-limit and positive-total premise is derived
from the genuine original source-zero high root and actual producer. The rho
query
retains the entire original raw LOW domain, including zero and arbitrary
spellings. Native parsing is used only at the actual target alpha epsilon.
Actual normalization computes its indicator for the stronger
clause. Genuine corrected-power/product arithmetic proves epsilon-cut
and greatest-epsilon equality in the nonsmall branch. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.Lambda

theorem mu_corrected_value (a : Nat) (ha : inputCheck a = true) :
    NativeContext.interpretation (alphaCode a) (Mu.muCode a) = Ordinal.omega0 ^
      (NativeContext.interpretation (alphaCode a) (Mu.mappedCoefficient a) +
        cond (NativeContext.SourceChi.chiCode (alphaCode a) (Mu.mappedCoefficient a))
          (1 : Ordinal.{0}) 0 + (OmegaQuotient.coefficientOffset a : Ordinal.{0})) := by
  rw [(Mu.muCode_spec a ha).2.2, Mu.sourceValue, ← Mu.chi_correct a ha]
  rfl

/-- Every genuine rho query below mu has the printed lambda bound. -/
theorem source_lemma_3_14_b (a lambdaOut query rhoOut : Nat)
    (hl : lambdaOut ∈ execute a)
    (hr : rhoOut ∈ NativeContext.SourceRho.Uniform.execute (alphaCode a) query)
    (hb : NativeContext.interpretation (alphaCode a) query ≤
      NativeContext.interpretation (alphaCode a) (Mu.muCode a)) :
    NativeContext.interpretation (alphaCode a) rhoOut ≤ NativeContext.interpretation (alphaCode a) lambdaOut := by
  have ha := (execute_spec a lambdaOut hl).1
  have hc := Mu.mappedCoefficient_spec a ha
  have hbound := NativeContext.SourceRho.Uniform.PowerBound.rho_le_corrected_power
    (alphaCode a) (Mu.mappedCoefficient a) (OmegaQuotient.coefficientOffset a)
    query rhoOut hc.1 hc.2 (RhoMuSupport.mappedCoefficient_zero_or_limit a ha) hr
    (by rw [← mu_corrected_value a ha]; exact hb)
  exact hbound.trans (by rw [execute_product a lambdaOut hl]; exact le_self_add)

/-- The printed strict false-indicator clause on EVERY original raw query.
Its coefficient positivity is a consequence of the actual high root. -/
theorem source_lemma_3_14_b_strict (a lambdaOut query rhoOut : Nat)
    (hl : lambdaOut ∈ execute a)
    (hr : rhoOut ∈ NativeContext.SourceRho.Uniform.execute (alphaCode a) query)
    (hb : NativeContext.interpretation (alphaCode a) query <
      NativeContext.interpretation (alphaCode a) (Mu.muCode a))
    (hχ : NativeContext.SourceChi.rawChiCode (alphaCode a) query = false) :
    NativeContext.interpretation (alphaCode a) rhoOut + NativeContext.base (alphaCode a) ≤
      NativeContext.interpretation (alphaCode a) lambdaOut := by
  have ha := (execute_spec a lambdaOut hl).1
  have hc := Mu.mappedCoefficient_spec a ha
  have hbound := NativeContext.SourceRho.Uniform.PowerBound.rho_add_base_le_corrected_power_raw
    (alphaCode a) (Mu.mappedCoefficient a) (OmegaQuotient.coefficientOffset a)
    query rhoOut hc.1 hc.2 (RhoMuSupport.mappedCoefficient_zero_or_limit a ha)
    (coefficient_total_positive a ha) hχ hr
    (by rw [← mu_corrected_value a ha]; exact hb)
  exact hbound.trans (by rw [execute_product a lambdaOut hl]; exact le_self_add)

/-- The actual nonsmall branch has identical epsilon cuts. -/
theorem source_lemma_3_14_c_epsilonCut (a out : Nat) (ho : out ∈ execute a)
    (hlarge : NativeContext.base (alphaCode a) ≤ NativeContext.interpretation (alphaCode a) (Mu.muCode a)) :
    MuLambdaEpsilonCut.epsilonCut (NativeContext.interpretation (alphaCode a) (Mu.muCode a)) =
      MuLambdaEpsilonCut.epsilonCut (NativeContext.interpretation (alphaCode a) out) := by
  have ha := (execute_spec a out ho).1
  rw [mu_corrected_value a ha, execute_product a out ho]
  exact MuLambdaEpsilonCut.epsilonCut_eq _ _ _ _ _
    (NativeContext.base_pos _ (alphaCode_baseCheck a ha)) (coefficient_total_positive a ha)
    (by simpa only [alpha_base a ha] using zeta_value_lt_root a ha)
    (by rw [← mu_corrected_value a ha]; exact hlarge)

/-- Both printed maxima genuinely exist and are greatest members. -/
theorem source_lemma_3_14_c_large (a out : Nat) (ho : out ∈ execute a)
    (hlarge : NativeContext.base (alphaCode a) ≤ NativeContext.interpretation (alphaCode a) (Mu.muCode a)) :
    MuLambdaEpsilonCut.maxE (NativeContext.interpretation (alphaCode a) (Mu.muCode a)) =
        MuLambdaEpsilonCut.maxE (NativeContext.interpretation (alphaCode a) out) ∧
      IsGreatest (MuLambdaEpsilonCut.epsilonCut
        (NativeContext.interpretation (alphaCode a) (Mu.muCode a)))
        (MuLambdaEpsilonCut.maxE (NativeContext.interpretation (alphaCode a) (Mu.muCode a))) ∧
      IsGreatest (MuLambdaEpsilonCut.epsilonCut (NativeContext.interpretation (alphaCode a) out))
        (MuLambdaEpsilonCut.maxE (NativeContext.interpretation (alphaCode a) out)) := by
  have ha := (execute_spec a out ho).1
  have hs := source_lemma_3_14_c_epsilonCut a out ho hlarge
  have hn : (MuLambdaEpsilonCut.epsilonCut
      (NativeContext.interpretation (alphaCode a) (Mu.muCode a))).Nonempty :=
    ⟨NativeContext.base (alphaCode a), NativeContext.SourceChi.epsilon_base _ (alphaCode_baseCheck a ha), hlarge⟩
  refine ⟨congrArg sSup hs, MuLambdaEpsilonCut.maxE_isGreatest _ hn, ?_⟩
  exact MuLambdaEpsilonCut.maxE_isGreatest _ (by rw [← hs]; exact hn)

/-- The complete small/nonsmall alternative has only an actual source
lambda execution as premise; no coefficient, bound or maximum is supplied. -/
theorem source_lemma_3_14_c (a out : Nat) (ho : out ∈ execute a) :
    (NativeContext.interpretation (alphaCode a) (Mu.muCode a) < NativeContext.base (alphaCode a) ∧
      NativeContext.base (alphaCode a) ≤ NativeContext.interpretation (alphaCode a) out ∧
      NativeContext.interpretation (alphaCode a) out < NativeContext.base (alphaCode a) * NativeContext.base (alphaCode a)) ∨
    (NativeContext.base (alphaCode a) ≤ NativeContext.interpretation (alphaCode a) (Mu.muCode a) ∧
      MuLambdaEpsilonCut.maxE (NativeContext.interpretation (alphaCode a) (Mu.muCode a)) =
        MuLambdaEpsilonCut.maxE (NativeContext.interpretation (alphaCode a) out)) := by
  by_cases hs : NativeContext.interpretation (alphaCode a) (Mu.muCode a) < NativeContext.base (alphaCode a)
  · exact Or.inl ⟨hs, source_lemma_3_14_c_small a out ho hs⟩
  · have hlarge := le_of_not_gt hs
    exact Or.inr ⟨hlarge, (source_lemma_3_14_c_large a out ho hlarge).1⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.Lambda
