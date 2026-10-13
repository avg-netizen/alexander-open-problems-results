import Alexander313.Wilken.PublicEpsilonNativeUnboundedLambda
import Alexander313.Wilken.PublicEpsilonNativeRootEndpointCollapse
import Alexander313.Wilken.HereditaryMuSmallLambdaSupport

/-!
# Source3.14(c) when actual full-domain mu is below beta

The original high root has genuinely positive divided head. Actual full
iota strict order against its real zero term gives a positive mapped head;
the genuine product therefore forces the actual total coefficient positive.
The real mu formula and zeta bound then give beta<=lambda<beta^2.
No coefficient, positivity, output or bound oracle occurs. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.Lambda

open ThetaCourse

theorem delta_positive (q root : Nat) (ha : inputCheck q root = true) :
    0 < interpretation q (deltaCode root) := by
  simpa only [deltaCode, OmegaQuotient.deltaCode, RootEndpointCollapse.deltaCode,
    OmegaQuotient.argumentCode, RootEndpointCollapse.argumentCode] using
    RootEndpointCollapse.delta_positive q root ha

theorem literalDelta_positive (q root : Nat) (ha : inputCheck q root = true) :
    0 < interpretation (betaCode q root) (literalCode q root (deltaCode root)) := by
  have hi := delta_input q root ha
  obtain ⟨_, t, he, ht, hn, hs⟩ := (PublicEpsilonUnboundedIota.inputCheck_exact q root _).mp hi
  have hr := (restricted_iff_sourceStar q root ha t ht hn).mpr hs
  have hp : 0 < denote q t := by
    simpa only [he, interpretation_code] using delta_positive q root ha
  let z := Normalization.zeroTree
  have hz : check q z = true := Normalization.zeroTree_checked q (source_checked q root ha)
  have hzn : Comparison.Normal q z := Normalization.zeroTree_normal q
  have hzr : Restricted q root z := OmegaQuotient.Support.zero_restricted q root
  have hv := transform_low_value q root ha z hz hzr (Nat.zero_le 1)
  have hlt := (transform_lt_iff q root ha z t hz ht hzn hn hzr hr).mpr
    (by simpa only [z, Normalization.zeroTree_denote] using hp)
  simpa only [he, literalCode_code q root ha t ht hn hr, interpretation_code,
    hv, z, Normalization.zeroTree_denote] using hlt

theorem coefficient_total_positive (q root : Nat) (ha : inputCheck q root = true) :
    0 < interpretation (betaCode q root) (Mu.mappedCoefficient q root) +
      (OmegaQuotient.coefficientOffset q root : Ordinal.{0}) := by
  have hd := literalDelta_positive q root ha
  have hp := MappedOmegaQuotient.literal_delta_coefficient_product q root ha
  change interpretation (betaCode q root) (literalCode q root (deltaCode root)) =
    base (betaCode q root) *
      (interpretation (betaCode q root) (Mu.mappedCoefficient q root) +
        (OmegaQuotient.coefficientOffset q root : Ordinal.{0})) at hp
  by_contra hnot
  have hz : interpretation (betaCode q root) (Mu.mappedCoefficient q root) +
      (OmegaQuotient.coefficientOffset q root : Ordinal.{0}) = 0 :=
    le_antisymm (le_of_not_gt hnot) bot_le
  rw [hp, hz, mul_zero] at hd
  exact (lt_irrefl (0 : Ordinal.{0})) hd

theorem source_lemma_3_14_c_small (q root out : Nat) (ho : out ∈ execute q root)
    (hsmall : interpretation (betaCode q root) (Mu.muCode q root) < base (betaCode q root)) :
    base (betaCode q root) ≤ interpretation (betaCode q root) out ∧
      interpretation (betaCode q root) out < base (betaCode q root) * base (betaCode q root) := by
  have ha := (execute_spec q root out ho).1
  have hp : Ordinal.omega0 ^
      (interpretation (betaCode q root) (Mu.mappedCoefficient q root) +
        cond (Mu.chi q root) (1 : Ordinal.{0}) 0 +
          (OmegaQuotient.coefficientOffset q root : Ordinal.{0})) < base (betaCode q root) := by
    rw [(Mu.muCode_spec q root ha).2.2, Mu.sourceValue, ← Mu.chi_correct q root ha] at hsmall
    exact hsmall
  exact MuSmallLambda.small_power_lambda_bounds _ _ _ _ _ _
    (SourceChi.epsilon_base _ (betaCode_baseCheck q root ha)) (coefficient_total_positive q root ha)
    (by simpa only [beta_base q root ha] using zeta_value_lt_root q root ha) hp
    (execute_product q root out ho)

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.Lambda
