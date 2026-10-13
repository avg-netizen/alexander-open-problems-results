import Alexander313.Wilken.SourceOneNativeLambdaRhoMu
import Alexander313.Wilken.HereditaryMuSmallLambdaSupport

/-!
# Original source-one small-mu half of source3.14(c)

Genuine source-zero positive Delta and full original iota strict order
against the original zero term force the actual total coefficient positive.
Only the target alpha uses the native epsilon dictionary. The actual
source-one mu formula and genuine SourceZeta0 bound give alpha<=lambda<alpha^2.
No native base-one source or positivity/bound oracle is used. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.Lambda

open OrderSupport

theorem delta_positive (a : Nat) (ha : inputCheck a = true) :
    0 < interpretation 0 (deltaCode a) := pos_iff_ne_zero.mpr (delta_nonzero a ha)

theorem literalDelta_positive (a : Nat) (ha : inputCheck a = true) :
    0 < NativeContext.interpretation (alphaCode a) (literalCode a (deltaCode a)) := by
  have hi := delta_input a ha
  obtain ⟨_, t, he, ht, hn, hs⟩ := (SourceOneIota.inputCheck_exact a _).mp hi
  have hr := (restricted_iff_sourceStar a ha t ht hn).mpr hs
  have hp : 0 < denote 0 t := by simpa only [he, interpretation_code] using delta_positive a ha
  let z := zeroTree 0
  have hz : check 0 z = true := (Bool.and_eq_true.mp (zeroTree_lowCheck 0)).1
  have hzn : Theta.Normal 0 z := Theta.Normalization.zeroTree_normal 0
  have hzr : Restricted a z := OmegaQuotient.zero_restricted a
  have hv := transform_low_value a ha z hz hzr (Nat.zero_le 1)
  have hlt := (transform_lt_iff a ha z t hz ht hzn hn hzr hr).mpr
    (by simpa only [z, zeroTree_denote] using hp)
  simpa only [he, literalCode_code a ha t ht hn hr, NativeContext.interpretation_code,
    hv, z, zeroTree_denote] using hlt

theorem coefficient_total_positive (a : Nat) (ha : inputCheck a = true) :
    0 < NativeContext.interpretation (alphaCode a) (Mu.mappedCoefficient a) +
      (OmegaQuotient.coefficientOffset a : Ordinal.{0}) := by
  have hd := literalDelta_positive a ha
  have hp := MappedOmegaQuotient.literal_delta_coefficient_product a ha
  change NativeContext.interpretation (alphaCode a) (literalCode a (deltaCode a)) =
    NativeContext.base (alphaCode a) *
      (NativeContext.interpretation (alphaCode a) (Mu.mappedCoefficient a) +
        (OmegaQuotient.coefficientOffset a : Ordinal.{0})) at hp
  by_contra hnot
  have hz : NativeContext.interpretation (alphaCode a) (Mu.mappedCoefficient a) +
      (OmegaQuotient.coefficientOffset a : Ordinal.{0}) = 0 :=
    le_antisymm (le_of_not_gt hnot) bot_le
  rw [hp, hz, mul_zero] at hd
  exact (lt_irrefl (0 : Ordinal.{0})) hd

theorem source_lemma_3_14_c_small (a out : Nat) (ho : out ∈ execute a)
    (hsmall : NativeContext.interpretation (alphaCode a) (Mu.muCode a) < NativeContext.base (alphaCode a)) :
    NativeContext.base (alphaCode a) ≤ NativeContext.interpretation (alphaCode a) out ∧
      NativeContext.interpretation (alphaCode a) out <
        NativeContext.base (alphaCode a) * NativeContext.base (alphaCode a) := by
  have ha := (execute_spec a out ho).1
  have hp : Ordinal.omega0 ^
      (NativeContext.interpretation (alphaCode a) (Mu.mappedCoefficient a) +
        cond (Mu.chi a) (1 : Ordinal.{0}) 0 +
          (OmegaQuotient.coefficientOffset a : Ordinal.{0})) < NativeContext.base (alphaCode a) := by
    rw [(Mu.muCode_spec a ha).2.2, Mu.sourceValue, ← Mu.chi_correct a ha] at hsmall
    exact hsmall
  exact MuSmallLambda.small_power_lambda_bounds _ _ _ _ _ _
    (NativeContext.SourceChi.epsilon_base _ (alphaCode_baseCheck a ha)) (coefficient_total_positive a ha)
    (by simpa only [alpha_base a ha] using zeta_value_lt_root a ha) hp
    (execute_product a out ho)

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.Lambda
