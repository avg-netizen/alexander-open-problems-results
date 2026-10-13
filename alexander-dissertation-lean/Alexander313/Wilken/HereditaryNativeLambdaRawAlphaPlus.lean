import Alexander313.Wilken.HereditaryNativeIotaAlphaPlus
import Alexander313.Wilken.HereditaryNativeLambdaRawBranches

/-!
# The original raw lambda alpha-plus bound

The actual root normalizer retains theta-zero and preserves its ORIGINAL
argument value. The literal original source successor endpoint consequently
agrees before and after normalization. Every executing raw proper-root lambda
output is below that original endpoint, in its actually selected context.
No normalization invariance or normalized-domain guard is a supplied premise.
Uncompiled proof candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Lambda.Branches.Raw

open NativePublicBridge (contextCode)

theorem normalized_argument_value (s a : Nat) (ha : inputCheck s a = true) :
    interpretation (contextCode s) (Lambda.argumentCode (normalizedRoot s a)) =
      interpretation (contextCode s) (Lambda.argumentCode a) := by
  obtain ⟨t, he, ht, hp⟩ := (inputCheck_exact s a).mp ha
  have harg := BaseTransformation.theta_argument_check (contextCode s) 0 t ht
  have hv := (Normalization.normalize_checked (contextCode s) t harg).2.2
  simpa only [he, normalizedRoot_theta s t ht, Lambda.argumentCode,
    Localization.argumentCode_theta, interpretation_code] using hv

/-- Literal source alpha-plus at the ORIGINAL raw argument is preserved by
the actual normalizer. This is derived from the normalizer's true semantics. -/
theorem normalized_source_alphaPlus (s a : Nat) (ha : inputCheck s a = true) :
    Iota.AlphaPlus.sourceValue s (normalizedRoot s a) = Iota.AlphaPlus.sourceValue s a := by
  unfold Iota.AlphaPlus.sourceValue
  rw [normalized_argument_value s a ha]

/-- Both actual raw proper-root branches satisfy source Lemma 2.48(b),
with the ORIGINAL raw source alpha-plus and the genuine output context. -/
theorem execute_lt_original_source_alphaPlus (s a out : Nat) (ho : out ∈ execute s a) :
    interpretation (Branches.outputContext s (normalizedRoot s a)) out <
      Iota.AlphaPlus.sourceValue s a := by
  have ha := (execute_spec s a out ho).1
  have hb : out ∈ Branches.execute s (normalizedRoot s a) := by
    simpa only [execute, ha, Bool.cond_true] using ho
  rw [← normalized_source_alphaPlus s a ha]
  exact Iota.AlphaPlus.branch_lambda_lt_sourceValue s (normalizedRoot s a) out hb

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Lambda.Branches.Raw
