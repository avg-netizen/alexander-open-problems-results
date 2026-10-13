import Alexander313.Wilken.HereditaryNativeIotaAlphaPlusSupport
import Alexander313.Wilken.HereditaryNativeIotaEnclosure
import Alexander313.Wilken.HereditaryNativeLambdaBranches

/-!
# The source alpha-plus bounds for actual iota and epsilon lambda

Alpha-plus is the ORIGINAL source collapse at argument Delta+eta+1,
as in Convention 2.28. The actual relative collapse of original Delta is
bounded by this source value using both genuine hull minima. The previously
constructed enclosure consequently proves the remaining bound of 2.46(a)
and both executing branches of 2.48(b), on their original source domains.
No alpha-plus identification, bound, admission or translation is assumed.
The stronger equality and same-value temporary-base return are not asserted.
These proof candidates are uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Iota.AlphaPlus

open NativePublicBridge (contextCode contextCode_checked)

noncomputable def sourceValue (s a : Nat) : Ordinal.{0} :=
  globalCollapse (base (contextCode s)) 0
    (interpretation (contextCode s) (Lambda.argumentCode a) + 1)

/-- This is the literal Convention 2.28 source endpoint, with its original
ANF high part and low residual. No least-epsilon surrogate is used. -/
theorem sourceValue_eq_delta_eta (s a : Nat) (ha : rootCheck s a = true) :
    sourceValue s a = globalCollapse (base (contextCode s)) 0
      (interpretation (contextCode s) (Lambda.deltaCode a) +
        interpretation (contextCode s) (Decomposition.lowCode 0 (Lambda.argumentCode a)) + 1) := by
  have hs := Decomposition.parts_reconstruct (contextCode s) 0 (Lambda.argumentCode a)
    (Lambda.argument_accepted s a ha)
  rw [sourceValue, ← hs]
  rfl

/-- The actual original successor collapse is strictly above its original
root, including the proper theta-zero non-epsilon branch. -/
theorem root_lt_sourceValue (s a : Nat) (ha : SourceZeta.inputCheck s a = true) :
    interpretation (contextCode s) a < sourceValue s a := by
  obtain ⟨t, he, ht, hn⟩ := (SourceZeta.inputCheck_exact s a).mp ha
  let q := contextCode s
  have hp := base_pos q (contextCode_checked s)
  have hA : GlobalNotation (base q) 1 (interpretation q (Lambda.argumentCode a)) := by
    apply globalNotation_embeds_next (base q) hp 0
    simpa only [Lambda.argumentCode, he, Localization.argumentCode_theta, interpretation_code] using
      checked_globalNotation q t (BaseTransformation.theta_argument_check q 0 t ht)
  have hAs : interpretation q (Lambda.argumentCode a) < omegaSequence (base q) 2 := by
    simpa only [Lambda.argumentCode, he, Localization.argumentCode_theta, interpretation_code] using
      FixedPoint.checked_theta_sort q 0 t ht
  have hroot : interpretation q a = globalCollapse (base q) 0
      (interpretation q (Lambda.argumentCode a)) := by
    simp only [he, Lambda.argumentCode, Localization.argumentCode_theta, interpretation_code]
    rfl
  rw [hroot]
  exact SourceCollapseSuccessors.global_collapse_lt_successor (base q) hp 0
    ⟨interpretation q (Lambda.argumentCode a), hA⟩ hAs

/-- The true target enclosure lies at or below the original source
alpha-plus. Target Delta admission and every finite return bound were
conclusions of the actual-minimum construction, not caller hypotheses. -/
theorem delta_enclosure_le_sourceValue (s a : Nat) (ha : rootCheck s a = true) :
    denote (alphaCode s a) (Enclosure.deltaEnclosureTerm s a) ≤ sourceValue s a := by
  obtain ⟨t, he, ht, hn, hh⟩ := (rootCheck_exact s a).mp ha
  let q := contextCode s
  have hq := contextCode_checked s
  have hqp := base_pos q hq
  have hc := Lambda.argument_accepted s a ha
  have htarg := BaseTransformation.theta_argument_check q 0 t ht
  have hA : GlobalNotation (base q) 1 (interpretation q (Lambda.argumentCode a)) := by
    apply globalNotation_embeds_next (base q) hqp 0
    simpa only [Lambda.argumentCode, he, Localization.argumentCode_theta, interpretation_code] using
      checked_globalNotation q t htarg
  have hAs : interpretation q (Lambda.argumentCode a) < omegaSequence (base q) 2 := by
    simpa only [Lambda.argumentCode, he, Localization.argumentCode_theta, interpretation_code] using
      FixedPoint.checked_theta_sort q 0 t ht
  have hroot : interpretation q a = globalCollapse (base q) 0
      (interpretation q (Lambda.argumentCode a)) := by
    simp only [he, Lambda.argumentCode, Localization.argumentCode_theta, interpretation_code]
    rfl
  have hb := global_relative_highPart_le_source_successor (base q) hqp
    (interpretation q (Lambda.argumentCode a)) (interpretation q (Lambda.deltaCode a))
    (interpretation q (Decomposition.lowCode 0 (Lambda.argumentCode a))) hA hAs
    (Decomposition.highPart_dvd q 0 (Lambda.argumentCode a) hc)
    (Decomposition.lowPart_bound q 0 (Lambda.argumentCode a) hc)
    (Decomposition.parts_reconstruct q 0 (Lambda.argumentCode a) hc).symm
  rw [(Enclosure.delta_enclosure_spec s a ha).2.2.1, alpha_base s a ha, hroot]
  exact hb

/-- The remaining actual bound in source Lemma 2.46(a). The only premise
is the original admitted weak-normal high root at the same source context. -/
theorem literalDelta_lt_sourceValue (s a : Nat) (ha : rootCheck s a = true) :
    interpretation (alphaCode s a) (literalCode s a (Lambda.deltaCode a)) < sourceValue s a :=
  (Enclosure.literalDelta_lt_enclosure s a ha).trans_le (delta_enclosure_le_sourceValue s a ha)

/-- Source Lemma 2.48(b) on the genuine executing epsilon branch. -/
theorem lambda_lt_sourceValue (s a out : Nat) (ho : out ∈ Lambda.execute s a) :
    interpretation (alphaCode s a) out < sourceValue s a :=
  (Enclosure.lambda_lt_enclosure s a out ho).trans_le
    (delta_enclosure_le_sourceValue s a (Lambda.execute_spec s a out ho).1)

/-- Source Lemma 2.48(b) for the actual full two-branch executing lambda.
The non-epsilon output remains in the original context; the epsilon output
uses the genuine alpha context. Both are below the SAME source alpha-plus. -/
theorem branch_lambda_lt_sourceValue (s a out : Nat)
    (ho : out ∈ Lambda.Branches.execute s a) :
    interpretation (Lambda.Branches.outputContext s a) out < sourceValue s a := by
  have ha := (Lambda.Branches.execute_spec s a out ho).1
  cases hh : rootCheck s a with
  | true =>
    have hl : out ∈ Lambda.execute s a := by
      simpa only [Lambda.Branches.execute, ha, hh, Bool.cond_true] using ho
    simpa only [Lambda.Branches.outputContext, hh, Bool.cond_true] using lambda_lt_sourceValue s a out hl
  | false =>
    have hz : out ∈ SourceZeta.zeta s a := by
      simpa only [Lambda.Branches.execute, ha, hh, Bool.cond_true, Bool.cond_false] using ho
    have hs := (SourceZeta.zeta_spec s a out hz).2.2.2.2
    simpa only [Lambda.Branches.outputContext, hh, Bool.cond_false] using
      hs.trans (root_lt_sourceValue s a (Lambda.Branches.original_input s a ha))

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Iota.AlphaPlus
