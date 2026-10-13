import Alexander313.Wilken.HereditaryNativeBoundedContextSourceReturn
import Alexander313.Wilken.HereditaryNativeBoundedContextIotaReturn
import Alexander313.Wilken.HereditaryNativeBoundedContextLambda
import Alexander313.Wilken.HereditaryNativeRelativeZeta

/-!
# Actual lambda translation at the original bounded intermediate root

The original domain here is the checked Normal HIGH intermediate root;
the non-epsilon intermediate branch is separate. The returned original
root is constructed by the genuine finite return.
Every zero-code branch retains its actual divided high part; the unchanged
or alpha-shifted low tail satisfies the proved literal STRICT/zeta identity.
Original admission supplies the full level-zero higher presentation, and
the original outer endpoint supplies the smaller-head bound. Actual iota
commutation and original order reflection identify the mapped high parts.
Both real lambda executions therefore have equal values at the SAME
canonical beta. No caller, return, STRICT, zeta or lambda oracle is supplied.
Uncompiled source candidates. The pi/base-change clause is separate.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.BoundedContextIota.Lambda.Translation

open NativePublicBridge (contextCode)
open SourceReturn SourceFixedPointLimits

private theorem rawTree_code_eq (q c : Nat) (hc : checkCode q c = true) :
    (ThetaCourse.rawTree c).code = c := by
  obtain ⟨t, he, ht⟩ := (checkCode_exact q c).mp hc
  rw [← he, ThetaCourse.rawTree_code]

private theorem sourceValue_of_parts (q root p c : Nat)
    (hc : Decomposition.inputCheck p c = true)
    (hΩ : omegaSequence (base q) 1 = omegaSequence (base p) 1)
    (hv : interpretation q (DirectZeta.argumentCode root) = interpretation p c) :
    DirectZeta.sourceValue q root = RelativeZeta.zetaValue (base q)
      (interpretation p (Decomposition.highCode 0 c))
      (interpretation p (Decomposition.lowCode 0 c)) := by
  unfold DirectZeta.sourceValue RelativeZeta.zetaValue FixedPoint.SourceStrict
    FixedPoint.delta FixedPoint.residual
  rw [hv, hΩ, ← (Decomposition.parts_code_value p 0 c hc).1,
    ← (Decomposition.parts_code_value p 0 c hc).2]

private theorem sourceValue_nodeCode (q c : Nat) (hc : Decomposition.inputCheck q c = true) :
    DirectZeta.sourceValue q (BoundedPublicReturn.nodeCode 0 c) = RelativeZeta.zetaValue (base q)
      (interpretation q (Decomposition.highCode 0 c))
      (interpretation q (Decomposition.lowCode 0 c)) := by
  apply sourceValue_of_parts q _ q c hc rfl
  rw [DirectZeta.argumentCode, BoundedPublicReturn.nodeCode, Localization.argumentCode_theta,
    rawTree_code_eq q c ((Decomposition.inputCheck_exact _ _).mp hc).1]

private theorem shiftedArgument_lowPart (s a c : Nat) (ha : Iota.rootCheck s a = true)
    (hc : Decomposition.inputCheck (contextCode s) c = true) :
    interpretation (contextCode s) (Decomposition.lowCode 0 (BoundedPublicReturn.shiftedArgument s a c)) =
      interpretation (contextCode s) a + interpretation (contextCode s) (Decomposition.lowCode 0 c) := by
  have hs := shiftedArgument_spec s a c ha hc
  have ht : interpretation (contextCode s) a + interpretation (contextCode s) (Decomposition.lowCode 0 c) <
      omegaSequence (base (contextCode s)) 1 :=
    omegaSequence_add_closed (base (contextCode s)) 0
      (Iota.root_below_first_cardinal s a ha) (Decomposition.lowPart_bound (contextCode s) 0 c hc)
  obtain ⟨δ, hδ⟩ := Decomposition.highPart_dvd (contextCode s) 0 c hc
  rw [(Decomposition.parts_code_value (contextCode s) 0 _ hs.1).2, hs.2, hδ,
    Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt ht]

/-- Every original bounded intermediate root has exactly the same literal
Definition2.42 zeta value as its actual returned original-source root. -/
theorem zeta_value (s a root : Nat) (ha : inputCheck s a root = true) :
    NativeContext.SourceZeta.sourceValue s (returnedRoot s a root) =
      DirectZeta.sourceValue (sourceCode s a) root := by
  obtain ⟨houter, ⟨t, he, ht, hn, hh⟩, hb⟩ := (rootCheck_exact s a root).mp ha
  let q := contextCode s
  let α := interpretation q a
  let c := BoundedPublicReturn.sourceTermCode s a t
  let Γ := interpretation q (Decomposition.highCode 0 c)
  let ρ := interpretation q (Decomposition.lowCode 0 c)
  have hac := BaseTransformation.theta_argument_check (sourceCode s a) 0 t ht
  have hr : Restricted s a root t := by
    simpa only [he, Localization.argumentCode_theta, ThetaCourse.rawTree_code] using argument_restricted s a root ha
  have hc := SourceReturn.sourceTermCode_spec s a root ha t hac hn hr
  have hp := Decomposition.parts_accepted q 0 c hc.1
  have hq := base_pos q (NativePublicBridge.contextCode_checked s)
  have hΩ : 0 < omegaSequence (base q) 1 := (omegaSequence_isSuccLimit (base q) 0).bot_lt
  have hhigh : omegaSequence (base q) 1 ≤ interpretation q c := by
    rw [hc.2, Iota.HeightSupport.root_omegaSequence_succ s a 0 houter]
    apply le_of_not_gt
    intro h
    exact (not_le_of_gt hh) ((denote_lt_iff_outerSort_le (sourceCode s a) t hac 1 (by omega)).mp h)
  have hΓ0 : 0 < Γ := by
    rw [(Decomposition.parts_code_value q 0 c hc.1).1]
    exact mul_pos hΩ ((Ordinal.div_pos hΩ.ne').mpr hhigh)
  have hz : FixedPoint.zeroCheck (Decomposition.highCode 0 c) = false := by
    apply Bool.eq_false_of_not_eq_true
    intro h
    exact (ne_of_gt hΓ0) ((FixedPoint.zeroCheck_exact q _ hp.1).mp h)
  have hroot : returnedRoot s a root = BoundedPublicReturn.zeroCode s a c := by
    simpa only [returnedRoot, he, ThetaCourse.rawTree_code, BoundedPublicReturn.sourceTermCode_theta,
      BoundedPublicReturn.thetaCode, beq_self_eq_true, Bool.cond_true]
  have harg : interpretation (sourceCode s a) (DirectZeta.argumentCode root) = interpretation q c := by
    rw [DirectZeta.argumentCode, he, Localization.argumentCode_theta, interpretation_code, hc.2]
  have hnew := sourceValue_of_parts (sourceCode s a) root q c hc.1
    (Iota.HeightSupport.root_omegaSequence_succ s a 0 houter).symm harg
  have hα := Iota.alpha_base s a houter
  change DirectZeta.sourceValue q (returnedRoot s a root) = _
  rw [hnew, hα, hroot]
  have hρ : ρ < omegaSequence (base q) 1 := Decomposition.lowPart_bound q 0 c hc.1
  have hΓd : omegaSequence (base q) 1 ∣ Γ := Decomposition.highPart_dvd q 0 c hc.1
  have hΓn : GlobalNotation (base q) 1 Γ := by
    simpa only [Γ, Decomposition.highCode, interpretation_code] using
      Decomposition.checked_all_levels q 1 (Decomposition.highPartTerm 0 c)
        (Decomposition.parts_checked q 0 c hc.1).1
  have hsort : interpretation q c < omegaSequence (base q) 2 := by
    rw [hc.2, Iota.HeightSupport.root_omegaSequence_succ s a 1 houter]
    exact FixedPoint.checked_theta_sort _ 0 t ht
  have hΓs : Γ < omegaSequence (base q) 2 := (Decomposition.parts_le q 0 c hc.1).1.trans_lt hsort
  have hhead := BoundedPublicReturn.nodeCode_spec q 0 (Decomposition.highCode 0 c) hp.1 hΓs
  simp only [BoundedPublicReturn.zeroCode, hz, Bool.cond_false]
  cases hcmp : Normalization.lessRawCode q a (BoundedPublicReturn.nodeCode 0 (Decomposition.highCode 0 c)) with
  | true =>
    have habove : α < globalCollapse (base q) 0 Γ := by
      simpa only [hhead.2] using ((Normalization.lessRawCode_exact q a _).mp hcmp).2.2
    simp only [hcmp, Bool.cond_true]
    rw [sourceValue_nodeCode q c hc.1]
    exact (RelativeZeta.source_head_above_zeta (base q) α hq
      (Iota.root_base_le s a houter) (Iota.root_below_first_cardinal s a houter)
      Γ hΓn hΓs hΓd habove ρ hρ).symm
  | false =>
    have hbelow : globalCollapse (base q) 0 Γ ≤ α := by
      apply le_of_not_gt
      intro hgt
      have hc' := (Normalization.lessRawCode_exact q a _).mpr
        ⟨Iota.root_original s a houter, ((Comparison.acceptedCode_exact q _).mp hhead.1).1,
          by simpa only [hhead.2] using hgt⟩
      simp only [hcmp, Bool.false_eq_true] at hc'
    let A := interpretation q (NativeContext.Lambda.argumentCode a)
    let Δ := interpretation q (NativeContext.Lambda.deltaCode a)
    let η := interpretation q (Decomposition.lowCode 0 (NativeContext.Lambda.argumentCode a))
    have hAinput := NativeContext.Lambda.argument_accepted s a houter
    have hAtree := Decomposition.input_tree q _ hAinput
    have hA0 : GlobalNotation (base q) 0 A := by
      rw [Decomposition.input_value q _ hAinput]
      exact checked_globalNotation q _ hAtree.1
    have hA : GlobalNotation (base q) 1 A := by
      exact globalNotation_embeds_next (base q) hq 0 hA0
    obtain ⟨u, hau, hu, hnu, hhu⟩ := (Iota.rootCheck_exact s a).mp houter
    have hAs : A < omegaSequence (base q) 2 := by
      simpa only [A, NativeContext.Lambda.argumentCode, hau, Localization.argumentCode_theta,
        interpretation_code] using FixedPoint.checked_theta_sort q 0 u hu
    have haA : α = globalCollapse (base q) 0 A := by
      simpa only [α, A, NativeContext.Lambda.argumentCode, hau, Localization.argumentCode_theta,
        interpretation_code] using
        (rfl : denote q (.theta 0 u) = globalCollapse (base q) 0 (denote q u))
    have hΓΔ : Γ < Δ := BoundedPublicReturn.converted_highPart_lt_delta s a c houter t ht hn
      (by simpa only [he, interpretation_code] using hb) hc.1 hc.2
    have hs := shiftedArgument_spec s a c houter hc.1
    simp only [hcmp, Bool.cond_false]
    rw [sourceValue_nodeCode q _ hs.1, shiftedArgument_highPart s a c houter hc.1,
      shiftedArgument_lowPart s a c houter hc.1]
    have hw := RelativeZeta.source_head_below_zeta (base q) hq A Δ η Γ hA hA0 hAs
      (Decomposition.highPart_dvd q 0 _ hAinput) (Decomposition.lowPart_bound q 0 _ hAinput)
      (Decomposition.parts_reconstruct q 0 _ hAinput).symm hΓn hΓd hΓ0 hΓΔ
      (by simpa only [← haA] using hbelow) ρ hρ
    simpa only [← haA] using hw

/-- The real old and intermediate literal iota high-part values agree.
Both actual Normal source presentations are derived and compared. -/
theorem literalDelta_value (s a root : Nat) (ha : inputCheck s a root = true) :
    interpretation (betaCode s a root)
        (Iota.literalCode s (returnedRoot s a root) (NativeContext.Lambda.deltaCode (returnedRoot s a root))) =
      interpretation (betaCode s a root) (literalDelta s a root) := by
  have hroot := returnedRoot_iota_caller s a root ha
  have hi := OmegaQuotient.argument_accepted s a root ha
  let t := Decomposition.highPartTerm 0 (OmegaQuotient.argumentCode root)
  have ht := (Decomposition.parts_checked (sourceCode s a) 0 _ hi).1
  have hn := (Decomposition.parts_normal (sourceCode s a) 0 _ hi).1
  have hr := delta_restricted s a root ha
  have hs := returnedTerm_spec s a root ha t ht hn hr
  have hcut := returnedTerm_restricted s a root ha t ht hn hr
  have ho := NativeContext.Lambda.argument_accepted s (returnedRoot s a root) hroot
  have hoc := (Decomposition.parts_accepted (contextCode s) 0 _ ho).1
  have hot := Decomposition.input_tree (contextCode s) _ hoc
  have hor := NativeContext.Lambda.delta_restricted s (returnedRoot s a root) hroot
  have hv : denote (contextCode s)
      (ThetaCourse.rawTree (NativeContext.Lambda.deltaCode (returnedRoot s a root))) =
        denote (contextCode s) (returnedTerm s a t) := by
    calc
      _ = interpretation (contextCode s) (NativeContext.Lambda.deltaCode (returnedRoot s a root)) :=
        Arithmetic.raw_value (contextCode s) _ ((Comparison.acceptedCode_exact _ _).mp hoc).1
      _ = interpretation (sourceCode s a) (OmegaQuotient.deltaCode root) :=
        returnedRoot_delta_value s a root ha
      _ = denote (sourceCode s a) t := rfl
      _ = denote (contextCode s) (returnedTerm s a t) := hs.2.2.symm
  have he := (Iota.transform_eq_iff s _ hroot _ _ hot.1 hs.1 hot.2 hs.2.1
    (by simpa only [NativeContext.Lambda.deltaCode, Decomposition.highCode,
      ThetaCourse.rawTree_code] using hor) hcut).mpr hv
  rw [returnedRoot_alphaCode s a root ha] at he
  have hcomm := transform_return_value s a root ha t ht hn hr
  have hold : Iota.literalCode s (returnedRoot s a root)
      (NativeContext.Lambda.deltaCode (returnedRoot s a root)) =
      (Iota.transform s (returnedRoot s a root)
        (ThetaCourse.rawTree (NativeContext.Lambda.deltaCode (returnedRoot s a root)))).code := by
    obtain ⟨_, u, heu, hu, hnu, hsu⟩ :=
      (Iota.inputCheck_exact s _ _).mp (NativeContext.Lambda.delta_input s _ hroot)
    simp only [Iota.literalCode, NativeContext.Lambda.delta_input s _ hroot, Bool.cond_true,
      heu, Iota.stateCode_code, ThetaCourse.rawTree_code]
  simpa only [hold, literalDelta, deltaCode, OmegaQuotient.deltaCode,
    literalCode_code s a root ha t ht hn hr, interpretation_code] using he.trans hcomm

/-- Both genuine executions realize the HIGH/epsilon intermediate case of
printed Lemma2.48(d) at the original positive-source bounded root. Their source caller and SAME
canonical beta are conclusions, not additional input hypotheses. -/
theorem execute_translation (s a root out : Nat) (ho : out ∈ execute s a root) :
    ∃ originalOut : Nat, originalOut ∈ NativeContext.Lambda.execute s (returnedRoot s a root) ∧
      Iota.alphaCode s (returnedRoot s a root) = betaCode s a root ∧
      interpretation (betaCode s a root) originalOut = interpretation (betaCode s a root) out := by
  have hn := execute_spec s a root out ho
  have hroot := returnedRoot_iota_caller s a root hn.1
  obtain ⟨originalOut, hold⟩ := NativeContext.Lambda.execute_returns s _ hroot
  have hv := (NativeContext.Lambda.execute_spec s _ originalOut hold).2.2
  rw [returnedRoot_alphaCode s a root hn.1, literalDelta_value s a root hn.1,
    zeta_value s a root hn.1] at hv
  exact ⟨originalOut, hold, returnedRoot_alphaCode s a root hn.1, hv.trans hn.2.2.2.symm⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.BoundedContextIota.Lambda.Translation
