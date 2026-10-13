import Alexander313.Wilken.SourceOneNativeBoundedContextLambdaTranslationSupport

/-!
# Genuine high lambda translation with the original source-one outer root

Every original high intermediate root derives its real source-zero returned
caller. Its unchanged or alpha-shifted tail satisfies the literal STRICT
and zeta identity. Original full level-zero notation, the smaller-head
bound, original order reflection and full iota return commutation are
constructed from the original two root guards. Both real executions agree
at the same canonical beta. No Native base-one parser or transport oracle.
The non-epsilon branch is separate. Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.BoundedContextLambda.Translation

open BoundedContextReturn TranslationSupport

theorem zeta_value (a b : Nat) (hi : inputCheck a b = true) :
    SourceZeta.sourceValue 0 (returnedRoot a b) = NativeContext.DirectZeta.sourceValue (alphaCode a) b := by
  obtain ⟨ha, hb⟩ := (inputCheck_exact a b).mp hi
  obtain ⟨_, ⟨t, he, ht, hn, hh⟩, hbound⟩ :=
    (NativeContext.PublicEpsilonIota.rootCheck_exact _ _).mp hb
  let α := interpretation 0 a
  let c := BoundedPublicReturn.sourceTermCode a t
  let Γ := interpretation 0 (SourceDecomposition.highCode 0 0 c)
  let ρ := interpretation 0 (SourceDecomposition.lowCode 0 0 c)
  have hac := NativeContext.BaseTransformation.theta_argument_check (alphaCode a) 0 t ht
  have hr : NativeContext.PublicEpsilonIota.Restricted (alphaCode a) b t := by
    simpa only [he, Localization.argumentCode_theta, ThetaCourse.rawTree_code] using
      NativeContext.PublicEpsilonIota.argument_restricted (alphaCode a) b hb
  have hc := BoundedContextReturn.sourceTermCode_spec a b ha hb t hac hn hr
  have hp := SourceDecomposition.parts_accepted 0 0 c hc.1
  have hΩ : 0 < omegaSequence (finiteBase 0) 1 := (omegaSequence_isSuccLimit (finiteBase 0) 0).bot_lt
  have hhigh : omegaSequence (finiteBase 0) 1 ≤ interpretation 0 c := by
    rw [hc.2, finiteBase_zero, HeightSupport.root_omegaSequence_succ a 0 ha]
    apply le_of_not_gt
    intro h
    exact (not_le_of_gt hh)
      ((NativeContext.denote_lt_iff_outerSort_le _ t hac 1 (by omega)).mp h)
  have hΓ0 : 0 < Γ := by
    rw [(SourceDecomposition.parts_code_value 0 0 c hc.1).1]
    exact mul_pos hΩ ((Ordinal.div_pos hΩ.ne').mpr hhigh)
  have hz : SourceFixedPoint.zeroCheck 0 (SourceDecomposition.highCode 0 0 c) = false := by
    apply Bool.eq_false_of_not_eq_true
    intro h
    exact (ne_of_gt hΓ0) ((SourceFixedPoint.zeroCheck_exact 0 _ hp.1).mp h)
  have hroot : returnedRoot a b = BoundedPublicReturn.zeroCode a c := by
    simpa only [returnedRoot, he, ThetaCourse.rawTree_code, BoundedPublicReturn.sourceTermCode_theta,
      BoundedPublicReturn.thetaCode, beq_self_eq_true, Bool.cond_true]
  have harg : NativeContext.interpretation (alphaCode a) (NativeContext.DirectZeta.argumentCode b) =
      interpretation 0 c := by
    rw [NativeContext.DirectZeta.argumentCode, he, Localization.argumentCode_theta,
      NativeContext.interpretation_code, hc.2]
  have hnew := directValue_of_parts (alphaCode a) b c hc.1
    (by simpa only [finiteBase_zero] using (HeightSupport.root_omegaSequence_succ a 0 ha).symm) harg
  rw [hnew, alpha_base a ha, hroot]
  have hρ : ρ < omegaSequence (finiteBase 0) 1 := SourceDecomposition.lowPart_bound 0 0 c hc.1
  have hΓd : omegaSequence (finiteBase 0) 1 ∣ Γ := SourceDecomposition.highPart_dvd 0 0 c hc.1
  have hΓn : GlobalNotation (finiteBase 0) 1 Γ := by
    simpa only [Γ, SourceDecomposition.highCode, interpretation_code] using
      SourceDecomposition.checked_all_levels 0 1 (SourceDecomposition.highPartTerm 0 0 c)
        (SourceDecomposition.parts_checked 0 0 c hc.1).1
  have hsort : interpretation 0 c < omegaSequence (finiteBase 0) 2 := by
    rw [hc.2, finiteBase_zero, HeightSupport.root_omegaSequence_succ a 1 ha]
    exact NativeContext.FixedPoint.checked_theta_sort _ 0 t ht
  have hΓs : Γ < omegaSequence (finiteBase 0) 2 := (SourceDecomposition.parts_le 0 0 c hc.1).1.trans_lt hsort
  have hhead := BoundedPublicReturn.nodeCode_spec 0 (SourceDecomposition.highCode 0 0 c) hp.1 hΓs
  have hαlow : α < omegaSequence (finiteBase 0) 1 := by
    simpa only [α, finiteBase_zero] using root_lt_first a ha
  have hαbase : finiteBase 0 ≤ α := by
    simpa only [α, finiteBase_zero] using (EpsilonOffsets.epsilon_one_lt (root_epsilon a ha)).le
  simp only [BoundedPublicReturn.zeroCode, hz, Bool.cond_false]
  cases hcmp : Theta.Normalization.lessRawCode 0 a
      (BoundedPublicReturn.nodeCode 0 (SourceDecomposition.highCode 0 0 c)) with
  | true =>
    have habove : α < globalCollapse (finiteBase 0) 0 Γ := by
      simpa only [hhead.2] using
        (Theta.Normalization.lessRawCode_correct 0 a _ (root_original a ha)
          ((Theta.acceptedCode_iff 0 _).mp hhead.1).1).mp hcmp
    simp only [hcmp, Bool.cond_true]
    rw [sourceValue_nodeCode c hc.1]
    exact (NativeContext.RelativeZeta.source_head_above_zeta (finiteBase 0) α (finiteBase_pos 0)
      hαbase hαlow Γ hΓn hΓs hΓd habove ρ hρ).symm
  | false =>
    have hbelow : globalCollapse (finiteBase 0) 0 Γ ≤ α := by
      apply le_of_not_gt
      intro hgt
      have hc' := (Theta.Normalization.lessRawCode_correct 0 a _ (root_original a ha)
        ((Theta.acceptedCode_iff 0 _).mp hhead.1).1).mpr (by simpa only [hhead.2] using hgt)
      simp only [hcmp, Bool.false_eq_true] at hc'
    let A := interpretation 0 (Lambda.argumentCode a)
    let Δ := interpretation 0 (Lambda.deltaCode a)
    let η := interpretation 0 (SourceDecomposition.lowCode 0 0 (Lambda.argumentCode a))
    have hAinput := Lambda.argument_accepted a ha
    have hAtree := SourceDecomposition.input_tree 0 _ hAinput
    have hA0 : GlobalNotation (finiteBase 0) 0 A := by
      rw [SourceDecomposition.input_value 0 _ hAinput]
      exact checked_globalNotation 0 _ hAtree.1
    have hA : GlobalNotation (finiteBase 0) 1 A :=
      globalNotation_embeds_next (finiteBase 0) (finiteBase_pos 0) 0 hA0
    obtain ⟨u, hau, hu, hnu, hhu⟩ := (rootCheck_exact a).mp ha
    have hAs : A < omegaSequence (finiteBase 0) 2 := by
      simpa only [A, Lambda.argumentCode, OmegaQuotient.argumentCode, hau,
        Localization.argumentCode_theta, interpretation_code] using SourceFixedPoint.checked_theta_sort 0 0 u hu
    have haA : α = globalCollapse (finiteBase 0) 0 A := by
      simp only [α, A, Lambda.argumentCode, OmegaQuotient.argumentCode, hau,
        Localization.argumentCode_theta, interpretation_code]
      rfl
    have hΓΔ : Γ < Δ := BoundedPublicReturn.converted_highPart_lt_delta a c ha t ht hn
      (by rw [← BoundedContextReturn.selected_endpoint a ha];
          simpa only [he, NativeContext.interpretation_code] using hbound) hc.1 hc.2
    have hs := shiftedArgument_spec a c ha hc.1
    simp only [hcmp, Bool.cond_false]
    rw [sourceValue_nodeCode _ hs.1, shiftedArgument_highPart a c ha hc.1,
      shiftedArgument_lowPart a c ha hc.1]
    have hw := NativeContext.RelativeZeta.source_head_below_zeta (finiteBase 0) (finiteBase_pos 0)
      A Δ η Γ hA hA0 hAs
      (SourceDecomposition.highPart_dvd 0 0 _ hAinput) (SourceDecomposition.lowPart_bound 0 0 _ hAinput)
      (SourceDecomposition.parts_reconstruct 0 0 _ hAinput).symm hΓn hΓd hΓ0 hΓΔ
      (by simpa only [← haA] using hbelow) ρ hρ
    simpa only [← haA] using hw

theorem literalDelta_value (a b : Nat) (hi : inputCheck a b = true) :
    NativeContext.interpretation (betaCode a b)
        (SourceOneIota.literalCode (returnedRoot a b) (Lambda.deltaCode (returnedRoot a b))) =
      NativeContext.interpretation (betaCode a b) (literalDelta a b) := by
  obtain ⟨ha, hb⟩ := (inputCheck_exact a b).mp hi
  have hroot := returnedRoot_iota_caller a b ha hb
  have hc := NativeContext.PublicEpsilonIota.OmegaQuotient.Support.argument_accepted _ _ hb
  let t := NativeContext.Decomposition.highPartTerm 0
    (NativeContext.PublicEpsilonIota.OmegaQuotient.argumentCode b)
  have ht := (NativeContext.Decomposition.parts_checked (alphaCode a) 0 _ hc).1
  have hn := (NativeContext.Decomposition.parts_normal (alphaCode a) 0 _ hc).1
  have hr := delta_restricted a b hi
  have hs := returnedTerm_spec a b ha hb t ht hn hr
  have hcut := returnedTerm_restricted a b ha hb t ht hn hr
  have ho := Lambda.argument_accepted (returnedRoot a b) hroot
  have hoc := (SourceDecomposition.parts_accepted 0 0 _ ho).1
  have hot := SourceDecomposition.input_tree 0 _ hoc
  have hor := Lambda.delta_restricted (returnedRoot a b) hroot
  have hv : denote 0 (ThetaCourse.rawTree (Lambda.deltaCode (returnedRoot a b))) =
      denote 0 (returnedTerm a t) := by
    calc
      _ = interpretation 0 (Lambda.deltaCode (returnedRoot a b)) := (SourceDecomposition.input_value 0 _ hoc).symm
      _ = NativeContext.interpretation (alphaCode a)
          (NativeContext.PublicEpsilonIota.OmegaQuotient.deltaCode b) := returnedRoot_delta_value a b ha hb
      _ = NativeContext.denote (alphaCode a) t := rfl
      _ = denote 0 (returnedTerm a t) := hs.2.2.symm
  have he := (SourceOneIota.transform_eq_iff _ hroot _ _ hot.1 hs.1 hot.2 hs.2.1
    (by simpa only [Lambda.deltaCode, OmegaQuotient.deltaCode, SourceDecomposition.highCode,
      ThetaCourse.rawTree_code] using hor) hcut).mpr hv
  rw [returnedRoot_alphaCode a b ha hb] at he
  have hcomm := transform_return_value a b ha hb t ht hn hr
  have hold : SourceOneIota.literalCode (returnedRoot a b) (Lambda.deltaCode (returnedRoot a b)) =
      (SourceOneIota.transform (returnedRoot a b) (ThetaCourse.rawTree (Lambda.deltaCode (returnedRoot a b)))).code := by
    obtain ⟨_, u, heu, hu, hnu, hsu⟩ :=
      (SourceOneIota.inputCheck_exact _ _).mp (Lambda.delta_input _ hroot)
    simp only [SourceOneIota.literalCode, Lambda.delta_input _ hroot, Bool.cond_true,
      heu, SourceOneIota.stateCode_code, ThetaCourse.rawTree_code]
  simpa only [hold, literalDelta, deltaCode, NativeContext.PublicEpsilonIota.OmegaQuotient.deltaCode,
    NativeContext.PublicEpsilonIota.literalCode_code _ _ hb t ht hn hr,
    NativeContext.interpretation_code] using he.trans hcomm

/-- The original source-one outer case of HIGH/epsilon Lemma2.48(d),
with the genuine source caller and same canonical beta derived. -/
theorem execute_translation (a b out : Nat) (ho : out ∈ execute a b) :
    ∃ originalOut : Nat, originalOut ∈ Lambda.execute (returnedRoot a b) ∧
      SourceOneIota.alphaCode (returnedRoot a b) = betaCode a b ∧
      NativeContext.interpretation (betaCode a b) originalOut = NativeContext.interpretation (betaCode a b) out := by
  have hn := execute_spec a b out ho
  obtain ⟨ha, hb⟩ := (inputCheck_exact a b).mp hn.1
  have hroot := returnedRoot_iota_caller a b ha hb
  obtain ⟨originalOut, hold⟩ := Lambda.execute_returns _ hroot
  have hv := (Lambda.execute_spec _ originalOut hold).2.2
  rw [returnedRoot_alphaCode a b ha hb, literalDelta_value a b hn.1, zeta_value a b hn.1] at hv
  exact ⟨originalOut, hold, returnedRoot_alphaCode a b ha hb, hv.trans hn.2.2.2.symm⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.BoundedContextLambda.Translation
