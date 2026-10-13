import Alexander313.Wilken.SourceOneNativeMuHeightSupport

/-!
# Actual source-one mu below the original alpha-plus

The original successor argument has genuine global notation, cardinal
range and a nonzero high part. Its actual source collapse is epsilon.
The computed iota coefficient is below the enclosed Delta; finite chi+k
and omega power then stay below that ORIGINAL endpoint. Actual original
source-one coverage also supplies checked Normal LOW representatives at
the same value. Normal and original raw execution are included. No chosen
return, endpoint, representation or contextual mu-plus oracle. Uncompiled.
-/

noncomputable section

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.Mu.Bounds

theorem source_successor_argument_spec (a : Nat) (ha : inputCheck a = true) :
    GlobalNotation (finiteBase 0) 0 (interpretation 0 (Lambda.argumentCode a) + 1) ∧
      interpretation 0 (Lambda.argumentCode a) + 1 < omegaSequence (finiteBase 0) 2 ∧
      omegaSequence (finiteBase 0) 1 ≤ interpretation 0 (Lambda.argumentCode a) + 1 := by
  obtain ⟨t, he, ht, hn, hh⟩ := (rootCheck_exact a).mp ha
  have hA : GlobalNotation (finiteBase 0) 0 (interpretation 0 (Lambda.argumentCode a)) := by
    simpa only [OmegaQuotient.argumentCode, he, Localization.argumentCode_theta,
      interpretation_code] using SourceDecomposition.checked_all_levels 0 0 t
        (OrderSupport.argument_checked 0 t ht)
  have hOne : GlobalNotation (finiteBase 0) 0 1 := by
    simpa only [OmegaQuotient.unitTerm_spec.2.2] using
      SourceDecomposition.checked_all_levels 0 0 OmegaQuotient.unitTerm OmegaQuotient.unitTerm_spec.1
  have hAs : interpretation 0 (Lambda.argumentCode a) < omegaSequence (finiteBase 0) 2 := by
    simpa only [OmegaQuotient.argumentCode, he, Localization.argumentCode_theta, interpretation_code] using
      SourceFixedPoint.checked_theta_sort 0 0 t ht
  exact ⟨hA.add hOne, (omegaSequence_isSuccLimit (finiteBase 0) 1).add_one_lt hAs,
    (Lambda.argument_not_low a ha).trans le_self_add⟩

theorem source_alphaPlus_epsilon (a : Nat) (ha : inputCheck a = true) :
    Ordinal.omega0 ^ Enclosure.sourceAlphaPlus a = Enclosure.sourceAlphaPlus a := by
  have hs := source_successor_argument_spec a ha
  have hn := globalNotation_embeds_next (finiteBase 0) (finiteBase_pos 0) 0 hs.1
  exact NativeContext.SourceChi.Powers.global_high_epsilon (finiteBase 0)
    (Or.inl finiteBase_zero) ⟨interpretation 0 (Lambda.argumentCode a) + 1, hn⟩ hs.2.1 hs.2.2

theorem source_alphaPlus_lt_source_boundary (a : Nat) (ha : inputCheck a = true) :
    Enclosure.sourceAlphaPlus a < globalBoundary (finiteBase 0) 0 := by
  have hs := source_successor_argument_spec a ha
  have hArg := globalNotation_sorted_lt_boundary (finiteBase 0) (finiteBase_pos 0) 0 0 le_rfl hs.1 hs.2.1
  have hEnd : GlobalNotation (finiteBase 0) 0 (Enclosure.sourceAlphaPlus a) :=
    GlobalNotation.collapse le_rfl hs.2.1 hs.1
  exact (globalNotation_low_iff_lt_boundary (finiteBase 0) (finiteBase_pos 0) 0 _).mp
    ⟨hEnd, (globalCollapse_bounds (finiteBase 0) (finiteBase_pos 0) 0 _ hArg).2⟩

theorem mappedCoefficient_lt_source_alphaPlus (a : Nat) (ha : inputCheck a = true) :
    NativeContext.interpretation (alphaCode a) (mappedCoefficient a) < Enclosure.sourceAlphaPlus a :=
  (HeightSupport.mappedCoefficient_le_delta a ha).trans_lt (Enclosure.source_lemma_2_46_a a ha)

theorem exponentCode_lt_source_alphaPlus (a : Nat) (ha : inputCheck a = true) :
    NativeContext.interpretation (alphaCode a) (exponentCode a) < Enclosure.sourceAlphaPlus a := by
  have he := source_alphaPlus_epsilon a ha
  have hp : Ordinal.IsPrincipal (· + ·) (Enclosure.sourceAlphaPlus a) := by
    rw [← he]
    exact Ordinal.isPrincipal_add_omega0_opow _
  have hn : (tail a : Ordinal.{0}) < Enclosure.sourceAlphaPlus a :=
    (Ordinal.natCast_lt_omega0 _).trans (epsilon_omega_lt he)
  have hs := NativeContext.OmegaPowerHeight.finiteTailCode_spec (alphaCode a)
    (mappedCoefficient a) (tail a) (mappedCoefficient_spec a ha).1
  rw [hs.2.2.1]
  exact hp (mappedCoefficient_lt_source_alphaPlus a ha) hn

theorem muCode_lt_source_alphaPlus (a : Nat) (ha : inputCheck a = true) :
    NativeContext.interpretation (alphaCode a) (muCode a) < Enclosure.sourceAlphaPlus a := by
  have hs := NativeContext.OmegaPowers.powerCode_spec (alphaCode a) (exponentCode a) (exponentCode_spec a ha).1
  rw [muCode_literal a ha, hs.2.2]
  exact (omegaPower_strictMono (exponentCode_lt_source_alphaPlus a ha)).trans_eq
    (source_alphaPlus_epsilon a ha)

theorem execute_lt_source_alphaPlus (a out : Nat) (ho : out ∈ execute a) :
    NativeContext.interpretation (alphaCode a) out < Enclosure.sourceAlphaPlus a := by
  obtain ⟨ha, rfl⟩ := (execute_graph a out).mp ho
  exact muCode_lt_source_alphaPlus a ha

theorem normalized_source_alphaPlus (a : Nat) (ha : Raw.inputCheck a = true) :
    Enclosure.sourceAlphaPlus (Raw.normalizedRoot a) = Enclosure.sourceAlphaPlus a :=
  Lambda.Raw.sourceAlphaPlus_normalized a ha

theorem raw_execute_lt_original_source_alphaPlus (a out : Nat) (ho : out ∈ Raw.execute a) :
    NativeContext.interpretation (Raw.outputContext a) out < Enclosure.sourceAlphaPlus a := by
  obtain ⟨ha, rfl⟩ := (Raw.execute_graph a out).mp ho
  have hb := muCode_lt_source_alphaPlus (Raw.normalizedRoot a) (Bool.and_eq_true.mp ha).2
  simpa only [Raw.muCode, ha, Bool.cond_true, Raw.outputContext, normalized_source_alphaPlus a ha] using hb

theorem normal_low_representative (ξ : Ordinal.{0}) (hξ : ξ < globalBoundary (finiteBase 0) 0) :
    ∃ t : RelativeTerm Nat, check 0 t = true ∧ Theta.Normal 0 t ∧ t.outerSort ≤ 1 ∧ denote 0 t = ξ := by
  obtain ⟨t, ht, hv⟩ := (SourceOne.PublicCodes.lt_boundary_iff_checked ξ).mp hξ
  have hc : check 0 t = true := by simpa only [check_zero] using (Bool.and_eq_true.mp ht).1
  have hn := OmegaQuotient.normalize_spec t hc
  have hvalue : denote 0 (Theta.Normalization.normalize 0 t) = ξ :=
    hn.2.2.trans (by simpa only [denote_zero] using hv)
  have hsmall : denote 0 (Theta.Normalization.normalize 0 t) < omegaSequence (finiteBase 0) 1 := by
    rw [hvalue]
    exact hξ.trans (globalBoundary_lt_cardinal (finiteBase 0) (finiteBase_pos 0) 0)
  exact ⟨Theta.Normalization.normalize 0 t, hn.1, hn.2.1,
    (denote_lt_iff_outerSort_le 0 _ hn.1 1 (by omega)).mp hsmall, hvalue⟩

theorem execute_source_code (a out : Nat) (ho : out ∈ execute a) :
    ∃ c : Nat, Theta.acceptedLowCode 0 c = true ∧
      interpretation 0 c = NativeContext.interpretation (alphaCode a) out := by
  have ha := (execute_spec a out ho).1
  obtain ⟨t, ht, hn, hl, hv⟩ := normal_low_representative _
    ((execute_lt_source_alphaPlus a out ho).trans (source_alphaPlus_lt_source_boundary a ha))
  refine ⟨t.code, (Theta.acceptedLowCode_iff 0 _).mpr ⟨?_, ?_⟩, ?_⟩
  · simp only [lowCheckCode_code, lowCheck, ht, hl, decide_true, Bool.true_and]
  · simpa only [ThetaCourse.rawTree_code] using hn
  · simpa only [interpretation_code] using hv

theorem raw_execute_source_code (a out : Nat) (ho : out ∈ Raw.execute a) :
    ∃ c : Nat, Theta.acceptedLowCode 0 c = true ∧
      interpretation 0 c = NativeContext.interpretation (Raw.outputContext a) out := by
  have ha := (Raw.execute_spec a out ho).1
  have hb : Enclosure.sourceAlphaPlus a < globalBoundary (finiteBase 0) 0 := by
    rw [← normalized_source_alphaPlus a ha]
    exact source_alphaPlus_lt_source_boundary _ (Bool.and_eq_true.mp ha).2
  obtain ⟨t, ht, hn, hl, hv⟩ := normal_low_representative _
    ((raw_execute_lt_original_source_alphaPlus a out ho).trans hb)
  refine ⟨t.code, (Theta.acceptedLowCode_iff 0 _).mpr ⟨?_, ?_⟩, ?_⟩
  · simp only [lowCheckCode_code, lowCheck, ht, hl, decide_true, Bool.true_and]
  · simpa only [ThetaCourse.rawTree_code] using hn
  · simpa only [interpretation_code] using hv

theorem execute_lt_public_endpoint (a out : Nat) (ho : out ∈ execute a) :
    NativeContext.interpretation (alphaCode a) out < finiteBase 1 := by
  obtain ⟨c, hc, hv⟩ := execute_source_code a out ho
  exact hv ▸ (lt_nextBase_iff_code 0 _).mpr ⟨c, ((Theta.acceptedLowCode_iff 0 c).mp hc).1, rfl⟩

theorem raw_execute_lt_public_endpoint (a out : Nat) (ho : out ∈ Raw.execute a) :
    NativeContext.interpretation (Raw.outputContext a) out < finiteBase 1 := by
  obtain ⟨c, hc, hv⟩ := raw_execute_source_code a out ho
  exact hv ▸ (lt_nextBase_iff_code 0 _).mpr ⟨c, ((Theta.acceptedLowCode_iff 0 c).mp hc).1, rfl⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.Mu.Bounds
