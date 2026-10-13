import Alexander313.Wilken.SourceOneRootRelativeCutoffRewrite
import Alexander313.Wilken.HereditaryNativeElementaryPublicReturn

/-!
# Complete original source-one zero-index scalar construction

Original check0/Theta.Normal0 syntax supplies every divided head, LOW tail,
selected written support and normalized arithmetic caller. LOW heads use
the genuinely corrected public omega power and actual bounded return0;
positive heads use the actual above-head or selected-support BOTH-minima
identity. No selected dictionary endpoint or Native base-one parser.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.RootScalar

open ThetaCourse RootSupportThreshold

theorem low_of_bound (c : Nat) (hc : argumentCheck c = true)
    (hb : interpretation 0 c < omegaSequence 1 1) : lowCheckCode 0 c = true := by
  have ht := SourceDecomposition.input_tree 0 c hc
  have hs : (rawTree c).outerSort ≤ 1 :=
    (denote_lt_iff_outerSort_le 0 _ ht.1 1 (by omega)).mp (by
      simpa only [finiteBase_zero, raw_value c hc] using hb)
  obtain ⟨t, he, hct⟩ := (checkCode_iff 0 c).mp
    ((SourceDecomposition.inputCheck_exact 0 c).mp hc).1
  simpa only [← he, lowCheckCode_code, lowCheck, hct, decide_eq_true_eq,
    Bool.true_and, rawTree_code] using hs

theorem acceptedLow_to_accepted (c : Nat) (hc : Theta.acceptedLowCode 0 c = true) :
    argumentCheck c = true ∧ lowCheckCode 0 c = true := by
  have hs := (Theta.acceptedLowCode_iff 0 c).mp hc
  have hcheck := (Bool.and_eq_true.mp (by simpa only [lowCheckCode_eq] using hs.1)).1
  exact ⟨(Theta.acceptedCode_iff 0 c).mpr ⟨hcheck, hs.2⟩, hs.1⟩

theorem node_low (k c : Nat) (hc : argumentCheck (nodeCode k c) = true) (hk : k = 0) :
    lowCheckCode 0 (nodeCode k c) = true := by
  subst k
  have ht := (SourceDecomposition.inputCheck_exact 0 _).mp hc
  have hchecked : check 0 (.theta 0 (rawTree c)) = true := by
    simpa only [nodeCode, BoundedPublicReturn.nodeCode, checkCode_code] using ht.1
  simp only [nodeCode, BoundedPublicReturn.nodeCode, lowCheckCode_code, lowCheck,
    hchecked, outerSort, Nat.zero_add, le_refl, decide_true, Bool.true_and]

/-- The ORIGINAL source-one LOW interval is below its real public epsilon
endpoint; this is not the false fixed-tau-one tower domination claim. -/
theorem low_public_bound (c : Nat) (hc : lowCheckCode 0 c = true) :
    interpretation 0 c < finiteBase 1 :=
  (lt_nextBase_iff_code 0 _).mpr ⟨c, hc, rfl⟩

def lowCode (b c : Nat) : Nat := SourceZeta.Transport.returnCode 0
  (NativeContext.ElementaryPublicReturn.collapseCode (alphaCode b) (Nat.pair 0 c))

theorem lowCode_primrec : Primrec₂ lowCode :=
  (SourceZeta.Transport.returnCode_primrec.comp (Primrec.const 0)
    (NativeContext.ElementaryPublicReturn.collapseCode_primrec.comp (alphaCode_primrec.comp Primrec.fst)
      (Primrec₂.natPair.comp (Primrec.const 0) Primrec.snd))).to₂

/-- Genuine root and ORIGINAL LOW argument admission derive the actual
public collapse bound, acceptedLOW return0 and SAME beta-collapse value. -/
theorem lowCode_spec (b c : Nat) (hb : rootCheck b = true)
    (hc : argumentCheck c = true) (hl : lowCheckCode 0 c = true) :
    argumentCheck (lowCode b c) = true ∧ lowCheckCode 0 (lowCode b c) = true ∧
      interpretation 0 (lowCode b c) = globalCollapse (interpretation 0 b) 0 (interpretation 0 c) := by
  have hpublic : unionCheck (Nat.pair 0 c) = true := by simpa only [unionCheck_pair] using hl
  have hcs : interpretation 0 c < omegaSequence 1 1 := by
    obtain ⟨t, he, ht⟩ := (lowCheckCode_iff 0 c).mp hl
    have hp := Bool.and_eq_true.mp ht
    simpa only [← he, interpretation_code, finiteBase_zero] using
      (denote_lt_iff_outerSort_le 0 t hp.1 1 (by omega)).mpr (of_decide_eq_true hp.2)
  have hs := NativeContext.ElementaryPublicReturn.collapseCode_spec (alphaCode b)
    (Nat.pair 0 c) (alphaCode_baseCheck b hb) hpublic (by
      simpa only [unionInterpretation_pair, alpha_base b hb,
        ← root_omegaSequence_pos b 1 hb (by omega)] using hcs)
  have hvalue : unionInterpretation
      (NativeContext.ElementaryPublicReturn.collapseCode (alphaCode b) (Nat.pair 0 c)) =
      globalCollapse (interpretation 0 b) 0 (interpretation 0 c) := by
    simpa only [alpha_base b hb, unionInterpretation_pair] using hs.2
  have hε := finiteBase_succ_omegaPower_eq_self 0
  have hp := epsilon_or_one_add_closed (Or.inr hε)
  have hβ : interpretation 0 b < finiteBase 1 := low_public_bound b (root_low b hb)
  have hξ : interpretation 0 c < finiteBase 1 := low_public_bound c hl
  have hlim := Ordinal.isSuccLimit_of_isPrincipal_add
    (Ordinal.one_lt_omega0.trans (epsilon_omega_lt hε)) hp
  have hexp : lowOmegaExponent (interpretation 0 b) (interpretation 0 c) < finiteBase 1 := by
    have hshift : lowOmegaBase (interpretation 0 b) + interpretation 0 c < finiteBase 1 :=
      hp ((lowOmegaBase_le _).trans_lt hβ) hξ
    exact (lowOmegaExponent_le_shift_succ _ _).trans_lt (hlim.add_one_lt hshift)
  have hbound : globalCollapse (interpretation 0 b) 0 (interpretation 0 c) < finiteBase 1 := by
    rw [globalCollapse_low_eq_omegaPower _ (Or.inr (root_epsilon b hb)) _
      (by simpa only [← root_omegaSequence_pos b 1 hb (by omega)] using hcs)]
    exact finiteBase_succ_omegaPower_closed 0 hexp
  have hr := SourceZeta.Transport.returnCode_spec 0 _ hs.1 (hvalue.trans_lt hbound)
  have ha := acceptedLow_to_accepted _ hr.1
  exact ⟨ha.1, ha.2, hr.2.trans hvalue⟩

def headAbove (b c : Nat) : Bool :=
  Theta.Normalization.lessRawCode 0 b (nodeCode 0 (argumentHeadCode c))

theorem headAbove_primrec : Primrec₂ headAbove :=
  (Theta.Normalization.Effective.lessRawCode_primrec.comp ((Primrec.const 0).pair
    (Primrec.fst.pair (BoundedPublicReturn.nodeCode_primrec.comp (Primrec.const 0)
      (argumentHeadCode_primrec.comp Primrec.snd))))).to₂

def selectedCode (b c : Nat) : Nat := (selected b (argumentHeadCode c)).getD 0

theorem selectedCode_primrec : Primrec₂ selectedCode :=
  (Primrec.option_getD.comp (selected_primrec.comp Primrec.fst
    (argumentHeadCode_primrec.comp Primrec.snd)) (Primrec.const 0)).to₂

def headStrict (b c : Nat) : Bool := Theta.Normalization.lessRawCode 0
  (argumentHeadCode c) (nodeHeadCode (selectedCode b c))

theorem headStrict_primrec : Primrec₂ headStrict :=
  (Theta.Normalization.Effective.lessRawCode_primrec.comp ((Primrec.const 0).pair
    ((argumentHeadCode_primrec.comp Primrec.snd).pair
      (nodeHeadCode_primrec.comp selectedCode_primrec)))).to₂

def kappaCode (b c : Nat) : Nat := cond (headStrict b c) (selectedCode b c)
  (Addition.normalizedSumCode 0
    (SourceDecomposition.lowCode 0 0 (Localization.argumentCode (selectedCode b c)))
    SourceFixedPoint.oneCode)

theorem kappaCode_primrec : Primrec₂ kappaCode := by
  have ht := SourceDecomposition.lowCode_primrec.comp ((Primrec.const 0).pair
    ((Primrec.const 0).pair (Localization.argumentCode_primrec.comp selectedCode_primrec)))
  exact (headStrict_primrec.cond selectedCode_primrec
    (Addition.normalizedSumCode_primrec.comp ((Primrec.const 0).pair
      (ht.pair (Primrec.const SourceFixedPoint.oneCode))))).to₂

def shiftedArgumentCode (b c : Nat) : Nat := Addition.normalizedSumCode 0 (argumentHeadCode c)
  (Addition.normalizedSumCode 0 (kappaCode b c) (SourceDecomposition.lowCode 0 0 c))

theorem shiftedArgumentCode_primrec : Primrec₂ shiftedArgumentCode := by
  have ht := SourceDecomposition.lowCode_primrec.comp ((Primrec.const 0).pair
    ((Primrec.const 0).pair Primrec.snd))
  have hs := Addition.normalizedSumCode_primrec.comp ((Primrec.const 0).pair
    (kappaCode_primrec.pair ht))
  exact (Addition.normalizedSumCode_primrec.comp ((Primrec.const 0).pair
    ((argumentHeadCode_primrec.comp Primrec.snd).pair hs))).to₂

def zeroCode (b c : Nat) : Nat :=
  cond (SourceFixedPoint.zeroCheck 0 (argumentHeadCode c)) (lowCode b c)
    (cond (headAbove b c) (nodeCode 0 c) (nodeCode 0 (shiftedArgumentCode b c)))

theorem zeroCode_primrec : Primrec₂ zeroCode :=
  ((SourceFixedPoint.zeroCheck_primrec.comp (Primrec.const 0)
    (argumentHeadCode_primrec.comp Primrec.snd)).cond lowCode_primrec
    (headAbove_primrec.cond (BoundedPublicReturn.nodeCode_primrec.comp (Primrec.const 0) Primrec.snd)
      (BoundedPublicReturn.nodeCode_primrec.comp (Primrec.const 0) shiftedArgumentCode_primrec))).to₂

theorem zeroCode_spec (b c : Nat) (hb : rootCheck b = true)
    (hc : argumentCheck c = true) (hcs : (rawTree c).outerSort ≤ 2) :
    argumentCheck (zeroCode b c) = true ∧ lowCheckCode 0 (zeroCode b c) = true ∧
      interpretation 0 (zeroCode b c) = globalCollapse (interpretation 0 b) 0 (interpretation 0 c) := by
  let Γ := interpretation 0 (argumentHeadCode c)
  let ρ := interpretation 0 (SourceDecomposition.lowCode 0 0 c)
  have hs : interpretation 0 c < omegaSequence 1 2 := by
    rw [← raw_value c hc, ← finiteBase_zero]
    exact (denote_lt_iff_outerSort_le 0 _ (raw_checked c hc) 2 (by omega)).mpr hcs
  have hd := SourceDecomposition.parts_reconstruct 0 0 c hc
  have hp := SourceDecomposition.parts_accepted 0 0 c hc
  have hΓs : Γ < omegaSequence 1 2 :=
    (SourceDecomposition.parts_le 0 0 c hc).1.trans_lt hs
  have hρ : ρ < omegaSequence 1 1 := SourceDecomposition.lowPart_bound 0 0 c hc
  have hΓd : omegaSequence 1 1 ∣ Γ := SourceDecomposition.highPart_dvd 0 0 c hc
  have hΓsort : (rawTree (argumentHeadCode c)).outerSort ≤ 2 := by
    rw [← raw_value _ hp.1, ← finiteBase_zero] at hΓs
    exact (denote_lt_iff_outerSort_le 0 _ (raw_checked _ hp.1) 2 (by omega)).mp hΓs
  have hhead := nodeCode_sorted_spec 0 (argumentHeadCode c) hp.1 (by simpa only [Nat.zero_add] using hΓsort)
  have hnode := nodeCode_sorted_spec 0 c hc (by simpa only [Nat.zero_add] using hcs)
  cases hz : SourceFixedPoint.zeroCheck 0 (argumentHeadCode c) with
  | true =>
    have hΓ0 : Γ = 0 := (SourceFixedPoint.zeroCheck_exact 0 _ hp.1).mp hz
    have hbound : interpretation 0 c < omegaSequence 1 1 := by
      rw [← hd, hΓ0, zero_add]
      exact hρ
    simpa only [zeroCode, hz, Bool.cond_true] using lowCode_spec b c hb hc (low_of_bound c hc hbound)
  | false =>
    have hΓ0 : 0 < Γ := by
      apply pos_iff_ne_zero.mpr
      intro he
      have ht := (SourceFixedPoint.zeroCheck_exact 0 _ hp.1).mpr he
      simp only [hz, Bool.false_eq_true] at ht
    cases ha : headAbove b c with
    | true =>
      have hβΓ := (Theta.Normalization.lessRawCode_correct 0 b _ (root_original b hb)
        ((SourceDecomposition.inputCheck_exact 0 _).mp hhead.1).1).mp ha
      have hΓn : GlobalNotation 1 1 Γ := by
        simpa only [finiteBase_zero, raw_value _ hp.1] using
          SourceFixedPoint.checked_notation_at 0 _ (raw_checked _ hp.1) 1
      have he := NativeContext.RelativeHighRewrite.global_relative_tail_eq_of_source_head_above
        1 (interpretation 0 b) zero_lt_one (root_base_le b hb) (root_lt_first b hb)
        Γ hΓn hΓs hΓd (by simpa only [hhead.2] using hβΓ) ρ hρ
      simp only [zeroCode, hz, ha, Bool.cond_false, Bool.cond_true]
      exact ⟨hnode.1, node_low 0 c hnode.1 rfl, by
        rw [hnode.2, ← hd]
        exact he.symm⟩
    | false =>
      have hi : RootSupportThreshold.inputCheck b (argumentHeadCode c) = true := by
        apply (RootSupportThreshold.inputCheck_exact b _).mpr
        refine ⟨hb, (sortedCheck_exact _).mpr ⟨hp.1, hΓsort⟩, ?_⟩
        apply le_of_not_gt
        intro hlt
        have ht := (Theta.Normalization.lessRawCode_correct 0 b _ (root_original b hb)
          ((SourceDecomposition.inputCheck_exact 0 _).mp hhead.1).1).mpr hlt
        have ht' : headAbove b c = true := ht
        simp only [ha, Bool.false_eq_true] at ht'
      obtain ⟨d, hsel⟩ := selected_exists b (argumentHeadCode c) hi
      have hchosen : selectedCode b c = d := by simp only [selectedCode, hsel, Option.getD_some]
      have hs := selected_spec b (argumentHeadCode c) d hi hsel
      have hdacc := (node_accepted d hs.2.1).1
      have hdarg := (node_accepted d hs.2.1).2
      have hdlow := (SourceDecomposition.parts_accepted 0 0 _ hdarg).2
      have hsum := Addition.normalizedSumCode_checked 0
        (SourceDecomposition.lowCode 0 0 (Localization.argumentCode d)) SourceFixedPoint.oneCode
        ((SourceDecomposition.inputCheck_exact 0 _).mp hdlow).1
        ((Theta.acceptedCode_iff 0 _).mp SourceFixedPoint.oneCode_accepted).1
      have hsumval : interpretation 0
          (Addition.normalizedSumCode 0 (SourceDecomposition.lowCode 0 0 (Localization.argumentCode d))
            SourceFixedPoint.oneCode) =
          SourceHighPartComparison.tailPart (omegaSequence 1 1)
            (interpretation 0 (Localization.argumentCode d)) + 1 := by
        rw [hsum.2, SourceFixedPoint.oneCode_value,
          (SourceDecomposition.parts_code_value 0 0 _ hdarg).2]
      have hκ : argumentCheck (kappaCode b c) = true ∧
          interpretation 0 (kappaCode b c) = RelativeCutoffRewrite.selectedTail (argumentHeadCode c) d ∧
          interpretation 0 (kappaCode b c) < omegaSequence 1 1 := by
        have htest : headStrict b c = true ↔ Γ < nodeHead d := by
          simpa only [headStrict, hchosen,
            (argumentHeadCode_spec _ hdarg).2, nodeHead, nodeHeadCode] using
            Theta.Normalization.lessRawCode_correct 0 (argumentHeadCode c) (nodeHeadCode d)
              ((SourceDecomposition.inputCheck_exact 0 _).mp hp.1).1
              ((SourceDecomposition.inputCheck_exact 0 _).mp (argumentHeadCode_spec _ hdarg).1).1
        cases hst : headStrict b c with
        | true =>
          have hv : interpretation 0 d < omegaSequence 1 1 := by
            obtain ⟨t, he, ht⟩ := (lowCheckCode_iff 0 d).mp (Localization.node_low 0 d hs.2.1)
            have hp := Bool.and_eq_true.mp ht
            simpa only [← he, interpretation_code, finiteBase_zero] using
              (denote_lt_iff_outerSort_le 0 t hp.1 1 (by omega)).mpr (of_decide_eq_true hp.2)
          simp only [kappaCode, hst, Bool.cond_true, hchosen]
          exact ⟨hdacc, by simp only [RelativeCutoffRewrite.selectedTail, if_pos (htest.mp hst)], hv⟩
        | false =>
          have hnot : ¬ Γ < nodeHead d := fun hlt => by
            have hh := htest.mpr hlt
            simp only [hst, Bool.false_eq_true] at hh
          have hv := (omegaSequence_isSuccLimit 1 0).add_one_lt
            (SourceDecomposition.lowPart_bound 0 0 _ hdarg)
          simp only [kappaCode, hst, Bool.cond_false, hchosen]
          exact ⟨hsum.1, hsumval.trans (by simp only [RelativeCutoffRewrite.selectedTail, if_neg hnot]),
            hsumval.trans_lt hv⟩
      have hsum1 := Addition.normalizedSumCode_checked 0 (kappaCode b c)
        (SourceDecomposition.lowCode 0 0 c)
        ((SourceDecomposition.inputCheck_exact 0 _).mp hκ.1).1
        ((SourceDecomposition.inputCheck_exact 0 _).mp hp.2).1
      have hsum2 := Addition.normalizedSumCode_checked 0 (argumentHeadCode c)
        (Addition.normalizedSumCode 0 (kappaCode b c) (SourceDecomposition.lowCode 0 0 c))
        ((SourceDecomposition.inputCheck_exact 0 _).mp hp.1).1
        ((SourceDecomposition.inputCheck_exact 0 _).mp hsum1.1).1
      have hshift : interpretation 0 (shiftedArgumentCode b c) =
          Γ + (RelativeCutoffRewrite.selectedTail (argumentHeadCode c) d + ρ) := by
        rw [shiftedArgumentCode, hsum2.2, hsum1.2, hκ.2.1]
      have htail := (omegaSequence_add_closed 1 0) hκ.2.2 hρ
      have hshiftbound : interpretation 0 (shiftedArgumentCode b c) < omegaSequence 1 2 := by
        rw [hshift, ← hκ.2.1]
        exact (omegaSequence_add_closed 1 1) hΓs (htail.trans (omegaSequence_step 1 1))
      have hout := BoundedPublicReturn.nodeCode_spec 0 (shiftedArgumentCode b c) hsum2.1 hshiftbound
      have he := RelativeCutoffRewrite.selected_relative_tail_eq b (argumentHeadCode c) d
        hi hsel hΓd hΓ0 ρ hρ
      simp only [zeroCode, hz, ha, Bool.cond_false]
      exact ⟨hout.1, node_low 0 _ hout.1 rfl,
        hout.2.trans ((congrArg (globalCollapse 1 0) hshift).trans
          (he.symm.trans (congrArg (globalCollapse (interpretation 0 b) 0) hd)))⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.RootScalar
