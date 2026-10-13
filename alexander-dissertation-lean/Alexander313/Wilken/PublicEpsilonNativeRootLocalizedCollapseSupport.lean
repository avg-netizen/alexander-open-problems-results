import Alexander313.Wilken.PublicEpsilonNativeRootScalarCollapseSupport
import Alexander313.Wilken.PublicEpsilonNativeRootSupportThreshold
import Alexander313.Wilken.HereditaryNativeRelativeCutoffRewrite

/-!
# Genuine finite callers for the localized larger-head scalar branch

The original root and Normal sorted argument are checked literally.
The actual larger-head and head-collapse comparisons recognize the only
exception of the established scalar dispatcher. Selection runs on the
actual HIGH head, since its source collapse, rather than the complete
argument's collapse, is bounded by beta. The written finite support
threshold and every arithmetic caller are constructed. No selected
endpoint, cutoff, representation or relative-collapse oracle. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RootLocalizedCollapse

open ThetaCourse

abbrev Query := RootAboveHeadCollapse.Query
abbrev headCode := RootAboveHeadCollapse.headCode
abbrev tailCode := RootBelowHeadCollapse.tailCode

def inputCheck (q b c : Nat) : Bool := RootLowCollapse.rootCheck q b &&
  (RootAboveHeadCollapse.argumentCheck q c &&
    (RootScalarCollapse.headLarger q b c && !RootAboveHeadCollapse.headAbove q b c))

theorem inputCheck_primrec : Primrec
    (fun p : Query => inputCheck p.1 p.2.1 p.2.2) :=
  Primrec.and.comp
    (RootLowCollapse.rootCheck_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
    (Primrec.and.comp (RootAboveHeadCollapse.argumentCheck_primrec.comp Primrec.fst
      (Primrec.snd.comp Primrec.snd)) (Primrec.and.comp RootScalarCollapse.headLarger_primrec
        (Primrec.not.comp RootAboveHeadCollapse.headAbove_primrec)))

theorem inputCheck_guards (q b c : Nat) (hi : inputCheck q b c = true) :
    RootLowCollapse.rootCheck q b = true ∧ RootAboveHeadCollapse.argumentCheck q c = true ∧
      RootScalarCollapse.headLarger q b c = true ∧
      RootAboveHeadCollapse.headAbove q b c = false := by
  simpa only [inputCheck, Bool.and_eq_true, Bool.not_eq_true', and_assoc] using hi

theorem inputCheck_exact (q b c : Nat) : inputCheck q b c = true ↔
    RootLowCollapse.rootCheck q b = true ∧ RootAboveHeadCollapse.argumentCheck q c = true ∧
      interpretation q (RootEndpointCollapse.deltaCode b) < interpretation q (headCode c) ∧
      globalCollapse (base q) 0 (interpretation q (headCode c)) ≤ interpretation q b := by
  constructor
  · intro hi
    have h := inputCheck_guards q b c hi
    refine ⟨h.1, h.2.1, (RootScalarCollapse.headLarger_exact q b c h.1 h.2.1).mp h.2.2.1,
      le_of_not_gt ?_⟩
    intro hlt
    have he := (RootAboveHeadCollapse.headAbove_exact q b c h.1 h.2.1).mpr hlt
    simp only [h.2.2.2, Bool.false_eq_true] at he
  · rintro ⟨hb, hc, hl, hu⟩
    have hn : RootAboveHeadCollapse.headAbove q b c = false :=
      Bool.eq_false_of_not_eq_true (fun he => hu.not_gt
        ((RootAboveHeadCollapse.headAbove_exact q b c hb hc).mp he))
    exact Bool.and_eq_true.mpr ⟨hb, Bool.and_eq_true.mpr ⟨hc, Bool.and_eq_true.mpr
      ⟨(RootScalarCollapse.headLarger_exact q b c hb hc).mpr hl,
        by simpa only [hn, Bool.not_false]⟩⟩⟩

theorem head_positive (q b c : Nat) (hi : inputCheck q b c = true) :
    0 < interpretation q (headCode c) :=
  (RootEndpointCollapse.delta_positive q b ((inputCheck_exact q b c).mp hi).1).trans
    ((inputCheck_exact q b c).mp hi).2.2.1

theorem argument_high (q b c : Nat) (hi : inputCheck q b c = true) :
    1 < (rawTree c).outerSort := by
  have h := (inputCheck_exact q b c).mp hi
  have hc := (RootAboveHeadCollapse.argumentCheck_exact q c).mp h.2.1
  have ht := (Comparison.acceptedCode_exact q c).mp hc.1
  have hd := RootAboveHeadCollapse.head_spec q c h.2.1
  have hh : omegaSequence (base q) 1 ≤ interpretation q c :=
    (Ordinal.le_of_dvd (head_positive q b c hi).ne' hd.2.2.1).trans
      (Decomposition.parts_le q 0 c hc.1).1
  apply lt_of_not_ge
  intro hl
  have hs := (denote_lt_iff_outerSort_le q _ (Arithmetic.raw_checked q c ht.1) 1 (by omega)).mpr hl
  rw [Arithmetic.raw_value q c ht.1] at hs
  exact (not_lt_of_ge hh) hs

theorem head_argument (q c : Nat) (hc : RootAboveHeadCollapse.argumentCheck q c = true) :
    RootAboveHeadCollapse.argumentCheck q (headCode c) = true := by
  have ha := (RootBelowHeadCollapse.parts_accepted q c hc).1
  have ht := ((Comparison.acceptedCode_exact q _).mp ha).1
  apply (RootAboveHeadCollapse.argumentCheck_exact q _).mpr
  refine ⟨ha, (denote_lt_iff_outerSort_le q _ (Arithmetic.raw_checked q _ ht) 2 (by omega)).mp ?_⟩
  rw [Arithmetic.raw_value q _ ht]
  exact (RootAboveHeadCollapse.head_spec q c hc).2.1

theorem headThetaCode_eq (c : Nat) :
    OmegaPowers.thetaCode (headCode c) = RootAboveHeadCollapse.headNodeCode c := by
  simp only [headCode, RootAboveHeadCollapse.headCode, Decomposition.highCode,
    OmegaPowers.thetaCode, rawTree_code, RootAboveHeadCollapse.headNodeCode]

/-- Selection is called on the actual head, so the original branch's
source-head bound supplies precisely the genuine threshold caller. -/
theorem threshold_caller (q b c : Nat) (hi : inputCheck q b c = true) :
    RootSupportThreshold.inputCheck q b (headCode c) = true := by
  have h := (inputCheck_exact q b c).mp hi
  apply (RootSupportThreshold.inputCheck_exact q b _).mpr
  refine ⟨h.1, head_argument q c h.2.1, ?_⟩
  rw [headThetaCode_eq, (RootAboveHeadCollapse.headNodeCode_spec q c h.2.1).2.2]
  exact h.2.2.2

def selectedCode (q b c : Nat) : Nat :=
  (RootSupportThreshold.selected q b (headCode c)).getD 0

theorem selectedCode_primrec : Primrec
    (fun p : Query => selectedCode p.1 p.2.1 p.2.2) :=
  Primrec.option_getD.comp (RootSupportThreshold.selected_primrec.comp
    (Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair
      (RootAboveHeadCollapse.headCode_primrec.comp (Primrec.snd.comp Primrec.snd)))))
    (Primrec.const 0)

theorem selectedCode_some (q b c : Nat) (hi : inputCheck q b c = true) :
    RootSupportThreshold.selected q b (headCode c) = some (selectedCode q b c) := by
  obtain ⟨d, hd⟩ := RootSupportThreshold.selected_exists q b _ (threshold_caller q b c hi)
  simp only [selectedCode, hd, Option.getD_some]

theorem head_idempotent (q c : Nat) (hc : RootAboveHeadCollapse.argumentCheck q c = true) :
    SourceHighPartComparison.highPart (omegaSequence (base q) 1)
      (interpretation q (headCode c)) = interpretation q (headCode c) := by
  obtain ⟨d, hd⟩ := (RootAboveHeadCollapse.head_spec q c hc).2.2.1
  rw [hd]
  change omegaSequence (base q) 1 *
    ((omegaSequence (base q) 1 * d) / omegaSequence (base q) 1) = omegaSequence (base q) 1 * d
  rw [Ordinal.mul_div_cancel _ (omegaSequence_isSuccLimit (base q) 0).bot_lt.ne']

/-- The selected code is an actual original written Normal theta node.
Its interval and requested-head bound are derived, including hidden support. -/
theorem selectedCode_spec (q b c : Nat) (hi : inputCheck q b c = true) :
    selectedCode q b c ∈ RootSupportThreshold.fullCodes b ∧
      lowCheckCode q (selectedCode q b c) = true ∧
      Comparison.acceptedCode q (selectedCode q b c) = true ∧
      interpretation q (headCode c) ≤ RootSupportThreshold.nodeHead q (selectedCode q b c) ∧
      interpretation q (selectedCode q b c) ≤ interpretation q b ∧
      interpretation q b < interpretation q (RootSupportThreshold.successorCode q (selectedCode q b c)) := by
  have hs := RootSupportThreshold.selected_interval q b (headCode c) (selectedCode q b c)
    (threshold_caller q b c hi) (selectedCode_some q b c hi)
  exact ⟨hs.1, hs.2.1, hs.2.2.1,
    by simpa only [head_idempotent q c (inputCheck_guards q b c hi).2.1] using hs.2.2.2.1,
    hs.2.2.2.2.2.1, hs.2.2.2.2.2.2⟩

theorem selectedCode_node (q b c : Nat) (hi : inputCheck q b c = true) :
    ∃ a : RelativeTerm Nat, selectedCode q b c = (.theta 0 a).code ∧
      check q (.theta 0 a) = true ∧ Comparison.Normal q a :=
  RootSupportThreshold.fullCodes_node q b _ (inputCheck_guards q b c hi).1
    (selectedCode_spec q b c hi).1

/-- The selected written support is itself a genuine original HIGH root.
This follows from its derived positive head, not from a new root oracle. -/
theorem selectedCode_root (q b c : Nat) (hi : inputCheck q b c = true) :
    RootLowCollapse.rootCheck q (selectedCode q b c) = true := by
  obtain ⟨a, he, ha, hna⟩ := selectedCode_node q b c hi
  have hp : 0 < RootSupportThreshold.nodeHead q (selectedCode q b c) :=
    (head_positive q b c hi).trans_le (selectedCode_spec q b c hi).2.2.2.1
  have hhead : 0 < SourceHighPartComparison.highPart (omegaSequence (base q) 1) (denote q a) := by
    simpa only [RootSupportThreshold.nodeHead, he, Localization.argumentCode_theta,
      interpretation_code] using hp
  have hΩ : omegaSequence (base q) 1 ≤ denote q a :=
    (Ordinal.le_of_dvd hhead.ne' (SourceHighPartComparison.highPart_dvd _ _)).trans
      (SourceHighPartComparison.highPart_le _ _)
  have hhigh : 1 < a.outerSort := by
    apply lt_of_not_ge
    intro hl
    have hs := (denote_lt_iff_outerSort_le q a
      (FixedPoint.checked_theta_argument q 0 a ha) 1 (by omega)).mpr hl
    exact (not_lt_of_ge hΩ) hs
  exact (RootLowCollapse.rootCheck_exact q _).mpr ⟨a, he, ha, hna, hhigh⟩

def selectedArgumentCode (q b c : Nat) : Nat := Localization.argumentCode (selectedCode q b c)

theorem selectedArgumentCode_primrec : Primrec
    (fun p : Query => selectedArgumentCode p.1 p.2.1 p.2.2) :=
  Localization.argumentCode_primrec.comp selectedCode_primrec

theorem selectedArgumentCode_accepted (q b c : Nat) (hi : inputCheck q b c = true) :
    Comparison.acceptedCode q (selectedArgumentCode q b c) = true :=
  (RootSupportThreshold.node_accepted q _ (selectedCode_node q b c hi)).2

def selectedTailCode (q b c : Nat) : Nat := Decomposition.lowCode 0 (selectedArgumentCode q b c)

theorem selectedTailCode_primrec : Primrec
    (fun p : Query => selectedTailCode p.1 p.2.1 p.2.2) :=
  Decomposition.lowCode_primrec.comp (Primrec.const 0) selectedArgumentCode_primrec

def firstTailCode (q b c : Nat) : Nat :=
  Arithmetic.addCode q (selectedTailCode q b c) (OmegaPowerHeight.numeralCode 1)

theorem firstTailCode_primrec : Primrec
    (fun p : Query => firstTailCode p.1 p.2.1 p.2.2) :=
  Arithmetic.addCode_primrec.comp (Primrec.fst.pair
    (selectedTailCode_primrec.pair (Primrec.const (OmegaPowerHeight.numeralCode 1))))

theorem firstTailCode_spec (q b c : Nat) (hi : inputCheck q b c = true) :
    Comparison.acceptedCode q (firstTailCode q b c) = true ∧
      interpretation q (firstTailCode q b c) = interpretation q (selectedTailCode q b c) + 1 ∧
      interpretation q (firstTailCode q b c) < omegaSequence (base q) 1 := by
  have ha := selectedArgumentCode_accepted q b c hi
  have hl := (Decomposition.parts_accepted q 0 _ ha).2
  have hu := OmegaPowerHeight.numeralCode_spec q 1
    (RootLowCollapse.source_checked q b (inputCheck_guards q b c hi).1)
  have hs := Arithmetic.addCode_spec q _ _ ((Comparison.acceptedCode_exact q _).mp hl).1
    ((Comparison.acceptedCode_exact q _).mp hu.2.1).1
  refine ⟨hs.1, ?_, ?_⟩
  · simpa only [firstTailCode, hu.2.2.1, Nat.cast_one] using hs.2.1
  · rw [show interpretation q (firstTailCode q b c) =
      interpretation q (selectedTailCode q b c) + 1 from
        by simpa only [firstTailCode, hu.2.2.1, Nat.cast_one] using hs.2.1]
    exact (omegaSequence_isSuccLimit (base q) 0).add_one_lt (Decomposition.lowPart_bound q 0 _ ha)

def headStrict (q b c : Nat) : Bool := Normalization.lessRawCode q (headCode c)
  (RootSupportThreshold.nodeHeadCode (selectedCode q b c))

theorem headStrict_primrec : Primrec
    (fun p : Query => headStrict p.1 p.2.1 p.2.2) :=
  Normalization.Effective.lessRawCode_primrec.comp (Primrec.fst.pair
    ((RootAboveHeadCollapse.headCode_primrec.comp (Primrec.snd.comp Primrec.snd)).pair
      (RootSupportThreshold.nodeHeadCode_primrec.comp selectedCode_primrec)))

theorem headStrict_exact (q b c : Nat) (hi : inputCheck q b c = true) :
    headStrict q b c = true ↔ interpretation q (headCode c) <
      RootSupportThreshold.nodeHead q (selectedCode q b c) := by
  have hhead := (RootBelowHeadCollapse.parts_accepted q c (inputCheck_guards q b c hi).2.1).1
  have hnode := RootSupportThreshold.argumentHeadCode_spec q _
    (selectedArgumentCode_accepted q b c hi)
  simpa only [headStrict, RootSupportThreshold.nodeHeadCode, RootSupportThreshold.nodeHead,
    selectedArgumentCode, ((Comparison.acceptedCode_exact q _).mp hhead).1,
    ((Comparison.acceptedCode_exact q _).mp hnode.1).1, hnode.2, true_and] using
      Normalization.lessRawCode_exact q (headCode c)
        (RootSupportThreshold.nodeHeadCode (selectedCode q b c))

def kappaCode (q b c : Nat) : Nat := cond (headStrict q b c)
  (selectedCode q b c) (firstTailCode q b c)

theorem kappaCode_primrec : Primrec
    (fun p : Query => kappaCode p.1 p.2.1 p.2.2) :=
  headStrict_primrec.cond selectedCode_primrec firstTailCode_primrec

theorem kappaCode_spec (q b c : Nat) (hi : inputCheck q b c = true) :
    Comparison.acceptedCode q (kappaCode q b c) = true ∧
      interpretation q (kappaCode q b c) < omegaSequence (base q) 1 := by
  cases hh : headStrict q b c with
  | false => simpa only [kappaCode, hh, Bool.cond_false] using
      ⟨(firstTailCode_spec q b c hi).1, (firstTailCode_spec q b c hi).2.2⟩
  | true =>
    have hs := selectedCode_spec q b c hi
    simpa only [kappaCode, hh, Bool.cond_true] using
      ⟨hs.2.2.1, (HeightBoundary.input_spec q _ hs.2.1).2.2⟩

/-- The actual finite shift realizes the genuinely selected all-tail
crossing. The original selected support derives the two branch values. -/
theorem kappaCode_value (q b c : Nat) (hi : inputCheck q b c = true) :
    interpretation q (kappaCode q b c) =
      RelativeCutoffRewrite.selectedTail q (headCode c) (selectedCode q b c) := by
  cases hh : headStrict q b c with
  | true =>
    have hl := (headStrict_exact q b c hi).mp hh
    simp only [kappaCode, hh, Bool.cond_true, RelativeCutoffRewrite.selectedTail, if_pos hl]
  | false =>
    have hn : ¬ (interpretation q (headCode c) <
        RootSupportThreshold.nodeHead q (selectedCode q b c)) := by
      intro hl
      have he := (headStrict_exact q b c hi).mpr hl
      simp only [hh, Bool.false_eq_true] at he
    have ht := firstTailCode_spec q b c hi
    have hv := (Decomposition.parts_code_value q 0 _ (selectedArgumentCode_accepted q b c hi)).2
    simpa only [kappaCode, hh, Bool.cond_false, RelativeCutoffRewrite.selectedTail,
      if_neg hn, selectedTailCode, hv, selectedArgumentCode] using ht.2.1

def insertedTailCode (q b c : Nat) : Nat := Arithmetic.addCode q (kappaCode q b c) (tailCode c)

theorem insertedTailCode_primrec : Primrec
    (fun p : Query => insertedTailCode p.1 p.2.1 p.2.2) :=
  Arithmetic.addCode_primrec.comp (Primrec.fst.pair (kappaCode_primrec.pair
    (RootBelowHeadCollapse.tailCode_primrec.comp (Primrec.snd.comp Primrec.snd))))

theorem insertedTailCode_spec (q b c : Nat) (hi : inputCheck q b c = true) :
    Comparison.acceptedCode q (insertedTailCode q b c) = true ∧
      interpretation q (insertedTailCode q b c) =
        interpretation q (kappaCode q b c) + interpretation q (tailCode c) ∧
      interpretation q (insertedTailCode q b c) < omegaSequence (base q) 1 := by
  have hk := kappaCode_spec q b c hi
  have hc := (inputCheck_guards q b c hi).2.1
  have ht := Arithmetic.addCode_spec q _ _ ((Comparison.acceptedCode_exact q _).mp hk.1).1
    ((Comparison.acceptedCode_exact q _).mp (RootBelowHeadCollapse.parts_accepted q c hc).2).1
  refine ⟨ht.1, ht.2.1, ?_⟩
  rw [show interpretation q (insertedTailCode q b c) =
    interpretation q (kappaCode q b c) + interpretation q (tailCode c) from ht.2.1]
  exact (omegaSequence_add_closed (base q) 0) hk.2 (RootAboveHeadCollapse.head_spec q c hc).2.2.2.1

def shiftedArgumentCode (q b c : Nat) : Nat := Arithmetic.addCode q (headCode c) (insertedTailCode q b c)

theorem shiftedArgumentCode_primrec : Primrec
    (fun p : Query => shiftedArgumentCode p.1 p.2.1 p.2.2) :=
  Arithmetic.addCode_primrec.comp (Primrec.fst.pair
    ((RootAboveHeadCollapse.headCode_primrec.comp (Primrec.snd.comp Primrec.snd)).pair
      insertedTailCode_primrec))

theorem shiftedArgumentCode_spec (q b c : Nat) (hi : inputCheck q b c = true) :
    Comparison.acceptedCode q (shiftedArgumentCode q b c) = true ∧
      interpretation q (shiftedArgumentCode q b c) =
        interpretation q (headCode c) +
          (interpretation q (kappaCode q b c) + interpretation q (tailCode c)) ∧
      interpretation q (shiftedArgumentCode q b c) < omegaSequence (base q) 2 := by
  have hc := (inputCheck_guards q b c hi).2.1
  have ht := insertedTailCode_spec q b c hi
  have hs := Arithmetic.addCode_spec q _ _
    ((Comparison.acceptedCode_exact q _).mp (RootBelowHeadCollapse.parts_accepted q c hc).1).1
    ((Comparison.acceptedCode_exact q _).mp ht.1).1
  refine ⟨hs.1, ?_, ?_⟩
  · simpa only [shiftedArgumentCode, ht.2.1] using hs.2.1
  · rw [show interpretation q (shiftedArgumentCode q b c) =
      interpretation q (headCode c) + interpretation q (insertedTailCode q b c) from hs.2.1]
    exact (omegaSequence_add_closed (base q) 1)
      (RootAboveHeadCollapse.head_spec q c hc).2.1 (ht.2.2.trans (omegaSequence_step (base q) 1))

/-- Every cutoff and minimum caller is derived from the ORIGINAL
computed localized guard and its genuine written head-only selection. -/
theorem relative_collapse_value (q b c : Nat) (hi : inputCheck q b c = true) :
    globalCollapse (interpretation q b) 0 (interpretation q c) =
      globalCollapse (base q) 0 (interpretation q (shiftedArgumentCode q b c)) := by
  have hc := (inputCheck_guards q b c hi).2.1
  have hp := RootAboveHeadCollapse.head_spec q c hc
  have he := RelativeCutoffRewrite.selected_relative_tail_eq q b (headCode c)
    (selectedCode q b c) (threshold_caller q b c hi) (selectedCode_some q b c hi)
    hp.2.2.1 (head_positive q b c hi) (interpretation q (tailCode c)) hp.2.2.2.1
  rw [← kappaCode_value q b c hi, hp.2.2.2.2] at he
  rw [(shiftedArgumentCode_spec q b c hi).2.1]
  exact he

def collapseCode (q b c : Nat) : Nat := cond (inputCheck q b c)
  (OmegaPowers.thetaCode (shiftedArgumentCode q b c)) 0

theorem collapseCode_primrec : Primrec
    (fun p : Query => collapseCode p.1 p.2.1 p.2.2) :=
  inputCheck_primrec.cond (OmegaPowers.thetaCode_primrec.comp shiftedArgumentCode_primrec)
    (Primrec.const 0)

/-- The actual finite source output is checked and Normal before its
relative scalar equation is proved from the genuine minima. -/
theorem collapseCode_checked (q b c : Nat) (hi : inputCheck q b c = true) :
    lowCheckCode q (collapseCode q b c) = true ∧
      Comparison.acceptedCode q (collapseCode q b c) = true ∧
      interpretation q (collapseCode q b c) =
        globalCollapse (base q) 0 (interpretation q (shiftedArgumentCode q b c)) := by
  have hs := shiftedArgumentCode_spec q b c hi
  have ht := RootEndpointCollapse.thetaCode_sorted_spec q _ hs.1 hs.2.2
  simpa only [collapseCode, hi, Bool.cond_true] using ht

/-- The constructed original-q Normal LOW output is exactly the genuine
beta-relative scalar value on the full localized branch. -/
theorem collapseCode_spec (q b c : Nat) (hi : inputCheck q b c = true) :
    lowCheckCode q (collapseCode q b c) = true ∧
      Comparison.acceptedCode q (collapseCode q b c) = true ∧
      interpretation q (collapseCode q b c) =
        globalCollapse (interpretation q b) 0 (interpretation q c) :=
  ⟨(collapseCode_checked q b c hi).1, (collapseCode_checked q b c hi).2.1,
    (collapseCode_checked q b c hi).2.2.trans (relative_collapse_value q b c hi).symm⟩

theorem collapseCode_rejected (q b c : Nat) (hi : inputCheck q b c = false) :
    collapseCode q b c = 0 := by simp only [collapseCode, hi, Bool.cond_false]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RootLocalizedCollapse
