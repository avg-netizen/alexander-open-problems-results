import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingContextAccumulationSupport

/-!
# Actual initialized contextual updates retain the original cut

A genuine reset relation can have an ordinary source spelling rather than
literal returnWord syntax. Actual lower execution derives its RAW tracker
and OWN bounds. The genuine next product constructs a complete next lower
Assignment; M-right order derives its FIRST cover at the original boundary.
The actual independent suffix dispatcher then preserves the literal prefix
and derives its next LOW, Normal and SAME-value entry relation. No next
code, next Assignment or whole-product mu cover is supplied. Actual factor traces reconstruct every original Assignment and derive
the complete retained/reset state induction. The actual terminal code is
read from the frames, preserving its spelling distinction from the prefix. Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.ContextAccumulation

open PublicEpsilonUnboundedIota SourceTrackingSequences
open Hereditary.FinePredecessor (stripLast)
open InsertionFidelitySupport (stripLast_append_nonempty)
open Hereditary.SourceAdditiveTrackingWordBounds (lastCode_append_nonempty)
open ReplacementFidelity (SameEntry)
open Alexander313.Wilken.MultiplicativeNormalForm MultiplicativePrincipalArithmetic

private theorem relation_checked {q r : Nat} {xs ys : List Nat}
    (hr : List.Forall₂ (SameEntry q r) xs ys) :
    ∀ d ∈ ys, lowCheckCode q d = true ∧ Comparison.acceptedCode q d = true := by
  induction hr with
  | nil => intro d hd; exact False.elim (List.not_mem_nil hd)
  | @cons c d xs ys he ht ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨he.1, he.2.1⟩
    · exact ih a ha

private theorem relation_of_values (q r : Nat) (xs ys : List Nat)
    (hv : ys.map (interpretation q) = xs.map (interpretation r))
    (ha : ∀ d ∈ ys, lowCheckCode q d = true ∧ Comparison.acceptedCode q d = true) :
    List.Forall₂ (SameEntry q r) xs ys := by
  induction xs generalizing ys with
  | nil =>
    have he : ys = [] := by simpa only [List.map_nil, List.map_eq_nil_iff] using hv
    subst ys
    exact .nil
  | cons c cs ih =>
    cases ys with
    | nil => simp only [List.map_nil, List.map_cons, List.nil_ne_cons] at hv
    | cons d ds =>
      have he := List.cons.inj hv
      exact .cons ⟨(ha d List.mem_cons_self).1, (ha d List.mem_cons_self).2, he.1⟩
        (ih ds he.2 (fun a hm => ha a (List.mem_cons_of_mem _ hm)))

private theorem branches_checked (q factor : Nat) (heads out : List Nat)
    (hh : SourceTrackingRaw.trackingCheck q heads = true)
    (hf : lowCheckCode q factor = true ∧ Comparison.acceptedCode q factor = true)
    (hm : IsMultiplicativePrincipal (interpretation q factor))
    (hb : interpretation q factor ≤ interpretation q (lastCode heads))
    (hc : ∀ d ∈ heads, lowCheckCode q d = true ∧ Comparison.acceptedCode q d = true)
    (ho : out ∈ Branches.execute ((q, factor), heads)) :
    ∀ d ∈ out, lowCheckCode q d = true ∧ Comparison.acceptedCode q d = true := by
  rcases Branches.execute_branch q factor heads out ho with ⟨hflag, he⟩ | ⟨hflag, hi⟩
  · intro d hd
    rw [he] at hd
    rcases List.mem_append.mp hd with hd | hd
    · exact hc d hd
    · simpa only [List.mem_singleton.mp hd] using hf
  · obtain ⟨rows, hr, hheads, hout, hchecked, hcases⟩ :=
      Insertion.execute_spec q factor heads out hh hf.1 hm hb hi
    rcases hcases with ⟨first, rest, hrows, he, hn⟩ |
      ⟨before, current, after, hne, hrows, he, hcover, hn⟩
    · intro d hd
      exact (hchecked first (by rw [hrows]; exact List.mem_cons_self)).2 d
        (by simpa only [he] using hd)
    · intro d hd
      rw [he] at hd
      rcases List.mem_append.mp hd with hd | hd
      · apply hc d
        rw [← hheads, hrows, List.map_append]
        exact List.mem_append_left _ hd
      · exact (hchecked current (by
          rw [hrows]
          exact List.mem_append_right _ List.mem_cons_self)).2 d hd

/-- This local operational consumer strengthens the existing FIRST-cut
VALUES theorem to the literal suffix and its complete next entry relation. -/
private theorem related_first_cut (q alpha input factor otherFactor : Nat)
    (before heads suffix word out : List Nat)
    (ha : RootLowCollapse.rootCheck q alpha = true)
    (ho : heads ∈ Assignment.execute (betaCode q alpha) input)
    (hstrict : base (betaCode q alpha) < interpretation (betaCode q alpha) input)
    (hown : interpretation (betaCode q alpha) input < Enclosure.sourceAlphaPlus q alpha)
    (hrel : List.Forall₂ (SameEntry q (betaCode q alpha)) heads suffix)
    (hne : before ≠ [])
    (hh : SourceTrackingRaw.trackingCheck q (before ++ suffix) = true)
    (hbefore : interpretation q (lastCode before) ≤ base (betaCode q alpha))
    (hf : lowCheckCode (betaCode q alpha) factor = true)
    (hd : SameEntry q (betaCode q alpha) factor otherFactor)
    (hm : IsMultiplicativePrincipal (interpretation (betaCode q alpha) factor))
    (hone : 1 < interpretation (betaCode q alpha) factor)
    (hb : interpretation (betaCode q alpha) factor ≤
      interpretation (betaCode q alpha) (lastCode heads))
    (hcover : interpretation (betaCode q alpha) (Insertion.firstCode word) ≤
      SourceTrackingRaw.Support.muValue q (lastCode before))
    (hw : word ∈ Branches.execute (((betaCode q alpha), factor), heads))
    (hu : out ∈ Branches.execute ((q, otherFactor), before ++ suffix)) :
    ∃ nextSuffix, out = before ++ nextSuffix ∧
      nextSuffix ∈ Branches.execute ((q, otherFactor), suffix) ∧
      List.Forall₂ (SameEntry q (betaCode q alpha)) word nextSuffix := by
  have hall := (Assignment.execute_spec _ input heads ho).2.1.2.1
  have htarget := ContextAssignmentReturn.raw_tracking_return q alpha ha heads suffix
    (Assignment.execute_tracking _ input heads ho) hrel (fun c hc => (hall c hc).trans_lt hown)
  have hsuffixNe := ((SourceTrackingRaw.trackingCheck_conditions q suffix).mp htarget).1
  have hlast := Hereditary.SourceAdditiveTrackingWordBounds.lastCode_values_eq
    (interpretation q) (interpretation (betaCode q alpha)) suffix heads hsuffixNe
      (ContextRowValues.returned_values hrel)
  have hm' : IsMultiplicativePrincipal (interpretation q otherFactor) := by
    rw [hd.2.2]; exact hm
  have hb' : interpretation q otherFactor ≤ interpretation q (lastCode suffix) := by
    rw [hd.2.2, hlast]; exact hb
  obtain ⟨nextSuffix, hn⟩ := Branches.execute_returns q otherFactor suffix htarget hd.1 hm' hb'
  have hv := ContextBranchValues.branches_values_eq q alpha input factor otherFactor
    heads suffix word nextSuffix ha ho hstrict hown hrel hf hd hm hb hw hn
  have ht := Branches.execute_tracking q otherFactor suffix nextSuffix htarget hd.1 hm'
    (by simpa only [hd.2.2] using hone) hb' hn
  have ht' := (SourceTrackingRaw.trackingCheck_conditions q nextSuffix).mp ht
  have hlow := AssignmentValueSupport.firstCode_low q nextSuffix ht'.1
    (fun c hc => (ConditionalReplacement.tracking_member_principal q nextSuffix ht c hc).1)
  have hfirst : interpretation q (Insertion.firstCode nextSuffix) =
      interpretation (betaCode q alpha) (Insertion.firstCode word) := by
    cases nextSuffix with
    | nil => exact False.elim (ht'.1 rfl)
    | cons a as =>
      cases word with
      | nil => simp only [List.map_cons, List.map_nil, List.cons_ne_nil] at hv
      | cons b bs =>
        simpa only [Insertion.firstCode, List.head?_cons, Option.getD_some] using (List.cons.inj hv).1
  have hraw : SourceTrackingRaw.Support.inputCheck q (lastCode before) = true := by
    apply ((SourceTrackingRaw.trackingCheck_conditions q (before ++ suffix)).mp hh).2.1.nodes
    rw [stripLast_append_nonempty before suffix hsuffixNe]
    exact List.mem_append_left _ (lastCode_mem before hne)
  obtain ⟨first, rest, hheads⟩ := List.exists_cons_of_ne_nil (Assignment.execute_nonempty _ input heads ho)
  have hr := hrel
  rw [hheads] at hr
  obtain ⟨other, otherRest, hentry, htail, hsuffix⟩ := List.forall₂_cons_left_iff.mp hr
  have hfront : interpretation q (lastCode before) < interpretation q other := by
    rw [hentry.2.2]
    exact hbefore.trans_lt (AssignmentFirst.execute_first_gt_base _ input first rest
      (by simpa only [hheads] using ho) hstrict)
  have hcut := ContextFirstCutSupport.branches_first_cut q otherFactor before other otherRest out nextSuffix
    hne (by simpa only [hsuffix] using hh) (by simpa only [hsuffix] using htarget)
    hfront hraw hlow (by rw [hfirst]; exact hcover)
    (by simpa only [hsuffix] using hu) (by simpa only [hsuffix] using hn)
  exact ⟨nextSuffix, hcut, hn, relation_of_values _ _ word nextSuffix hv
    (branches_checked q otherFactor suffix nextSuffix htarget ⟨hd.1, hd.2.1⟩ hm' hb'
      (relation_checked hrel) hn)⟩

/-- Actual current lower provenance and real whole branch execution
construct the next Assignment, LF and complete literal retained relation.
The actual fixed greater raised FIRST supplies its cover by derived order. -/
theorem initialized_update (q : Nat) (original : List Nat) (head greater input factor : Nat)
    (before heads suffix ys out : List Nat)
    (hw : SourceTrackingRaw.trackingCheck q original = true) (hh : head ∈ stripLast original)
    (hg : lowCheckCode q greater = true) (hmg : IsMultiplicativePrincipal (interpretation q greater))
    (hhead : interpretation q head < interpretation q greater)
    (hgreater : interpretation q greater ≤ interpretation q (lastCode original))
    (hy : ys ∈ Replacement.raisedReplacement q head greater)
    (hcover : Insertion.coverCheck q (lastCode before) (Insertion.firstCode ys) = true)
    (ho : heads ∈ Assignment.execute (ReplacementSupport.raisedBaseCode q head) input)
    (hstrict : base (ReplacementSupport.raisedBaseCode q head) <
      interpretation (ReplacementSupport.raisedBaseCode q head) input)
    (hinput : interpretation (ReplacementSupport.raisedBaseCode q head) input < interpretation q greater)
    (hrel : List.Forall₂ (SameEntry q (ReplacementSupport.raisedBaseCode q head)) heads suffix)
    (hne : before ≠ []) (hfull : SourceTrackingRaw.trackingCheck q (before ++ suffix) = true)
    (hbefore : interpretation q (lastCode before) ≤ interpretation q head)
    (hf : lowCheckCode q factor = true ∧ Comparison.acceptedCode q factor = true)
    (hm : IsMultiplicativePrincipal (interpretation q factor)) (hone : 1 < interpretation q factor)
    (hsmall : interpretation q factor < interpretation q greater)
    (hcut : interpretation q factor ≤ lf (interpretation (ReplacementSupport.raisedBaseCode q head) input))
    (hu : out ∈ Branches.execute ((q, factor), before ++ suffix)) :
    ∃ next nextHeads nextSuffix, out = before ++ nextSuffix ∧
      interpretation (ReplacementSupport.raisedBaseCode q head) next =
        interpretation (ReplacementSupport.raisedBaseCode q head) input * interpretation q factor ∧
      base (ReplacementSupport.raisedBaseCode q head) < interpretation (ReplacementSupport.raisedBaseCode q head) next ∧
      interpretation (ReplacementSupport.raisedBaseCode q head) next < interpretation q greater ∧
      nextHeads ∈ Assignment.execute (ReplacementSupport.raisedBaseCode q head) next ∧
      lf (interpretation (ReplacementSupport.raisedBaseCode q head) next) = interpretation q factor ∧
      List.Forall₂ (SameEntry q (ReplacementSupport.raisedBaseCode q head)) nextHeads nextSuffix := by
  have hraw := ((SourceTrackingRaw.trackingCheck_conditions q original).mp hw).2.1.nodes head hh
  have hroot := (SourceTrackingRaw.Support.rootCode_spec q head hraw).2.1
  have he := ReplacementFidelity.raisedBase_eq_betaCode q head hraw
  have hbase := (ReplacementSupport.raisedBaseCode_spec q head hraw).2.1
  have hproperNe : stripLast original ≠ [] := by intro hn; rw [hn] at hh; exact List.not_mem_nil hh
  have hown := hinput.le.trans_lt (hgreater.trans_lt
    (EndpointSupport.tracking_final_lt_endpoints q original hw hproperNe head hh))
  obtain ⟨otherFactor, hsearch⟩ := ReplacementSupport.raisedSearch_returns q head factor hraw hf.1
  have hs := ReplacementSupport.raisedSearch_spec q head factor otherFactor hraw hf.1 hsearch
  have hd : SameEntry q (ReplacementSupport.raisedBaseCode q head) otherFactor factor :=
    ⟨hf.1, hf.2, hs.2.2.symm⟩
  have hm' : IsMultiplicativePrincipal (interpretation (ReplacementSupport.raisedBaseCode q head) otherFactor) := by
    rw [hs.2.2]; exact hm
  have hone' : 1 < interpretation (ReplacementSupport.raisedBaseCode q head) otherFactor := by
    rw [hs.2.2]; exact hone
  have hcut' : interpretation (ReplacementSupport.raisedBaseCode q head) otherFactor ≤
      lf (interpretation (ReplacementSupport.raisedBaseCode q head) input) := by
    rw [hs.2.2]; exact hcut
  have hlast := hcut'.trans (Assignment.execute_last_bounds _ input heads ho).1
  obtain ⟨updateWord, hupdate⟩ := Branches.execute_returns _ otherFactor heads
    (Assignment.execute_tracking _ input heads ho) hs.1 hm' hlast
  obtain ⟨next, nextHeads, hproduct, hnextLow, hnextAccepted, hvalue, hnextStrict,
    hnext, hvalues, hlf⟩ := FactorUpdateExecution.product_update_returns _ input otherFactor heads updateWord
      ho hs.1 hm' hone' hstrict hcut' hupdate
  have hnextSmall : interpretation (ReplacementSupport.raisedBaseCode q head) next < interpretation q greater := by
    rw [hvalue, hs.2.2]
    exact hmg.2.2 hinput hsmall
  have hfirst := ContextAccumulationSupport.assignment_first_le_raised q head greater next nextHeads ys
    hraw hg hmg hhead hnext hnextSmall hy
  have hnextCover : interpretation (ReplacementSupport.raisedBaseCode q head) (Insertion.firstCode updateWord) ≤
      SourceTrackingRaw.Support.muValue q (lastCode before) := by
    rw [AssignmentValueSupport.firstCode_values_eq _ updateWord nextHeads hvalues]
    exact hfirst.trans ((Insertion.coverCheck_exact q _ _).mp hcover).2.2
  have hbefore' : interpretation q (lastCode before) ≤ base (ReplacementSupport.raisedBaseCode q head) := by
    rw [hbase]; exact hbefore
  obtain ⟨nextSuffix, hout, hbranch, hnextRel⟩ := related_first_cut q
    (SourceTrackingRaw.Support.rootCode q head) input otherFactor factor before heads suffix updateWord out
    hroot (by simpa only [he] using ho) (by simpa only [he] using hstrict)
    (by simpa only [he] using hown) (by simpa only [he] using hrel) hne hfull
    (by simpa only [he] using hbefore')
    (by simpa only [he] using hs.1) (by simpa only [he] using hd)
    (by simpa only [he] using hm') (by simpa only [he] using hone')
    (by simpa only [he] using hlast) (by simpa only [he] using hnextCover)
    (by simpa only [he] using hupdate) hu
  have hreturnedValues : nextSuffix.map (interpretation q) =
      updateWord.map (interpretation (ReplacementSupport.raisedBaseCode q head)) := by
    simpa only [he] using ContextRowValues.returned_values hnextRel
  have hrel' : List.Forall₂ (SameEntry q (ReplacementSupport.raisedBaseCode q head)) nextHeads nextSuffix :=
    relation_of_values _ _ nextHeads nextSuffix
      (hreturnedValues.trans hvalues)
      (relation_checked hnextRel)
  exact ⟨next, nextHeads, nextSuffix, hout, by simpa only [hs.2.2] using hvalue,
    hnextStrict, hnextSmall, hnext, by simpa only [hs.2.2] using hlf, hrel'⟩

private theorem reference_suffix (q : Nat) (before suffix : List Nat)
    (hr : SourceTrackingRaw.Reference q (before ++ suffix)) : SourceTrackingRaw.Reference q suffix := by
  revert hr
  induction before with
  | nil => intro hr; exact hr
  | cons a before ih =>
    intro hr
    exact ih (InsertionFidelitySupport.reference_tail q a (before ++ suffix) hr)

/-- The genuine retained RAW head supplies the singleton suffix floor;
positivity alone would not supply the native base bound. -/
private theorem retained_tracking_suffix (q : Nat) (before : List Nat) (head : Nat) (after : List Nat)
    (hhead : SourceTrackingRaw.Support.inputCheck q head = true)
    (hh : SourceTrackingRaw.trackingCheck q (before ++ head :: after) = true) :
    SourceTrackingRaw.trackingCheck q (head :: after) = true := by
  have hs := (SourceTrackingRaw.trackingCheck_conditions q _).mp hh
  have hp := stripLast_append_nonempty before (head :: after) (List.cons_ne_nil _ _)
  have hl := lastCode_append_nonempty before (head :: after) (List.cons_ne_nil _ _)
  have href : SourceTrackingRaw.Reference q (stripLast (head :: after)) :=
    reference_suffix q before _ (by simpa only [hp] using hs.2.1)
  apply (SourceTrackingRaw.trackingCheck_conditions q _).mpr
  refine ⟨List.cons_ne_nil _ _, href, ?_, ?_, ?_, ?_⟩
  · simpa only [hl] using hs.2.2.1
  · simpa only [hl] using hs.2.2.2.1
  · simpa only [hl] using hs.2.2.2.2.1
  · cases after with
    | nil =>
      simpa only [stripLast_singleton, if_pos rfl, lastCode_singleton] using
        ((SourceTrackingRaw.Support.inputCheck_exact q head).mp hhead).2.1.le
    | cons a after =>
      have hn : stripLast (head :: a :: after) ≠ [] := by
        rw [SkTracking.Support.stripLast_cons_nonempty head (a :: after) (List.cons_ne_nil _ _)]
        exact List.cons_ne_nil _ _
      have hwhole : stripLast (before ++ head :: a :: after) ≠ [] := by
        rw [hp]
        intro he
        exact hn (List.append_eq_nil_iff.mp he).2
      have hb := hs.2.2.2.2.2
      rw [if_neg hwhole, hp, hl, lastCode_append_nonempty before _ hn] at hb
      simpa only [if_neg hn] using hb

private theorem word_some_head (q : Nat) (first : InsertionSupport.Row) (rest : List InsertionSupport.Row)
    (selected : Insertion.Candidate) (hs : Insertion.choose q (first :: rest) = some selected) :
    ∃ after, Insertion.word q (first :: rest) = first.1 :: after := by
  cases rest with
  | nil => simp only [Insertion.choose_singleton, Option.none_ne_some] at hs
  | cons current later =>
    cases ht : Insertion.choose q (current :: later) with
    | some chosen =>
      exact ⟨Insertion.word q (current :: later),
        SmallInsertionIntervalOrderSupport.word_cons_some q first _ chosen ht⟩
    | none =>
      cases hc : Insertion.coverCheck q first.1 (Insertion.firstCode current.2) with
      | false =>
        simp only [Insertion.choose_pair, ht, hc, Bool.cond_false, Option.none_ne_some] at hs
      | true =>
        refine ⟨current.2, ?_⟩
        simp only [Insertion.word, Insertion.choose_pair, ht, hc, Bool.cond_true,
          List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.singleton_append]

/-- An arbitrary retained old suffix is never treated as a lower Assignment.
The actual NONE reset alone derives lower provenance and its processed LF. -/
theorem uninitialized_update (q : Nat) (original : List Nat) (head greater factor : Nat)
    (before after ys out : List Nat)
    (hw : SourceTrackingRaw.trackingCheck q original = true) (hh : head ∈ stripLast original)
    (hne : before ≠ []) (hfull : SourceTrackingRaw.trackingCheck q (before ++ head :: after) = true)
    (hfront : interpretation q (lastCode before) < interpretation q head)
    (hf : lowCheckCode q factor = true ∧ Comparison.acceptedCode q factor = true)
    (hm : IsMultiplicativePrincipal (interpretation q factor)) (hone : 1 < interpretation q factor)
    (hb : interpretation q factor ≤ interpretation q (lastCode (before ++ head :: after)))
    (hg : lowCheckCode q greater = true) (hmg : IsMultiplicativePrincipal (interpretation q greater))
    (hhead : interpretation q head < interpretation q greater)
    (hsmall : interpretation q factor < interpretation q greater)
    (hy : ys ∈ Replacement.raisedReplacement q head greater)
    (hcover : Insertion.coverCheck q (lastCode before) (Insertion.firstCode ys) = true)
    (ho : out ∈ Branches.execute ((q, factor), before ++ head :: after)) :
    ∃ suffix, out = before ++ suffix ∧
      ((∃ nextAfter, suffix = head :: nextAfter) ∨
        ∃ input heads,
          interpretation (ReplacementSupport.raisedBaseCode q head) input =
            interpretation q head * interpretation q factor ∧
          base (ReplacementSupport.raisedBaseCode q head) <
            interpretation (ReplacementSupport.raisedBaseCode q head) input ∧
          interpretation (ReplacementSupport.raisedBaseCode q head) input < interpretation q greater ∧
          heads ∈ Assignment.execute (ReplacementSupport.raisedBaseCode q head) input ∧
          lf (interpretation (ReplacementSupport.raisedBaseCode q head) input) = interpretation q factor ∧
          List.Forall₂ (SameEntry q (ReplacementSupport.raisedBaseCode q head)) heads suffix) := by
  have hraw := ((SourceTrackingRaw.trackingCheck_conditions q original).mp hw).2.1.nodes head hh
  have ht := retained_tracking_suffix q before head after hraw hfull
  have hb' : interpretation q factor ≤ interpretation q (lastCode (head :: after)) := by
    simpa only [lastCode_append_nonempty before (head :: after) (List.cons_ne_nil _ _)] using hb
  obtain ⟨suffix, hs⟩ := Branches.execute_returns q factor (head :: after) ht hf.1 hm hb'
  have htracker := Branches.execute_tracking q factor (head :: after) suffix ht hf.1 hm hone hb' hs
  have hneSuffix := ((SourceTrackingRaw.trackingCheck_conditions q suffix).mp htracker).1
  have hlow := AssignmentValueSupport.firstCode_low q suffix hneSuffix
    (fun c hc => (ConditionalReplacement.tracking_member_principal q suffix htracker c hc).1)
  have hprefixRaw : SourceTrackingRaw.Support.inputCheck q (lastCode before) = true := by
    apply ((SourceTrackingRaw.trackingCheck_conditions q _).mp hfull).2.1.nodes
    rw [stripLast_append_nonempty before (head :: after) (List.cons_ne_nil _ _)]
    exact List.mem_append_left _ (lastCode_mem before hne)
  have hcut (hpass : Insertion.coverCheck q (lastCode before) (Insertion.firstCode suffix) = true) :
      out = before ++ suffix :=
    ContextFirstCutSupport.branches_first_cut q factor before head after out suffix hne hfull ht
      hfront hprefixRaw hlow ((Insertion.coverCheck_exact q _ _).mp hpass).2.2 ho hs
  have hc : Insertion.coverCheck q (lastCode before) head = true :=
    (Insertion.coverCheck_exact q _ _).mpr ⟨hprefixRaw,
      ((SourceTrackingRaw.Support.inputCheck_exact q head).mp hraw).1,
      by simpa only [lastCode_append_singleton] using
        LocalizationSupport.tracking_cut_cover q (before ++ head :: after) before head after
          hfull rfl hne⟩
  rcases Branches.execute_branch q factor (head :: after) suffix hs with ⟨hflag, he⟩ | ⟨hflag, hi⟩
  · have hshead : suffix = head :: (after ++ [factor]) := by
      simpa only [List.cons_append] using he
    have hpass : Insertion.coverCheck q (lastCode before) (Insertion.firstCode suffix) = true := by
      simpa only [hshead, Insertion.firstCode, List.head?_cons, Option.getD_some] using hc
    exact ⟨suffix, hcut hpass, Or.inl ⟨after ++ [factor], hshead⟩⟩
  · obtain ⟨rows, hr, he⟩ := (Part.mem_map_iff (Insertion.word q)).mp hi
    have hrelation := InsertionSupport.executeRows_relation q factor (head :: after) rows hr
    obtain ⟨row, rest, hrow, hrest, hrows⟩ := List.forall₂_cons_left_iff.mp hrelation
    cases hchoice : Insertion.choose q rows with
    | some selected =>
      obtain ⟨nextAfter, hwhead⟩ := word_some_head q row rest selected
        (by simpa only [hrows] using hchoice)
      have hwhead' : Insertion.word q rows = head :: nextAfter := by
        simpa only [hrows, hrow.1] using hwhead
      have hshead : suffix = head :: nextAfter := he.symm.trans hwhead'
      have hpass : Insertion.coverCheck q (lastCode before) (Insertion.firstCode suffix) = true := by
        simpa only [hshead, Insertion.firstCode, List.head?_cons, Option.getD_some] using hc
      exact ⟨suffix, hcut hpass, Or.inl ⟨nextAfter, hshead⟩⟩
    | none =>
      have hcond : row.2 ∈ ConditionalReplacement.execute q head factor := by
        simpa only [hrow.1] using hrow.2
      have hsrow : suffix = row.2 := by
        simp only [← he, Insertion.word, hchoice, hrows, List.head?_cons, Option.getD_some]
      obtain ⟨input, heads, hv, ht, ha, hl, hrel⟩ :=
        ContextAccumulationSupport.reset_assignment_last q head factor row.2 hraw hf.1 hm hone hcond
      have hbelow : interpretation (ReplacementSupport.raisedBaseCode q head) input < interpretation q greater :=
        hv.trans_lt (hmg.2.2 hhead hsmall)
      have hfirst := ContextAccumulationSupport.assignment_first_le_raised q head greater input heads ys
        hraw hg hmg hhead ha hbelow hy
      have hvalues := ContextRowValues.returned_values hrel
      have hfirstRow : interpretation q (Insertion.firstCode row.2) =
          interpretation (ReplacementSupport.raisedBaseCode q head) (Insertion.firstCode heads) := by
        cases hroweq : row.2 with
        | nil =>
          have hn : heads = [] := by
            simpa only [hroweq, List.map_nil, List.map_eq_nil_iff] using hvalues.symm
          exact False.elim (Assignment.execute_nonempty _ input heads ha hn)
        | cons a as =>
          cases hheads : heads with
          | nil => exact False.elim (Assignment.execute_nonempty _ input heads ha hheads)
          | cons b bs =>
            have hi : interpretation q a :: as.map (interpretation q) =
                interpretation (ReplacementSupport.raisedBaseCode q head) b ::
                  bs.map (interpretation (ReplacementSupport.raisedBaseCode q head)) := by
              simpa only [hroweq, hheads, List.map_cons] using hvalues
            simpa only [hroweq, hheads, Insertion.firstCode, List.head?_cons, Option.getD_some] using
              (List.cons.inj hi).1
      have hpass : Insertion.coverCheck q (lastCode before) (Insertion.firstCode suffix) = true := by
        apply (Insertion.coverCheck_exact q _ _).mpr
        refine ⟨hprefixRaw, hlow, ?_⟩
        rw [hsrow, hfirstRow]
        exact hfirst.trans ((Insertion.coverCheck_exact q _ _).mp hcover).2.2
      refine ⟨suffix, hcut hpass, Or.inr ⟨input, heads, hv, ht, hbelow, ha, hl, ?_⟩⟩
      simpa only [hsrow] using hrel

/-- This code is read from the actual written factor frames. It is not
identified with the original prefix code merely from equal values. -/
def terminalCode (current : Nat) : List IntervalFrames.Frame → Nat
  | [] => current
  | frame :: frames => terminalCode frame.2.1 frames

theorem segment_terminal_value {q target bound current : Nat} {frames : List IntervalFrames.Frame}
    (hs : IntervalFrames.Segment q target bound current frames) :
    interpretation q (terminalCode current frames) = interpretation q target := by
  induction hs with
  | nil terminal hv => exact hv
  | cons current child factor frames hf hsmall ht ih => exact ih

/-- The independent complete execution derives the actual terminal
Assignment and all actual reverse branches at that exact terminal code. -/
theorem segment_execute_bottom {q target bound current : Nat} {frames : List IntervalFrames.Frame}
    (hs : IntervalFrames.Segment q target bound current frames) (out : List Nat)
    (ho : out ∈ Assignment.execute q current) :
    ∃ heads, heads ∈ Assignment.execute q (terminalCode current frames) ∧
      IntervalFrames.Unwind q frames heads out := by
  induction hs generalizing out with
  | nil terminal hv => exact ⟨out, ho, .nil out⟩
  | cons current child factor frames hf hsmall ht ih =>
    obtain ⟨middle, hm, hb⟩ := IntervalFactors.actual_factor_child q current child factor out hf ho
    obtain ⟨heads, hh, hu⟩ := ih middle hm
    exact ⟨heads, hh, .cons current child factor frames heads middle out hu hb⟩

/-- The arbitrary retained suffix and actual initialized lower Assignment
are separate states. The LF is the LF of the actual current input. -/
def State (q head greater current : Nat) (suffix : List Nat) : Prop :=
  (∃ after, suffix = head :: after) ∨
    ∃ input heads,
      base (ReplacementSupport.raisedBaseCode q head) <
        interpretation (ReplacementSupport.raisedBaseCode q head) input ∧
      interpretation (ReplacementSupport.raisedBaseCode q head) input < interpretation q greater ∧
      heads ∈ Assignment.execute (ReplacementSupport.raisedBaseCode q head) input ∧
      lf (interpretation (ReplacementSupport.raisedBaseCode q head) input) = lf (interpretation q current) ∧
      List.Forall₂ (SameEntry q (ReplacementSupport.raisedBaseCode q head)) heads suffix

/-- Actual Factor/Unwind observations reconstruct every current complete
Assignment and derive every retained/reset state. The actual bottom code
is read from the frames, preserving the native spelling distinction. -/
theorem unwind_states {q target greater current : Nat} {frames : List IntervalFrames.Frame}
    (hs : IntervalFrames.Segment q target greater current frames)
    (original out before : List Nat) (head : Nat) (ys : List Nat)
    (hw : SourceTrackingRaw.trackingCheck q original = true) (hh : head ∈ stripLast original)
    (hne : before ≠ []) (hfront : interpretation q (lastCode before) < interpretation q head)
    (hg : lowCheckCode q greater = true) (hm : IsMultiplicativePrincipal (interpretation q greater))
    (hhead : interpretation q head < interpretation q greater)
    (hgreater : interpretation q greater ≤ interpretation q (lastCode original))
    (hy : ys ∈ Replacement.raisedReplacement q head greater)
    (hcover : Insertion.coverCheck q (lastCode before) (Insertion.firstCode ys) = true)
    (hstart : ∃ after, original = before ++ head :: after) :
    original ∈ Assignment.execute q (terminalCode current frames) →
    IntervalFrames.Unwind q frames original out →
    out ∈ Assignment.execute q current ∧
      ∃ suffix, out = before ++ suffix ∧ State q head greater current suffix := by
  induction hs generalizing out with
  | nil terminal hv =>
    intro hbottom hu
    cases hu
    obtain ⟨after, he⟩ := hstart
    exact ⟨hbottom, head :: after, he, Or.inl ⟨after, rfl⟩⟩
  | cons current child factor frames hf hsmall ht ih =>
    intro hbottom hu
    cases hu with
    | cons current child factor frames original middle out htail hbranch =>
      obtain ⟨hchild, suffix, hmiddle, hstate⟩ := ih middle hbottom htail
      have hcurrent := Assignment.execute_factor q current child factor middle out hf hchild hbranch
      have hfull : SourceTrackingRaw.trackingCheck q (before ++ suffix) = true := by
        simpa only [hmiddle] using Assignment.execute_tracking q child middle hchild
      obtain ⟨hcaller, hpLow, hpAccepted, hfLow, hfAccepted, hpCaller, hpFloor, hpLess,
        hM, hone, hproduct, hlf, hcount⟩ := Factor.execute_spec q current (child, factor) hf
      have hcut := Factor.Bounds.execute_last_le_prefix_last q current (child, factor) hf
      have hlast := hcut.trans (Assignment.execute_last_bounds q child middle hchild).1
      rcases hstate with ⟨after, he⟩ | ⟨input, heads, hstrict, hinput, ho, hlastFactor, hrel⟩
      · obtain ⟨nextSuffix, hout, hnext⟩ := uninitialized_update q original head greater factor
          before after ys out hw hh hne (by simpa only [he] using hfull) hfront
          ⟨hfLow, hfAccepted⟩ hM hone (by simpa only [hmiddle, he] using hlast)
          hg hm hhead hsmall hy hcover (by simpa only [hmiddle, he] using hbranch)
        refine ⟨hcurrent, nextSuffix, hout, ?_⟩
        rcases hnext with hn | ⟨next, nextHeads, hv, hs, hb, ha, hl, hr⟩
        · exact Or.inl hn
        · exact Or.inr ⟨next, nextHeads, hs, hb, ha, hl.trans hlf, hr⟩
      · have hcut' : interpretation q factor ≤
          lf (interpretation (ReplacementSupport.raisedBaseCode q head) input) := by
          rw [hlastFactor]
          exact hcut
        obtain ⟨next, nextHeads, nextSuffix, hout, hv, hs, hb, ha, hl, hr⟩ := initialized_update
          q original head greater input factor before heads suffix ys out hw hh hg hm hhead
          hgreater hy hcover ho hstrict hinput hrel hne hfull hfront.le
          ⟨hfLow, hfAccepted⟩ hM hone hsmall hcut' (by simpa only [hmiddle] using hbranch)
        exact ⟨hcurrent, nextSuffix, hout, Or.inr ⟨next, nextHeads, hs, hb, ha, hl.trans hlf, hr⟩⟩

private theorem assignment_lex_raised (q head greater input : Nat) (heads suffix ys : List Nat)
    (hh : SourceTrackingRaw.Support.inputCheck q head = true) (hg : lowCheckCode q greater = true)
    (hm : IsMultiplicativePrincipal (interpretation q greater))
    (hhead : interpretation q head < interpretation q greater)
    (ho : heads ∈ Assignment.execute (ReplacementSupport.raisedBaseCode q head) input)
    (hlt : interpretation (ReplacementSupport.raisedBaseCode q head) input < interpretation q greater)
    (hr : List.Forall₂ (SameEntry q (ReplacementSupport.raisedBaseCode q head)) heads suffix)
    (hy : ys ∈ Replacement.raisedReplacement q head greater) :
    List.Lex (· < ·) (suffix.map (interpretation q)) (ys.map (interpretation q)) := by
  obtain ⟨rightWord, hw, ht, hv, hlen, hchecked⟩ :=
    Replacement.raisedReplacement_spec q head greater ys hh hg hm hhead hy
  obtain ⟨right, hs, hword⟩ := (Part.mem_map_iff _).mp hw
  have hi := ReplacementSupport.raisedSearch_multiplicative q head greater right hh hg hm hhead hs
  have hs' := ReplacementSupport.raisedSearch_spec q head greater right hh hg hs
  have har : rightWord ∈ Assignment.execute (ReplacementSupport.raisedBaseCode q head) right := by
    rw [← hword]
    exact Assignment.execute_multiplicative _ right hi
  rw [ContextRowValues.returned_values hr, hv]
  exact AssignmentCoverPrefix.execute_right_multiplicative_lex _ input right heads rightWord hi
    (by rw [hs'.2.2]; exact hlt) ho har

/-- The actual complete unwind compares to the fixed executing greater
raised row while retaining its original literal preceding word. -/
theorem unwind_lex {q target greater current : Nat} {frames : List IntervalFrames.Frame}
    (hs : IntervalFrames.Segment q target greater current frames)
    (original out before : List Nat) (head : Nat) (ys : List Nat)
    (hbottom : original ∈ Assignment.execute q (terminalCode current frames))
    (hw : SourceTrackingRaw.trackingCheck q original = true) (hh : head ∈ stripLast original)
    (hne : before ≠ []) (hfront : interpretation q (lastCode before) < interpretation q head)
    (hg : lowCheckCode q greater = true) (hm : IsMultiplicativePrincipal (interpretation q greater))
    (hhead : interpretation q head < interpretation q greater)
    (hgreater : interpretation q greater ≤ interpretation q (lastCode original))
    (hy : ys ∈ Replacement.raisedReplacement q head greater)
    (hcover : Insertion.coverCheck q (lastCode before) (Insertion.firstCode ys) = true)
    (hstart : ∃ after, original = before ++ head :: after)
    (hu : IntervalFrames.Unwind q frames original out) :
    List.Lex (· < ·) (out.map (interpretation q)) ((before ++ ys).map (interpretation q)) := by
  obtain ⟨ha, suffix, he, hsuffix⟩ := unwind_states hs original out before head ys
    hw hh hne hfront hg hm hhead hgreater hy hcover hstart hbottom hu
  have hraw := ((SourceTrackingRaw.trackingCheck_conditions q original).mp hw).2.1.nodes head hh
  have hlex : List.Lex (· < ·) (suffix.map (interpretation q)) (ys.map (interpretation q)) := by
    rcases hsuffix with ⟨after, hafter⟩ | ⟨input, heads, hstrict, hinput, ho, hl, hrel⟩
    · have hneYs : ys ≠ [] := by
        obtain ⟨rightWord, hr, ht, hv, hlen, hchecked⟩ :=
          Replacement.raisedReplacement_spec q head greater ys hraw hg hm hhead hy
        intro hn
        have hl := hlen
        rw [hn, List.length_nil] at hl
        exact ((SourceTrackingSequences.trackingCheck_exact _ rightWord).mp ht).1
          (List.length_eq_zero_iff.mp hl.symm)
      obtain ⟨first, rest, hys⟩ := List.exists_cons_of_ne_nil hneYs
      have hl : interpretation q head < interpretation q first :=
        FrameOrderSupport.raised_replacement_member_gt_head q head greater ys hraw hg hm hhead hy first
          (by rw [hys]; exact List.mem_cons_self)
      simpa only [hafter, hys, List.map_cons] using
        (List.Lex.rel hl : List.Lex (· < ·)
          (interpretation q head :: after.map (interpretation q)) (interpretation q first :: rest.map (interpretation q)))
    · exact assignment_lex_raised q head greater input heads suffix ys hraw hg hm hhead ho hinput hrel hy
  simpa only [he, List.map_append] using List.Lex.append_left (· < ·) hlex (before.map (interpretation q))

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.ContextAccumulation
