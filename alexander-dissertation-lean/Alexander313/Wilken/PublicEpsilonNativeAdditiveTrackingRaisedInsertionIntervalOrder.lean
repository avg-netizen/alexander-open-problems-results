import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingContextAccumulation

/-!
# Actual selected raised updates compare every smaller interval assignment

The actual complete smaller execution supplies its real terminal code and
reverse factor unwind. Its terminal word has the greater child VALUES,
without a Normal syntax injection. Actual independently executing row tables
therefore select the same position and replacement VALUES. Applying the
retained/reset state proof at that real terminal word derives the entire
comparison with the actual greater output. No terminal word, trace, retained
prefix, lower suffix Assignment or lexical bound is supplied. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.RaisedInsertionIntervalOrder

open PublicEpsilonUnboundedIota SourceTrackingSequences
open Hereditary.FinePredecessor (stripLast)
open InsertionFidelitySupport (stripLast_append_nonempty)
open SkTracking.Support (stripLast_cons_nonempty)
open Alexander313.Wilken.MultiplicativeNormalForm MultiplicativePrincipalArithmetic

private theorem selected_unwind_lex {q target factor input : Nat} {frames : List IntervalFrames.Frame}
    (hs : IntervalFrames.Segment q target factor input frames)
    (heads xs : List Nat) (rows : List InsertionSupport.Row) (n : Nat) (replacement : List Nat)
    (hh : heads ∈ Assignment.execute q (ContextAccumulation.terminalCode input frames))
    (hr : rows ∈ InsertionSupport.executeRows q factor heads)
    (hchoice : Insertion.choose q rows = some (n, replacement))
    (hf : lowCheckCode q factor = true) (hm : IsMultiplicativePrincipal (interpretation q factor))
    (hb : interpretation q factor ≤ interpretation q (lastCode heads))
    (hlarge : interpretation q (Insertion.firstCode (heads.drop n)) < interpretation q factor)
    (hu : IntervalFrames.Unwind q frames heads xs) :
    List.Lex (· < ·) (xs.map (interpretation q)) ((Insertion.word q rows).map (interpretation q)) := by
  obtain ⟨before, current, after, hne, hrows, hn, hword, hcover, hnone⟩ :=
    Insertion.choose_spec q rows n replacement hchoice
  have hrelation := InsertionSupport.executeRows_relation q factor heads rows hr
  have hheads := InsertionSupport.relation_heads q factor hrelation
  have hsplit : heads = before.map Prod.fst ++ current.1 :: after.map Prod.fst := by
    simpa only [hrows, List.map_append, List.map_cons] using hheads.symm
  have hn' : n = (before.map Prod.fst).length := by simpa only [List.length_map] using hn
  have hselected : Insertion.firstCode (heads.drop n) = current.1 := by
    simp only [hsplit, hn', List.drop_left, Insertion.firstCode, List.head?_cons, Option.getD_some]
  have hhead : interpretation q current.1 < interpretation q factor := by
    simpa only [hselected] using hlarge
  have hraw := Assignment.execute_tracking q _ heads hh
  have hsource := (SourceTrackingRaw.trackingCheck_conditions q heads).mp hraw
  have hafter : after.map Prod.fst ≠ [] := by
    intro he
    have hlast : interpretation q factor ≤ interpretation q current.1 := by
      simpa only [hsplit, he, lastCode_append_singleton] using hb
    exact hhead.not_ge hlast
  have hprefix := hsource.2.1
  rw [hsplit, stripLast_append_nonempty _ _ (List.cons_ne_nil _ _),
    stripLast_cons_nonempty current.1 _ hafter] at hprefix
  have hproper : current.1 ∈ stripLast heads := by
    rw [hsplit, stripLast_append_nonempty _ _ (List.cons_ne_nil _ _),
      stripLast_cons_nonempty current.1 _ hafter]
    exact List.mem_append_right _ List.mem_cons_self
  have hhRaw := hsource.2.1.nodes current.1 hproper
  have hbeforeNe : before.map Prod.fst ≠ [] := by
    intro he
    exact hne (List.map_eq_nil_iff.mp he)
  have href : SourceTrackingRaw.Reference q (before.map Prod.fst ++ [current.1]) :=
    InsertionFidelitySupport.reference_prefix q (before.map Prod.fst ++ [current.1])
      (stripLast (after.map Prod.fst))
      (by simpa only [List.append_assoc, List.singleton_append] using hprefix)
  have hstrict : ((before.map Prod.fst).map (interpretation q) ++
      [interpretation q current.1]).Pairwise (· < ·) := by
    simpa only [List.map_append, List.map_singleton] using href.strict
  have hfront := (List.pairwise_append.mp hstrict).2.2 _
    (List.mem_map.mpr ⟨lastCode (before.map Prod.fst), lastCode_mem _ hbeforeNe, rfl⟩)
    _ List.mem_cons_self
  have hcurrentMem : current ∈ rows := by rw [hrows]; exact List.mem_append_right _ List.mem_cons_self
  have hcall := (InsertionSupport.relation_members q factor hrelation current hcurrentMem).2
  have hraisedCheck : ConditionalReplacement.raisedCheck q current.1 factor = true :=
    (ConditionalReplacement.raisedCheck_exact q current.1 factor
      ((SourceTrackingRaw.Support.inputCheck_exact q current.1).mp hhRaw).1 hf).mpr hhead
  have hraised : current.2 ∈ Replacement.raisedReplacement q current.1 factor := by
    simpa only [ConditionalReplacement.execute, hraisedCheck, Bool.cond_true] using hcall
  have hcover' : Insertion.coverCheck q (lastCode (before.map Prod.fst))
      (Insertion.firstCode current.2) = true := by simpa only [hword] using hcover
  have hlex := ContextAccumulation.unwind_lex hs heads xs (before.map Prod.fst)
    current.1 current.2 hh hraw hproper hbeforeNe hfront hf hm hhead hb hraised hcover'
    ⟨after.map Prod.fst, hsplit⟩ hu
  have hout : Insertion.word q rows = before.map Prod.fst ++ current.2 := by
    rw [Insertion.word, hchoice, hn, hrows, List.take_left, hword]
  simpa only [hout] using hlex

/-- Only the actual greater observed raised choice is assumed. Complete
independent assignments derive the real smaller trace and every cut state. -/
theorem execute_raised_selected_interval_lex (q greater prefix factor input : Nat)
    (heads xs ys : List Nat) (rows : List InsertionSupport.Row) (n : Nat) (replacement : List Nat)
    (hf : (prefix, factor) ∈ Factor.execute q greater)
    (hh : heads ∈ Assignment.execute q prefix)
    (ha : BranchesSupport.appendCheck q factor heads = false)
    (hr : rows ∈ InsertionSupport.executeRows q factor heads)
    (hs : Insertion.choose q rows = some (n, replacement))
    (hlarge : interpretation q (Insertion.firstCode (heads.drop n)) < interpretation q factor)
    (hx : xs ∈ Assignment.execute q input) (hy : ys ∈ Assignment.execute q greater)
    (hl : interpretation q prefix < interpretation q input)
    (hlt : interpretation q input < interpretation q greater) :
    List.Lex (· < ·) (xs.map (interpretation q)) (ys.map (interpretation q)) := by
  obtain ⟨middle, hm, hb⟩ := IntervalFactors.actual_factor_child q greater prefix factor ys hf hy
  have hmiddle : middle = heads := Part.mem_unique hm hh
  have hi : ys ∈ Insertion.execute ((q, factor), heads) := by
    simpa only [hmiddle, Branches.execute, ha, Bool.cond_false] using hb
  have hys : ys = Insertion.word q rows := Part.mem_unique hi (Part.mem_map (Insertion.word q) hr)
  obtain ⟨frames, hseg⟩ := IntervalFrames.interval_segment_returns q greater prefix factor input hf
    (Assignment.execute_spec q input xs hx).1 hl hlt
  obtain ⟨bottom, hbottom, hunwind⟩ := ContextAccumulation.segment_execute_bottom hseg xs hx
  have hvalue := ContextAccumulation.segment_terminal_value hseg
  have hbottomValues : bottom.map (interpretation q) = heads.map (interpretation q) :=
    Assignment.ValueInvariance.execute_values_eq q _ prefix bottom heads hbottom hh hvalue
  obtain ⟨_, _, _, hfLow, hfAccepted, _, _, _, hM, hone, _, _, _⟩ :=
    Factor.execute_spec q greater (prefix, factor) hf
  have hfactorBound : interpretation q factor ≤ interpretation q (lastCode heads) :=
    (Factor.Bounds.execute_last_le_prefix_last q greater (prefix, factor) hf).trans
      (Assignment.execute_last_bounds q prefix heads hh).1
  have hbottomBound : interpretation q factor ≤ interpretation q (lastCode bottom) := by
    have hlf : interpretation q factor ≤ lf (interpretation q (ContextAccumulation.terminalCode input frames)) := by
      rw [hvalue]
      exact Factor.Bounds.execute_last_le_prefix_last q greater (prefix, factor) hf
    exact hlf.trans (Assignment.execute_last_bounds q _ bottom hbottom).1
  have hraw := Assignment.execute_tracking q prefix heads hh
  have hbottomRaw := Assignment.execute_tracking q _ bottom hbottom
  obtain ⟨otherRows, hotherRows⟩ := InsertionSupport.executeRows_returns q factor bottom hbottomRaw hfLow hM hbottomBound
  have hrowValues := AssignmentValueSupport.executeRows_values_eq q factor factor heads bottom
    hraw hbottomRaw hfLow hfLow hM hfactorBound hbottomBound rfl hbottomValues.symm rows otherRows hr hotherRows
  have hvalid := AssignmentValueSupport.executeRows_valid q factor heads hraw hfLow hM hfactorBound rows hr
  have hotherValid := AssignmentValueSupport.executeRows_valid q factor bottom hbottomRaw hfLow hM hbottomBound otherRows hotherRows
  have hchoices := AssignmentValueSupport.choose_values_eq q rows otherRows hrowValues hvalid hotherValid
  obtain ⟨candidate, hcandidate, hcandidateValues⟩ : ∃ candidate,
      Insertion.choose q otherRows = some candidate ∧
      AssignmentValueSupport.candidateValues q (n, replacement) = AssignmentValueSupport.candidateValues q candidate := by
    cases hc : Insertion.choose q otherRows with
    | none => simp only [hs, hc, Option.map_some, Option.map_none, Option.some_ne_none] at hchoices
    | some candidate =>
      exact ⟨candidate, hc, by simpa only [hs, hc, Option.map_some, Option.some.injEq] using hchoices⟩
  have hn : n = candidate.1 := congrArg Prod.fst hcandidateValues
  have hdropValues : (bottom.drop n).map (interpretation q) = (heads.drop n).map (interpretation q) := by
    simpa only [List.map_drop] using congrArg (List.drop n) hbottomValues
  have hlargeBottom : interpretation q (Insertion.firstCode (bottom.drop candidate.1)) < interpretation q factor := by
    rw [← hn, AssignmentValueSupport.firstCode_values_eq q _ _ hdropValues]
    exact hlarge
  have hlex := selected_unwind_lex hseg bottom xs otherRows candidate.1 candidate.2
    hbottom hotherRows hcandidate hfLow hM hbottomBound hlargeBottom hunwind
  have houtputValues := AssignmentValueSupport.insertion_word_values_eq q rows otherRows hrowValues hvalid hotherValid
  simpa only [← houtputValues, ← hys] using hlex

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.RaisedInsertionIntervalOrder
