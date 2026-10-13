import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingContextBranchCutSupport

/-!
# Exact contextual cuts need only the actual updated suffix FIRST cover

If a later suffix transition passes, the genuine right-priority selector
retains every earlier head without testing the boundary. Otherwise its
actual suffix word is the current replacement, so the actual whole suffix
FIRST cover is exactly the needed boundary test. Independently executing
suffix tables follow from the real full chronological relation. No bound
on all suffix values by the boundary mu is needed. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.ContextFirstCutSupport

open PublicEpsilonUnboundedIota SourceTrackingSequences
open InsertionSupport (Row)
open Hereditary.FinePredecessor (stripLast stripLast_split)
open ReplacementFidelity (SameEntry)
open Hereditary.SourceAdditiveTrackingWordBounds (lastCode_append_nonempty)

theorem choose_append_some (q : Nat) (prefix rows : List Row) (selected : Insertion.Candidate)
    (hs : Insertion.choose q rows = some selected) :
    ∃ candidate, Insertion.choose q (prefix ++ rows) = some candidate := by
  induction prefix with
  | nil => exact ⟨selected, hs⟩
  | cons row prefix ih =>
    obtain ⟨candidate, hc⟩ := ih
    exact ⟨(candidate.1 + 1, candidate.2), by
      simpa only [List.cons_append] using
        AssignmentCoverPrefixSupport.choose_prepend q row _ candidate.1 candidate.2 hc⟩

theorem word_append_some (q : Nat) (prefix rows : List Row) (selected : Insertion.Candidate)
    (hs : Insertion.choose q rows = some selected) :
    Insertion.word q (prefix ++ rows) = prefix.map Prod.fst ++ Insertion.word q rows := by
  induction prefix with
  | nil => rfl
  | cons row prefix ih =>
    obtain ⟨candidate, hc⟩ := choose_append_some q prefix rows selected hs
    simpa only [List.cons_append, List.map_cons,
      SmallInsertionIntervalOrderSupport.word_cons_some q row _ candidate hc] using
        congrArg (List.cons row.1) ih

/-- This test concerns the actual whole suffix FIRST. A later suffix
selection itself retains the boundary; a default supplies the true row FIRST. -/
theorem word_first_covered_cut (q : Nat) (prefix : List Row) (previous current : Row)
    (rest : List Row)
    (hc : Insertion.coverCheck q previous.1
      (Insertion.firstCode (Insertion.word q (current :: rest))) = true) :
    Insertion.word q (prefix ++ previous :: current :: rest) =
      (prefix.map Prod.fst ++ [previous.1]) ++ Insertion.word q (current :: rest) := by
  cases hs : Insertion.choose q (current :: rest) with
  | some selected =>
    simpa only [List.append_assoc, List.singleton_append, List.map_append,
      List.map_singleton] using word_append_some q (prefix ++ [previous]) _ selected hs
  | none =>
    have hp : Insertion.coverCheck q previous.1 (Insertion.firstCode current.2) = true := by
      simpa only [Insertion.word, hs, List.head?_cons, Option.getD_some] using hc
    exact ContextInsertionCutSupport.word_passing_cut q prefix previous current rest hp

/-- The concrete full table reconstructs its independently executing
suffix; actual suffix output membership and FIRST cover derive the exact cut. -/
theorem insertion_first_cut (q factor : Nat) (before : List Nat) (first : Nat)
    (rest out suffix : List Nat) (hne : before ≠ [])
    (hraw : SourceTrackingRaw.Support.inputCheck q (lastCode before) = true)
    (hlow : lowCheckCode q (Insertion.firstCode suffix) = true)
    (hcover : interpretation q (Insertion.firstCode suffix) ≤
      SourceTrackingRaw.Support.muValue q (lastCode before))
    (ho : out ∈ Insertion.execute ((q, factor), before ++ first :: rest))
    (hs : suffix ∈ Insertion.execute ((q, factor), first :: rest)) :
    out = before ++ suffix := by
  obtain ⟨rows, hr, hout⟩ := (Part.mem_map_iff _).mp ho
  obtain ⟨prefix, tail, hrows, hp, ht⟩ :=
    ContextInsertionCutSupport.executeRows_split q factor before (first :: rest) rows hr
  have hrelation := InsertionSupport.executeRows_relation q factor (first :: rest) tail ht
  obtain ⟨current, after, hc, ha, rfl⟩ := List.forall₂_cons_left_iff.mp hrelation
  have hprefixNe : prefix ≠ [] := by
    intro he
    exact hne (by simpa only [he, List.map_nil] using hp.symm)
  obtain ⟨previous, hsplit, hmem⟩ := stripLast_split prefix hprefixNe
  have hbefore : before = (stripLast prefix).map Prod.fst ++ [previous.1] := by
    calc
      before = prefix.map Prod.fst := hp.symm
      _ = (stripLast prefix).map Prod.fst ++ [previous.1] := by
        simpa only [List.map_append, List.map_singleton] using
          congrArg (List.map Prod.fst) hsplit
  have hprevious : lastCode before = previous.1 := by
    rw [hbefore, lastCode_append_singleton]
  have hword : suffix = Insertion.word q (current :: after) := by
    obtain ⟨otherRows, hm, hw⟩ := (Part.mem_map_iff _).mp hs
    have heq := Part.mem_unique ht hm
    simpa only [heq] using hw.symm
  have hpass : Insertion.coverCheck q previous.1
      (Insertion.firstCode (Insertion.word q (current :: after))) = true := by
    apply (Insertion.coverCheck_exact q _ _).mpr
    simpa only [← hprevious, ← hword] using And.intro hraw (And.intro hlow hcover)
  have hrowcut : rows = stripLast prefix ++ previous :: current :: after := by
    calc
      rows = prefix ++ (current :: after) := hrows
      _ = stripLast prefix ++ previous :: current :: after := by
        simpa only [List.append_assoc, List.singleton_append] using
          congrArg (fun xs : List Row => xs ++ current :: after) hsplit
  calc
    out = Insertion.word q rows := hout.symm
    _ = Insertion.word q (stripLast prefix ++ previous :: current :: after) := by
      rw [hrowcut]
    _ = ((stripLast prefix).map Prod.fst ++ [previous.1]) ++
        Insertion.word q (current :: after) :=
      word_first_covered_cut q (stripLast prefix) previous current after hpass
    _ = before ++ suffix := by rw [← hbefore, ← hword]

/-- Both actual printed branches retain the cut from the actual updated
suffix FIRST cover. The complete suffix product need not be mu-covered. -/
theorem branches_first_cut (q factor : Nat) (before : List Nat) (first : Nat)
    (rest out suffix : List Nat) (hne : before ≠ [])
    (hh : SourceTrackingRaw.trackingCheck q (before ++ first :: rest) = true)
    (ht : SourceTrackingRaw.trackingCheck q (first :: rest) = true)
    (hfront : interpretation q (lastCode before) < interpretation q first)
    (hraw : SourceTrackingRaw.Support.inputCheck q (lastCode before) = true)
    (hlow : lowCheckCode q (Insertion.firstCode suffix) = true)
    (hcover : interpretation q (Insertion.firstCode suffix) ≤
      SourceTrackingRaw.Support.muValue q (lastCode before))
    (ho : out ∈ Branches.execute ((q, factor), before ++ first :: rest))
    (hs : suffix ∈ Branches.execute ((q, factor), first :: rest)) :
    out = before ++ suffix := by
  have hflag := ContextBranchCutSupport.appendCheck_at_cut q factor before first rest hne hh ht hfront
  rcases Branches.execute_branch q factor (before ++ first :: rest) out ho with
    ⟨ha, he⟩ | ⟨ha, hi⟩
  · have hsflag := hflag.symm.trans ha
    have heq : suffix = (first :: rest) ++ [factor] := by
      simpa only [Branches.execute, hsflag, Bool.cond_true, Part.mem_some_iff] using hs
    simpa only [heq, List.append_assoc] using he
  · have hsflag := hflag.symm.trans ha
    have hi' : suffix ∈ Insertion.execute ((q, factor), first :: rest) := by
      simpa only [Branches.execute, hsflag, Bool.cond_false] using hs
    exact insertion_first_cut q factor before first rest out suffix hne hraw hlow hcover hi hi'

/-- Genuine lower execution supplies the returned RAW suffix and its
independently executing next dispatcher. Only that actual next FIRST is
covered at the original boundary; the complete product can exceed its mu. -/
theorem contextual_update_at_first_cut (q alpha input factor otherFactor : Nat)
    (before heads returnedHeads word out : List Nat)
    (ha : RootLowCollapse.rootCheck q alpha = true)
    (ho : heads ∈ Assignment.execute (betaCode q alpha) input)
    (hstrict : base (betaCode q alpha) < interpretation (betaCode q alpha) input)
    (hown : interpretation (betaCode q alpha) input < Enclosure.sourceAlphaPlus q alpha)
    (hrel : List.Forall₂ (SameEntry q (betaCode q alpha)) heads returnedHeads)
    (hne : before ≠ [])
    (hh : SourceTrackingRaw.trackingCheck q (before ++ returnedHeads) = true)
    (hbefore : interpretation q (lastCode before) < base (betaCode q alpha))
    (hf : lowCheckCode (betaCode q alpha) factor = true)
    (hd : SameEntry q (betaCode q alpha) factor otherFactor)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal
      (interpretation (betaCode q alpha) factor))
    (hone : 1 < interpretation (betaCode q alpha) factor)
    (hb : interpretation (betaCode q alpha) factor ≤
      interpretation (betaCode q alpha) (lastCode heads))
    (hraw : SourceTrackingRaw.Support.inputCheck q (lastCode before) = true)
    (hcover : interpretation (betaCode q alpha) (Insertion.firstCode word) ≤
      SourceTrackingRaw.Support.muValue q (lastCode before))
    (hw : word ∈ Branches.execute (((betaCode q alpha), factor), heads))
    (hu : out ∈ Branches.execute ((q, otherFactor), before ++ returnedHeads)) :
    out.map (interpretation q) = before.map (interpretation q) ++
      word.map (interpretation (betaCode q alpha)) := by
  have hlower := Assignment.execute_tracking _ input heads ho
  have hall := (Assignment.execute_spec _ input heads ho).2.1.2.1
  have htarget := ContextAssignmentReturn.raw_tracking_return q alpha ha heads returnedHeads
    hlower hrel (fun c hc => (hall c hc).trans_lt hown)
  have hreturnedNe := ((SourceTrackingRaw.trackingCheck_conditions q returnedHeads).mp htarget).1
  have hlast := Hereditary.SourceAdditiveTrackingWordBounds.lastCode_values_eq
    (interpretation q) (interpretation (betaCode q alpha)) returnedHeads heads hreturnedNe
      (ContextRowValues.returned_values hrel)
  have hm' : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q otherFactor) := by
    rw [hd.2.2]
    exact hm
  have hone' : 1 < interpretation q otherFactor := by simpa only [hd.2.2] using hone
  have hb' : interpretation q otherFactor ≤ interpretation q (lastCode returnedHeads) := by
    rw [hd.2.2, hlast]
    exact hb
  obtain ⟨suffix, hsuffix⟩ := Branches.execute_returns q otherFactor returnedHeads
    htarget hd.1 hm' hb'
  have hvalues := ContextBranchValues.branches_values_eq q alpha input factor otherFactor
    heads returnedHeads word suffix ha ho hstrict hown hrel hf hd hm hb hw hsuffix
  have hsraw := Branches.execute_tracking q otherFactor returnedHeads suffix
    htarget hd.1 hm' hone' hb' hsuffix
  have hsne := ((SourceTrackingRaw.trackingCheck_conditions q suffix).mp hsraw).1
  have hslow : lowCheckCode q (Insertion.firstCode suffix) = true :=
    AssignmentValueSupport.firstCode_low q suffix hsne
      (fun c hc => (ConditionalReplacement.tracking_member_principal q suffix hsraw c hc).1)
  have hfirstValues : interpretation q (Insertion.firstCode suffix) =
      interpretation (betaCode q alpha) (Insertion.firstCode word) := by
    cases suffix with
    | nil => exact False.elim (hsne rfl)
    | cons c tail =>
      cases word with
      | nil => simp only [List.map_cons, List.map_nil, List.cons_ne_nil] at hvalues
      | cons d rest =>
        simpa only [List.map_cons, Insertion.firstCode, List.head?_cons, Option.getD_some] using
          (List.cons.inj hvalues).1
  have hscover : interpretation q (Insertion.firstCode suffix) ≤
      SourceTrackingRaw.Support.muValue q (lastCode before) := by
    rw [hfirstValues]
    exact hcover
  obtain ⟨first, rest, hheads⟩ := List.exists_cons_of_ne_nil (Assignment.execute_nonempty _ input heads ho)
  have hr := hrel
  rw [hheads] at hr
  obtain ⟨other, otherRest, hfirst, htail, hreturned⟩ := List.forall₂_cons_left_iff.mp hr
  have hfirstStrict := AssignmentFirst.execute_first_gt_base _ input first rest
    (by simpa only [hheads] using ho) hstrict
  have hfront : interpretation q (lastCode before) < interpretation q other := by
    rw [hfirst.2.2]
    exact hbefore.trans hfirstStrict
  have hcut := branches_first_cut q otherFactor before other otherRest out suffix hne
    (by simpa only [hreturned] using hh) (by simpa only [hreturned] using htarget) hfront
    hraw hslow hscover (by simpa only [hreturned] using hu)
      (by simpa only [hreturned] using hsuffix)
  simp only [hcut, List.map_append, hvalues]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.ContextFirstCutSupport
