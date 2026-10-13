import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingContextDefaultAccumulationSupport

/-!
# Genuine raised default interval order at actual native terminal spelling

The actual NONE table output is its first raised row. Independent smaller
execution derives every real Factor frame and its exact terminal execution.
Actual row covariance transports NONE and the raised first position to that
terminal spelling. Retained-head/reset induction then derives whole-word
order without any preceding cover or arbitrary initial lower Assignment.
Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.RaisedDefaultIntervalOrder

open PublicEpsilonUnboundedIota SourceTrackingSequences
open Hereditary.FinePredecessor (stripLast)
open SkTracking.Support (stripLast_cons_nonempty)
open ReplacementFidelity (SameEntry)
open Alexander313.Wilken.MultiplicativeNormalForm MultiplicativePrincipalArithmetic


/-- Every actual frame derives its complete original Assignment and the
honest whole-word retained/reset state, at the actual terminal code. -/
theorem unwind_states {q target greater current : Nat} {frames : List IntervalFrames.Frame}
    (hs : IntervalFrames.Segment q target greater current frames)
    (original out : List Nat) (head : Nat)
    (hw : SourceTrackingRaw.trackingCheck q original = true) (hh : head ∈ stripLast original)
    (hm : IsMultiplicativePrincipal (interpretation q greater))
    (hhead : interpretation q head < interpretation q greater)
    (hgreater : interpretation q greater ≤ interpretation q (lastCode original))
    (hstart : ∃ after, original = head :: after) :
    original ∈ Assignment.execute q (ContextAccumulation.terminalCode current frames) →
    IntervalFrames.Unwind q frames original out →
    out ∈ Assignment.execute q current ∧ ContextAccumulation.State q head greater current out := by
  have hraw := ((SourceTrackingRaw.trackingCheck_conditions q original).mp hw).2.1.nodes head hh
  induction hs generalizing out with
  | nil terminal hv =>
    intro hbottom hu
    cases hu
    exact ⟨hbottom, Or.inl hstart⟩
  | cons current child factor frames hf hsmall ht ih =>
    intro hbottom hu
    cases hu with
    | cons current child factor frames original middle out htail hbranch =>
      obtain ⟨hchild, hstate⟩ := ih middle hbottom htail
      have hcurrent := Assignment.execute_factor q current child factor middle out hf hchild hbranch
      obtain ⟨_, _, _, hfLow, hfAccepted, _, _, _, hM, hone, _, hlf, _⟩ :=
        Factor.execute_spec q current (child, factor) hf
      have hcut := Factor.Bounds.execute_last_le_prefix_last q current (child, factor) hf
      rcases hstate with ⟨after, he⟩ | ⟨input, heads, hstrict, hinput, ho, hlastFactor, hrel⟩
      · have hn := ContextDefaultAccumulationSupport.uninitialized_update q head greater factor after out
          hraw ⟨hfLow, hfAccepted⟩ hM hone hm hhead hsmall (by simpa only [he] using hbranch)
        refine ⟨hcurrent, ?_⟩
        rcases hn with hn | ⟨next, nextHeads, hs, hb, ha, hl, hr⟩
        · exact Or.inl hn
        · exact Or.inr ⟨next, nextHeads, hs, hb, ha, hl.trans hlf, hr⟩
      · have hcut' : interpretation q factor ≤
          lf (interpretation (ReplacementSupport.raisedBaseCode q head) input) := by
          rw [hlastFactor]
          exact hcut
        obtain ⟨next, nextHeads, hs, hb, ha, hl, hr⟩ :=
          ContextDefaultAccumulationSupport.initialized_update q original head greater input factor
            heads middle out hw hh hm hgreater ho hstrict hinput hrel
            ⟨hfLow, hfAccepted⟩ hM hone hsmall hcut' hbranch
        exact ⟨hcurrent, Or.inr ⟨next, nextHeads, hs, hb, ha, hl.trans hlf, hr⟩⟩
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


/-- Every observed finite unwind is strictly below the fixed actual
raised row, whether FIRST is retained or a genuine reset initialized it. -/
theorem unwind_lex {q target greater current : Nat} {frames : List IntervalFrames.Frame}
    (hs : IntervalFrames.Segment q target greater current frames)
    (original out : List Nat) (head : Nat) (ys : List Nat)
    (hbottom : original ∈ Assignment.execute q (ContextAccumulation.terminalCode current frames))
    (hw : SourceTrackingRaw.trackingCheck q original = true) (hh : head ∈ stripLast original)
    (hg : lowCheckCode q greater = true) (hm : IsMultiplicativePrincipal (interpretation q greater))
    (hhead : interpretation q head < interpretation q greater)
    (hgreater : interpretation q greater ≤ interpretation q (lastCode original))
    (hy : ys ∈ Replacement.raisedReplacement q head greater)
    (hstart : ∃ after, original = head :: after)
    (hu : IntervalFrames.Unwind q frames original out) :
    List.Lex (· < ·) (out.map (interpretation q)) (ys.map (interpretation q)) := by
  have hsuffix := (unwind_states hs original out head hw hh hm hhead hgreater hstart hbottom hu).2
  have hraw := ((SourceTrackingRaw.trackingCheck_conditions q original).mp hw).2.1.nodes head hh
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
  · exact assignment_lex_raised q head greater input heads out ys hraw hg hm hhead ho hinput hrel hy

private theorem default_unwind_lex {q target factor input : Nat} {frames : List IntervalFrames.Frame}
    (hs : IntervalFrames.Segment q target factor input frames)
    (heads xs : List Nat) (rows : List InsertionSupport.Row)
    (hh : heads ∈ Assignment.execute q (ContextAccumulation.terminalCode input frames))
    (hr : rows ∈ InsertionSupport.executeRows q factor heads)
    (hchoice : Insertion.choose q rows = none)
    (hf : lowCheckCode q factor = true) (hm : IsMultiplicativePrincipal (interpretation q factor))
    (hb : interpretation q factor ≤ interpretation q (lastCode heads))
    (hlarge : interpretation q (Insertion.firstCode heads) < interpretation q factor)
    (hu : IntervalFrames.Unwind q frames heads xs) :
    List.Lex (· < ·) (xs.map (interpretation q)) ((Insertion.word q rows).map (interpretation q)) := by
  obtain ⟨head, rest, hheads⟩ := List.exists_cons_of_ne_nil (Assignment.execute_nonempty q _ heads hh)
  have hhead : interpretation q head < interpretation q factor := by
    simpa only [hheads, Insertion.firstCode, List.head?_cons, Option.getD_some] using hlarge
  have hrest : rest ≠ [] := by
    intro he
    have hlast : interpretation q factor ≤ interpretation q head := by
      simpa only [hheads, he, lastCode_singleton] using hb
    exact hhead.not_ge hlast
  have hproper : head ∈ stripLast heads := by
    rw [hheads, stripLast_cons_nonempty head rest hrest]
    exact List.mem_cons_self
  have hraw := Assignment.execute_tracking q _ heads hh
  have hhRaw := ((SourceTrackingRaw.trackingCheck_conditions q heads).mp hraw).2.1.nodes head hproper
  have hrelation := InsertionSupport.executeRows_relation q factor heads rows hr
  rw [hheads] at hrelation
  obtain ⟨row, tail, hrow, htail, hrows⟩ := List.forall₂_cons_left_iff.mp hrelation
  have hc : row.2 ∈ ConditionalReplacement.execute q head factor := by simpa only [hrow.1] using hrow.2
  have hflag : ConditionalReplacement.raisedCheck q head factor = true :=
    (ConditionalReplacement.raisedCheck_exact q head factor
      ((SourceTrackingRaw.Support.inputCheck_exact q head).mp hhRaw).1 hf).mpr hhead
  have hraised : row.2 ∈ Replacement.raisedReplacement q head factor := by
    simpa only [ConditionalReplacement.execute, hflag, Bool.cond_true] using hc
  have hout : Insertion.word q rows = row.2 := by
    simp only [Insertion.word, hchoice, hrows, List.head?_cons, Option.getD_some]
  simpa only [hout] using unwind_lex hs heads xs head row.2 hh hraw hproper hf hm hhead hb
    hraised ⟨rest, hheads⟩ hu

/-- Only the actual greater observed raised choice is assumed. Complete
independent assignments derive the real smaller trace and every cut state. -/
theorem execute_raised_default_interval_lex (q greater prefix factor input : Nat)
    (heads xs ys : List Nat) (rows : List InsertionSupport.Row)
    (hf : (prefix, factor) ∈ Factor.execute q greater)
    (hh : heads ∈ Assignment.execute q prefix)
    (ha : BranchesSupport.appendCheck q factor heads = false)
    (hr : rows ∈ InsertionSupport.executeRows q factor heads)
    (hs : Insertion.choose q rows = none)
    (hlarge : interpretation q (Insertion.firstCode heads) < interpretation q factor)
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
  have hnone : Insertion.choose q otherRows = none := by
    cases hc : Insertion.choose q otherRows with
    | none => rfl
    | some candidate =>
      simp only [hs, hc, Option.map_none, Option.map_some, Option.none_ne_some] at hchoices
  have hlargeBottom : interpretation q (Insertion.firstCode bottom) < interpretation q factor := by
    rw [AssignmentValueSupport.firstCode_values_eq q _ _ hbottomValues]
    exact hlarge
  have hlex := default_unwind_lex hseg bottom xs otherRows hbottom hotherRows hnone
    hfLow hM hbottomBound hlargeBottom hunwind
  have houtputValues := AssignmentValueSupport.insertion_word_values_eq q rows otherRows hrowValues hvalid hotherValid
  simpa only [← houtputValues, ← hys] using hlex

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.RaisedDefaultIntervalOrder
