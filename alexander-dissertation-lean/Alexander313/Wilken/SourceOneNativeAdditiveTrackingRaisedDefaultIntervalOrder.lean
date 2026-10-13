import Alexander313.Wilken.SourceOneNativeAdditiveTrackingContextDefaultAccumulationSupport

/-!
# Actual raised default insertion orders every smaller interval execution

The greater table has no passing transition and starts at a proper epsilon
head below its real last factor. Its genuine output is the independently
executing raised row at that head. Real smaller Factor Segment and Unwind
memberships derive all complete original Assignments and each retained-head
or initialized lower state. Thus every smaller output is lexically below
the real raised default output, without a preceding cover, an assumed old
suffix Assignment, numerical fuel or supplied accumulation inequality.
Source-only uncompiled candidates in literal original source zero.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.RaisedDefaultIntervalOrder

open NativeContext.SourceTrackingSequences
open Hereditary.FinePredecessor (stripLast)
open SkTracking.Support (stripLast_cons_nonempty)
open Alexander313.Wilken.MultiplicativeNormalForm
open IntervalFrames

/-- Every actual frame reconstructs its source Assignment and derives
its honest retained-head or initialized lower state. -/
theorem unwind_states {target greater current : Nat} {frames : List Frame}
    (hs : Segment target greater current frames)
    (original out : List Nat) (head : Nat)
    (hbottom : original ∈ Assignment.execute target)
    (hw : SourceTrackingRaw.trackingCheck original = true) (hh : head ∈ stripLast original)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 greater))
    (hhead : interpretation 0 head < interpretation 0 greater)
    (hgreater : interpretation 0 greater ≤ interpretation 0 (lastCode original))
    (hstart : ∃ after, original = head :: after)
    (hu : Unwind frames original out) :
    out ∈ Assignment.execute current ∧ ContextAccumulation.State head greater current out := by
  have hraw := ((SourceTrackingRaw.trackingCheck_exact original).mp hw).2.1.nodes head hh
  induction hs generalizing out with
  | nil =>
    cases hu
    exact ⟨hbottom, Or.inl hstart⟩
  | cons current child factor frames hf hsmall ht ih =>
    cases hu with
    | cons current child factor frames original middle out htail hbranch =>
      obtain ⟨hchild, hstate⟩ := ih middle htail
      have hcurrent := Assignment.execute_factor current child factor middle out hf hchild hbranch
      obtain ⟨hcaller, hpAccepted, hfAccepted, hpCaller, hpFloor, hpLess, hM, hone,
        hproduct, hlf, hcount⟩ := Factor.execute_spec current (child, factor) hf
      have hcut := Factor.Bounds.execute_last_le_prefix_last current (child, factor) hf
      rcases hstate with ⟨after, he⟩ | ⟨input, heads, hstrict, hinput, ho, hlastFactor, hrel⟩
      · have hn := ContextDefaultAccumulationSupport.uninitialized_update head greater factor after out
          hraw hfAccepted hM hone hm hhead hsmall (by simpa only [he] using hbranch)
        refine ⟨hcurrent, ?_⟩
        rcases hn with hn | ⟨next, nextHeads, hs, hb, ha, hl, hr⟩
        · exact Or.inl hn
        · exact Or.inr ⟨next, nextHeads, hs, hb, ha, hl.trans hlf, hr⟩
      · have hcut' : interpretation 0 factor ≤
          lf (NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) input) := by
          rw [hlastFactor]
          exact hcut
        obtain ⟨next, nextHeads, hs, hb, ha, hl, hr⟩ :=
          ContextDefaultAccumulationSupport.initialized_update original head greater input factor
            heads middle out hw hh hm hgreater ho hstrict hinput hrel hfAccepted hM hone hsmall hcut' hbranch
        exact ⟨hcurrent, Or.inr ⟨next, nextHeads, hs, hb, ha, hl.trans hlf, hr⟩⟩

private theorem assignment_lex_raised (head greater input : Nat) (heads suffix ys : List Nat)
    (hh : SourceTrackingRaw.Support.inputCheck head = true)
    (hg : lowCheckCode 0 greater = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 greater))
    (hhead : interpretation 0 head < interpretation 0 greater)
    (ho : heads ∈ NativeContext.SourceAdditiveTracking.Assignment.execute
      (ReplacementSupport.raisedBaseCode head) input)
    (hlt : NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) input < interpretation 0 greater)
    (hr : List.Forall₂ (Replacement.EntryMatches (ReplacementSupport.raisedBaseCode head)) heads suffix)
    (hy : ys ∈ Replacement.raisedReplacement head greater) :
    List.Lex (· < ·) (suffix.map (interpretation 0)) (ys.map (interpretation 0)) := by
  obtain ⟨rightWord, hw, he, ht, hv, hlen, hchecked⟩ :=
    Replacement.raisedReplacement_spec head greater ys hh hg hm hhead hy
  obtain ⟨right, hs, hword⟩ := (Part.mem_map_iff _).mp hw
  have hi := ReplacementSupport.raisedSearch_multiplicative head greater right hh hg hm hhead hs
  have hs' := ReplacementSupport.raisedSearch_spec head greater right hg hs
  have har : rightWord ∈ NativeContext.SourceAdditiveTracking.Assignment.execute
      (ReplacementSupport.raisedBaseCode head) right := by
    rw [← hword]
    exact NativeContext.SourceAdditiveTracking.Assignment.execute_multiplicative _ right hi
  rw [ContextRelatedFirstCut.relation_values hr, hv]
  exact NativeContext.SourceAdditiveTracking.AssignmentCoverPrefix.execute_right_multiplicative_lex
    _ input right heads rightWord hi (by rw [hs'.2.2]; exact hlt) ho har

/-- The whole real unwind is strictly before the fixed genuine raised
row, whether its original FIRST survives or an actual reset initialized it. -/
theorem unwind_lex {target greater current : Nat} {frames : List Frame}
    (hs : Segment target greater current frames)
    (original out : List Nat) (head : Nat) (ys : List Nat)
    (hbottom : original ∈ Assignment.execute target)
    (hw : SourceTrackingRaw.trackingCheck original = true) (hh : head ∈ stripLast original)
    (hg : lowCheckCode 0 greater = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 greater))
    (hhead : interpretation 0 head < interpretation 0 greater)
    (hgreater : interpretation 0 greater ≤ interpretation 0 (lastCode original))
    (hy : ys ∈ Replacement.raisedReplacement head greater)
    (hstart : ∃ after, original = head :: after)
    (hu : Unwind frames original out) :
    List.Lex (· < ·) (out.map (interpretation 0)) (ys.map (interpretation 0)) := by
  have hsuffix := (unwind_states hs original out head hbottom hw hh hm hhead hgreater hstart hu).2
  have hraw := ((SourceTrackingRaw.trackingCheck_exact original).mp hw).2.1.nodes head hh
  rcases hsuffix with ⟨after, hafter⟩ | ⟨input, heads, hstrict, hinput, ho, hl, hrel⟩
  · have hfirst := FrameOrderSupport.raised_first_strict head greater ys hraw hg hm hhead hy
    have hneYs : ys ≠ [] := by
      obtain ⟨rightWord, hr, he, ht, hv, hlen, hchecked⟩ :=
        Replacement.raisedReplacement_spec head greater ys hraw hg hm hhead hy
      intro hn
      have hl := hlen
      rw [hn, List.length_nil] at hl
      exact ((NativeContext.SourceTrackingSequences.trackingCheck_exact _ rightWord).mp ht).1
        (List.length_eq_zero_iff.mp hl.symm)
    obtain ⟨first, rest, hys⟩ := List.exists_cons_of_ne_nil hneYs
    have hl : interpretation 0 head < interpretation 0 first := by
      simpa only [hys, Insertion.firstCode, List.head?_cons, Option.getD_some] using hfirst
    simpa only [hafter, hys, List.map_cons] using
      (List.Lex.rel hl : List.Lex (· < ·)
        (interpretation 0 head :: after.map (interpretation 0)) (interpretation 0 first :: rest.map (interpretation 0)))
  · exact assignment_lex_raised head greater input heads out ys hraw hg hm hhead ho hinput hrel hy

/-- The actual NONE and raised first-row guards derive all contextual
provenance and compare every independently executing smaller interval input. -/
theorem execute_raised_default_interval_lex (greater prefix factor input : Nat)
    (heads xs ys : List Nat) (rows : List InsertionSupport.Row)
    (hf : (prefix, factor) ∈ Factor.execute greater)
    (hh : heads ∈ Assignment.execute prefix)
    (ha : BranchesSupport.appendCheck factor heads = false)
    (hr : rows ∈ InsertionSupport.executeRows factor heads)
    (hs : Insertion.choose rows = none)
    (hlarge : interpretation 0 (Insertion.firstCode heads) < interpretation 0 factor)
    (hx : xs ∈ Assignment.execute input) (hy : ys ∈ Assignment.execute greater)
    (hl : interpretation 0 prefix < interpretation 0 input)
    (hlt : interpretation 0 input < interpretation 0 greater) :
    List.Lex (· < ·) (xs.map (interpretation 0)) (ys.map (interpretation 0)) := by
  obtain ⟨head, rest, hheads⟩ := List.exists_cons_of_ne_nil (Assignment.execute_nonempty prefix heads hh)
  have hhead : interpretation 0 head < interpretation 0 factor := by
    simpa only [hheads, Insertion.firstCode, List.head?_cons, Option.getD_some] using hlarge
  obtain ⟨middle, hm, hb⟩ := FrameFactorOrder.actual_factor_child greater prefix factor ys hf hy
  have hmiddle : middle = heads := Part.mem_unique hm hh
  have hi : ys ∈ Insertion.execute (factor, heads) := by
    simpa only [hmiddle, Branches.execute, ha, Bool.cond_false] using hb
  have hys : ys = Insertion.word rows := Part.mem_unique hi (Part.mem_map Insertion.word hr)
  have hfactor := Factor.execute_spec greater (prefix, factor) hf
  have hfLow := ((Theta.acceptedLowCode_iff 0 factor).mp hfactor.2.2.1).1
  have hM := hfactor.2.2.2.2.2.2.1
  have hfactorBound : interpretation 0 factor ≤ interpretation 0 (lastCode heads) :=
    (Factor.Bounds.execute_last_le_prefix_last greater (prefix, factor) hf).trans
      (Assignment.execute_last_bounds prefix heads hh).1
  have hrest : rest ≠ [] := by
    intro he
    have hlast : interpretation 0 factor ≤ interpretation 0 head := by
      simpa only [hheads, he, lastCode_singleton] using hfactorBound
    exact hhead.not_ge hlast
  have hproper : head ∈ stripLast heads := by
    rw [hheads, stripLast_cons_nonempty head rest hrest]
    exact List.mem_cons_self
  have hraw := Assignment.execute_tracking prefix heads hh
  have hhRaw := ((SourceTrackingRaw.trackingCheck_exact heads).mp hraw).2.1.nodes head hproper
  have hrelation := InsertionSupport.executeRows_relation factor heads rows hr
  rw [hheads] at hrelation
  obtain ⟨row, tail, hrow, htail, hrows⟩ := List.forall₂_cons_left_iff.mp hrelation
  have hc : row.2 ∈ ConditionalReplacement.execute head factor := by simpa only [hrow.1] using hrow.2
  have hflag : ConditionalReplacement.raisedCheck head factor = true :=
    (ConditionalReplacement.raisedCheck_exact head factor
      ((SourceTrackingRaw.Support.inputCheck_exact head).mp hhRaw).1 hfLow).mpr hhead
  have hraised : row.2 ∈ Replacement.raisedReplacement head factor := by
    simpa only [ConditionalReplacement.execute, hflag, Bool.cond_true] using hc
  have hout : ys = row.2 := by
    simp only [hys, Insertion.word, hs, hrows, List.head?_cons, Option.getD_some]
  obtain ⟨frames, bottom, hseg, hbottom, hunwind⟩ :=
    IntervalFrames.execute_interval_frames greater prefix factor input xs hf hx hl hlt
  have heq : bottom = heads := Part.mem_unique hbottom hh
  have htrace : IntervalFrames.Unwind frames heads xs := by simpa only [heq] using hunwind
  have hlex := unwind_lex hseg heads xs head row.2 hh hraw hproper hfLow hM hhead
    hfactorBound hraised ⟨rest, hheads⟩ htrace
  simpa only [hout] using hlex

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.RaisedDefaultIntervalOrder
