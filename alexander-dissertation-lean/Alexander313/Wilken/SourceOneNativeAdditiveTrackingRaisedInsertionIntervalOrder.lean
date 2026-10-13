import Alexander313.Wilken.SourceOneNativeAdditiveTrackingContextAccumulation

/-!
# Actual raised selected insertion orders every smaller interval execution

The real greater selector identifies its original head and returned raised
row. Its head-factor comparison and actual factor-to-LAST bound force that
head into the proper epsilon prefix, deriving every RAW and strict cut
caller. Independent smaller execution supplies its actual finite factor
Segment and reverse Unwind. Retained-head/reset induction then compares the
whole smaller output with the real greater selected replacement, preserving
the literal original prefix. No suffix assignment, update trace, selected
position witness or lexical bound is supplied. The actual selected raised
case remains an honest observed computation guard. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.RaisedInsertionIntervalOrder

open NativeContext.SourceTrackingSequences
open Hereditary.FinePredecessor (stripLast)
open SkTracking.Support (stripLast_cons_nonempty)

/-- Every independently executing smaller interval input lies strictly
before the real greater selected raised insertion, at any child length
and selected location. Every retained cut and lower assignment is derived. -/
theorem execute_raised_selected_interval_lex (greater prefix factor input : Nat)
    (heads xs ys : List Nat) (rows : List InsertionSupport.Row)
    (n : Nat) (replacement : List Nat)
    (hf : (prefix, factor) ∈ Factor.execute greater)
    (hh : heads ∈ Assignment.execute prefix)
    (ha : BranchesSupport.appendCheck factor heads = false)
    (hr : rows ∈ InsertionSupport.executeRows factor heads)
    (hs : Insertion.choose rows = some (n, replacement))
    (hlarge : interpretation 0 (Insertion.firstCode (heads.drop n)) < interpretation 0 factor)
    (hx : xs ∈ Assignment.execute input) (hy : ys ∈ Assignment.execute greater)
    (hl : interpretation 0 prefix < interpretation 0 input)
    (hlt : interpretation 0 input < interpretation 0 greater) :
    List.Lex (· < ·) (xs.map (interpretation 0)) (ys.map (interpretation 0)) := by
  obtain ⟨middle, hm, hb⟩ := FrameFactorOrder.actual_factor_child greater prefix factor ys hf hy
  have hmiddle : middle = heads := Part.mem_unique hm hh
  have hi : ys ∈ Insertion.execute (factor, heads) := by
    simpa only [hmiddle, Branches.execute, ha, Bool.cond_false] using hb
  have hys : ys = Insertion.word rows := Part.mem_unique hi (Part.mem_map Insertion.word hr)
  obtain ⟨before, current, after, hne, hrows, hn, hword, hcover, hnone⟩ :=
    Insertion.choose_spec rows n replacement hs
  have hrelation := InsertionSupport.executeRows_relation factor heads rows hr
  have hheads := InsertionSupport.relation_heads factor hrelation
  have hsplit : heads = before.map Prod.fst ++ current.1 :: after.map Prod.fst := by
    simpa only [hrows, List.map_append, List.map_cons] using hheads.symm
  have hn' : n = (before.map Prod.fst).length := by simpa only [List.length_map] using hn
  have hselected : Insertion.firstCode (heads.drop n) = current.1 := by
    simp only [hsplit, hn', List.drop_left, Insertion.firstCode, List.head?_cons, Option.getD_some]
  have hhead : interpretation 0 current.1 < interpretation 0 factor := by
    simpa only [hselected] using hlarge
  have hfactor := Factor.execute_spec greater (prefix, factor) hf
  have hfLow := ((Theta.acceptedLowCode_iff 0 factor).mp hfactor.2.2.1).1
  have hM := hfactor.2.2.2.2.2.2.1
  have hfactorBound : interpretation 0 factor ≤ interpretation 0 (lastCode heads) :=
    (Factor.Bounds.execute_last_le_prefix_last greater (prefix, factor) hf).trans
      (Assignment.execute_last_bounds prefix heads hh).1
  have hraw := Assignment.execute_tracking prefix heads hh
  have hsource := (SourceTrackingRaw.trackingCheck_exact heads).mp hraw
  have hafter : after.map Prod.fst ≠ [] := by
    intro he
    have hlast : interpretation 0 factor ≤ interpretation 0 current.1 := by
      simpa only [hsplit, he, lastCode_append_singleton] using hfactorBound
    exact hhead.not_ge hlast
  have hprefix := hsource.2.1
  rw [hsplit, InsertionFidelity.stripLast_append_nonempty _ _ (List.cons_ne_nil _ _),
    stripLast_cons_nonempty current.1 _ hafter] at hprefix
  have hproper : current.1 ∈ stripLast heads := by
    rw [hsplit, InsertionFidelity.stripLast_append_nonempty _ _ (List.cons_ne_nil _ _),
      stripLast_cons_nonempty current.1 _ hafter]
    exact List.mem_append_right _ List.mem_cons_self
  have hhRaw := hsource.2.1.nodes current.1 hproper
  have hbeforeNe : before.map Prod.fst ≠ [] := by
    intro he
    exact hne (List.map_eq_nil_iff.mp he)
  have href : SourceTrackingRaw.Reference (before.map Prod.fst ++ [current.1]) :=
    InsertionFidelity.reference_prefix (before.map Prod.fst ++ [current.1])
      (stripLast (after.map Prod.fst))
      (by simpa only [List.append_assoc, List.singleton_append] using hprefix)
  have hstrict : ((before.map Prod.fst).map (interpretation 0) ++
      [interpretation 0 current.1]).Pairwise (· < ·) := by
    simpa only [List.map_append, List.map_singleton] using href.strict
  have hfront := (List.pairwise_append.mp hstrict).2.2 _
    (List.mem_map.mpr ⟨lastCode (before.map Prod.fst), lastCode_mem _ hbeforeNe, rfl⟩)
    _ List.mem_cons_self
  have hcurrentMem : current ∈ rows := by rw [hrows]; exact List.mem_append_right _ List.mem_cons_self
  have hcall := (InsertionSupport.relation_members factor hrelation current hcurrentMem).2
  have hraisedCheck : ConditionalReplacement.raisedCheck current.1 factor = true :=
    (ConditionalReplacement.raisedCheck_exact current.1 factor
      ((SourceTrackingRaw.Support.inputCheck_exact current.1).mp hhRaw).1 hfLow).mpr hhead
  have hraised : current.2 ∈ Replacement.raisedReplacement current.1 factor := by
    simpa only [ConditionalReplacement.execute, hraisedCheck, Bool.cond_true] using hcall
  have hcover' : Insertion.coverCheck (lastCode (before.map Prod.fst))
      (Insertion.firstCode current.2) = true := by simpa only [hword] using hcover
  obtain ⟨frames, bottom, hseg, hbottom, hunwind⟩ :=
    IntervalFrames.execute_interval_frames greater prefix factor input xs hf hx hl hlt
  have heq : bottom = heads := Part.mem_unique hbottom hh
  have htrace : IntervalFrames.Unwind frames heads xs := by simpa only [heq] using hunwind
  have hlex := ContextAccumulation.unwind_lex hseg heads xs (before.map Prod.fst)
    current.1 current.2 hh hraw hproper hbeforeNe hfront hfLow hM hhead hfactorBound
    hraised hcover' ⟨after.map Prod.fst, hsplit⟩ htrace
  have hys' : ys = before.map Prod.fst ++ current.2 := by
    rw [hys, Insertion.word, hs, hn, hrows, List.take_left, hword]
  simpa only [hys'] using hlex

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.RaisedInsertionIntervalOrder
