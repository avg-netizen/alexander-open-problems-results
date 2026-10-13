import Alexander313.Wilken.SourceOneNativeAdditiveTrackingSmallInsertionIntervalOrderSupport

/-!
# All accumulated updates below an actual ordinary selected row

The greater actual insertion selects its written head h with factor F<=h.
Its ordinary product h*F is covered by the preceding original epsilon.
Every real smaller factor is below F, and the first suffix value stays
between h and h times the accumulated quotient. Its next ordinary product
is therefore still covered at the same literal cut. The true scan may
select later rows; the proven first-suffix alternative handles both cases.
Genuine factor descent derives every update and the final strict Lex.
The genuinely raised selected-row class F>h remains separate. Original
source check zero throughout; source-only uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.SmallInsertionIntervalOrder

open SmallInsertionIntervalOrderSupport
open NativeContext.SourceTrackingSequences (lastCode)

/-- No suffix shape is assumed. Real reverse factor updates retain the
original cut and bound their FIRST by the genuine current quotient. -/
theorem segment_small_cut {greater prefix factor current : Nat}
    {frames : List IntervalFrames.Frame}
    (hseg : IntervalFrames.Segment prefix factor current frames)
    (hf : (prefix, factor) ∈ Factor.execute greater)
    (heads : List Nat) (hbase : heads ∈ Assignment.execute prefix)
    (before : List Nat) (head : Nat) (after : List Nat)
    (hsplit : heads = before ++ head :: after) (hne : before ≠ [])
    (hroot : SourceTrackingRaw.Support.inputCheck (lastCode before) = true)
    (hsmall : interpretation 0 factor ≤ interpretation 0 head)
    (hcover : interpretation 0 head * interpretation 0 factor ≤
      SourceTrackingRaw.Support.muValue (lastCode before))
    (hr : interpretation 0 current < interpretation 0 greater)
    (out : List Nat) (ho : out ∈ Assignment.execute current) :
    ∃ first tail, out = before ++ first :: tail ∧
      interpretation 0 head ≤ interpretation 0 first ∧
      interpretation 0 first ≤ interpretation 0 head *
        (interpretation 0 current / interpretation 0 prefix) := by
  have htrack := Assignment.execute_tracking prefix heads hbase
  have hheadMem : head ∈ heads := by rw [hsplit]; exact List.mem_append_right _ List.mem_cons_self
  have hheadPos := (ConditionalReplacement.tracking_member_principal heads htrack head hheadMem).2.1
  have hprefixInput := (Factor.execute_spec greater (prefix, factor) hf).2.2.2.1
  have hprefixSpec := (Assignment.inputCheck_exact prefix).mp hprefixInput
  have hprefixPos := Order.one_le_iff_pos.mp hprefixSpec.2.1
  revert hr out
  induction hseg with
  | nil =>
    intro hr out ho
    have hout : out = heads := Part.mem_unique ho hbase
    refine ⟨head, after, hout.trans hsplit, le_rfl, ?_⟩
    have hdiv : interpretation 0 prefix / interpretation 0 prefix = 1 := by
      simpa only [mul_one] using Ordinal.mul_div_cancel 1 (ne_of_gt hprefixPos)
    simpa only [hdiv, mul_one] using (le_rfl : interpretation 0 head ≤ interpretation 0 head)
  | cons current child last frames hs hlastSmall ht ih =>
    intro hr out ho
    obtain ⟨middle, hh, hb⟩ := FrameFactorOrder.actual_factor_child current child last out hs ho
    obtain ⟨_, _, hlow, hchildInput, _, hchildLt, hm, hone, hproduct, _, _⟩ :=
      Factor.execute_spec current (child, last) hs
    obtain ⟨first, tail, hmiddle, hfirstLower, hfirstUpper⟩ :=
      ih (hchildLt.trans hr) middle hh
    have hfloor := SingletonIntervalOrder.segment_input_floor ht
    have hl := hfloor.trans_lt hchildLt
    have hc := (Assignment.execute_spec current out ho).1
    have hq := EpsilonSingletonIntervalOrder.quotient_bounds greater prefix factor current hf hc hl hr
    have hchildAdd := ((Assignment.inputCheck_exact child).mp hchildInput).2.2
    have hpc := MultiplicativePrincipalInterval.principal_quotient_spec hprefixPos
      hprefixSpec.2.2 hchildAdd hfloor
    have hresidual : (interpretation 0 child / interpretation 0 prefix) * interpretation 0 last =
        interpretation 0 current / interpretation 0 prefix := by
      calc
        (interpretation 0 child / interpretation 0 prefix) * interpretation 0 last =
            (interpretation 0 prefix *
              ((interpretation 0 child / interpretation 0 prefix) * interpretation 0 last)) /
                interpretation 0 prefix := (Ordinal.mul_div_cancel _ (ne_of_gt hprefixPos)).symm
        _ = interpretation 0 current / interpretation 0 prefix := by
          rw [← mul_assoc, hpc.2.2, ← hproduct]
    have hproductBound : interpretation 0 first * interpretation 0 last ≤
        interpretation 0 head * (interpretation 0 current / interpretation 0 prefix) := by
      calc
        interpretation 0 first * interpretation 0 last ≤
            (interpretation 0 head * (interpretation 0 child / interpretation 0 prefix)) *
              interpretation 0 last := mul_le_mul_left hfirstUpper _
        _ = interpretation 0 head * (interpretation 0 current / interpretation 0 prefix) := by
          rw [mul_assoc, hresidual]
    have hcoverNow : interpretation 0 first * interpretation 0 last ≤
        SourceTrackingRaw.Support.muValue (lastCode before) :=
      (hproductBound.trans ((Ordinal.isNormal_mul_right hheadPos).strictMono hq.2.1).le).trans hcover
    have hsmallNow : interpretation 0 last ≤ interpretation 0 first :=
      hlastSmall.le.trans (hsmall.trans hfirstLower)
    have hmiddleTrack : SourceTrackingRaw.trackingCheck (before ++ first :: tail) = true := by
      simpa only [hmiddle] using Assignment.execute_tracking child middle hh
    have hb' : out ∈ Branches.execute (last, before ++ first :: tail) := by
      simpa only [hmiddle] using hb
    obtain ⟨next, rest, hout, hvalue⟩ := branches_small_cut before first last tail out hne
      hmiddleTrack hroot ((Theta.acceptedLowCode_iff 0 last).mp hlow).1 hsmallNow hcoverNow hb'
    refine ⟨next, rest, hout, ?_, ?_⟩
    · rcases hvalue with hvalue | hvalue
      · rw [hvalue]; exact hfirstLower
      · rw [hvalue]
        exact hfirstLower.trans (Ordinal.le_mul_left _ hm.1)
    · rcases hvalue with hvalue | hvalue
      · rw [hvalue]
        exact (Ordinal.le_mul_left _ hm.1).trans hproductBound
      · rw [hvalue]; exact hproductBound

/-- The observed selected position identifies the actual written head.
When its computed factor is no greater than that head, every smaller
interval input is strictly ordered against the independently executed
greater output. Earlier and later actual rows need no shape restriction. -/
theorem execute_small_selected_interval_lex (greater prefix factor input : Nat)
    (heads xs ys : List Nat) (rows : List InsertionSupport.Row)
    (n : Nat) (replacement : List Nat)
    (hf : (prefix, factor) ∈ Factor.execute greater)
    (hh : heads ∈ Assignment.execute prefix)
    (ha : BranchesSupport.appendCheck factor heads = false)
    (hr : rows ∈ InsertionSupport.executeRows factor heads)
    (hs : Insertion.choose rows = some (n, replacement))
    (hsmall : interpretation 0 factor ≤ interpretation 0 (Insertion.firstCode (heads.drop n)))
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
  have hrel := InsertionSupport.executeRows_relation factor heads rows hr
  have hheads := InsertionSupport.relation_heads factor hrel
  have hsplit : heads = before.map Prod.fst ++ current.1 :: after.map Prod.fst := by
    simpa only [hrows, List.map_append, List.map_cons] using hheads.symm
  have hn' : n = (before.map Prod.fst).length := by simpa only [List.length_map] using hn
  have hselected : Insertion.firstCode (heads.drop n) = current.1 := by
    simp only [hsplit, hn', List.drop_left, Insertion.firstCode,
      List.head?_cons, Option.getD_some]
  have hsmall' : interpretation 0 factor ≤ interpretation 0 current.1 := by
    simpa only [hselected] using hsmall
  have hcurrentMem : current ∈ rows := by rw [hrows]; exact List.mem_append_right _ List.mem_cons_self
  have hcall := (InsertionSupport.relation_members factor hrel current hcurrentMem).2
  have hheadLow := (ConditionalReplacement.tracking_member_principal heads
    (Assignment.execute_tracking prefix heads hh) current.1
    (by rw [hsplit]; exact List.mem_append_right _ List.mem_cons_self)).1
  have hfactorLow := ((Theta.acceptedLowCode_iff 0 factor).mp
    (Factor.execute_spec greater (prefix, factor) hf).2.2.1).1
  obtain ⟨d, hd, hchecked, hv⟩ := EpsilonSingletonIntervalOrderSupport.conditional_small
    current.1 factor current.2 hheadLow hfactorLow hsmall' hcall
  have hcovered : SourceTrackingRaw.Support.inputCheck (lastCode (before.map Prod.fst)) = true ∧
      interpretation 0 current.1 * interpretation 0 factor ≤
        SourceTrackingRaw.Support.muValue (lastCode (before.map Prod.fst)) := by
    have hc := (Insertion.coverCheck_exact _ _).mp hcover
    have hc' : SourceTrackingRaw.Support.inputCheck (lastCode (before.map Prod.fst)) = true ∧
        lowCheckCode 0 d = true ∧ interpretation 0 d ≤
          SourceTrackingRaw.Support.muValue (lastCode (before.map Prod.fst)) := by
      simpa only [hword, hd, Insertion.firstCode, List.head?_cons, Option.getD_some] using hc
    exact ⟨hc'.1, by rw [← hv]; exact hc'.2.2⟩
  have hbeforeNe : before.map Prod.fst ≠ [] := by
    intro he
    exact hne (List.map_eq_nil_iff.mp he)
  obtain ⟨frames, hseg⟩ := IntervalFrames.interval_segment_returns greater prefix factor input hf
    (Assignment.execute_spec input xs hx).1 hl hlt
  obtain ⟨first, tail, hxs, hfirstLower, hfirstUpper⟩ := segment_small_cut hseg hf heads hh
    (before.map Prod.fst) current.1 (after.map Prod.fst) hsplit hbeforeNe
    hcovered.1 hsmall' hcovered.2 hlt xs hx
  have hheadPos := (ConditionalReplacement.tracking_member_principal heads
    (Assignment.execute_tracking prefix heads hh) current.1
    (by rw [hsplit]; exact List.mem_append_right _ List.mem_cons_self)).2.1
  have hq := EpsilonSingletonIntervalOrder.quotient_bounds greater prefix factor input hf
    (Assignment.execute_spec input xs hx).1 hl hlt
  have hfirstLt : interpretation 0 first < interpretation 0 d := by
    rw [hv]
    exact hfirstUpper.trans_lt ((Ordinal.isNormal_mul_right hheadPos).strictMono hq.2.1)
  have hys' : ys = before.map Prod.fst ++ [d] := by
    rw [hys, Insertion.word, hs, hn, hrows, List.take_left, hword, hd]
  have hlex : List.Lex (· < ·) (interpretation 0 first :: tail.map (interpretation 0))
      [interpretation 0 d] := List.Lex.rel hfirstLt
  simpa only [hxs, hys', List.map_append, List.map_cons, List.map_singleton] using
    List.Lex.append_left (· < ·) hlex ((before.map Prod.fst).map (interpretation 0))

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.SmallInsertionIntervalOrder
