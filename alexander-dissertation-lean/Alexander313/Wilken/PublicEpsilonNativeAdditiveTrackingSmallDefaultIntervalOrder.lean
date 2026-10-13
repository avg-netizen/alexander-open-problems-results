import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingSmallDefaultIntervalOrderSupport

/-!
# Accumulated comparison with the actual ordinary default row

The greater actual table has no passing transition and F<=its FIRST h.
Every actual trace factor is below F, so the FIRST row remains ordinary.
The real unchanged/product alternatives bound FIRST by h times the whole
cumulative quotient, which is strictly below F. Terminal prefix equality
uses genuine full-assignment VALUES invariance. No singleton suffix,
preceding cover or update inequality is supplied. Raised default and
raised selected rows remain separate. Source-only uncompiled SAME-q.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.SmallDefaultIntervalOrder

open PublicEpsilonUnboundedIota SmallDefaultIntervalOrderSupport
open SourceTrackingSequences (lastCode)
open Alexander313.Wilken.MultiplicativeNormalForm

theorem segment_first_bounds {q greater prefix factor current : Nat}
    {frames : List IntervalFrames.Frame}
    (hseg : IntervalFrames.Segment q prefix factor current frames)
    (hf : (prefix, factor) ∈ Factor.execute q greater)
    (head : Nat) (rest : List Nat) (hbase : head :: rest ∈ Assignment.execute q prefix)
    (hsmall : interpretation q factor ≤ interpretation q head)
    (out : List Nat) (ho : out ∈ Assignment.execute q current) :
    ∃ first : Ordinal.{0}, ∃ tail : List Ordinal.{0},
      out.map (interpretation q) = first :: tail ∧ interpretation q head ≤ first ∧
      first ≤ interpretation q head * (interpretation q current / interpretation q prefix) := by
  obtain ⟨_, hprefixLow, _, _, _, _, hprefixBase, _, _, _, _, _, _⟩ :=
    Factor.execute_spec q greater (prefix, factor) hf
  have hprefixPos := (base_pos q (HeightBoundary.input_spec q prefix hprefixLow).2.1).trans_le hprefixBase
  revert out
  induction hseg with
  | nil terminal hv =>
    intro out ho
    have hout := Assignment.ValueInvariance.execute_values_eq q terminal prefix out (head :: rest) ho hbase hv
    refine ⟨interpretation q head, rest.map (interpretation q), ?_, le_rfl, ?_⟩
    · simpa only [List.map_cons] using hout
    · simpa only [hv, Ordinal.div_self (ne_of_gt hprefixPos), mul_one] using
        (le_rfl : interpretation q head ≤ interpretation q head)
  | cons current child last frames hs hlastSmall ht ih =>
    intro out ho
    obtain ⟨middle, hh, hb⟩ := IntervalFactors.actual_factor_child q current child last out hs ho
    obtain ⟨_, _, _, hlow, _, _, _, _, hm, _, _, _, _⟩ :=
      Factor.execute_spec q current (child, last) hs
    obtain ⟨first, tail, hmiddleValues, hfirstLower, hfirstUpper⟩ := ih middle hh
    obtain ⟨writtenFirst, writtenTail, hshape, hfirst, htail⟩ := List.map_eq_cons_iff.mp hmiddleValues
    have hfirstLower' : interpretation q head ≤ interpretation q writtenFirst := by
      simpa only [hfirst] using hfirstLower
    have hchildQ := (IntervalFrameProducts.segment_actual_quotient q greater prefix factor child frames hf ht).1
    have hcurrentQ := (IntervalFrameProducts.segment_actual_quotient q greater prefix factor current
      ((current, (child, last)) :: frames) hf (.cons current child last frames hs hlastSmall ht)).1
    have hquotientProduct : (interpretation q child / interpretation q prefix) * interpretation q last =
        interpretation q current / interpretation q prefix := by
      rw [hcurrentQ, hchildQ]
      simp only [List.reverse_cons, List.map_append, List.map_singleton,
        factorProduct_append, factorProduct, mul_one]
    have hproductBound : interpretation q writtenFirst * interpretation q last ≤
        interpretation q head * (interpretation q current / interpretation q prefix) := by
      calc
        interpretation q writtenFirst * interpretation q last ≤
            (interpretation q head * (interpretation q child / interpretation q prefix)) *
              interpretation q last := mul_le_mul_left (by simpa only [hfirst] using hfirstUpper) _
        _ = interpretation q head * (interpretation q current / interpretation q prefix) := by
          rw [mul_assoc, hquotientProduct]
    have hmiddleTrack : SourceTrackingRaw.trackingCheck q (writtenFirst :: writtenTail) = true := by
      simpa only [hshape] using Assignment.execute_tracking q child middle hh
    have hbound := (Factor.Bounds.execute_last_le_prefix_last q current (child, last) hs).trans
      (Assignment.execute_spec q child middle hh).2.1.2.2.1
    have hbound' : interpretation q last ≤ interpretation q (lastCode (writtenFirst :: writtenTail)) := by
      simpa only [hshape] using hbound
    have hb' : out ∈ Branches.execute ((q, last), writtenFirst :: writtenTail) := by
      simpa only [hshape] using hb
    obtain ⟨next, more, hout, hvalue⟩ := branches_small_first q writtenFirst last writtenTail out
      hmiddleTrack hlow hm hbound' (hlastSmall.le.trans (hsmall.trans hfirstLower')) hb'
    refine ⟨interpretation q next, more.map (interpretation q), ?_, ?_, ?_⟩
    · simp only [hout, List.map_cons]
    · rcases hvalue with hv | hv
      · rw [hv]; exact hfirstLower'
      · rw [hv]; exact hfirstLower'.trans (Ordinal.le_mul_left _ hm.1)
    · rcases hvalue with hv | hv
      · rw [hv]; exact (Ordinal.le_mul_left _ hm.1).trans hproductBound
      · rw [hv]; exact hproductBound

/-- Observed NONE and the ordinary FIRST test derive strict comparison
with every smaller input in the actual greater factor interval. -/
theorem execute_small_default_interval_lex (q greater prefix factor input : Nat)
    (heads xs ys : List Nat) (rows : List InsertionSupport.Row)
    (hf : (prefix, factor) ∈ Factor.execute q greater)
    (hh : heads ∈ Assignment.execute q prefix)
    (ha : BranchesSupport.appendCheck q factor heads = false)
    (hr : rows ∈ InsertionSupport.executeRows q factor heads)
    (hs : Insertion.choose q rows = none)
    (hsmall : interpretation q factor ≤ interpretation q (Insertion.firstCode heads))
    (hx : xs ∈ Assignment.execute q input) (hy : ys ∈ Assignment.execute q greater)
    (hl : interpretation q prefix < interpretation q input)
    (hlt : interpretation q input < interpretation q greater) :
    List.Lex (· < ·) (xs.map (interpretation q)) (ys.map (interpretation q)) := by
  obtain ⟨head, rest, hheads⟩ := List.exists_cons_of_ne_nil (Assignment.execute_nonempty q prefix heads hh)
  have hbase : head :: rest ∈ Assignment.execute q prefix := by simpa only [hheads] using hh
  have hsmall' : interpretation q factor ≤ interpretation q head := by
    simpa only [hheads, Insertion.firstCode, List.head?_cons, Option.getD_some] using hsmall
  obtain ⟨middle, hm, hb⟩ := IntervalFactors.actual_factor_child q greater prefix factor ys hf hy
  have hmiddle : middle = heads := Part.mem_unique hm hh
  have hi : ys ∈ Insertion.execute ((q, factor), heads) := by
    simpa only [hmiddle, Branches.execute, ha, Bool.cond_false] using hb
  have hys : ys = Insertion.word q rows := Part.mem_unique hi (Part.mem_map (Insertion.word q) hr)
  have hrel := InsertionSupport.executeRows_relation q factor heads rows hr
  rw [hheads] at hrel
  obtain ⟨a, after, hmatch, ht, hrows⟩ := List.forall₂_cons_left_iff.mp hrel
  obtain ⟨_, _, _, hfactorLow, _, _, _, _, hfactorM, _, _, _, _⟩ :=
    Factor.execute_spec q greater (prefix, factor) hf
  have htrack := Assignment.execute_tracking q prefix _ hbase
  have hfactorBound := (Factor.Bounds.execute_last_le_prefix_last q greater (prefix, factor) hf).trans
    (Assignment.execute_spec q prefix _ hbase).2.1.2.2.1
  obtain ⟨d, hd, hc, hv⟩ := EpsilonSingletonIntervalOrderSupport.conditional_small q
    (head :: rest) htrack head factor List.mem_cons_self hfactorLow hfactorM hfactorBound hsmall' a.2 hmatch.2
  have hs' : Insertion.choose q (a :: after) = none := by simpa only [hrows] using hs
  have hout : ys = [d] := hys.trans ((congrArg (Insertion.word q) hrows).trans
    ((Insertion.word_default q a after hs').1.trans hd))
  obtain ⟨frames, hseg⟩ := IntervalFrames.interval_segment_returns q greater prefix factor input hf
    (Assignment.execute_spec q input xs hx).1 hl hlt
  obtain ⟨first, tail, hxs, hfirstLower, hfirstUpper⟩ := segment_first_bounds hseg hf head rest hbase hsmall' xs hx
  have hheadPos := (ConditionalReplacement.tracking_member_principal q (head :: rest)
    htrack head List.mem_cons_self).2.1
  have hq := IntervalFrameProducts.segment_actual_quotient q greater prefix factor input frames hf hseg
  have hfirstLt : first < interpretation q d := by
    rw [hv]
    exact hfirstUpper.trans_lt ((Ordinal.isNormal_mul_right hheadPos).strictMono (hq.1.trans_lt hq.2))
  simpa only [hxs, hout, List.map_cons, List.map_nil] using
    (List.Lex.rel hfirstLt : List.Lex (· < ·) (first :: tail) [interpretation q d])

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.SmallDefaultIntervalOrder
