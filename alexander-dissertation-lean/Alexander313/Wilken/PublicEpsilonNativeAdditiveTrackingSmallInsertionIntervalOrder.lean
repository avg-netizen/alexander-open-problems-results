import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingSmallInsertionIntervalOrderSupport

/-!
# All actual quotient updates below an ordinary selected insertion row

The greater executed scan selects head h with F<=h, so its replacement is
the covered ordinary product h*F. Every actual smaller trace factor is
below F. At the same value cut, the first suffix remains between h and h
times the cumulative quotient. Its next ordinary product is still covered;
the concrete greatest scan retains the cut, even when it selects later.
The terminal prefix agrees in VALUES through actual full-assignment
invariance, not code injection. The genuinely raised selected row F>h
remains separate. Source-only uncompiled original SAME-q candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.SmallInsertionIntervalOrder

open PublicEpsilonUnboundedIota SmallInsertionIntervalOrderSupport
open SourceTrackingSequences (lastCode lastCode_mem)
open Alexander313.Wilken.MultiplicativeNormalForm MultiplicativePrincipalArithmetic

/-- The real trace retains a VALUE cut with a bounded FIRST, regardless
of the actual later suffix and its raw spellings. -/
theorem segment_small_cut {q greater prefix factor current : Nat}
    {frames : List IntervalFrames.Frame}
    (hseg : IntervalFrames.Segment q prefix factor current frames)
    (hf : (prefix, factor) ∈ Factor.execute q greater)
    (heads : List Nat) (hbase : heads ∈ Assignment.execute q prefix)
    (before : List Nat) (head : Nat) (after : List Nat)
    (hsplit : heads = before ++ head :: after) (hne : before ≠ [])
    (hroot : SourceTrackingRaw.Support.inputCheck q (lastCode before) = true)
    (hsmall : interpretation q factor ≤ interpretation q head)
    (hcover : interpretation q head * interpretation q factor ≤
      SourceTrackingRaw.Support.muValue q (lastCode before))
    (out : List Nat) (ho : out ∈ Assignment.execute q current) :
    ∃ first : Ordinal.{0}, ∃ tail : List Ordinal.{0},
      out.map (interpretation q) = before.map (interpretation q) ++ first :: tail ∧
      interpretation q head ≤ first ∧
      first ≤ interpretation q head * (interpretation q current / interpretation q prefix) := by
  have htrack := Assignment.execute_tracking q prefix heads hbase
  have hheadMem : head ∈ heads := by rw [hsplit]; exact List.mem_append_right _ List.mem_cons_self
  have hheadPos := (ConditionalReplacement.tracking_member_principal q heads htrack head hheadMem).2.1
  obtain ⟨_, hprefixLow, _, _, _, _, hprefixBase, _, _, _, _, _, _⟩ :=
    Factor.execute_spec q greater (prefix, factor) hf
  have hprefixPos := (base_pos q (HeightBoundary.input_spec q prefix hprefixLow).2.1).trans_le hprefixBase
  revert out
  induction hseg with
  | nil terminal hv =>
    intro out ho
    have hout := Assignment.ValueInvariance.execute_values_eq q terminal prefix out heads ho hbase hv
    refine ⟨interpretation q head, after.map (interpretation q), ?_, le_rfl, ?_⟩
    · simpa only [hsplit, List.map_append, List.map_cons] using hout
    · simpa only [hv, Ordinal.div_self (ne_of_gt hprefixPos), mul_one] using
        (le_rfl : interpretation q head ≤ interpretation q head)
  | cons current child last frames hs hlastSmall ht ih =>
    intro out ho
    obtain ⟨middle, hh, hb⟩ := IntervalFactors.actual_factor_child q current child last out hs ho
    obtain ⟨_, _, _, hlow, _, _, _, _, hm, _, _, _, _⟩ :=
      Factor.execute_spec q current (child, last) hs
    obtain ⟨first, tail, hmiddleValues, hfirstLower, hfirstUpper⟩ := ih middle hh
    obtain ⟨earlier, suffix, hmiddle, hearlier, hsuffix⟩ := List.map_eq_append_iff.mp hmiddleValues
    obtain ⟨writtenFirst, writtenTail, hsuffixShape, hfirst, htail⟩ := List.map_eq_cons_iff.mp hsuffix
    have hfirstLower' : interpretation q head ≤ interpretation q writtenFirst := by
      simpa only [hfirst] using hfirstLower
    have hshape : middle = earlier ++ writtenFirst :: writtenTail := by
      simpa only [hsuffixShape] using hmiddle
    have hearlierNe : earlier ≠ [] := by
      intro he
      have hn : before.map (interpretation q) = [] := by
        simpa only [he, List.map_nil] using hearlier.symm
      exact hne (List.map_eq_nil_iff.mp hn)
    have hmiddleTrack : SourceTrackingRaw.trackingCheck q (earlier ++ writtenFirst :: writtenTail) = true := by
      simpa only [hshape] using Assignment.execute_tracking q child middle hh
    have hreference := InsertionFidelitySupport.tracking_prefix_reference q middle earlier
      writtenFirst writtenTail (Assignment.execute_tracking q child middle hh) hshape
    have hearlierRoot := hreference.nodes _ (lastCode_mem earlier hearlierNe)
    have hlastValues := SourceAdditiveTrackingWordBounds.lastCode_values_eq
      (interpretation q) (interpretation q) earlier before hearlierNe hearlier
    have hmu := SourceTrackingRaw.Support.muValue_invariant q (lastCode earlier) (lastCode before)
      hearlierRoot hroot hlastValues
    have hchildQ := (IntervalFrameProducts.segment_actual_quotient q greater prefix factor child frames hf ht).1
    have hcurrentQ := IntervalFrameProducts.segment_actual_quotient q greater prefix factor current
      ((current, (child, last)) :: frames) hf (.cons current child last frames hs hlastSmall ht)
    have hquotientProduct : (interpretation q child / interpretation q prefix) * interpretation q last =
        interpretation q current / interpretation q prefix := by
      rw [hcurrentQ.1, hchildQ]
      simp only [List.reverse_cons, List.map_append, List.map_singleton,
        factorProduct_append, factorProduct, mul_one]
    have hquotientLt : interpretation q current / interpretation q prefix < interpretation q factor :=
      hcurrentQ.1.trans_lt hcurrentQ.2
    have hproductBound : interpretation q writtenFirst * interpretation q last ≤
        interpretation q head * (interpretation q current / interpretation q prefix) := by
      calc
        interpretation q writtenFirst * interpretation q last ≤
            (interpretation q head * (interpretation q child / interpretation q prefix)) *
              interpretation q last := mul_le_mul_left (by simpa only [hfirst] using hfirstUpper) _
        _ = interpretation q head * (interpretation q current / interpretation q prefix) := by
          rw [mul_assoc, hquotientProduct]
    have hcoverNow : interpretation q writtenFirst * interpretation q last ≤
        SourceTrackingRaw.Support.muValue q (lastCode earlier) := by
      rw [hmu]
      exact (hproductBound.trans ((Ordinal.isNormal_mul_right hheadPos).strictMono hquotientLt).le).trans hcover
    have hsmallNow : interpretation q last ≤ interpretation q writtenFirst := by
      rw [hfirst]
      exact hlastSmall.le.trans (hsmall.trans hfirstLower)
    have hbound := (Factor.Bounds.execute_last_le_prefix_last q current (child, last) hs).trans
      (Assignment.execute_spec q child middle hh).2.1.2.2.1
    have hbound' : interpretation q last ≤ interpretation q (lastCode (earlier ++ writtenFirst :: writtenTail)) := by
      simpa only [hshape] using hbound
    have hb' : out ∈ Branches.execute ((q, last), earlier ++ writtenFirst :: writtenTail) := by
      simpa only [hshape] using hb
    obtain ⟨next, rest, hout, hvalue⟩ := branches_small_cut q earlier writtenFirst last writtenTail out
      hearlierNe hmiddleTrack hearlierRoot hlow hm hbound' hsmallNow hcoverNow hb'
    refine ⟨interpretation q next, rest.map (interpretation q), ?_, ?_, ?_⟩
    · simp only [hout, List.map_append, List.map_cons, hearlier]
    · rcases hvalue with hvalue | hvalue
      · rw [hvalue, hfirst]; exact hfirstLower
      · rw [hvalue]
        exact hfirstLower'.trans (Ordinal.le_mul_left _ hm.1)
    · rcases hvalue with hvalue | hvalue
      · rw [hvalue]; exact (Ordinal.le_mul_left _ hm.1).trans hproductBound
      · rw [hvalue]; exact hproductBound

/-- The observed actual selected row is ordinary. Its covered product
dominates every smaller interval execution, with no restriction on child
length, selected position or the suffix emitted by intervening updates. -/
theorem execute_small_selected_interval_lex (q greater prefix factor input : Nat)
    (heads xs ys : List Nat) (rows : List InsertionSupport.Row) (n : Nat) (replacement : List Nat)
    (hf : (prefix, factor) ∈ Factor.execute q greater)
    (hh : heads ∈ Assignment.execute q prefix)
    (ha : BranchesSupport.appendCheck q factor heads = false)
    (hr : rows ∈ InsertionSupport.executeRows q factor heads)
    (hs : Insertion.choose q rows = some (n, replacement))
    (hsmall : interpretation q factor ≤ interpretation q (Insertion.firstCode (heads.drop n)))
    (hx : xs ∈ Assignment.execute q input) (hy : ys ∈ Assignment.execute q greater)
    (hl : interpretation q prefix < interpretation q input)
    (hlt : interpretation q input < interpretation q greater) :
    List.Lex (· < ·) (xs.map (interpretation q)) (ys.map (interpretation q)) := by
  obtain ⟨middle, hm, hb⟩ := IntervalFactors.actual_factor_child q greater prefix factor ys hf hy
  have hmiddle : middle = heads := Part.mem_unique hm hh
  have hi : ys ∈ Insertion.execute ((q, factor), heads) := by
    simpa only [hmiddle, Branches.execute, ha, Bool.cond_false] using hb
  have hys : ys = Insertion.word q rows := Part.mem_unique hi (Part.mem_map (Insertion.word q) hr)
  obtain ⟨before, current, after, hne, hrows, hn, hword, hcover, hnone⟩ :=
    Insertion.choose_spec q rows n replacement hs
  have hrel := InsertionSupport.executeRows_relation q factor heads rows hr
  have hheads := InsertionSupport.relation_heads q factor hrel
  have hsplit : heads = before.map Prod.fst ++ current.1 :: after.map Prod.fst := by
    simpa only [hrows, List.map_append, List.map_cons] using hheads.symm
  have hn' : n = (before.map Prod.fst).length := by simpa only [List.length_map] using hn
  have hselected : Insertion.firstCode (heads.drop n) = current.1 := by
    simp only [hsplit, hn', List.drop_left, Insertion.firstCode, List.head?_cons, Option.getD_some]
  have hsmall' : interpretation q factor ≤ interpretation q current.1 := by simpa only [hselected] using hsmall
  have hcurrentMem : current ∈ rows := by rw [hrows]; exact List.mem_append_right _ List.mem_cons_self
  have hcall := (InsertionSupport.relation_members q factor hrel current hcurrentMem).2
  obtain ⟨_, _, _, hfactorLow, _, _, _, _, hfactorM, _, _, _, _⟩ :=
    Factor.execute_spec q greater (prefix, factor) hf
  have htrack := Assignment.execute_tracking q prefix heads hh
  have hfactorBound := (Factor.Bounds.execute_last_le_prefix_last q greater (prefix, factor) hf).trans
    (Assignment.execute_spec q prefix heads hh).2.1.2.2.1
  obtain ⟨d, hd, hlow, hv⟩ := EpsilonSingletonIntervalOrderSupport.conditional_small q heads htrack
    current.1 factor (by rw [hsplit]; exact List.mem_append_right _ List.mem_cons_self)
    hfactorLow hfactorM hfactorBound hsmall' current.2 hcall
  have hcovered : SourceTrackingRaw.Support.inputCheck q (lastCode (before.map Prod.fst)) = true ∧
      interpretation q current.1 * interpretation q factor ≤
        SourceTrackingRaw.Support.muValue q (lastCode (before.map Prod.fst)) := by
    have hc := (Insertion.coverCheck_exact q _ _).mp hcover
    have hc' : SourceTrackingRaw.Support.inputCheck q (lastCode (before.map Prod.fst)) = true ∧
        lowCheckCode q d = true ∧ interpretation q d ≤
          SourceTrackingRaw.Support.muValue q (lastCode (before.map Prod.fst)) := by
      simpa only [hword, hd, Insertion.firstCode, List.head?_cons, Option.getD_some] using hc
    exact ⟨hc'.1, by rw [← hv]; exact hc'.2.2⟩
  have hbeforeNe : before.map Prod.fst ≠ [] := by intro he; exact hne (List.map_eq_nil_iff.mp he)
  obtain ⟨frames, hseg⟩ := IntervalFrames.interval_segment_returns q greater prefix factor input hf
    (Assignment.execute_spec q input xs hx).1 hl hlt
  obtain ⟨first, tail, hxs, hfirstLower, hfirstUpper⟩ := segment_small_cut hseg hf heads hh
    (before.map Prod.fst) current.1 (after.map Prod.fst) hsplit hbeforeNe
    hcovered.1 hsmall' hcovered.2 xs hx
  have hheadPos := (ConditionalReplacement.tracking_member_principal q heads htrack current.1
    (by rw [hsplit]; exact List.mem_append_right _ List.mem_cons_self)).2.1
  have hq := IntervalFrameProducts.segment_actual_quotient q greater prefix factor input frames hf hseg
  have hquotientLt : interpretation q input / interpretation q prefix < interpretation q factor := hq.1.trans_lt hq.2
  have hfirstLt : first < interpretation q d := by
    rw [hv]
    exact hfirstUpper.trans_lt ((Ordinal.isNormal_mul_right hheadPos).strictMono hquotientLt)
  have hys' : ys = before.map Prod.fst ++ [d] := by
    rw [hys, Insertion.word, hs, hn, hrows, List.take_left, hword, hd]
  have hlex : List.Lex (· < ·) (first :: tail) [interpretation q d] := List.Lex.rel hfirstLt
  simpa only [hxs, hys', List.map_append, List.map_singleton] using
    List.Lex.append_left (· < ·) hlex ((before.map Prod.fst).map (interpretation q))

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.SmallInsertionIntervalOrder
