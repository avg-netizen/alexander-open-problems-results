import Alexander313.Wilken.SourceOneNativeAdditiveTrackingSmallDefaultIntervalOrderSupport

/-!
# All accumulated updates below the actual ordinary default row

The independently executed greater table has no passing transition and
its first written head h satisfies F<=h. Its genuine output is [h*F].
Every actual smaller factor is below F, so each actual FIRST remains an
ordinary row. The proven unchanged/product alternatives maintain FIRST
between h and h times the genuine accumulated quotient; since that
quotient is below F, strict whole-word Lex follows at FIRST alone.
No preceding cover, universal singleton shape or update bound is supplied.
Raised default rows remain separate. Source-only uncompiled check zero.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.SmallDefaultIntervalOrder

open SmallDefaultIntervalOrderSupport

/-- Every genuine reverse update bounds FIRST, regardless of whether
the actual scan uses the default, retains a later cut, or appends its factor. -/
theorem segment_first_bounds {greater prefix factor current : Nat}
    {frames : List IntervalFrames.Frame}
    (hseg : IntervalFrames.Segment prefix factor current frames)
    (hf : (prefix, factor) ∈ Factor.execute greater)
    (head : Nat) (rest : List Nat) (hbase : head :: rest ∈ Assignment.execute prefix)
    (hsmall : interpretation 0 factor ≤ interpretation 0 head)
    (hr : interpretation 0 current < interpretation 0 greater)
    (out : List Nat) (ho : out ∈ Assignment.execute current) :
    ∃ first tail, out = first :: tail ∧ interpretation 0 head ≤ interpretation 0 first ∧
      interpretation 0 first ≤ interpretation 0 head *
        (interpretation 0 current / interpretation 0 prefix) := by
  have hprefixInput := (Factor.execute_spec greater (prefix, factor) hf).2.2.2.1
  have hprefixSpec := (Assignment.inputCheck_exact prefix).mp hprefixInput
  have hprefixPos := Order.one_le_iff_pos.mp hprefixSpec.2.1
  revert hr out
  induction hseg with
  | nil =>
    intro hr out ho
    have hout : out = head :: rest := Part.mem_unique ho hbase
    refine ⟨head, rest, hout, le_rfl, ?_⟩
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
    have hmiddleTrack : SourceTrackingRaw.trackingCheck (first :: tail) = true := by
      simpa only [hmiddle] using Assignment.execute_tracking child middle hh
    have hb' : out ∈ Branches.execute (last, first :: tail) := by
      simpa only [hmiddle] using hb
    obtain ⟨next, more, hout, hvalue⟩ := branches_small_first first last tail out hmiddleTrack
      ((Theta.acceptedLowCode_iff 0 last).mp hlow).1
      (hlastSmall.le.trans (hsmall.trans hfirstLower)) hb'
    refine ⟨next, more, hout, ?_, ?_⟩
    · rcases hvalue with hv | hv
      · rw [hv]; exact hfirstLower
      · rw [hv]; exact hfirstLower.trans (Ordinal.le_mul_left _ hm.1)
    · rcases hvalue with hv | hv
      · rw [hv]; exact (Ordinal.le_mul_left _ hm.1).trans hproductBound
      · rw [hv]; exact hproductBound

/-- NoCover is observed from the real table computation. The actual
ordinary first-row test suffices for strict comparison with every smaller
input in the genuine factor interval, without any child-length restriction. -/
theorem execute_small_default_interval_lex (greater prefix factor input : Nat)
    (heads xs ys : List Nat) (rows : List InsertionSupport.Row)
    (hf : (prefix, factor) ∈ Factor.execute greater)
    (hh : heads ∈ Assignment.execute prefix)
    (ha : BranchesSupport.appendCheck factor heads = false)
    (hr : rows ∈ InsertionSupport.executeRows factor heads)
    (hs : Insertion.choose rows = none)
    (hsmall : interpretation 0 factor ≤ interpretation 0 (Insertion.firstCode heads))
    (hx : xs ∈ Assignment.execute input) (hy : ys ∈ Assignment.execute greater)
    (hl : interpretation 0 prefix < interpretation 0 input)
    (hlt : interpretation 0 input < interpretation 0 greater) :
    List.Lex (· < ·) (xs.map (interpretation 0)) (ys.map (interpretation 0)) := by
  obtain ⟨head, rest, hheads⟩ := List.exists_cons_of_ne_nil (Assignment.execute_nonempty prefix heads hh)
  have hbase : head :: rest ∈ Assignment.execute prefix := by simpa only [hheads] using hh
  have hsmall' : interpretation 0 factor ≤ interpretation 0 head := by
    simpa only [hheads, Insertion.firstCode, List.head?_cons, Option.getD_some] using hsmall
  obtain ⟨middle, hm, hb⟩ := FrameFactorOrder.actual_factor_child greater prefix factor ys hf hy
  have hmiddle : middle = heads := Part.mem_unique hm hh
  have hi : ys ∈ Insertion.execute (factor, heads) := by
    simpa only [hmiddle, Branches.execute, ha, Bool.cond_false] using hb
  have hys : ys = Insertion.word rows := Part.mem_unique hi (Part.mem_map Insertion.word hr)
  have hrel := InsertionSupport.executeRows_relation factor heads rows hr
  rw [hheads] at hrel
  obtain ⟨a, after, hmatch, ht, hrows⟩ := List.forall₂_cons_left_iff.mp hrel
  have hlow := (ConditionalReplacement.tracking_member_principal (head :: rest)
    (Assignment.execute_tracking prefix _ hbase) head List.mem_cons_self).1
  have hfactorLow := ((Theta.acceptedLowCode_iff 0 factor).mp
    (Factor.execute_spec greater (prefix, factor) hf).2.2.1).1
  obtain ⟨d, hd, hc, hv⟩ := EpsilonSingletonIntervalOrderSupport.conditional_small
    head factor a.2 hlow hfactorLow hsmall' hmatch.2
  have hs' : Insertion.choose (a :: after) = none := by simpa only [hrows] using hs
  have hout : ys = [d] := hys.trans ((congrArg Insertion.word hrows).trans
    ((Insertion.word_default a after hs').1.trans hd))
  obtain ⟨frames, hseg⟩ := IntervalFrames.interval_segment_returns greater prefix factor input hf
    (Assignment.execute_spec input xs hx).1 hl hlt
  obtain ⟨first, tail, hxs, hfirstLower, hfirstUpper⟩ :=
    segment_first_bounds hseg hf head rest hbase hsmall' hlt xs hx
  have hheadPos := (ConditionalReplacement.tracking_member_principal (head :: rest)
    (Assignment.execute_tracking prefix _ hbase) head List.mem_cons_self).2.1
  have hq := EpsilonSingletonIntervalOrder.quotient_bounds greater prefix factor input hf
    (Assignment.execute_spec input xs hx).1 hl hlt
  have hfirstLt : interpretation 0 first < interpretation 0 d := by
    rw [hv]
    exact hfirstUpper.trans_lt ((Ordinal.isNormal_mul_right hheadPos).strictMono hq.2.1)
  simpa only [hxs, hout, List.map_cons, List.map_nil] using
    (List.Lex.rel hfirstLt : List.Lex (· < ·)
      (interpretation 0 first :: tail.map (interpretation 0)) [interpretation 0 d])

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.SmallDefaultIntervalOrder
