import Alexander313.Wilken.SourceOneNativeAdditiveTrackingAppendIntervalOrderSupport

/-!
# Genuine interval order at an arbitrary actual append child word

The greater actual append flag supplies a covered final epsilon of its
independently executed recursive child word. Every smaller residual is
strictly below the greater factor and hence below that final head. The
real last-row product remains covered, so greatest insertion retains all
literal original heads throughout every actual smaller factor frame.
The final residual quotient is strictly smaller than the greater factor.
No restriction on the child word's length, selected index or accumulated
update inequality is supplied. Greater insertion remains separate.
Original source check zero is retained. Source-only uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.AppendIntervalOrder

open AppendIntervalOrderSupport
open NativeContext.SourceTrackingSequences (lastCode)
open Alexander313.Wilken.MultiplicativeNormalForm MultiplicativePrincipalArithmetic

/-- On the true greater append branch, every real accumulated smaller
update retains the entire independently executing original child word. -/
theorem segment_append_shape {greater prefix factor current : Nat}
    {frames : List IntervalFrames.Frame}
    (hseg : IntervalFrames.Segment prefix factor current frames)
    (hf : (prefix, factor) ∈ Factor.execute greater)
    (heads : List Nat) (hbase : heads ∈ Assignment.execute prefix)
    (ha : BranchesSupport.appendCheck factor heads = true)
    (hr : interpretation 0 current < interpretation 0 greater)
    (out : List Nat) (ho : out ∈ Assignment.execute current) :
    (current = prefix ∧ out = heads) ∨
      ∃ d, out = heads ++ [d] ∧ 1 < interpretation 0 d ∧
        interpretation 0 d = interpretation 0 current / interpretation 0 prefix := by
  have htrack := Assignment.execute_tracking prefix heads hbase
  have hne := Assignment.execute_nonempty prefix heads hbase
  have happend := (BranchesSupport.appendCheck_exact factor heads htrack).mp ha
  have hprefixInput := (Factor.execute_spec greater (prefix, factor) hf).2.2.2.1
  have hprefixSpec := (Assignment.inputCheck_exact prefix).mp hprefixInput
  have hprefixPos : 0 < interpretation 0 prefix := Order.one_le_iff_pos.mp hprefixSpec.2.1
  have hfactorLast : interpretation 0 factor ≤ interpretation 0 (lastCode heads) :=
    (Factor.Bounds.execute_last_le_prefix_last greater (prefix, factor) hf).trans
      (Assignment.execute_spec prefix heads hbase).2.1.2.2.1
  revert hr out
  induction hseg with
  | nil =>
    intro hr out ho
    exact Or.inl ⟨rfl, Part.mem_unique ho hbase⟩
  | cons current child last frames hs hsmall ht ih =>
    intro hr out ho
    obtain ⟨middle, hh, hb⟩ := FrameFactorOrder.actual_factor_child current child last out hs ho
    obtain ⟨_, _, hlow, hchildInput, _, hchildLt, hm, hone, hproduct, _, _⟩ :=
      Factor.execute_spec current (child, last) hs
    have hfloor := SingletonIntervalOrder.segment_input_floor ht
    have hl := hfloor.trans_lt hchildLt
    have hc := (Assignment.execute_spec current out ho).1
    have hq := EpsilonSingletonIntervalOrder.quotient_bounds greater prefix factor current hf hc hl hr
    have hshape := ih (hchildLt.trans hr) middle hh
    rcases hshape with ⟨hchild, hmiddle⟩ | ⟨d, hmiddle, hdpos, hdvalue⟩
    · subst child
      have halast : BranchesSupport.appendCheck last heads = true :=
        BranchesOrderSupport.appendCheck_smaller heads last factor
          ((Theta.acceptedLowCode_iff 0 last).mp hlow).1 hsmall.le ha
      have hout : out = heads ++ [last] := by
        simpa only [hmiddle, Branches.execute, halast, Bool.cond_true,
          Part.mem_some_iff] using hb
      have hvalue : interpretation 0 last = interpretation 0 current / interpretation 0 prefix := by
        rw [hproduct, Ordinal.mul_div_cancel _ (ne_of_gt hprefixPos)]
      exact Or.inr ⟨last, hout, hone, hvalue⟩
    · have hchildAdd := ((Assignment.inputCheck_exact child).mp hchildInput).2.2
      have hpc := MultiplicativePrincipalInterval.principal_quotient_spec hprefixPos
        hprefixSpec.2.2 hchildAdd hfloor
      have hchildStrict : interpretation 0 prefix < interpretation 0 child := by
        rw [← hpc.2.2]
        have hdelta : 1 < interpretation 0 child / interpretation 0 prefix := by
          simpa only [hdvalue] using hdpos
        simpa only [mul_one] using (Ordinal.isNormal_mul_right hprefixPos).strictMono hdelta
      have hqc := EpsilonSingletonIntervalOrder.quotient_bounds greater prefix factor child
        hf hchildInput hchildStrict (hchildLt.trans hr)
      have hlast := EpsilonSingletonIntervalOrder.last_le_child_quotient greater prefix factor
        current child last hf hc hl hr hs hchildStrict
      have hsmallTail : interpretation 0 d < interpretation 0 (lastCode heads) := by
        rw [hdvalue]
        exact hqc.2.1.trans_le hfactorLast
      have hresidual : interpretation 0 d * interpretation 0 last =
          interpretation 0 current / interpretation 0 prefix := by
        calc
          interpretation 0 d * interpretation 0 last =
              (interpretation 0 prefix * (interpretation 0 d * interpretation 0 last)) /
                interpretation 0 prefix := (Ordinal.mul_div_cancel _ (ne_of_gt hprefixPos)).symm
          _ = interpretation 0 current / interpretation 0 prefix := by
            rw [← mul_assoc, hdvalue, hpc.2.2, ← hproduct]
      have hmiddleTrack : SourceTrackingRaw.trackingCheck (heads ++ [d]) = true := by
        simpa only [hmiddle] using Assignment.execute_tracking child middle hh
      have hb' : out ∈ Branches.execute (last, heads ++ [d]) := by
        simpa only [hmiddle] using hb
      obtain ⟨next, hout, hvalue⟩ := branches_tail_covered heads d last out hne hmiddleTrack
        happend.1 ((Theta.acceptedLowCode_iff 0 last).mp hlow).1
        (by simpa only [hdvalue] using hlast) hsmallTail
        (by rw [hresidual]; exact hq.2.1.le.trans happend.2.2.2) hb'
      have hv : interpretation 0 next = interpretation 0 current / interpretation 0 prefix :=
        hvalue.trans hresidual
      exact Or.inr ⟨next, hout, by rw [hv]; exact hq.1, hv⟩

/-- Arbitrarily long independently executed original child words are
handled throughout the genuine greater interval when its actual printed
append flag is true. The greater insertion case is not asserted. -/
theorem execute_interval_append_lex (greater prefix factor current : Nat)
    (heads xs ys : List Nat)
    (hf : (prefix, factor) ∈ Factor.execute greater)
    (hbase : heads ∈ Assignment.execute prefix)
    (ha : BranchesSupport.appendCheck factor heads = true)
    (hx : xs ∈ Assignment.execute current) (hy : ys ∈ Assignment.execute greater)
    (hl : interpretation 0 prefix < interpretation 0 current)
    (hr : interpretation 0 current < interpretation 0 greater) :
    List.Lex (· < ·) (xs.map (interpretation 0)) (ys.map (interpretation 0)) := by
  obtain ⟨frames, hs⟩ := IntervalFrames.interval_segment_returns greater prefix factor current hf
    (Assignment.execute_spec current xs hx).1 hl hr
  have hshape := segment_append_shape hs hf heads hbase ha hr xs hx
  rcases hshape with ⟨hcurrent, hxs⟩ | ⟨d, hxs, hdpos, hv⟩
  · exact False.elim (hl.ne (congrArg (interpretation 0) hcurrent).symm)
  · obtain ⟨middle, hm, hb⟩ := FrameFactorOrder.actual_factor_child greater prefix factor ys hf hy
    have hmiddle : middle = heads := Part.mem_unique hm hbase
    have hys : ys = heads ++ [factor] := by
      simpa only [hmiddle, Branches.execute, ha, Bool.cond_true, Part.mem_some_iff] using hb
    have hq := EpsilonSingletonIntervalOrder.quotient_bounds greater prefix factor current hf
      (Assignment.execute_spec current xs hx).1 hl hr
    have hlast : interpretation 0 d < interpretation 0 factor := by rw [hv]; exact hq.2.1
    have hlex : List.Lex (· < ·) [interpretation 0 d] [interpretation 0 factor] :=
      List.Lex.rel hlast
    simpa only [hxs, hys, List.map_append, List.map_singleton] using
      (List.Lex.append_left (· < ·) hlex (heads.map (interpretation 0)))

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.AppendIntervalOrder
