import Alexander313.Wilken.SourceOneNativeAdditiveTrackingEpsilonSingletonIntervalOrderSupport

/-!
# All genuine quotient updates at an actual original epsilon singleton

The greater printed append flag is derived from its actual execution.
If it is false, the greater output is its genuine singleton product and
the smaller assignment's actual ALL bound already decides strict order.
If it is true, every smaller residual quotient is below the genuinely
covered greater factor. Actual two-row insertion therefore retains the
literal original epsilon head through every real factor frame. Neither
universal pair shape nor an accumulated update inequality is assumed.
Longer recursive child words remain separate. Source-only uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.EpsilonSingletonIntervalOrder

open EpsilonSingletonIntervalOrderSupport
open NativeContext.SourceTrackingSequences (lastCode_singleton)
open Alexander313.Wilken.MultiplicativeNormalForm MultiplicativePrincipalArithmetic

/-- Every intervening actual input has its genuinely computed smaller
positive principal quotient, including its exact cancellation equation. -/
theorem quotient_bounds (greater prefix factor current : Nat)
    (hf : (prefix, factor) ∈ Factor.execute greater)
    (hc : Assignment.inputCheck current = true)
    (hl : interpretation 0 prefix < interpretation 0 current)
    (hr : interpretation 0 current < interpretation 0 greater) :
    1 < interpretation 0 current / interpretation 0 prefix ∧
      interpretation 0 current / interpretation 0 prefix < interpretation 0 factor ∧
      Ordinal.IsPrincipal (· + ·) (interpretation 0 current / interpretation 0 prefix) ∧
        interpretation 0 prefix * (interpretation 0 current / interpretation 0 prefix) =
          interpretation 0 current := by
  obtain ⟨_, _, _, hp, hfloor, _, _, _, hproduct, _, _⟩ :=
    Factor.execute_spec greater (prefix, factor) hf
  have he := (Assignment.inputCheck_exact prefix).mp hp
  have hi := (Assignment.inputCheck_exact current).mp hc
  exact MultiplicativePrincipalInterval.strict_quotient_bounds
    (Order.one_le_iff_pos.mp hfloor) he.2.2 hi.2.2 hl (hr.trans_eq hproduct)

/-- When the next real child is strictly above the original prefix, the
current quotient has more than one factor. Actual descending MNF order
then bounds the removed factor by that remaining quotient product. -/
theorem last_le_child_quotient (greater prefix factor current child last : Nat)
    (hf : (prefix, factor) ∈ Factor.execute greater)
    (hc : Assignment.inputCheck current = true)
    (hl : interpretation 0 prefix < interpretation 0 current)
    (hr : interpretation 0 current < interpretation 0 greater)
    (hs : (child, last) ∈ Factor.execute current)
    (hchild : interpretation 0 prefix < interpretation 0 child) :
    interpretation 0 last ≤ interpretation 0 child / interpretation 0 prefix := by
  have hq := quotient_bounds greater prefix factor current hf hc hl hr
  have hstep := IntervalFactors.interval_factor_step greater prefix factor current child last hf hc hl hr hs
  have hpos : 0 < interpretation 0 prefix := by
    exact Order.one_le_iff_pos.mp (Factor.execute_spec greater (prefix, factor) hf).2.2.2.2.1
  have hqpos := zero_lt_one.trans hq.1
  have hne : canonicalMNF (interpretation 0 current / interpretation 0 prefix) ≠ [] := by
    intro hn
    exact (ne_of_gt hq.1) ((canonicalMNF_nil_iff hqpos hq.2.2.1).mp hn)
  have hlast : interpretation 0 last = lf (interpretation 0 current / interpretation 0 prefix) := by
    rw [(Factor.execute_spec current (child, last) hs).2.2.2.2.2.2.2.2.2.1]
    change lastFactor (canonicalMNF (interpretation 0 current)) =
      lastFactor (canonicalMNF (interpretation 0 current / interpretation 0 prefix))
    rw [hstep.1, MultiplicativePrincipalInterval.Factors.lastFactor_append _ _ hne]
  have hnon : ¬ IsMultiplicativePrincipal (interpretation 0 current / interpretation 0 prefix) := by
    intro hm
    have he : interpretation 0 child = interpretation 0 prefix := by
      simpa only [(source_prefix_last_multiplicative hm).1, mul_one] using hstep.2.2.1
    exact hchild.ne he.symm
  have hremaining : interpretation 0 child / interpretation 0 prefix =
      factorProduct (factorPrefix (canonicalMNF (interpretation 0 current / interpretation 0 prefix))) := by
    rw [hstep.2.2.1, Ordinal.mul_div_cancel _ (ne_of_gt hpos)]
  rw [hlast, hremaining]
  exact MultiplicativeFactorRemoval.Bounds.source_last_le_prefix_product hqpos hq.2.2.1 hnon

/-- On the true greater append branch, actual factor descent and actual
small pair tables keep precisely the original head and covered residual.
The real terminal prefix assignment supplies the only initial singleton. -/
theorem segment_covered_shape {greater prefix factor current : Nat}
    {frames : List IntervalFrames.Frame}
    (hseg : IntervalFrames.Segment prefix factor current frames)
    (hf : (prefix, factor) ∈ Factor.execute greater)
    (hbase : [prefix] ∈ Assignment.execute prefix)
    (he : Ordinal.omega0 ^ interpretation 0 prefix = interpretation 0 prefix)
    (hcover : interpretation 0 factor ≤ SourceTrackingRaw.Support.muValue prefix)
    (hr : interpretation 0 current < interpretation 0 greater)
    (out : List Nat) (ho : out ∈ Assignment.execute current) :
    (current = prefix ∧ out = [prefix]) ∨
      ∃ d, out = [prefix, d] ∧ 1 < interpretation 0 d ∧
        interpretation 0 d = interpretation 0 current / interpretation 0 prefix := by
  revert hr out
  induction hseg with
  | nil =>
    intro hr out ho
    exact Or.inl ⟨rfl, Part.mem_unique ho hbase⟩
  | cons current child last frames hs hsmall ht ih =>
    intro hr out ho
    obtain ⟨heads, hh, hb⟩ := FrameFactorOrder.actual_factor_child current child last out hs ho
    obtain ⟨_, _, hlow, hchildInput, _, hchildLt, hm, hone, hproduct, _, _⟩ :=
      Factor.execute_spec current (child, last) hs
    have hfloor := SingletonIntervalOrder.segment_input_floor ht
    have hl := hfloor.trans_lt hchildLt
    have hc := (Assignment.execute_spec current out ho).1
    have hq := quotient_bounds greater prefix factor current hf hc hl hr
    have hfactor := Factor.Bounds.execute_last_le_prefix greater (prefix, factor) hf
    have hshape := ih (hchildLt.trans hr) heads hh
    rcases hshape with ⟨hchild, hheads⟩ | ⟨d, hheads, hdpos, hdvalue⟩
    · subst child
      have hb' : out ∈ Branches.execute (last, [prefix]) := by simpa only [hheads] using hb
      have hout := branches_singleton_covered prefix last out
        (Assignment.execute_tracking prefix [prefix] hbase) he
        ((Theta.acceptedLowCode_iff 0 last).mp hlow).1
        (hsmall.le.trans hcover) hb'
      have hvalue : interpretation 0 last = interpretation 0 current / interpretation 0 prefix := by
        rw [hproduct, Ordinal.mul_div_cancel _ (ne_of_gt (EpsilonOffsets.epsilon_pos_principal he).1)]
      exact Or.inr ⟨last, hout, hone, hvalue⟩
    · have hprefixPos := (EpsilonOffsets.epsilon_pos_principal he).1
      have hchildAdd := ((Assignment.inputCheck_exact child).mp hchildInput).2.2
      have hpc := MultiplicativePrincipalInterval.principal_quotient_spec hprefixPos
        (EpsilonOffsets.epsilon_pos_principal he).2 hchildAdd hfloor
      have hchildStrict : interpretation 0 prefix < interpretation 0 child := by
        rw [← hpc.2.2]
        have hdelta : 1 < interpretation 0 child / interpretation 0 prefix := by
          simpa only [hdvalue] using hdpos
        simpa only [mul_one] using (Ordinal.isNormal_mul_right hprefixPos).strictMono hdelta
      have hqc := quotient_bounds greater prefix factor child hf hchildInput hchildStrict
        (hchildLt.trans hr)
      have hlast := last_le_child_quotient greater prefix factor current child last hf hc hl hr hs hchildStrict
      have hsmallTail : interpretation 0 d < interpretation 0 prefix := by
        rw [hdvalue]
        exact hqc.2.1.trans_le hfactor
      have hresidual : interpretation 0 d * interpretation 0 last =
          interpretation 0 current / interpretation 0 prefix := by
        calc
          interpretation 0 d * interpretation 0 last =
              (interpretation 0 prefix * (interpretation 0 d * interpretation 0 last)) /
                interpretation 0 prefix := (Ordinal.mul_div_cancel _ (ne_of_gt hprefixPos)).symm
          _ = interpretation 0 current / interpretation 0 prefix := by
            rw [← mul_assoc, hdvalue, hpc.2.2, ← hproduct]
      have htrack : SourceTrackingRaw.trackingCheck [prefix, d] = true := by
        simpa only [hheads] using Assignment.execute_tracking child heads hh
      have hb' : out ∈ Branches.execute (last, [prefix, d]) := by simpa only [hheads] using hb
      obtain ⟨next, hout, hvalue⟩ := branches_pair_covered prefix d last out htrack
        ((Theta.acceptedLowCode_iff 0 last).mp hlow).1
        (by simpa only [hdvalue] using hlast) hsmallTail
        (by rw [hresidual]; exact hq.2.1.le.trans hcover) hb'
      have hv : interpretation 0 next = interpretation 0 current / interpretation 0 prefix :=
        hvalue.trans hresidual
      exact Or.inr ⟨next, hout, by rw [hv]; exact hq.1, hv⟩

/-- Any actual smaller complete output precedes the independently executed
greater singleton product. No shape of the smaller word is required. -/
theorem execute_false_append_lex (greater prefix factor current : Nat) (xs ys : List Nat)
    (hf : (prefix, factor) ∈ Factor.execute greater)
    (hbase : [prefix] ∈ Assignment.execute prefix)
    (hfalse : BranchesSupport.appendCheck factor [prefix] = false)
    (hx : xs ∈ Assignment.execute current) (hy : ys ∈ Assignment.execute greater)
    (hr : interpretation 0 current < interpretation 0 greater) :
    List.Lex (· < ·) (xs.map (interpretation 0)) (ys.map (interpretation 0)) := by
  obtain ⟨heads, hh, hb⟩ := FrameFactorOrder.actual_factor_child greater prefix factor ys hf hy
  have hheads : heads = [prefix] := Part.mem_unique hh hbase
  have hi : ys ∈ Insertion.execute (factor, [prefix]) := by
    simpa only [hheads, Branches.execute, hfalse, Bool.cond_false] using hb
  obtain ⟨_, _, hlow, _, _, _, hm, _, hproduct, _, _⟩ :=
    Factor.execute_spec greater (prefix, factor) hf
  obtain ⟨d, hout, hv⟩ := SingletonIntervalOrderSupport.insertion_singleton_small prefix factor ys
    (Assignment.execute_tracking prefix [prefix] hbase)
    ((Theta.acceptedLowCode_iff 0 factor).mp hlow).1 hm
    (Factor.Bounds.execute_last_le_prefix greater (prefix, factor) hf) hi
  cases hs : xs with
  | nil => exact False.elim (Assignment.execute_nonempty current [] hx rfl)
  | cons first rest =>
    have hm : first ∈ xs := by simpa only [hs] using (List.mem_cons_self : first ∈ first :: rest)
    have hfirst := (Assignment.execute_all_bounds current xs hx first hm).trans_lt hr
    simpa only [hs, hout, List.map_cons, List.map_singleton, hv, ← hproduct] using
      (List.Lex.rel hfirst : List.Lex (· < ·)
        (interpretation 0 first :: rest.map (interpretation 0)) [interpretation 0 greater])

/-- Both actual printed greater branches yield strict complete assignment
order throughout the genuine interval at an actually executing epsilon
singleton prefix. Every quotient factor and smaller update is derived. -/
theorem execute_interval_lex (greater prefix factor current : Nat) (xs ys : List Nat)
    (hf : (prefix, factor) ∈ Factor.execute greater)
    (hbase : [prefix] ∈ Assignment.execute prefix)
    (he : Ordinal.omega0 ^ interpretation 0 prefix = interpretation 0 prefix)
    (hx : xs ∈ Assignment.execute current) (hy : ys ∈ Assignment.execute greater)
    (hl : interpretation 0 prefix < interpretation 0 current)
    (hr : interpretation 0 current < interpretation 0 greater) :
    List.Lex (· < ·) (xs.map (interpretation 0)) (ys.map (interpretation 0)) := by
  cases ha : BranchesSupport.appendCheck factor [prefix] with
  | false => exact execute_false_append_lex greater prefix factor current xs ys hf hbase ha hx hy hr
  | true =>
    have ht := Assignment.execute_tracking prefix [prefix] hbase
    have hcover : interpretation 0 factor ≤ SourceTrackingRaw.Support.muValue prefix := by
      simpa only [lastCode_singleton] using ((BranchesSupport.appendCheck_exact factor [prefix] ht).mp ha).2.2.2
    obtain ⟨frames, hs⟩ := IntervalFrames.interval_segment_returns greater prefix factor current hf
      (Assignment.execute_spec current xs hx).1 hl hr
    have hshape := segment_covered_shape hs hf hbase he hcover hr xs hx
    rcases hshape with ⟨hcurrent, hxs⟩ | ⟨d, hxs, hdpos, hv⟩
    · exact False.elim (hl.ne (congrArg (interpretation 0) hcurrent).symm)
    · obtain ⟨heads, hh, hb⟩ := FrameFactorOrder.actual_factor_child greater prefix factor ys hf hy
      have hheads : heads = [prefix] := Part.mem_unique hh hbase
      have hys : ys = [prefix, factor] := by
        simpa only [hheads, Branches.execute, ha, Bool.cond_true, Part.mem_some_iff,
          List.singleton_append] using hb
      have hq := quotient_bounds greater prefix factor current hf
        (Assignment.execute_spec current xs hx).1 hl hr
      have hlast : interpretation 0 d < interpretation 0 factor := by rw [hv]; exact hq.2.1
      simpa only [hxs, hys, List.map_cons, List.map_nil] using
        (List.Lex.cons (List.Lex.rel hlast) : List.Lex (· < ·)
          [interpretation 0 prefix, interpretation 0 d]
          [interpretation 0 prefix, interpretation 0 factor])

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.EpsilonSingletonIntervalOrder
