import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingEpsilonSingletonIntervalOrderSupport
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingSingletonIntervalOrder

/-!
# Actual accumulated quotient updates at an executed singleton prefix

When the greater update genuinely appends, its original mu cover bounds
every smaller quotient product. Real factor descent therefore retains
the original prefix and computes that quotient as the second entry.
When the greater update does not append, its actual singleton product
lies above EVERY value of the smaller full output. No universal pair
claim is made across a failed cover. The prefix singleton is independently
executed; epsilon and non-epsilon cases are both included. Longer prefix
words and full different-prefix order remain separate. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.EpsilonSingletonIntervalOrder

open PublicEpsilonUnboundedIota SourceTrackingSequences
open EpsilonSingletonIntervalOrderSupport SingletonIntervalOrderSupport
open Alexander313.Wilken.MultiplicativeNormalForm MultiplicativePrincipalArithmetic

private theorem quotient_step_spec (q greater prefix factor current child last : Nat)
    (hf : (prefix, factor) ∈ Factor.execute q greater)
    (hc : Assignment.inputCheck q current = true)
    (hl : interpretation q prefix < interpretation q current)
    (hr : interpretation q current < interpretation q greater)
    (hstep : (child, last) ∈ Factor.execute q current) :
    1 < interpretation q current / interpretation q prefix ∧
      interpretation q current / interpretation q prefix < interpretation q factor ∧
      interpretation q current / interpretation q prefix < interpretation q prefix ∧
      (interpretation q child / interpretation q prefix) * interpretation q last =
        interpretation q current / interpretation q prefix ∧
      (interpretation q prefix < interpretation q child →
        interpretation q last ≤ interpretation q child / interpretation q prefix) := by
  obtain ⟨_, hlow, _, _, _, hcaller, hbase, _, _, hone, hgreater, _, _⟩ :=
    Factor.execute_spec q greater (prefix, factor) hf
  have hp := (Assignment.inputCheck_exact q prefix).mp hcaller
  have hi := (Assignment.inputCheck_exact q current).mp hc
  have hpos := (base_pos q (HeightBoundary.input_spec q prefix hlow).2.1).trans_le hbase
  have hbound := Factor.Bounds.execute_last_le_prefix q greater (prefix, factor) hf
  have hfinal := Factor.Bounds.execute_last_le_prefix_last q greater (prefix, factor) hf
  have hs := MultiplicativePrincipalInterval.descending_interval_spec hpos hp.2.2 hi.2.2
    hbound hl (hr.trans_eq hgreater)
  have ht := MultiplicativePrincipalInterval.Factors.interval_factor_stack hpos hp.2.2 hi.2.2
    hone hfinal hl (hr.trans_eq hgreater)
  have hnext := IntervalFactors.interval_factor_step q greater prefix factor current child last
    hf hc hl hr hstep
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hlast, _⟩ :=
    Factor.execute_spec q current (child, last) hstep
  have hlast' : interpretation q last = lf (interpretation q current / interpretation q prefix) := by
    rw [hlast]
    change lastFactor (canonicalMNF (interpretation q current)) =
      lastFactor (canonicalMNF (interpretation q current / interpretation q prefix))
    rw [ht.2.2.2.1, MultiplicativePrincipalInterval.Factors.lastFactor_append _ _ ht.2.2.2.2.1]
  have hchild : interpretation q child = interpretation q prefix *
      factorProduct (factorPrefix
        (canonicalMNF (interpretation q current / interpretation q prefix))) := hnext.2.2.1
  have hquot : interpretation q child / interpretation q prefix =
      factorProduct (factorPrefix
        (canonicalMNF (interpretation q current / interpretation q prefix))) := by
    rw [hchild, Ordinal.mul_div_cancel _ (ne_of_gt hpos)]
  refine ⟨hs.2.1, hs.2.2.1, hs.2.2.2.1, ?_, ?_⟩
  · rw [hquot, hlast']
    exact (source_prefix_last (zero_lt_one.trans hs.2.1) hs.2.2.2.2.2.1).symm
  · intro hstrict
    have hnon : ¬ IsMultiplicativePrincipal (interpretation q current / interpretation q prefix) := by
      intro hm
      have he := (source_prefix_last_multiplicative hm).1
      have hz : interpretation q child = interpretation q prefix := by
        simpa only [he, mul_one] using hchild
      exact (ne_of_gt hstrict) hz
    rw [hlast', hquot]
    exact MultiplicativeFactorRemoval.Bounds.source_last_le_prefix_product
      (zero_lt_one.trans hs.2.1) hs.2.2.2.2.2.1 hnon

theorem intervening_covered_pair_values (q greater prefix factor : Nat)
    (hf : (prefix, factor) ∈ Factor.execute q greater)
    (hbase : [prefix] ∈ Assignment.execute q prefix)
    (happend : BranchesSupport.appendCheck q factor [prefix] = true) :
    ∀ current xs, xs ∈ Assignment.execute q current →
      interpretation q prefix < interpretation q current →
      interpretation q current < interpretation q greater →
      xs.map (interpretation q) =
        [interpretation q prefix, interpretation q current / interpretation q prefix] := by
  have htrack := Assignment.execute_tracking q prefix [prefix] hbase
  have hflag := (BranchesSupport.appendCheck_exact q factor [prefix] htrack).mp happend
  have hroot : SourceTrackingRaw.Support.inputCheck q prefix = true := by
    simpa only [lastCode_singleton] using hflag.1
  have hcover : interpretation q factor ≤ SourceTrackingRaw.Support.muValue q prefix := by
    simpa only [lastCode_singleton] using hflag.2.2.2
  obtain ⟨_, hlp, _, _, _, hprefix, hbaseval, _, _, _, hgreater, _, _⟩ :=
    Factor.execute_spec q greater (prefix, factor) hf
  have hp := (Assignment.inputCheck_exact q prefix).mp hprefix
  have hpos := (base_pos q (HeightBoundary.input_spec q prefix hlp).2.1).trans_le hbaseval
  let P : Nat → Prop := fun n => ∀ current : Nat,
    (canonicalMNF (interpretation q current)).length = n →
    ∀ xs : List Nat, xs ∈ Assignment.execute q current →
      interpretation q prefix < interpretation q current →
      interpretation q current < interpretation q greater →
      xs.map (interpretation q) =
        [interpretation q prefix, interpretation q current / interpretation q prefix]
  have hall : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro current hn xs hx hl hr
      have hc := (Assignment.execute_spec q current xs hx).1
      obtain ⟨child, last, hstep, hstack, hremaining, hchild, hlast⟩ :=
        IntervalFactors.interval_factor_returns q greater prefix factor current hf hc hl hr
      obtain ⟨_, _, _, hlow, _, hcaller, _, hlt, hm, _, hproduct, _, hcount⟩ :=
        Factor.execute_spec q current (child, last) hstep
      obtain ⟨heads, hh, hb⟩ := IntervalFactors.actual_factor_child q current child last xs hstep hx
      have hquot := quotient_step_spec q greater prefix factor current child last hf hc hl hr hstep
      have hremainingPos := (isMNF_product_principal
        (MultiplicativeFactorRemoval.factorPrefix_reduced
          (canonicalMNF (interpretation q current / interpretation q prefix))
          (canonicalMNF_reduced _)).1).1
      have hfloor : interpretation q prefix ≤ interpretation q child := by
        rw [hchild]
        exact Ordinal.le_mul_left _ hremainingPos
      have hupper := hlt.trans hr
      rcases lt_or_eq_of_le hfloor with hstrict | heq
      · have hcount' : (canonicalMNF (interpretation q child)).length < n := by
          simpa only [hn] using hcount
        have hvalues := ih _ hcount' child rfl heads hh hstrict hupper
        obtain ⟨head, tail, hheads, hhead, htail⟩ := pair_values_shape q heads _ _ hvalues
        have ht : SourceTrackingRaw.trackingCheck q [head, tail] = true := by
          simpa only [hheads] using Assignment.execute_tracking q child heads hh
        have hsmall : interpretation q last ≤ interpretation q tail := by
          rw [htail]
          exact hquot.2.2.2.2 hstrict
        have hchildPrincipal := (Assignment.inputCheck_exact q child).mp hcaller
        have hdelta := MultiplicativePrincipalInterval.descending_interval_spec hpos hp.2.2
          hchildPrincipal.2.2 (Factor.Bounds.execute_last_le_prefix q greater (prefix, factor) hf)
          hstrict (hupper.trans_eq hgreater)
        have htailSmall : interpretation q tail < interpretation q head := by
          rw [htail, hhead]
          exact hdelta.2.2.2.1
        have hmu := SourceTrackingRaw.Support.muValue_invariant q head prefix
          (pair_head_input q head tail ht) hroot hhead
        have hcovered : interpretation q tail * interpretation q last ≤
            SourceTrackingRaw.Support.muValue q head := by
          rw [htail, hmu, hquot.2.2.2.1]
          exact hquot.2.1.le.trans hcover
        have hb' : xs ∈ Branches.execute ((q, last), [head, tail]) := by
          simpa only [hheads] using hb
        obtain ⟨d, hout, hv⟩ := branches_pair_covered q head tail last xs ht hlow hm
          hsmall htailSmall hcovered hb'
        simp only [hout, List.map_cons, List.map_nil, hhead, hv, htail, hquot.2.2.2.1]
      · have hvalues := Assignment.ValueInvariance.execute_values_eq q child prefix heads [prefix]
          hh hbase heq.symm
        have hs := FrameFactorOrder.appendCheck_smaller q [prefix] htrack last factor hlow hlast happend
        have hv : [prefix, last] ∈ Branches.execute ((q, last), [prefix]) := by
          simpa only [Branches.execute, hs, Bool.cond_true] using (Part.mem_some [prefix, last])
        have hactualTrack := Assignment.execute_tracking q child heads hh
        have hbound := (Factor.Bounds.execute_last_le_prefix_last q current (child, last) hstep).trans
          (Assignment.execute_spec q child heads hh).2.1.2.2.1
        have hprefixBound : interpretation q last ≤ interpretation q prefix :=
          (Factor.Bounds.execute_last_le_prefix q current (child, last) hstep).trans_eq heq.symm
        have he := Assignment.ValueInvariance.branches_values_eq q last last heads [prefix]
          hactualTrack htrack hlow hlow hm hbound
          (by simpa only [lastCode_singleton] using hprefixBound) rfl hvalues xs [prefix, last] hb hv
        have hchildquot : interpretation q child / interpretation q prefix = 1 := by
          rw [← heq, Ordinal.div_self (ne_of_gt hpos)]
        have hlastq : interpretation q last = interpretation q current / interpretation q prefix := by
          simpa only [hchildquot, one_mul] using hquot.2.2.2.1
        simpa only [List.map_cons, List.map_nil, hlastq] using he
  intro current xs hx hl hr
  exact hall _ current rfl xs hx hl hr

theorem execute_interval_lex (q greater prefix factor current : Nat) (xs ys : List Nat)
    (hf : (prefix, factor) ∈ Factor.execute q greater)
    (hbase : [prefix] ∈ Assignment.execute q prefix)
    (hx : xs ∈ Assignment.execute q current) (hy : ys ∈ Assignment.execute q greater)
    (hl : interpretation q prefix < interpretation q current)
    (hr : interpretation q current < interpretation q greater) :
    List.Lex (· < ·) (xs.map (interpretation q)) (ys.map (interpretation q)) := by
  obtain ⟨heads, hh, hb⟩ := IntervalFactors.actual_factor_child q greater prefix factor ys hf hy
  have he : heads = [prefix] := Part.mem_unique hh hbase
  have ht := Assignment.execute_tracking q prefix [prefix] hbase
  have hb' : ys ∈ Branches.execute ((q, factor), [prefix]) := by simpa only [he] using hb
  obtain ⟨_, hlowPrefix, _, hlow, _, hcaller, hbaseval, _, hm, _, hproduct, _, _⟩ :=
    Factor.execute_spec q greater (prefix, factor) hf
  have hbound := Factor.Bounds.execute_last_le_prefix q greater (prefix, factor) hf
  cases ha : BranchesSupport.appendCheck q factor [prefix] with
  | true =>
    have hxs := intervening_covered_pair_values q greater prefix factor hf hbase ha current xs hx hl hr
    have hys : ys = [prefix, factor] := by
      simpa only [Branches.execute, ha, Bool.cond_true, Part.mem_some_iff] using hb'
    have hp := (Assignment.inputCheck_exact q prefix).mp hcaller
    have hi := (Assignment.inputCheck_exact q current).mp (Assignment.execute_spec q current xs hx).1
    have hpos := (base_pos q (HeightBoundary.input_spec q prefix hlowPrefix).2.1).trans_le hbaseval
    have hq := MultiplicativePrincipalInterval.strict_quotient_bounds hpos hp.2.2 hi.2.2 hl
      (hr.trans_eq hproduct)
    simp only [hxs, hys, List.map_cons, List.map_nil]
    exact List.Lex.cons (List.Lex.rel hq.2.1)
  | false =>
    have hi : ys ∈ Insertion.execute ((q, factor), [prefix]) := by
      simpa only [Branches.execute, ha, Bool.cond_false] using hb'
    obtain ⟨d, hout, hv⟩ := insertion_singleton_small q prefix factor ys ht hlow hm hbound hi
    have hys : ys.map (interpretation q) = [interpretation q greater] := by
      simpa only [hout, List.map_singleton, hv, ← hproduct]
    have hresult := (Assignment.execute_spec q current xs hx).2.1
    have hne := ((SourceTrackingRaw.trackingCheck_conditions q xs).mp hresult.1).1
    cases xs with
    | nil => exact False.elim (hne rfl)
    | cons a rest =>
      rw [List.map_cons, hys]
      exact List.Lex.rel ((hresult.2.1 a List.mem_cons_self).trans_lt hr)

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.EpsilonSingletonIntervalOrder
