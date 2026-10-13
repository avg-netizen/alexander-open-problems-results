import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingAppendIntervalOrderSupport

/-!
# Every quotient update below an actual greater append at any headword

The greater printed append branch supplies the actual epsilon and cover
at the last independently computed child entry. Every intervening quotient
is below that covered factor. The first real update appends its residual;
every later update has a residual below the earlier epsilon and its final
passing transition retains the whole original headword. Equality of child
values uses actual full assignment value invariance, never code injection.
Only the true greater append branch is claimed; the false greater insertion
and general inter-input comparison remain separate. Source-only uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.AppendIntervalOrder

open PublicEpsilonUnboundedIota
open AppendIntervalOrderSupport
open SourceTrackingSequences (lastCode)
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

/-- Actual quotient descent retains all original child entries in VALUES,
with one genuine covered residual. There is no assumed suffix or index. -/
theorem intervening_append_values (q greater prefix factor : Nat) (original : List Nat)
    (hf : (prefix, factor) ∈ Factor.execute q greater)
    (hbase : original ∈ Assignment.execute q prefix)
    (happend : BranchesSupport.appendCheck q factor original = true) :
    ∀ current xs, xs ∈ Assignment.execute q current →
      interpretation q prefix < interpretation q current →
      interpretation q current < interpretation q greater →
      xs.map (interpretation q) = original.map (interpretation q) ++
        [interpretation q current / interpretation q prefix] := by
  have htrack := Assignment.execute_tracking q prefix original hbase
  have hne := Assignment.execute_nonempty q prefix original hbase
  have hflag := (BranchesSupport.appendCheck_exact q factor original htrack).mp happend
  have hroot := hflag.1
  have hcover := hflag.2.2.2
  obtain ⟨_, hlp, _, _, _, hprefix, hbaseval, _, _, _, hgreater, _, _⟩ :=
    Factor.execute_spec q greater (prefix, factor) hf
  have hp := (Assignment.inputCheck_exact q prefix).mp hprefix
  have hpos := (base_pos q (HeightBoundary.input_spec q prefix hlp).2.1).trans_le hbaseval
  have hfactorBound := (Factor.Bounds.execute_last_le_prefix_last q greater (prefix, factor) hf).trans
    (Assignment.execute_spec q prefix original hbase).2.1.2.2.1
  let P : Nat → Prop := fun n => ∀ current : Nat,
    (canonicalMNF (interpretation q current)).length = n →
    ∀ xs : List Nat, xs ∈ Assignment.execute q current →
      interpretation q prefix < interpretation q current →
      interpretation q current < interpretation q greater →
      xs.map (interpretation q) = original.map (interpretation q) ++
        [interpretation q current / interpretation q prefix]
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
        obtain ⟨earlier, tail, hheads, hearlier, htail⟩ :=
          suffix_values_shape q heads original _ hvalues
        have hnEarlier : earlier ≠ [] := by
          intro he
          have hnMap : original.map (interpretation q) = [] := by
            simpa only [he, List.map_nil] using hearlier.symm
          exact hne (List.map_eq_nil_iff.mp hnMap)
        have hlastValue := SourceAdditiveTrackingWordBounds.lastCode_values_eq
          (interpretation q) (interpretation q) earlier original hnEarlier hearlier
        have ht : SourceTrackingRaw.trackingCheck q (earlier ++ [tail]) = true := by
          simpa only [hheads] using Assignment.execute_tracking q child heads hh
        have hsmall : interpretation q last ≤ interpretation q tail := by
          rw [htail]
          exact hquot.2.2.2.2 hstrict
        have hchildPrincipal := (Assignment.inputCheck_exact q child).mp hcaller
        have hdelta := MultiplicativePrincipalInterval.descending_interval_spec hpos hp.2.2
          hchildPrincipal.2.2 (Factor.Bounds.execute_last_le_prefix q greater (prefix, factor) hf)
          hstrict (hupper.trans_eq hgreater)
        have htailSmall : interpretation q tail < interpretation q (lastCode earlier) := by
          rw [htail, hlastValue]
          exact hdelta.2.2.1.trans_le hfactorBound
        have hmu := SourceTrackingRaw.Support.muValue_invariant q
          (lastCode earlier) (lastCode original)
          (suffix_last_input q earlier tail hnEarlier ht) hroot hlastValue
        have hcovered : interpretation q tail * interpretation q last ≤
            SourceTrackingRaw.Support.muValue q (lastCode earlier) := by
          rw [htail, hmu, hquot.2.2.2.1]
          exact hquot.2.1.le.trans hcover
        have hb' : xs ∈ Branches.execute ((q, last), earlier ++ [tail]) := by
          simpa only [hheads] using hb
        obtain ⟨d, hout, hv⟩ := branches_suffix_covered q earlier tail last xs hnEarlier ht
          hlow hm hsmall htailSmall hcovered hb'
        simp only [hout, List.map_append, List.map_singleton, hearlier, hv, htail,
          hquot.2.2.2.1]
      · have hvalues := Assignment.ValueInvariance.execute_values_eq q child prefix heads original
          hh hbase heq.symm
        have hs := FrameFactorOrder.appendCheck_smaller q original htrack last factor hlow hlast happend
        have hv : original ++ [last] ∈ Branches.execute ((q, last), original) := by
          simpa only [Branches.execute, hs, Bool.cond_true] using (Part.mem_some (original ++ [last]))
        have hactualTrack := Assignment.execute_tracking q child heads hh
        have hbound := (Factor.Bounds.execute_last_le_prefix_last q current (child, last) hstep).trans
          (Assignment.execute_spec q child heads hh).2.1.2.2.1
        have hlastValues := SourceAdditiveTrackingWordBounds.lastCode_values_eq
          (interpretation q) (interpretation q) heads original
          (Assignment.execute_nonempty q child heads hh) hvalues
        have hvirtualBound := hbound.trans_eq hlastValues
        have he := Assignment.ValueInvariance.branches_values_eq q last last heads original
          hactualTrack htrack hlow hlow hm hbound hvirtualBound rfl hvalues
          xs (original ++ [last]) hb hv
        have hchildquot : interpretation q child / interpretation q prefix = 1 := by
          rw [← heq, Ordinal.div_self (ne_of_gt hpos)]
        have hlastq : interpretation q last = interpretation q current / interpretation q prefix := by
          simpa only [hchildquot, one_mul] using hquot.2.2.2.1
        simpa only [List.map_append, List.map_singleton, hlastq] using he
  intro current xs hx hl hr
  exact hall _ current rfl xs hx hl hr

/-- Complete independent assignments are strictly ordered throughout the
genuine greater-factor interval whenever its real child appends. The child
word may have arbitrary length and original raw spellings. -/
theorem execute_interval_lex (q greater prefix factor current : Nat)
    (original xs ys : List Nat)
    (hf : (prefix, factor) ∈ Factor.execute q greater)
    (hbase : original ∈ Assignment.execute q prefix)
    (happend : BranchesSupport.appendCheck q factor original = true)
    (hx : xs ∈ Assignment.execute q current) (hy : ys ∈ Assignment.execute q greater)
    (hl : interpretation q prefix < interpretation q current)
    (hr : interpretation q current < interpretation q greater) :
    List.Lex (· < ·) (xs.map (interpretation q)) (ys.map (interpretation q)) := by
  have hxs := intervening_append_values q greater prefix factor original hf hbase happend current xs hx hl hr
  obtain ⟨heads, hh, hb⟩ := IntervalFactors.actual_factor_child q greater prefix factor ys hf hy
  have hheads : heads = original := Part.mem_unique hh hbase
  have hys : ys = original ++ [factor] := by
    simpa only [hheads, Branches.execute, happend, Bool.cond_true, Part.mem_some_iff] using hb
  have hc := (Assignment.execute_spec q current xs hx).1
  obtain ⟨_, hlow, _, _, _, hcaller, hbaseval, _, _, _, hgreater, _, _⟩ :=
    Factor.execute_spec q greater (prefix, factor) hf
  have hp := (Assignment.inputCheck_exact q prefix).mp hcaller
  have hi := (Assignment.inputCheck_exact q current).mp hc
  have hpos := (base_pos q (HeightBoundary.input_spec q prefix hlow).2.1).trans_le hbaseval
  have hq := MultiplicativePrincipalInterval.descending_interval_spec hpos hp.2.2 hi.2.2
    (Factor.Bounds.execute_last_le_prefix q greater (prefix, factor) hf) hl (hr.trans_eq hgreater)
  rw [hxs, hys, List.map_append, List.map_singleton]
  exact List.Lex.append_left (· < ·) (List.Lex.rel hq.2.2.1) (original.map (interpretation q))

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.AppendIntervalOrder
