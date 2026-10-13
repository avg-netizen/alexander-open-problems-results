import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingSingletonIntervalOrderSupport
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingAssignmentValueInvariance

/-!
# A genuine several-factor interval comparison at a non-epsilon singleton child

The original greater recursive prefix actually executes as its literal
singleton and is non-epsilon. The real smaller factor program removes
the genuine quotient stack. Every remaining child is at least that prefix;
at equality actual complete value invariance identifies its singleton,
and above it the real canonical factor count decreases. Every genuine
small dispatcher therefore remains singleton at the actual product.
This proves the several-quotient-factor subcase without an accumulated
update inequality premise. Epsilon or longer child words remain separate.
Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.SingletonIntervalOrder

open PublicEpsilonUnboundedIota SourceTrackingSequences
open SingletonIntervalOrderSupport
open Alexander313.Wilken.MultiplicativeNormalForm MultiplicativePrincipalArithmetic

theorem intervening_singleton_values (q greater prefix factor : Nat)
    (hf : (prefix, factor) ∈ Factor.execute q greater)
    (hbase : [prefix] ∈ Assignment.execute q prefix)
    (hno : Ordinal.omega0 ^ interpretation q prefix ≠ interpretation q prefix) :
    ∀ current xs, xs ∈ Assignment.execute q current →
      interpretation q prefix < interpretation q current →
      interpretation q current < interpretation q greater →
      xs.map (interpretation q) = [interpretation q current] := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hgreater, _, _⟩ :=
    Factor.execute_spec q greater (prefix, factor) hf
  let P : Nat → Prop := fun n => ∀ current : Nat,
    (canonicalMNF (interpretation q current)).length = n →
    ∀ xs : List Nat, xs ∈ Assignment.execute q current →
      interpretation q prefix < interpretation q current →
      interpretation q current < interpretation q greater →
      xs.map (interpretation q) = [interpretation q current]
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
      have hp := MultiplicativeFactorRemoval.factorPrefix_reduced
        (canonicalMNF (interpretation q current / interpretation q prefix))
        (canonicalMNF_reduced _)
      have hpos := (isMNF_product_principal hp.1).1
      have hfloor : interpretation q prefix ≤ interpretation q child := by
        rw [hchild]
        exact Ordinal.le_mul_left _ hpos
      have hupper : interpretation q child < interpretation q greater := hlt.trans hr
      have hvalues : heads.map (interpretation q) = [interpretation q child] := by
        rcases lt_or_eq_of_le hfloor with hstrict | heq
        · have hcount' : (canonicalMNF (interpretation q child)).length < n := by
            simpa only [hn] using hcount
          exact ih _ hcount' child rfl heads hh hstrict hupper
        · have he := Assignment.ValueInvariance.execute_values_eq q child prefix heads [prefix]
            hh hbase heq.symm
          simpa only [List.map_singleton, heq] using he
      obtain ⟨head, hheads, hvalue⟩ := singleton_values_shape q heads _ hvalues
      have ht : SourceTrackingRaw.trackingCheck q [head] = true := by
        simpa only [hheads] using Assignment.execute_tracking q child heads hh
      have hbound : interpretation q last ≤ interpretation q head := by
        rw [hvalue]
        exact Factor.Bounds.execute_last_le_prefix q current (child, last) hstep
      have hnon : Ordinal.omega0 ^ interpretation q head ≠ interpretation q head := by
        rw [hvalue]
        rcases lt_or_eq_of_le hfloor with hstrict | heq
        · have hs := MultiplicativePrincipalInterval.intervening_not_multiplicative
            (Factor.Bounds.execute_last_le_prefix q greater (prefix, factor) hf) hstrict
            (hupper.trans_eq hgreater)
          exact fun he => hs (SourceMultiplicativePrincipal.epsilon_multiplicative _ he)
        · simpa only [heq] using hno
      have hb' : xs ∈ Branches.execute ((q, last), [head]) := by
        simpa only [hheads] using hb
      obtain ⟨d, hout, hv⟩ := branches_singleton_non_epsilon q head last xs ht hlow hm hbound hnon hb'
      simpa only [hout, List.map_singleton, hv, hvalue, ← hproduct]
  intro current xs hx hl hr
  exact hall _ current rfl xs hx hl hr

theorem execute_interval_lex (q greater prefix factor current : Nat) (xs ys : List Nat)
    (hf : (prefix, factor) ∈ Factor.execute q greater)
    (hbase : [prefix] ∈ Assignment.execute q prefix)
    (hno : Ordinal.omega0 ^ interpretation q prefix ≠ interpretation q prefix)
    (hx : xs ∈ Assignment.execute q current) (hy : ys ∈ Assignment.execute q greater)
    (hl : interpretation q prefix < interpretation q current)
    (hr : interpretation q current < interpretation q greater) :
    List.Lex (· < ·) (xs.map (interpretation q)) (ys.map (interpretation q)) := by
  have hxs := intervening_singleton_values q greater prefix factor hf hbase hno current xs hx hl hr
  obtain ⟨heads, hh, hb⟩ := IntervalFactors.actual_factor_child q greater prefix factor ys hf hy
  have he : heads = [prefix] := Part.mem_unique hh hbase
  have ht := Assignment.execute_tracking q prefix [prefix] hbase
  obtain ⟨_, _, _, hlow, _, _, _, _, hm, _, hproduct, _, _⟩ :=
    Factor.execute_spec q greater (prefix, factor) hf
  have hbound := Factor.Bounds.execute_last_le_prefix q greater (prefix, factor) hf
  have hb' : ys ∈ Branches.execute ((q, factor), [prefix]) := by simpa only [he] using hb
  obtain ⟨d, hout, hv⟩ := branches_singleton_non_epsilon q prefix factor ys ht hlow hm hbound hno hb'
  have hys : ys.map (interpretation q) = [interpretation q greater] := by
    simpa only [hout, List.map_singleton, hv, ← hproduct]
  simpa only [hxs, hys] using
    (List.Lex.rel hr : List.Lex (· < ·) [interpretation q current] [interpretation q greater])

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.SingletonIntervalOrder
