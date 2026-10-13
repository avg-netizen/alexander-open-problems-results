import Alexander313.Wilken.SourceOneNativeAdditiveTrackingSingletonIntervalOrderSupport

/-!
# A genuine original several-factor interval at a non-epsilon singleton child

The greater recursive prefix has an actual literal singleton assignment
and is non-epsilon. The real finite original factor segment keeps every
remaining child above that prefix. Every factor is below the greater
factor, itself below the prefix, so each actual update remains small.
Actual nonmultiplicative guards exclude epsilon intermediate heads.
Independent full execution therefore yields the singleton actual product
throughout the entire segment. No supplied fuel, child word, flag or
accumulation inequality is used. Epsilon and longer child words remain
separate. Source-only uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.SingletonIntervalOrder

open SingletonIntervalOrderSupport
open Alexander313.Wilken.MultiplicativePrincipalArithmetic

theorem segment_input_floor {target bound current : Nat} {frames : List IntervalFrames.Frame}
    (hs : IntervalFrames.Segment target bound current frames) :
    interpretation 0 target ≤ interpretation 0 current := by
  induction hs with
  | nil => exact le_rfl
  | cons current child factor frames hf hsmall ht ih =>
    obtain ⟨_, _, _, _, _, _, hm, _, hproduct, _, _⟩ :=
      Factor.execute_spec current (child, factor) hf
    exact ih.trans (by rw [hproduct]; exact Ordinal.le_mul_left _ hm.1)

theorem segment_non_epsilon {target bound current : Nat} {frames : List IntervalFrames.Frame}
    (hs : IntervalFrames.Segment target bound current frames)
    (hno : Ordinal.omega0 ^ interpretation 0 target ≠ interpretation 0 target) :
    Ordinal.omega0 ^ interpretation 0 current ≠ interpretation 0 current := by
  cases hs with
  | nil => exact hno
  | cons current child factor frames hf hsmall ht =>
    have hi := (Factor.inputCheck_exact current).mp (Factor.execute_spec current (child, factor) hf).1
    exact fun he => hi.2.2.2 (NativeContext.SourceMultiplicativePrincipal.epsilon_multiplicative _ he)

theorem segment_singleton_values {prefix factor current : Nat} {frames : List IntervalFrames.Frame}
    (hs : IntervalFrames.Segment prefix factor current frames)
    (hbase : [prefix] ∈ Assignment.execute prefix)
    (hno : Ordinal.omega0 ^ interpretation 0 prefix ≠ interpretation 0 prefix)
    (hbound : interpretation 0 factor ≤ interpretation 0 prefix)
    (out : List Nat) (ho : out ∈ Assignment.execute current) :
    out.map (interpretation 0) = [interpretation 0 current] := by
  induction hs generalizing out with
  | nil =>
    have he : out = [prefix] := Part.mem_unique ho hbase
    simp only [he, List.map_singleton]
  | cons current child last frames hf hsmall ht ih =>
    obtain ⟨heads, hh, hb⟩ := FrameFactorOrder.actual_factor_child current child last out hf ho
    have hvalues := ih heads hh
    obtain ⟨head, hheads, hvalue⟩ := singleton_values_shape heads _ hvalues
    have htrack : SourceTrackingRaw.trackingCheck [head] = true := by
      simpa only [hheads] using Assignment.execute_tracking child heads hh
    obtain ⟨_, _, hlow, _, _, _, hm, _, hproduct, _, _⟩ :=
      Factor.execute_spec current (child, last) hf
    have hfactor : interpretation 0 last ≤ interpretation 0 head := by
      rw [hvalue]
      exact hsmall.le.trans (hbound.trans (segment_input_floor ht))
    have hnon : Ordinal.omega0 ^ interpretation 0 head ≠ interpretation 0 head := by
      simpa only [hvalue] using segment_non_epsilon ht hno
    have hb' : out ∈ Branches.execute (last, [head]) := by
      simpa only [hheads] using hb
    obtain ⟨d, hout, hv⟩ := branches_singleton_non_epsilon head last out htrack
      ((Theta.acceptedLowCode_iff 0 last).mp hlow).1 hm hfactor hnon hb'
    simpa only [hout, List.map_singleton, hv, hvalue, ← hproduct]

theorem intervening_singleton_values (greater prefix factor current : Nat) (out : List Nat)
    (hf : (prefix, factor) ∈ Factor.execute greater)
    (hbase : [prefix] ∈ Assignment.execute prefix)
    (hno : Ordinal.omega0 ^ interpretation 0 prefix ≠ interpretation 0 prefix)
    (ho : out ∈ Assignment.execute current)
    (hl : interpretation 0 prefix < interpretation 0 current)
    (hr : interpretation 0 current < interpretation 0 greater) :
    out.map (interpretation 0) = [interpretation 0 current] := by
  obtain ⟨frames, hs⟩ := IntervalFrames.interval_segment_returns greater prefix factor current hf
    (Assignment.execute_spec current out ho).1 hl hr
  exact segment_singleton_values hs hbase hno
    (Factor.Bounds.execute_last_le_prefix greater (prefix, factor) hf) out ho

theorem execute_interval_lex (greater prefix factor current : Nat) (xs ys : List Nat)
    (hf : (prefix, factor) ∈ Factor.execute greater)
    (hbase : [prefix] ∈ Assignment.execute prefix)
    (hno : Ordinal.omega0 ^ interpretation 0 prefix ≠ interpretation 0 prefix)
    (hx : xs ∈ Assignment.execute current) (hy : ys ∈ Assignment.execute greater)
    (hl : interpretation 0 prefix < interpretation 0 current)
    (hr : interpretation 0 current < interpretation 0 greater) :
    List.Lex (· < ·) (xs.map (interpretation 0)) (ys.map (interpretation 0)) := by
  have hxs := intervening_singleton_values greater prefix factor current xs hf hbase hno hx hl hr
  obtain ⟨heads, hh, hb⟩ := FrameFactorOrder.actual_factor_child greater prefix factor ys hf hy
  have he : heads = [prefix] := Part.mem_unique hh hbase
  have ht := Assignment.execute_tracking prefix [prefix] hbase
  obtain ⟨_, _, hlow, _, _, _, hm, _, hproduct, _, _⟩ :=
    Factor.execute_spec greater (prefix, factor) hf
  have hbound := Factor.Bounds.execute_last_le_prefix greater (prefix, factor) hf
  have hb' : ys ∈ Branches.execute (factor, [prefix]) := by simpa only [he] using hb
  obtain ⟨d, hout, hv⟩ := branches_singleton_non_epsilon prefix factor ys ht
    ((Theta.acceptedLowCode_iff 0 factor).mp hlow).1 hm hbound hno hb'
  have hys : ys.map (interpretation 0) = [interpretation 0 greater] := by
    simpa only [hout, List.map_singleton, hv, ← hproduct]
  simpa only [hxs, hys] using
    (List.Lex.rel hr : List.Lex (· < ·) [interpretation 0 current] [interpretation 0 greater])

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.SingletonIntervalOrder
