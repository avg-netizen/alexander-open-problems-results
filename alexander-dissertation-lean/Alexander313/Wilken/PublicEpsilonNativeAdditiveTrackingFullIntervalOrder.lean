import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingRaisedDefaultIntervalOrder
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingRaisedInsertionIntervalOrder
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingSmallDefaultIntervalOrder
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingSmallInsertionIntervalOrder
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingAppendIntervalOrder

/-!
# All actual printed native greater branches in the critical factor interval

The independently executing greater Assignment derives its real child
and dispatcher. Its literal append flag selects append or actual insertion;
the concrete greatest selector then selects NONE or a real transition.
The ordinary/raised comparison at that observed written head exhausts the
remaining cases. The established actual factor-unwind proofs therefore
compare every smaller interval execution, with no branch/index/suffix
Assignment, accumulated order or endpoint oracle. Source-only uncompiled candidates in genuine native epsilon contexts.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.IntervalOrder

/-- A genuine greater Factor and two independent complete Assignments
suffice for strict word order throughout its critical prefix interval. -/
theorem execute_interval_lex (q greater prefix factor input : Nat) (xs ys : List Nat)
    (hf : (prefix, factor) ∈ Factor.execute q greater)
    (hx : xs ∈ Assignment.execute q input) (hy : ys ∈ Assignment.execute q greater)
    (hl : interpretation q prefix < interpretation q input)
    (hr : interpretation q input < interpretation q greater) :
    List.Lex (· < ·) (xs.map (interpretation q)) (ys.map (interpretation q)) := by
  obtain ⟨heads, hh, hb⟩ := IntervalFactors.actual_factor_child q greater prefix factor ys hf hy
  cases ha : BranchesSupport.appendCheck q factor heads with
  | true =>
    exact AppendIntervalOrder.execute_interval_lex q greater prefix factor input heads xs ys
      hf hh ha hx hy hl hr
  | false =>
    have hi : ys ∈ Insertion.execute ((q, factor), heads) := by
      simpa only [Branches.execute, ha, Bool.cond_false] using hb
    obtain ⟨rows, hrows, hword⟩ := (Part.mem_map_iff (Insertion.word q)).mp hi
    cases hs : Insertion.choose q rows with
    | none =>
      by_cases hsmall : interpretation q factor ≤ interpretation q (Insertion.firstCode heads)
      · exact SmallDefaultIntervalOrder.execute_small_default_interval_lex q greater prefix factor input
          heads xs ys rows hf hh ha hrows hs hsmall hx hy hl hr
      · exact RaisedDefaultIntervalOrder.execute_raised_default_interval_lex q greater prefix factor input
          heads xs ys rows hf hh ha hrows hs (lt_of_not_ge hsmall) hx hy hl hr
    | some chosen =>
      obtain ⟨n, replacement⟩ := chosen
      by_cases hsmall : interpretation q factor ≤ interpretation q (Insertion.firstCode (heads.drop n))
      · exact SmallInsertionIntervalOrder.execute_small_selected_interval_lex q greater prefix factor input
          heads xs ys rows n replacement hf hh ha hrows hs hsmall hx hy hl hr
      · exact RaisedInsertionIntervalOrder.execute_raised_selected_interval_lex q greater prefix factor input
          heads xs ys rows n replacement hf hh ha hrows hs (lt_of_not_ge hsmall) hx hy hl hr

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.IntervalOrder
