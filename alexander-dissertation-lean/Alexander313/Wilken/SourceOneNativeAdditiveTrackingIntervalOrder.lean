import Alexander313.Wilken.SourceOneNativeAdditiveTrackingRaisedDefaultIntervalOrder
import Alexander313.Wilken.SourceOneNativeAdditiveTrackingRaisedInsertionIntervalOrder
import Alexander313.Wilken.SourceOneNativeAdditiveTrackingSmallDefaultIntervalOrder
import Alexander313.Wilken.SourceOneNativeAdditiveTrackingSmallInsertionIntervalOrder
import Alexander313.Wilken.SourceOneNativeAdditiveTrackingAppendIntervalOrder

/-!
# All actual printed greater branches in the critical factor interval

The independently executing greater Assignment derives its real child
and dispatcher. Its literal append flag selects append or actual insertion;
the concrete greatest selector then selects NONE or a real transition.
The ordinary/raised comparison at that observed written head exhausts the
remaining cases. The established actual factor-unwind proofs therefore
compare every smaller interval execution, with no branch/index/suffix
Assignment, accumulated order or endpoint oracle. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.IntervalOrder

/-- A genuine greater Factor and two independent complete Assignments
suffice for strict word order throughout its critical prefix interval. -/
theorem execute_interval_lex (greater prefix factor input : Nat) (xs ys : List Nat)
    (hf : (prefix, factor) ∈ Factor.execute greater)
    (hx : xs ∈ Assignment.execute input) (hy : ys ∈ Assignment.execute greater)
    (hl : interpretation 0 prefix < interpretation 0 input)
    (hr : interpretation 0 input < interpretation 0 greater) :
    List.Lex (· < ·) (xs.map (interpretation 0)) (ys.map (interpretation 0)) := by
  obtain ⟨heads, hh, hb⟩ := FrameFactorOrder.actual_factor_child greater prefix factor ys hf hy
  cases ha : BranchesSupport.appendCheck factor heads with
  | true =>
    exact AppendIntervalOrder.execute_interval_append_lex greater prefix factor input heads xs ys
      hf hh ha hx hy hl hr
  | false =>
    have hi : ys ∈ Insertion.execute (factor, heads) := by
      simpa only [Branches.execute, ha, Bool.cond_false] using hb
    obtain ⟨rows, hrows, hword⟩ := (Part.mem_map_iff Insertion.word).mp hi
    cases hs : Insertion.choose rows with
    | none =>
      by_cases hsmall : interpretation 0 factor ≤ interpretation 0 (Insertion.firstCode heads)
      · exact SmallDefaultIntervalOrder.execute_small_default_interval_lex greater prefix factor input
          heads xs ys rows hf hh ha hrows hs hsmall hx hy hl hr
      · exact RaisedDefaultIntervalOrder.execute_raised_default_interval_lex greater prefix factor input
          heads xs ys rows hf hh ha hrows hs (lt_of_not_ge hsmall) hx hy hl hr
    | some chosen =>
      obtain ⟨n, replacement⟩ := chosen
      by_cases hsmall : interpretation 0 factor ≤ interpretation 0 (Insertion.firstCode (heads.drop n))
      · exact SmallInsertionIntervalOrder.execute_small_selected_interval_lex greater prefix factor input
          heads xs ys rows n replacement hf hh ha hrows hs hsmall hx hy hl hr
      · exact RaisedInsertionIntervalOrder.execute_raised_selected_interval_lex greater prefix factor input
          heads xs ys rows n replacement hf hh ha hrows hs (lt_of_not_ge hsmall) hx hy hl hr

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.IntervalOrder
