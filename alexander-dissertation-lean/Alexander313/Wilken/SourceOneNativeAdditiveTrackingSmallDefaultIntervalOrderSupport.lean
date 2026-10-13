import Alexander313.Wilken.SourceOneNativeAdditiveTrackingSmallInsertionIntervalOrder

/-!
# Genuine FIRST alternatives without a preceding covered cut

The actual first ordinary row is its singleton product. If no transition
passes, that actual row supplies FIRST; if a transition passes, the real
scan retains the unchanged first written head. A true printed append also
retains that head. No selection, suffix or output shape is assumed.
Original check zero throughout; source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.SmallDefaultIntervalOrderSupport

/-- Genuine execution and the first row's ordinary test derive exactly
the unchanged/product FIRST alternative, for any independently executed tail. -/
theorem insertion_small_first (head factor : Nat) (rest out : List Nat)
    (hh : SourceTrackingRaw.trackingCheck (head :: rest) = true)
    (hf : lowCheckCode 0 factor = true)
    (hb : interpretation 0 factor ≤ interpretation 0 head)
    (ho : out ∈ Insertion.execute (factor, head :: rest)) :
    ∃ first tail, out = first :: tail ∧
      (interpretation 0 first = interpretation 0 head ∨
        interpretation 0 first = interpretation 0 head * interpretation 0 factor) := by
  obtain ⟨rows, hr, hout⟩ := (Part.mem_map_iff Insertion.word).mp ho
  have hrel := InsertionSupport.executeRows_relation factor (head :: rest) rows hr
  obtain ⟨a, after, ha, ht, he⟩ := List.forall₂_cons_left_iff.mp hrel
  have hlow := (ConditionalReplacement.tracking_member_principal (head :: rest)
    hh head List.mem_cons_self).1
  obtain ⟨d, hd, hc, hv⟩ := EpsilonSingletonIntervalOrderSupport.conditional_small
    head factor a.2 hlow hf hb ha.2
  cases hs : Insertion.choose (a :: after) with
  | none =>
    have hw := (Insertion.word_default a after hs).1
    refine ⟨d, [], ?_, Or.inr hv⟩
    exact hout.symm.trans ((congrArg Insertion.word he).trans (hw.trans hd))
  | some selected =>
    obtain ⟨tail, hw⟩ := SmallInsertionIntervalOrderSupport.word_selected_first a after selected hs
    refine ⟨head, tail, ?_, Or.inl rfl⟩
    exact hout.symm.trans ((congrArg Insertion.word he).trans
      (hw.trans (congrArg (fun x : Nat => x :: tail) ha.1)))

/-- Both real branches derive the same FIRST alternative. A literal
factor append leaves FIRST unchanged even when the whole tail is nonempty. -/
theorem branches_small_first (head factor : Nat) (rest out : List Nat)
    (hh : SourceTrackingRaw.trackingCheck (head :: rest) = true)
    (hf : lowCheckCode 0 factor = true)
    (hb : interpretation 0 factor ≤ interpretation 0 head)
    (ho : out ∈ Branches.execute (factor, head :: rest)) :
    ∃ first tail, out = first :: tail ∧
      (interpretation 0 first = interpretation 0 head ∨
        interpretation 0 first = interpretation 0 head * interpretation 0 factor) := by
  rcases Branches.execute_branch factor (head :: rest) out ho with ⟨ha, he⟩ | ⟨ha, hi⟩
  · exact ⟨head, rest ++ [factor], by simpa only [List.cons_append] using he, Or.inl rfl⟩
  · exact insertion_small_first head factor rest out hh hf hb hi

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.SmallDefaultIntervalOrderSupport
