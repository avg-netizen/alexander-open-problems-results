import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingSmallInsertionIntervalOrder

/-!
# Actual ordinary FIRST alternatives without a preceding cut

The first real row is its singleton product. A true later selection
retains its unchanged written head; no selection uses that product.
Actual append also retains FIRST. Each alternative follows from actual
row and branch membership, not a supplied word shape. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.SmallDefaultIntervalOrderSupport

open Alexander313.Wilken.MultiplicativePrincipalArithmetic
open SourceTrackingSequences (lastCode)

theorem insertion_small_first (q head factor : Nat) (rest out : List Nat)
    (hh : SourceTrackingRaw.trackingCheck q (head :: rest) = true)
    (hf : lowCheckCode q factor = true) (hm : IsMultiplicativePrincipal (interpretation q factor))
    (hbound : interpretation q factor ≤ interpretation q (lastCode (head :: rest)))
    (hb : interpretation q factor ≤ interpretation q head)
    (ho : out ∈ Insertion.execute ((q, factor), head :: rest)) :
    ∃ first tail, out = first :: tail ∧
      (interpretation q first = interpretation q head ∨
        interpretation q first = interpretation q head * interpretation q factor) := by
  obtain ⟨rows, hr, hout⟩ := (Part.mem_map_iff (Insertion.word q)).mp ho
  have hrel := InsertionSupport.executeRows_relation q factor (head :: rest) rows hr
  obtain ⟨a, after, ha, ht, he⟩ := List.forall₂_cons_left_iff.mp hrel
  obtain ⟨d, hd, hlow, hv⟩ := EpsilonSingletonIntervalOrderSupport.conditional_small q
    (head :: rest) hh head factor List.mem_cons_self hf hm hbound hb a.2 ha.2
  cases hs : Insertion.choose q (a :: after) with
  | none =>
    have hw := (Insertion.word_default q a after hs).1
    refine ⟨d, [], ?_, Or.inr hv⟩
    exact hout.symm.trans ((congrArg (Insertion.word q) he).trans (hw.trans hd))
  | some selected =>
    obtain ⟨tail, hw⟩ := SmallInsertionIntervalOrderSupport.word_selected_first q a after selected hs
    refine ⟨head, tail, ?_, Or.inl rfl⟩
    exact hout.symm.trans ((congrArg (Insertion.word q) he).trans
      (hw.trans (congrArg (fun x : Nat => x :: tail) ha.1)))

theorem branches_small_first (q head factor : Nat) (rest out : List Nat)
    (hh : SourceTrackingRaw.trackingCheck q (head :: rest) = true)
    (hf : lowCheckCode q factor = true) (hm : IsMultiplicativePrincipal (interpretation q factor))
    (hbound : interpretation q factor ≤ interpretation q (lastCode (head :: rest)))
    (hb : interpretation q factor ≤ interpretation q head)
    (ho : out ∈ Branches.execute ((q, factor), head :: rest)) :
    ∃ first tail, out = first :: tail ∧
      (interpretation q first = interpretation q head ∨
        interpretation q first = interpretation q head * interpretation q factor) := by
  rcases Branches.execute_branch q factor (head :: rest) out ho with ⟨ha, he⟩ | ⟨ha, hi⟩
  · exact ⟨head, rest ++ [factor], by simpa only [List.cons_append] using he, Or.inl rfl⟩
  · exact insertion_small_first q head factor rest out hh hf hm hbound hb hi

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.SmallDefaultIntervalOrderSupport
