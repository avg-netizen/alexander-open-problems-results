import Alexander313.Wilken.SourceOneNativeAdditiveTrackingIntervalFrames

/-!
# Actual singleton updates in the original check-zero dictionary

The independently executing replacement table of a one-entry original
headword has one actual row and no passing transition. A genuine small
factor therefore returns its singleton product. For a non-epsilon head
the actual printed append test is false. All flags and memberships are
derived from original check-zero execution, never a Native base-one
parser or an assumed update equation. Source-only uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.SingletonIntervalOrderSupport

open NativeContext.SourceTrackingSequences (lastCode lastCode_singleton)
open Alexander313.Wilken.MultiplicativePrincipalArithmetic

theorem singleton_values_shape (xs : List Nat) (value : Ordinal.{0})
    (he : xs.map (interpretation 0) = [value]) :
    ∃ head, xs = [head] ∧ interpretation 0 head = value := by
  have hn : xs.length = 1 := by
    simpa only [List.length_map, List.length_singleton] using congrArg List.length he
  obtain ⟨head, rfl⟩ := List.length_eq_one_iff.mp hn
  exact ⟨head, rfl, by simpa only [List.map_singleton, List.singleton_inj] using he⟩

theorem insertion_singleton_small (head factor : Nat) (out : List Nat)
    (hh : SourceTrackingRaw.trackingCheck [head] = true)
    (hf : lowCheckCode 0 factor = true)
    (hm : IsMultiplicativePrincipal (interpretation 0 factor))
    (hb : interpretation 0 factor ≤ interpretation 0 head)
    (ho : out ∈ Insertion.execute (factor, [head])) :
    ∃ d, out = [d] ∧ interpretation 0 d = interpretation 0 head * interpretation 0 factor := by
  obtain ⟨rows, hr, he⟩ := (Part.mem_map_iff Insertion.word).mp ho
  have hrel := InsertionSupport.executeRows_relation factor [head] rows hr
  have hheads := InsertionSupport.relation_heads factor hrel
  have hn : rows.length = 1 := by
    simpa only [List.length_map, List.length_singleton] using congrArg List.length hheads
  obtain ⟨row, hrow⟩ := List.length_eq_one_iff.mp hn
  rw [hrow] at hrel hheads he
  have hhead : row.1 = head := by
    simpa only [List.map_singleton, List.singleton_inj] using hheads
  have hc := (InsertionSupport.relation_members factor hrel row List.mem_cons_self).2
  have hcond : row.2 ∈ ConditionalReplacement.execute head factor := by
    simpa only [hhead] using hc
  have hout : out = row.2 := he.symm.trans
    (Insertion.word_default row [] (Insertion.choose_singleton row)).1
  have hs := ConditionalReplacement.execute_spec [head] hh head factor
    List.mem_cons_self hf hm (by simpa only [lastCode_singleton] using hb) row.2 hcond
  rcases hs.2.2.2.2 with hraised | ⟨hsmall, d, hd, hv⟩
  · exact False.elim (hraised.1.not_ge hb)
  · exact ⟨d, hout.trans hd, hv⟩

theorem branches_singleton_non_epsilon (head factor : Nat) (out : List Nat)
    (hh : SourceTrackingRaw.trackingCheck [head] = true)
    (hf : lowCheckCode 0 factor = true)
    (hm : IsMultiplicativePrincipal (interpretation 0 factor))
    (hb : interpretation 0 factor ≤ interpretation 0 head)
    (hno : Ordinal.omega0 ^ interpretation 0 head ≠ interpretation 0 head)
    (ho : out ∈ Branches.execute (factor, [head])) :
    ∃ d, out = [d] ∧ interpretation 0 d = interpretation 0 head * interpretation 0 factor := by
  have ha : BranchesSupport.appendCheck factor [head] = false :=
    Bool.eq_false_of_not_eq_true (by
      intro ha
      have hs := (BranchesSupport.appendCheck_exact factor [head] hh).mp ha
      have hr : SourceTrackingRaw.Support.inputCheck head = true := by
        simpa only [lastCode_singleton] using hs.1
      exact hno ((SourceTrackingRaw.Support.inputCheck_exact head).mp hr).2.2)
  have hi : out ∈ Insertion.execute (factor, [head]) := by
    simpa only [Branches.execute, ha, Bool.cond_false] using ho
  exact insertion_singleton_small head factor out hh hf hm hb hi

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.SingletonIntervalOrderSupport
