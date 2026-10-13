import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingIntervalFactors

/-!
# Actual singleton small updates

The actual replacement table of a one-entry headword has one row and no
passing transition. A genuine small factor therefore produces its literal
singleton principal product. When the actual old head is non-epsilon,
the real append test is false, so the printed dispatcher uses precisely
that independently executing insertion. No replacement or flag is input.
Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.SingletonIntervalOrderSupport

open PublicEpsilonUnboundedIota SourceTrackingSequences
open Alexander313.Wilken.MultiplicativePrincipalArithmetic

theorem singleton_values_shape (q : Nat) (xs : List Nat) (value : Ordinal.{0})
    (he : xs.map (interpretation q) = [value]) :
    ∃ head, xs = [head] ∧ interpretation q head = value := by
  have hn : xs.length = 1 := by
    simpa only [List.length_map, List.length_singleton] using congrArg List.length he
  obtain ⟨head, rfl⟩ := List.length_eq_one_iff.mp hn
  exact ⟨head, rfl, by simpa only [List.map_singleton, List.singleton_inj] using he⟩

theorem insertion_singleton_small (q head factor : Nat) (out : List Nat)
    (hh : SourceTrackingRaw.trackingCheck q [head] = true)
    (hf : lowCheckCode q factor = true)
    (hm : IsMultiplicativePrincipal (interpretation q factor))
    (hb : interpretation q factor ≤ interpretation q head)
    (ho : out ∈ Insertion.execute ((q, factor), [head])) :
    ∃ d, out = [d] ∧ interpretation q d = interpretation q head * interpretation q factor := by
  obtain ⟨rows, hr, he⟩ := (Part.mem_map_iff (Insertion.word q)).mp ho
  have hrel := InsertionSupport.executeRows_relation q factor [head] rows hr
  have hheads := InsertionSupport.relation_heads q factor hrel
  have hn : rows.length = 1 := by
    simpa only [List.length_map, List.length_singleton] using congrArg List.length hheads
  obtain ⟨row, hrow⟩ := List.length_eq_one_iff.mp hn
  rw [hrow] at hrel hheads he
  have hhead : row.1 = head := by
    simpa only [List.map_singleton, List.singleton_inj] using hheads
  have hc := (InsertionSupport.relation_members q factor hrel row List.mem_cons_self).2
  have hcond : row.2 ∈ ConditionalReplacement.execute q head factor := by
    simpa only [hhead] using hc
  have hout : out = row.2 := he.symm.trans
    (Insertion.word_default q row [] (Insertion.choose_singleton q row)).1
  have hs := ConditionalReplacement.execute_spec q [head] hh head factor
    List.mem_cons_self hf hm (by simpa only [lastCode_singleton] using hb) row.2 hcond
  rcases hs.2.2 with hraised | ⟨hsmall, d, hd, hv⟩
  · exact False.elim (hraised.1.not_ge hb)
  · exact ⟨d, hout.trans hd, hv⟩

theorem branches_singleton_non_epsilon (q head factor : Nat) (out : List Nat)
    (hh : SourceTrackingRaw.trackingCheck q [head] = true)
    (hf : lowCheckCode q factor = true)
    (hm : IsMultiplicativePrincipal (interpretation q factor))
    (hb : interpretation q factor ≤ interpretation q head)
    (hno : Ordinal.omega0 ^ interpretation q head ≠ interpretation q head)
    (ho : out ∈ Branches.execute ((q, factor), [head])) :
    ∃ d, out = [d] ∧ interpretation q d = interpretation q head * interpretation q factor := by
  have ha : BranchesSupport.appendCheck q factor [head] = false :=
    Bool.eq_false_of_not_eq_true (by
      intro ha
      have hs := (BranchesSupport.appendCheck_exact q factor [head] hh).mp ha
      have hr : SourceTrackingRaw.Support.inputCheck q head = true := by
        simpa only [lastCode_singleton] using hs.1
      exact hno ((SourceTrackingRaw.Support.inputCheck_exact q head).mp hr).2.2)
  have hi : out ∈ Insertion.execute ((q, factor), [head]) := by
    simpa only [Branches.execute, ha, Bool.cond_false] using ho
  exact insertion_singleton_small q head factor out hh hf hm hb hi

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.SingletonIntervalOrderSupport
