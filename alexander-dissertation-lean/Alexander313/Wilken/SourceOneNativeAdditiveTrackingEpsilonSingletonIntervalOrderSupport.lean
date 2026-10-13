import Alexander313.Wilken.SourceOneNativeAdditiveTrackingSingletonIntervalOrder

/-!
# Actual covered small updates at an original epsilon singleton

The real original conditional branch returns the singleton product when
its factor is no greater than its written head. A two-row actual table
retains the literal first head exactly when its independently tested mu
covers the second actual product. Thus a covered residual stays behind
its original epsilon head; no pair-output or selected-index equation is
assumed. All source checks remain original check zero. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.EpsilonSingletonIntervalOrderSupport

open NativeContext.SourceTrackingSequences (lastCode lastCode_singleton stripLast_singleton)
open Hereditary.FinePredecessor (stripLast)
open Alexander313.Wilken.MultiplicativePrincipalArithmetic MultiplicativeNormalForm

/-- The actual small conditional branch, including its original LOW code. -/
theorem conditional_small (head factor : Nat) (out : List Nat)
    (hh : lowCheckCode 0 head = true) (hf : lowCheckCode 0 factor = true)
    (hb : interpretation 0 factor ≤ interpretation 0 head)
    (ho : out ∈ ConditionalReplacement.execute head factor) :
    ∃ d, out = [d] ∧ Theta.acceptedLowCode 0 d = true ∧
      interpretation 0 d = interpretation 0 head * interpretation 0 factor := by
  have hr : ConditionalReplacement.raisedCheck head factor = false :=
    Bool.eq_false_of_not_eq_true (fun hr =>
      ((ConditionalReplacement.raisedCheck_exact head factor hh hf).mp hr).not_ge hb)
  have hs : out ∈ Product.smallReplacement head factor := by
    simpa only [ConditionalReplacement.execute, hr, Bool.cond_false] using ho
  exact Product.smallReplacement_spec head factor out hs

/-- Both actual rows are executed. The only passing transition uses the
real original mu, and its true flag derives the unchanged first code. -/
theorem insertion_pair_covered (head tail factor : Nat) (out : List Nat)
    (hh : SourceTrackingRaw.trackingCheck [head, tail] = true)
    (hf : lowCheckCode 0 factor = true)
    (hb : interpretation 0 factor ≤ interpretation 0 tail)
    (hc : interpretation 0 tail * interpretation 0 factor ≤
      SourceTrackingRaw.Support.muValue head)
    (ho : out ∈ Insertion.execute (factor, [head, tail])) :
    ∃ d, out = [head, d] ∧ interpretation 0 d =
      interpretation 0 tail * interpretation 0 factor := by
  obtain ⟨rows, hr, he⟩ := (Part.mem_map_iff Insertion.word).mp ho
  have hrel := InsertionSupport.executeRows_relation factor [head, tail] rows hr
  obtain ⟨a, rest, ha, ht, hrows⟩ := List.forall₂_cons_left_iff.mp hrel
  obtain ⟨b, rest', htail, hn, hrest⟩ := List.forall₂_cons_left_iff.mp ht
  have hnil : rest' = [] := List.forall₂_nil_left_iff.mp hn
  have hlow := (ConditionalReplacement.tracking_member_principal [head, tail] hh tail
    (List.mem_cons_of_mem _ List.mem_cons_self)).1
  obtain ⟨d, hd, hchecked, hv⟩ := conditional_small tail factor b.2 hlow hf hb htail.2
  have hroot : SourceTrackingRaw.Support.inputCheck head = true := by
    have hs := (SourceTrackingRaw.trackingCheck_exact [head, tail]).mp hh
    exact hs.2.1.nodes head (by change head ∈ [head]; exact List.mem_cons_self)
  have hcover : Insertion.coverCheck a.1 (Insertion.firstCode b.2) = true := by
    apply (Insertion.coverCheck_exact _ _).mpr
    simpa only [ha.1, hd, Insertion.firstCode, List.head?_cons, Option.getD_some] using
      (show SourceTrackingRaw.Support.inputCheck head = true ∧ lowCheckCode 0 d = true ∧
        interpretation 0 d ≤ SourceTrackingRaw.Support.muValue head from
        ⟨hroot, ((Theta.acceptedLowCode_iff 0 d).mp hchecked).1, by simpa only [hv] using hc⟩)
  have hs : Insertion.choose [a, b] = some (1, b.2) := by
    simp only [Insertion.choose_pair, Insertion.choose_singleton, hcover, Bool.cond_true]
  have hw : Insertion.word rows = [head, d] := by
    simp only [hrows, hrest, hnil, Insertion.word, hs, List.take_succ_cons,
      List.take_zero, List.map_cons, List.map_nil, List.singleton_append, ha.1, hd]
  exact ⟨d, he.symm.trans hw, hv⟩

/-- A residual below its earlier epsilon cannot meet the printed strict
final-head test. Its covered product is therefore the actual pair output. -/
theorem branches_pair_covered (head tail factor : Nat) (out : List Nat)
    (hh : SourceTrackingRaw.trackingCheck [head, tail] = true)
    (hf : lowCheckCode 0 factor = true)
    (hb : interpretation 0 factor ≤ interpretation 0 tail)
    (ht : interpretation 0 tail < interpretation 0 head)
    (hc : interpretation 0 tail * interpretation 0 factor ≤
      SourceTrackingRaw.Support.muValue head)
    (ho : out ∈ Branches.execute (factor, [head, tail])) :
    ∃ d, out = [head, d] ∧ interpretation 0 d =
      interpretation 0 tail * interpretation 0 factor := by
  have ha : BranchesSupport.appendCheck factor [head, tail] = false :=
    Bool.eq_false_of_not_eq_true (fun ha => by
      have hs := (BranchesSupport.appendCheck_exact factor [head, tail] hh).mp ha
      have hstrict : interpretation 0 head < interpretation 0 tail := by
        simpa [stripLast, lastCode] using hs.2.1
      exact ht.not_ge hstrict.le)
  have hi : out ∈ Insertion.execute (factor, [head, tail]) := by
    simpa only [Branches.execute, ha, Bool.cond_false] using ho
  exact insertion_pair_covered head tail factor out hh hf hb hc hi

/-- At an actual original epsilon singleton, genuine cover derives the
printed append branch, with the original source floor one. -/
theorem branches_singleton_covered (head factor : Nat) (out : List Nat)
    (hh : SourceTrackingRaw.trackingCheck [head] = true)
    (he : Ordinal.omega0 ^ interpretation 0 head = interpretation 0 head)
    (hf : lowCheckCode 0 factor = true)
    (hc : interpretation 0 factor ≤ SourceTrackingRaw.Support.muValue head)
    (ho : out ∈ Branches.execute (factor, [head])) : out = [head, factor] := by
  have hl := (ConditionalReplacement.tracking_member_principal [head] hh head List.mem_cons_self).1
  have hr := (SourceTrackingRaw.Support.inputCheck_exact head).mpr
    ⟨hl, EpsilonOffsets.epsilon_one_lt he, he⟩
  have ha : BranchesSupport.appendCheck factor [head] = true :=
    (BranchesSupport.appendCheck_exact factor [head] hh).mpr
      ⟨by simpa only [lastCode_singleton] using hr,
        by simpa only [stripLast_singleton, if_pos rfl, lastCode_singleton] using
          EpsilonOffsets.epsilon_one_lt he,
        hf, by simpa only [lastCode_singleton] using hc⟩
  simpa only [Branches.execute, ha, Bool.cond_true, Part.mem_some_iff,
    List.singleton_append] using ho

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.EpsilonSingletonIntervalOrderSupport
