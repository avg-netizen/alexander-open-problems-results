import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingSingletonIntervalOrderSupport

/-!
# Genuine covered updates of a two-entry original headword

Actual small replacements at both written rows and the real cover of the
second product force the executing selector to retain the first head.
The tail is below that head, so the printed append flag is genuinely
false. No replacement row, output pair or selector flag is supplied.
These are original SAME-q callers; uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.EpsilonSingletonIntervalOrderSupport

open PublicEpsilonUnboundedIota
open Alexander313.Wilken.MultiplicativePrincipalArithmetic
open SourceTrackingSequences (lastCode lastCode_singleton stripLast_append_singleton)
open Hereditary.FinePredecessor (stripLast)

theorem pair_head_input (q head tail : Nat)
    (hh : SourceTrackingRaw.trackingCheck q [head, tail] = true) :
    SourceTrackingRaw.Support.inputCheck q head = true := by
  have hstrip : stripLast [head, tail] = [head] := by
    change stripLast ([head] ++ [tail]) = [head]
    exact stripLast_append_singleton _ _
  exact ((SourceTrackingRaw.trackingCheck_conditions q [head, tail]).mp hh).2.1.nodes
    head (by rw [hstrip]; exact List.mem_cons_self)

theorem pair_values_shape (q : Nat) (xs : List Nat) (a b : Ordinal.{0})
    (he : xs.map (interpretation q) = [a, b]) :
    ∃ head tail, xs = [head, tail] ∧ interpretation q head = a ∧ interpretation q tail = b := by
  cases xs with
  | nil => simp only [List.map_nil, List.nil_ne_cons] at he
  | cons head rest =>
    cases rest with
    | nil => simp only [List.map_cons, List.map_nil, List.cons.injEq, List.nil_ne_cons,
        and_false] at he
    | cons tail rest =>
      have hs := List.cons.inj he
      have ht := List.cons.inj hs.2
      have hn : rest = [] := List.map_eq_nil_iff.mp ht.2
      exact ⟨head, tail, by rw [hn], hs.1, ht.1⟩

theorem conditional_small (q : Nat) (heads : List Nat)
    (hh : SourceTrackingRaw.trackingCheck q heads = true) (head factor : Nat)
    (hhead : head ∈ heads) (hf : lowCheckCode q factor = true)
    (hm : IsMultiplicativePrincipal (interpretation q factor))
    (hbound : interpretation q factor ≤ interpretation q (lastCode heads))
    (hsmall : interpretation q factor ≤ interpretation q head)
    (out : List Nat) (ho : out ∈ ConditionalReplacement.execute q head factor) :
    ∃ d, out = [d] ∧ lowCheckCode q d = true ∧
      interpretation q d = interpretation q head * interpretation q factor := by
  have hs := ConditionalReplacement.execute_spec q heads hh head factor hhead hf hm hbound out ho
  rcases hs.2.2 with hraised | ⟨hle, d, hd, hv⟩
  · exact False.elim (hraised.1.not_ge hsmall)
  · exact ⟨d, hd, (hs.2.1 d (by rw [hd]; exact List.mem_cons_self)).1, hv⟩

theorem insertion_pair_covered (q head tail factor : Nat) (out : List Nat)
    (hh : SourceTrackingRaw.trackingCheck q [head, tail] = true)
    (hf : lowCheckCode q factor = true)
    (hm : IsMultiplicativePrincipal (interpretation q factor))
    (hsmall : interpretation q factor ≤ interpretation q tail)
    (htail : interpretation q tail ≤ interpretation q head)
    (hcover : interpretation q tail * interpretation q factor ≤ SourceTrackingRaw.Support.muValue q head)
    (ho : out ∈ Insertion.execute ((q, factor), [head, tail])) :
    ∃ d, out = [head, d] ∧
      interpretation q d = interpretation q tail * interpretation q factor := by
  obtain ⟨rows, hr, he⟩ := (Part.mem_map_iff (Insertion.word q)).mp ho
  have hrel := InsertionSupport.executeRows_relation q factor [head, tail] rows hr
  obtain ⟨a, rest, ha, ht, hrows⟩ := List.forall₂_cons_left_iff.mp hrel
  obtain ⟨b, rest', hb, hn, hrest⟩ := List.forall₂_cons_left_iff.mp ht
  have hnil : rest' = [] := List.forall₂_nil_left_iff.mp hn
  have hrows' : rows = [a, b] := by simpa only [hrest, hnil] using hrows
  have hbound : interpretation q factor ≤ interpretation q (lastCode [head, tail]) := by
    simpa only [SkTracking.Support.lastCode_cons_nonempty head [tail] (List.cons_ne_nil _ _),
      lastCode_singleton] using hsmall
  have hca : a.2 ∈ ConditionalReplacement.execute q head factor := ha.2
  have hcb : b.2 ∈ ConditionalReplacement.execute q tail factor := hb.2
  obtain ⟨da, hda, hla, hva⟩ := conditional_small q [head, tail] hh head factor
    List.mem_cons_self hf hm hbound (hsmall.trans htail) a.2 hca
  obtain ⟨db, hdb, hlb, hvb⟩ := conditional_small q [head, tail] hh tail factor
    (List.mem_cons_of_mem _ List.mem_cons_self) hf hm hbound hsmall b.2 hcb
  have hroot := pair_head_input q head tail hh
  have hc : Insertion.coverCheck q a.1 (Insertion.firstCode b.2) = true := by
    apply (Insertion.coverCheck_exact q _ _).mpr
    simpa only [ha.1, hdb, Insertion.firstCode, List.head?_cons, Option.getD_some, hvb] using
      And.intro hroot (And.intro hlb hcover)
  have hs : Insertion.choose q [a, b] = some (1, b.2) := by
    simp only [Insertion.choose_pair, Insertion.choose_singleton, hc, Bool.cond_true]
  have hw : Insertion.word q rows = [head, db] := by
    simp only [hrows', Insertion.word, hs, List.take_succ_cons, List.take_zero,
      List.map_cons, List.map_nil, List.singleton_append, ha.1, hdb]
  exact ⟨db, he.symm.trans hw, hvb⟩

theorem branches_pair_covered (q head tail factor : Nat) (out : List Nat)
    (hh : SourceTrackingRaw.trackingCheck q [head, tail] = true)
    (hf : lowCheckCode q factor = true)
    (hm : IsMultiplicativePrincipal (interpretation q factor))
    (hsmall : interpretation q factor ≤ interpretation q tail)
    (htail : interpretation q tail < interpretation q head)
    (hcover : interpretation q tail * interpretation q factor ≤ SourceTrackingRaw.Support.muValue q head)
    (ho : out ∈ Branches.execute ((q, factor), [head, tail])) :
    ∃ d, out = [head, d] ∧
      interpretation q d = interpretation q tail * interpretation q factor := by
  have hstrip : stripLast [head, tail] = [head] := by
    change stripLast ([head] ++ [tail]) = [head]
    exact stripLast_append_singleton _ _
  have ha : BranchesSupport.appendCheck q factor [head, tail] = false :=
    Bool.eq_false_of_not_eq_true (by
      intro he
      have hs := (BranchesSupport.appendCheck_exact q factor [head, tail] hh).mp he
      have hlt : interpretation q head < interpretation q tail := by
        simpa only [hstrip, lastCode_singleton,
          SkTracking.Support.lastCode_cons_nonempty head [tail] (List.cons_ne_nil _ _),
          List.cons_ne_nil, if_false] using hs.2.1
      exact htail.not_ge hlt.le)
  have hi : out ∈ Insertion.execute ((q, factor), [head, tail]) := by
    simpa only [Branches.execute, ha, Bool.cond_false] using ho
  exact insertion_pair_covered q head tail factor out hh hf hm hsmall htail.le hcover hi

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.EpsilonSingletonIntervalOrderSupport
