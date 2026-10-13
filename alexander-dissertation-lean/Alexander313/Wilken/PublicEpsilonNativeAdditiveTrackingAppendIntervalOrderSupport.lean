import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingEpsilonSingletonIntervalOrder

/-!
# Real covered final transitions after an arbitrary original headword

The actually executed last replacement is its ordinary small product.
Its real mu cover at the preceding written epsilon forces the rightmost
transition to pass. The concrete selector therefore retains every earlier
head, irrespective of the replacement rows before this final transition.
No suffix shape, selector index or replacement output is supplied.
These are original SAME-q callers; source-only uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.AppendIntervalOrderSupport

open PublicEpsilonUnboundedIota
open Alexander313.Wilken.MultiplicativePrincipalArithmetic
open SourceTrackingSequences (lastCode lastCode_mem lastCode_append_singleton stripLast_append_singleton)
open Hereditary.FinePredecessor (stripLast stripLast_split)
open InsertionSupport (Row Matches)

private theorem rows_last_pair (q factor : Nat) (before : List Nat)
    (head tail : Nat) (rows : List Row)
    (hr : List.Forall₂ (Matches q factor) (before ++ [head, tail]) rows) :
    ∃ earlier a b, rows = earlier ++ [a, b] ∧ earlier.map Prod.fst = before ∧
      Matches q factor head a ∧ Matches q factor tail b := by
  induction before generalizing rows with
  | nil =>
    obtain ⟨a, rest, ha, ht, hrows⟩ := List.forall₂_cons_left_iff.mp hr
    obtain ⟨b, rest', hb, hn, hrest⟩ := List.forall₂_cons_left_iff.mp ht
    have hnil : rest' = [] := List.forall₂_nil_left_iff.mp hn
    exact ⟨[], a, b, by simpa only [hrest, hnil] using hrows, rfl, ha, hb⟩
  | cons c cs ih =>
    obtain ⟨r, rest, hmatch, htail, hrows⟩ := List.forall₂_cons_left_iff.mp hr
    obtain ⟨earlier, a, b, he, hm, ha, hb⟩ := ih rest htail
    refine ⟨r :: earlier, a, b, ?_, ?_, ha, hb⟩
    · simpa only [he, List.cons_append] using hrows
    · simp only [List.map_cons, hmatch.1, hm]

private theorem choose_last_transition (q : Nat) (before : List Row) (a b : Row)
    (hc : Insertion.coverCheck q a.1 (Insertion.firstCode b.2) = true) :
    Insertion.choose q (before ++ [a, b]) = some (before.length + 1, b.2) := by
  induction before with
  | nil => simp only [List.nil_append, List.length_nil, Nat.zero_add,
      Insertion.choose_pair, Insertion.choose_singleton, hc, Bool.cond_true]
  | cons r before ih =>
    cases before with
    | nil => simp only [List.cons_append, List.nil_append, List.length_cons,
        List.length_nil, Nat.zero_add, Insertion.choose_pair, Insertion.choose_singleton,
        hc, Bool.cond_true, ih]
    | cons s rest =>
      simp only [List.cons_append, List.length_cons, Insertion.choose_pair,
        Insertion.choose_singleton, hc, Bool.cond_true, ih]

private theorem word_last_transition (q : Nat) (before : List Row) (a b : Row)
    (hc : Insertion.coverCheck q a.1 (Insertion.firstCode b.2) = true) :
    Insertion.word q (before ++ [a, b]) = (before ++ [a]).map Prod.fst ++ b.2 := by
  have hs := choose_last_transition q before a b hc
  have he : before ++ [a, b] = (before ++ [a]) ++ [b] := by
    simp only [List.append_assoc, List.singleton_append]
  have hn : before.length + 1 = (before ++ [a]).length := by
    simp only [List.length_append, List.length_singleton]
  rw [Insertion.word, hs, he, hn, List.take_left]

theorem suffix_values_shape (q : Nat) (xs original : List Nat) (value : Ordinal.{0})
    (he : xs.map (interpretation q) = original.map (interpretation q) ++ [value]) :
    ∃ heads tail, xs = heads ++ [tail] ∧
      heads.map (interpretation q) = original.map (interpretation q) ∧
        interpretation q tail = value := by
  obtain ⟨heads, suffix, hx, hh, hs⟩ := List.map_eq_append_iff.mp he
  obtain ⟨tail, ht, hv⟩ := List.map_eq_singleton_iff.mp hs
  exact ⟨heads, tail, by simpa only [ht] using hx, hh, hv⟩

theorem suffix_last_input (q : Nat) (heads : List Nat) (tail : Nat)
    (hne : heads ≠ [])
    (hh : SourceTrackingRaw.trackingCheck q (heads ++ [tail]) = true) :
    SourceTrackingRaw.Support.inputCheck q (lastCode heads) = true := by
  have hr := ((SourceTrackingRaw.trackingCheck_conditions q (heads ++ [tail])).mp hh).2.1
  have hs : stripLast (heads ++ [tail]) = heads := stripLast_append_singleton heads tail
  exact hr.nodes _ (by rw [hs]; exact lastCode_mem heads hne)

theorem insertion_suffix_covered (q : Nat) (heads : List Nat) (tail factor : Nat)
    (out : List Nat) (hne : heads ≠ [])
    (hh : SourceTrackingRaw.trackingCheck q (heads ++ [tail]) = true)
    (hf : lowCheckCode q factor = true)
    (hm : IsMultiplicativePrincipal (interpretation q factor))
    (hsmall : interpretation q factor ≤ interpretation q tail)
    (hcover : interpretation q tail * interpretation q factor ≤
      SourceTrackingRaw.Support.muValue q (lastCode heads))
    (ho : out ∈ Insertion.execute ((q, factor), heads ++ [tail])) :
    ∃ d, out = heads ++ [d] ∧
      interpretation q d = interpretation q tail * interpretation q factor := by
  obtain ⟨head, hheads, _⟩ := stripLast_split heads hne
  have hwhole : heads ++ [tail] = stripLast heads ++ [head, tail] := by
    simpa only [List.append_assoc, List.singleton_append] using
      congrArg (fun xs : List Nat => xs ++ [tail]) hheads
  obtain ⟨rows, hr, he⟩ := (Part.mem_map_iff (Insertion.word q)).mp ho
  have hrel := InsertionSupport.executeRows_relation q factor (heads ++ [tail]) rows hr
  rw [hwhole] at hrel
  obtain ⟨earlier, a, b, hrows, hearlier, ha, hb⟩ :=
    rows_last_pair q factor (stripLast heads) head tail rows hrel
  have hbound : interpretation q factor ≤ interpretation q (lastCode (heads ++ [tail])) := by
    simpa only [lastCode_append_singleton] using hsmall
  obtain ⟨d, hd, hlow, hv⟩ := EpsilonSingletonIntervalOrderSupport.conditional_small
    q (heads ++ [tail]) hh tail factor (List.mem_append_right _ List.mem_cons_self)
    hf hm hbound hsmall b.2 hb.2
  have hroot := suffix_last_input q heads tail hne hh
  have hlast : lastCode heads = head := by
    simpa only [lastCode_append_singleton] using congrArg lastCode hheads
  have hc : Insertion.coverCheck q a.1 (Insertion.firstCode b.2) = true := by
    apply (Insertion.coverCheck_exact q _ _).mpr
    simpa only [ha.1, hd, Insertion.firstCode, List.head?_cons, Option.getD_some,
      hv, hlast] using And.intro hroot (And.intro hlow hcover)
  have hw : Insertion.word q rows = heads ++ [d] := by
    rw [hrows, word_last_transition q earlier a b hc]
    simp only [List.map_append, List.map_singleton, hearlier, ha.1, hd,
      ← List.append_assoc, ← hheads]
  exact ⟨d, he.symm.trans hw, hv⟩

theorem branches_suffix_covered (q : Nat) (heads : List Nat) (tail factor : Nat)
    (out : List Nat) (hne : heads ≠ [])
    (hh : SourceTrackingRaw.trackingCheck q (heads ++ [tail]) = true)
    (hf : lowCheckCode q factor = true)
    (hm : IsMultiplicativePrincipal (interpretation q factor))
    (hsmall : interpretation q factor ≤ interpretation q tail)
    (htail : interpretation q tail < interpretation q (lastCode heads))
    (hcover : interpretation q tail * interpretation q factor ≤
      SourceTrackingRaw.Support.muValue q (lastCode heads))
    (ho : out ∈ Branches.execute ((q, factor), heads ++ [tail])) :
    ∃ d, out = heads ++ [d] ∧
      interpretation q d = interpretation q tail * interpretation q factor := by
  have ha : BranchesSupport.appendCheck q factor (heads ++ [tail]) = false :=
    Bool.eq_false_of_not_eq_true (by
      intro ha
      have hs := (BranchesSupport.appendCheck_exact q factor (heads ++ [tail]) hh).mp ha
      have hlt : interpretation q (lastCode heads) < interpretation q tail := by
        simpa only [stripLast_append_singleton, lastCode_append_singleton,
          if_neg hne] using hs.2.1
      exact htail.not_ge hlt.le)
  have hi : out ∈ Insertion.execute ((q, factor), heads ++ [tail]) := by
    simpa only [Branches.execute, ha, Bool.cond_false] using ho
  exact insertion_suffix_covered q heads tail factor out hne hh hf hm hsmall hcover hi

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.AppendIntervalOrderSupport
