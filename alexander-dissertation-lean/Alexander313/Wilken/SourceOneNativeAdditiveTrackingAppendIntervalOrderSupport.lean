import Alexander313.Wilken.SourceOneNativeAdditiveTrackingEpsilonSingletonIntervalOrder

/-!
# Actual final-row retention behind an arbitrary original headword

A passing final transition has greatest priority in the actual insertion
scan, whatever the earlier rows do. Actual sequential row provenance and
the real original mu cover therefore retain every literal initial head
and replace only the small final residual. No selected index or retained
word is an input oracle. All source checks remain original check zero.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.AppendIntervalOrderSupport

open InsertionSupport (Row)
open NativeContext.SourceTrackingSequences (lastCode lastCode_append_singleton
  stripLast_append_singleton)
open Hereditary.FinePredecessor (stripLast stripLast_split)

/-- The actual right-priority scan retains every written row before its
passing final pair, with no restriction on any earlier cover flag. -/
theorem word_final_pair (before : List Row) (a b : Row)
    (hc : Insertion.coverCheck a.1 (Insertion.firstCode b.2) = true) :
    Insertion.word (before ++ [a, b]) = (before.map Prod.fst ++ [a.1]) ++ b.2 := by
  induction before with
  | nil =>
    have hs : Insertion.choose [a, b] = some (1, b.2) := by
      simp only [Insertion.choose_pair, Insertion.choose_singleton, hc, Bool.cond_true]
    simp only [List.nil_append, List.map_nil, Insertion.word, hs,
      List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil]
  | cons x before ih =>
    obtain ⟨_, selected, hs⟩ := CoverPrefixSupport.passing_transition_prefix before a b [] hc
    have hs' : Insertion.choose (before ++ [a, b]) = some selected := by
      simpa only [List.append_nil] using hs
    simp only [List.cons_append, CoverPrefixSupport.word_cons_some x _ selected hs',
      ih, List.map_cons]

/-- Genuine sequential execution identifies the final two rows and all
unchanged earlier head spellings. The final pending tail is actually empty. -/
theorem rows_at_final_pair (factor : Nat) (before : List Nat) (head tail : Nat)
    (rows : List Row)
    (hr : List.Forall₂ (InsertionSupport.Matches factor) (before ++ [head, tail]) rows) :
    ∃ prefix a b, rows = prefix ++ [a, b] ∧ prefix.map Prod.fst = before ∧
      a.1 = head ∧ b.1 = tail ∧ b.2 ∈ ConditionalReplacement.execute tail factor := by
  induction before generalizing rows with
  | nil =>
    obtain ⟨a, rest, ha, ht, rfl⟩ := List.forall₂_cons_left_iff.mp hr
    obtain ⟨b, rest', hb, hn, rfl⟩ := List.forall₂_cons_left_iff.mp ht
    have he : rest' = [] := List.forall₂_nil_left_iff.mp hn
    exact ⟨[], a, b, by simp only [he, List.nil_append], rfl, ha.1, hb.1, hb.2⟩
  | cons x before ih =>
    obtain ⟨a, rest, ha, ht, rfl⟩ := List.forall₂_cons_left_iff.mp hr
    obtain ⟨prefix, b, c, he, hp, hb, hc, hcall⟩ := ih rest ht
    refine ⟨a :: prefix, b, c, ?_, ?_, hb, hc, hcall⟩
    · simpa only [List.cons_append] using congrArg (List.cons a) he
    · simp only [List.map_cons, ha.1, hp]

/-- The actual final small conditional product is covered by the real
mu of the last initial head. Its passing row retains the whole headword. -/
theorem insertion_tail_covered (heads : List Nat) (tail factor : Nat) (out : List Nat)
    (hne : heads ≠ [])
    (hh : SourceTrackingRaw.trackingCheck (heads ++ [tail]) = true)
    (hroot : SourceTrackingRaw.Support.inputCheck (lastCode heads) = true)
    (hf : lowCheckCode 0 factor = true)
    (hb : interpretation 0 factor ≤ interpretation 0 tail)
    (hc : interpretation 0 tail * interpretation 0 factor ≤
      SourceTrackingRaw.Support.muValue (lastCode heads))
    (ho : out ∈ Insertion.execute (factor, heads ++ [tail])) :
    ∃ d, out = heads ++ [d] ∧ interpretation 0 d =
      interpretation 0 tail * interpretation 0 factor := by
  obtain ⟨rows, hr, hout⟩ := (Part.mem_map_iff Insertion.word).mp ho
  have hrel := InsertionSupport.executeRows_relation factor (heads ++ [tail]) rows hr
  obtain ⟨head, he, hl⟩ := stripLast_split heads hne
  have hhead : head = lastCode heads := by rw [he, lastCode_append_singleton]
  have hrel' : List.Forall₂ (InsertionSupport.Matches factor)
      (stripLast heads ++ [head, tail]) rows := by
    rw [he, List.append_assoc, List.singleton_append] at hrel
    exact hrel
  obtain ⟨prefix, a, b, hrows, hprefix, ha, hbrow, hcall⟩ :=
    rows_at_final_pair factor (stripLast heads) head tail rows hrel'
  have hlow := (ConditionalReplacement.tracking_member_principal (heads ++ [tail]) hh
    tail (List.mem_append_right _ List.mem_cons_self)).1
  obtain ⟨d, hd, hchecked, hv⟩ := EpsilonSingletonIntervalOrderSupport.conditional_small
    tail factor b.2 hlow hf hb hcall
  have hcover : Insertion.coverCheck a.1 (Insertion.firstCode b.2) = true := by
    apply (Insertion.coverCheck_exact _ _).mpr
    simpa only [ha, hhead, hd, Insertion.firstCode, List.head?_cons, Option.getD_some] using
      (show SourceTrackingRaw.Support.inputCheck (lastCode heads) = true ∧
        lowCheckCode 0 d = true ∧ interpretation 0 d ≤
          SourceTrackingRaw.Support.muValue (lastCode heads) from
        ⟨hroot, ((Theta.acceptedLowCode_iff 0 d).mp hchecked).1,
          by simpa only [hv] using hc⟩)
  have hw : Insertion.word rows = heads ++ [d] := by
    simp only [hrows, word_final_pair prefix a b hcover, hprefix, ha, hd, ← he]
  exact ⟨d, hout.symm.trans hw, hv⟩

/-- A residual below the last initial head fails the genuine printed
strict-final-head test, and the actual covered final row retains all heads. -/
theorem branches_tail_covered (heads : List Nat) (tail factor : Nat) (out : List Nat)
    (hne : heads ≠ [])
    (hh : SourceTrackingRaw.trackingCheck (heads ++ [tail]) = true)
    (hroot : SourceTrackingRaw.Support.inputCheck (lastCode heads) = true)
    (hf : lowCheckCode 0 factor = true)
    (hb : interpretation 0 factor ≤ interpretation 0 tail)
    (ht : interpretation 0 tail < interpretation 0 (lastCode heads))
    (hc : interpretation 0 tail * interpretation 0 factor ≤
      SourceTrackingRaw.Support.muValue (lastCode heads))
    (ho : out ∈ Branches.execute (factor, heads ++ [tail])) :
    ∃ d, out = heads ++ [d] ∧ interpretation 0 d =
      interpretation 0 tail * interpretation 0 factor := by
  have ha : BranchesSupport.appendCheck factor (heads ++ [tail]) = false :=
    Bool.eq_false_of_not_eq_true (fun ha => by
      have hs := (BranchesSupport.appendCheck_exact factor (heads ++ [tail]) hh).mp ha
      have hstrict : interpretation 0 (lastCode heads) < interpretation 0 tail := by
        simpa only [stripLast_append_singleton, if_neg hne,
          lastCode_append_singleton] using hs.2.1
      exact ht.not_ge hstrict.le)
  have hi : out ∈ Insertion.execute (factor, heads ++ [tail]) := by
    simpa only [Branches.execute, ha, Bool.cond_false] using ho
  exact insertion_tail_covered heads tail factor out hne hh hroot hf hb hc hi

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.AppendIntervalOrderSupport
