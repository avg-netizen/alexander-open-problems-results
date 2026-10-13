import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingAppendIntervalOrder
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingIntervalFrameProducts

/-!
# Real FIRST retention at a covered ordinary selected row

The actual right-priority scan keeps the first unchanged suffix head when
a later transition passes, and otherwise uses its actual singleton product
at the covered cut. Every earlier written head is retained. Sequential
row memberships derive the singleton and cover; no selected index or
replacement spelling is supplied. Raised selected rows remain separate.
Source-only uncompiled candidates on the original SAME-q grammar.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.SmallInsertionIntervalOrderSupport

open PublicEpsilonUnboundedIota
open InsertionSupport (Row Matches)
open SourceTrackingSequences (lastCode lastCode_append_singleton)
open Hereditary.FinePredecessor (stripLast stripLast_split)
open Alexander313.Wilken.MultiplicativePrincipalArithmetic

theorem word_cons_some (q : Nat) (a : Row) (rows : List Row) (selected : Insertion.Candidate)
    (hs : Insertion.choose q rows = some selected) :
    Insertion.word q (a :: rows) = a.1 :: Insertion.word q rows := by
  have hp := AssignmentCoverPrefixSupport.choose_prepend q a rows selected.1 selected.2 hs
  change (match Insertion.choose q (a :: rows) with
    | none => ((a :: rows).head?.getD (0, [])).2
    | some c => ((a :: rows).take c.1).map Prod.fst ++ c.2) = _
  rw [hp]
  change ((a :: rows).take (selected.1 + 1)).map Prod.fst ++ selected.2 = _
  rw [List.take_succ_cons, List.map_cons, List.cons_append]
  rw [Insertion.word, hs]

theorem word_selected_first (q : Nat) (a : Row) (rest : List Row)
    (selected : Insertion.Candidate) (hs : Insertion.choose q (a :: rest) = some selected) :
    ∃ tail, Insertion.word q (a :: rest) = a.1 :: tail := by
  cases rest with
  | nil => simp only [Insertion.choose_singleton, Option.none_ne_some] at hs
  | cons b rest =>
    cases ht : Insertion.choose q (b :: rest) with
    | some later => exact ⟨Insertion.word q (b :: rest), word_cons_some q a _ later ht⟩
    | none =>
      have hc : Insertion.coverCheck q a.1 (Insertion.firstCode b.2) = true := by
        cases hc : Insertion.coverCheck q a.1 (Insertion.firstCode b.2) with
        | true => rfl
        | false =>
          simp only [Insertion.choose_pair, ht, hc, Bool.cond_false, Option.none_ne_some] at hs
      have hp : Insertion.choose q (a :: b :: rest) = some (1, b.2) := by
        simp only [Insertion.choose_pair, ht, hc, Bool.cond_true]
      refine ⟨b.2, ?_⟩
      simp only [Insertion.word, hp, List.take_succ_cons, List.take_zero,
        List.map_cons, List.map_nil, List.singleton_append]

theorem word_cut_first (q : Nat) (before : List Row) (a b : Row) (rest : List Row) (d : Nat)
    (hd : b.2 = [d]) (hc : Insertion.coverCheck q a.1 (Insertion.firstCode b.2) = true) :
    ∃ first tail, Insertion.word q (before ++ a :: b :: rest) =
      (before.map Prod.fst ++ [a.1]) ++ first :: tail ∧ (first = b.1 ∨ first = d) := by
  induction before with
  | nil =>
    cases hs : Insertion.choose q (b :: rest) with
    | some selected =>
      obtain ⟨tail, ht⟩ := word_selected_first q b rest selected hs
      refine ⟨b.1, tail, ?_, Or.inl rfl⟩
      simp only [List.map_nil, List.nil_append, word_cons_some q a _ selected hs,
        ht, List.singleton_append]
    | none =>
      have hp : Insertion.choose q (a :: b :: rest) = some (1, b.2) := by
        simp only [Insertion.choose_pair, hs, hc, Bool.cond_true]
      refine ⟨d, [], ?_, Or.inr rfl⟩
      simp only [List.map_nil, List.nil_append, Insertion.word, hp, hd,
        List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil]
  | cons x before ih =>
    obtain ⟨first, tail, ht, hf⟩ := ih
    obtain ⟨n, replacement, hs, _⟩ :=
      AssignmentCoverPrefixSupport.choose_after_passing q before a b rest hc
    refine ⟨first, tail, ?_, hf⟩
    simp only [List.cons_append, word_cons_some q x _ (n, replacement) hs,
      ht, List.map_cons]

theorem rows_at_cut (q factor : Nat) (before : List Nat) (d next : Nat)
    (after : List Nat) (rows : List Row)
    (hr : List.Forall₂ (Matches q factor) (before ++ d :: next :: after) rows) :
    ∃ prefix a b rest, rows = prefix ++ a :: b :: rest ∧ prefix.map Prod.fst = before ∧
      a.1 = d ∧ b.1 = next ∧ b.2 ∈ ConditionalReplacement.execute q next factor := by
  induction before generalizing rows with
  | nil =>
    obtain ⟨a, tail, ha, ht, rfl⟩ := List.forall₂_cons_left_iff.mp hr
    obtain ⟨b, rest, hb, hrest, rfl⟩ := List.forall₂_cons_left_iff.mp ht
    exact ⟨[], a, b, rest, rfl, rfl, ha.1, hb.1, hb.2⟩
  | cons x before ih =>
    obtain ⟨a, tail, ha, ht, rfl⟩ := List.forall₂_cons_left_iff.mp hr
    obtain ⟨prefix, b, c, rest, he, hp, hb, hc, hcall⟩ := ih tail ht
    refine ⟨a :: prefix, b, c, rest, ?_, ?_, hb, hc, hcall⟩
    · simpa only [List.cons_append] using congrArg (List.cons a) he
    · simp only [List.map_cons, ha.1, hp]

theorem insertion_small_cut (q : Nat) (before : List Nat) (first factor : Nat)
    (after out : List Nat) (hne : before ≠ [])
    (hh : SourceTrackingRaw.trackingCheck q (before ++ first :: after) = true)
    (hroot : SourceTrackingRaw.Support.inputCheck q (lastCode before) = true)
    (hf : lowCheckCode q factor = true) (hm : IsMultiplicativePrincipal (interpretation q factor))
    (hbound : interpretation q factor ≤ interpretation q (lastCode (before ++ first :: after)))
    (hb : interpretation q factor ≤ interpretation q first)
    (hc : interpretation q first * interpretation q factor ≤ SourceTrackingRaw.Support.muValue q (lastCode before))
    (ho : out ∈ Insertion.execute ((q, factor), before ++ first :: after)) :
    ∃ next tail, out = before ++ next :: tail ∧
      (interpretation q next = interpretation q first ∨
        interpretation q next = interpretation q first * interpretation q factor) := by
  obtain ⟨rows, hr, hout⟩ := (Part.mem_map_iff (Insertion.word q)).mp ho
  have hrel := InsertionSupport.executeRows_relation q factor (before ++ first :: after) rows hr
  obtain ⟨last, he, _⟩ := stripLast_split before hne
  have hlast : last = lastCode before := by rw [he, lastCode_append_singleton]
  have hrel' : List.Forall₂ (Matches q factor) (stripLast before ++ last :: first :: after) rows := by
    rw [he, List.append_assoc, List.singleton_append] at hrel
    exact hrel
  obtain ⟨prefix, a, b, rest, hrows, hp, ha, hbrow, hcall⟩ :=
    rows_at_cut q factor (stripLast before) last first after rows hrel'
  obtain ⟨d, hd, hlow, hv⟩ := EpsilonSingletonIntervalOrderSupport.conditional_small q
    (before ++ first :: after) hh first factor (List.mem_append_right _ List.mem_cons_self)
    hf hm hbound hb b.2 hcall
  have hpass : Insertion.coverCheck q a.1 (Insertion.firstCode b.2) = true := by
    apply (Insertion.coverCheck_exact q _ _).mpr
    simpa only [ha, hlast, hd, Insertion.firstCode, List.head?_cons, Option.getD_some] using
      (show SourceTrackingRaw.Support.inputCheck q (lastCode before) = true ∧
        lowCheckCode q d = true ∧ interpretation q d ≤ SourceTrackingRaw.Support.muValue q (lastCode before) from
        ⟨hroot, hlow, by simpa only [hv] using hc⟩)
  obtain ⟨next, tail, hw, hn⟩ := word_cut_first q prefix a b rest d hd hpass
  have hout' : out = before ++ next :: tail := by
    calc
      out = Insertion.word q rows := hout.symm
      _ = (prefix.map Prod.fst ++ [a.1]) ++ next :: tail := by rw [hrows]; exact hw
      _ = before ++ next :: tail := by rw [hp, ha, ← he]
  refine ⟨next, tail, hout', ?_⟩
  rcases hn with hn | hn
  · exact Or.inl (congrArg (interpretation q) (hn.trans hbrow))
  · exact Or.inr ((congrArg (interpretation q) hn).trans hv)

theorem branches_small_cut (q : Nat) (before : List Nat) (first factor : Nat)
    (after out : List Nat) (hne : before ≠ [])
    (hh : SourceTrackingRaw.trackingCheck q (before ++ first :: after) = true)
    (hroot : SourceTrackingRaw.Support.inputCheck q (lastCode before) = true)
    (hf : lowCheckCode q factor = true) (hm : IsMultiplicativePrincipal (interpretation q factor))
    (hbound : interpretation q factor ≤ interpretation q (lastCode (before ++ first :: after)))
    (hb : interpretation q factor ≤ interpretation q first)
    (hc : interpretation q first * interpretation q factor ≤ SourceTrackingRaw.Support.muValue q (lastCode before))
    (ho : out ∈ Branches.execute ((q, factor), before ++ first :: after)) :
    ∃ next tail, out = before ++ next :: tail ∧
      (interpretation q next = interpretation q first ∨
        interpretation q next = interpretation q first * interpretation q factor) := by
  rcases Branches.execute_branch q factor (before ++ first :: after) out ho with ⟨ha, he⟩ | ⟨ha, hi⟩
  · refine ⟨first, after ++ [factor], ?_, Or.inl rfl⟩
    simpa only [List.append_assoc, List.cons_append] using he
  · exact insertion_small_cut q before first factor after out hne hh hroot hf hm hbound hb hc hi

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.SmallInsertionIntervalOrderSupport
