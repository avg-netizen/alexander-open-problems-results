import Alexander313.Wilken.SourceOneNativeAdditiveTrackingAppendIntervalOrder

/-!
# Genuine retention at a covered ordinary selected row

The actual greatest scan either keeps the first unchanged suffix head
because a later transition passes, or uses its independently executed
singleton product at the covered cut. Every earlier written head is
retained in both cases. Actual row provenance and original check-zero mu
derive this alternative; no chosen index, suffix shape or output equality
is supplied. Raised selected rows remain separate. Source-only uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.SmallInsertionIntervalOrderSupport

open InsertionSupport (Row)
open NativeContext.SourceTrackingSequences (lastCode lastCode_append_singleton)
open Hereditary.FinePredecessor (stripLast stripLast_split)

/-- Any actual selection in a nonempty row tail preserves its first
unchanged head. This follows from choose, including the last passing pair. -/
theorem word_selected_first (a : Row) (rest : List Row) (selected : Insertion.Candidate)
    (hs : Insertion.choose (a :: rest) = some selected) :
    ∃ tail, Insertion.word (a :: rest) = a.1 :: tail := by
  cases rest with
  | nil => simp only [Insertion.choose_singleton, Option.none_ne_some] at hs
  | cons b rest =>
    cases ht : Insertion.choose (b :: rest) with
    | some later =>
      exact ⟨Insertion.word (b :: rest),
        CoverPrefixSupport.word_cons_some a (b :: rest) later ht⟩
    | none =>
      have hc : Insertion.coverCheck a.1 (Insertion.firstCode b.2) = true := by
        cases hc : Insertion.coverCheck a.1 (Insertion.firstCode b.2) with
        | true => rfl
        | false =>
          simp only [Insertion.choose_pair, ht, hc, Bool.cond_false, Option.none_ne_some] at hs
      have hp : Insertion.choose (a :: b :: rest) = some (1, b.2) := by
        simp only [Insertion.choose_pair, ht, hc, Bool.cond_true]
      refine ⟨b.2, ?_⟩
      simp only [Insertion.word, hp, List.take_succ_cons, List.take_zero,
        List.map_cons, List.map_nil, List.singleton_append]

/-- A genuinely covered singleton row retains the cut. Its new first
suffix code is the old written head or that actual singleton product. -/
theorem word_cut_first (before : List Row) (a b : Row) (rest : List Row) (d : Nat)
    (hd : b.2 = [d])
    (hc : Insertion.coverCheck a.1 (Insertion.firstCode b.2) = true) :
    ∃ first tail, Insertion.word (before ++ a :: b :: rest) =
      (before.map Prod.fst ++ [a.1]) ++ first :: tail ∧ (first = b.1 ∨ first = d) := by
  induction before with
  | nil =>
    cases hs : Insertion.choose (b :: rest) with
    | some selected =>
      obtain ⟨tail, ht⟩ := word_selected_first b rest selected hs
      refine ⟨b.1, tail, ?_, Or.inl rfl⟩
      simp only [List.map_nil, List.nil_append,
        CoverPrefixSupport.word_cons_some a (b :: rest) selected hs, ht,
        List.singleton_append]
    | none =>
      have hp : Insertion.choose (a :: b :: rest) = some (1, b.2) := by
        simp only [Insertion.choose_pair, hs, hc, Bool.cond_true]
      refine ⟨d, [], ?_, Or.inr rfl⟩
      simp only [List.map_nil, List.nil_append, Insertion.word, hp, hd,
        List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil]
  | cons x before ih =>
    obtain ⟨first, tail, ht, hf⟩ := ih
    obtain ⟨_, selected, hs⟩ := CoverPrefixSupport.passing_transition_prefix before a b rest hc
    refine ⟨first, tail, ?_, hf⟩
    simp only [List.cons_append, CoverPrefixSupport.word_cons_some x _ selected hs,
      ht, List.map_cons]

/-- Actual sequential replacements derive the covered singleton at the
first suffix head. Every earlier original code is retained, and the new
FIRST value is unchanged or multiplied by this actual factor. -/
theorem insertion_small_cut (before : List Nat) (first factor : Nat) (after out : List Nat)
    (hne : before ≠ [])
    (hh : SourceTrackingRaw.trackingCheck (before ++ first :: after) = true)
    (hroot : SourceTrackingRaw.Support.inputCheck (lastCode before) = true)
    (hf : lowCheckCode 0 factor = true)
    (hb : interpretation 0 factor ≤ interpretation 0 first)
    (hc : interpretation 0 first * interpretation 0 factor ≤
      SourceTrackingRaw.Support.muValue (lastCode before))
    (ho : out ∈ Insertion.execute (factor, before ++ first :: after)) :
    ∃ next tail, out = before ++ next :: tail ∧
      (interpretation 0 next = interpretation 0 first ∨
        interpretation 0 next = interpretation 0 first * interpretation 0 factor) := by
  obtain ⟨rows, hr, hout⟩ := (Part.mem_map_iff Insertion.word).mp ho
  have hrel := InsertionSupport.executeRows_relation factor (before ++ first :: after) rows hr
  obtain ⟨last, he, hl⟩ := stripLast_split before hne
  have hlast : last = lastCode before := by rw [he, lastCode_append_singleton]
  have hrel' : List.Forall₂ (InsertionSupport.Matches factor)
      (stripLast before ++ last :: first :: after) rows := by
    rw [he, List.append_assoc, List.singleton_append] at hrel
    exact hrel
  obtain ⟨prefix, a, b, rest, hrows, hp, ha, hbrow, hcall⟩ :=
    CoverPrefixSupport.rows_at_cut factor (stripLast before) last first after rows hrel'
  have hlow := (ConditionalReplacement.tracking_member_principal (before ++ first :: after)
    hh first (List.mem_append_right _ List.mem_cons_self)).1
  obtain ⟨d, hd, hchecked, hv⟩ := EpsilonSingletonIntervalOrderSupport.conditional_small
    first factor b.2 hlow hf hb hcall
  have hpass : Insertion.coverCheck a.1 (Insertion.firstCode b.2) = true := by
    apply (Insertion.coverCheck_exact _ _).mpr
    simpa only [ha, hlast, hd, Insertion.firstCode, List.head?_cons, Option.getD_some] using
      (show SourceTrackingRaw.Support.inputCheck (lastCode before) = true ∧
        lowCheckCode 0 d = true ∧ interpretation 0 d ≤
          SourceTrackingRaw.Support.muValue (lastCode before) from
        ⟨hroot, ((Theta.acceptedLowCode_iff 0 d).mp hchecked).1,
          by simpa only [hv] using hc⟩)
  obtain ⟨next, tail, hw, hn⟩ := word_cut_first prefix a b rest d hd hpass
  have hout' : out = before ++ next :: tail := by
    calc
      out = Insertion.word rows := hout.symm
      _ = (prefix.map Prod.fst ++ [a.1]) ++ next :: tail := by rw [hrows]; exact hw
      _ = before ++ next :: tail := by rw [hp, ha, ← he]
  refine ⟨next, tail, hout', ?_⟩
  rcases hn with hn | hn
  · exact Or.inl (congrArg (interpretation 0) (hn.trans hbrow))
  · exact Or.inr ((congrArg (interpretation 0) hn).trans hv)

/-- The real printed append preserves the old FIRST. Otherwise the
actual covered cut gives the ordinary-product alternative above. -/
theorem branches_small_cut (before : List Nat) (first factor : Nat) (after out : List Nat)
    (hne : before ≠ [])
    (hh : SourceTrackingRaw.trackingCheck (before ++ first :: after) = true)
    (hroot : SourceTrackingRaw.Support.inputCheck (lastCode before) = true)
    (hf : lowCheckCode 0 factor = true)
    (hb : interpretation 0 factor ≤ interpretation 0 first)
    (hc : interpretation 0 first * interpretation 0 factor ≤
      SourceTrackingRaw.Support.muValue (lastCode before))
    (ho : out ∈ Branches.execute (factor, before ++ first :: after)) :
    ∃ next tail, out = before ++ next :: tail ∧
      (interpretation 0 next = interpretation 0 first ∨
        interpretation 0 next = interpretation 0 first * interpretation 0 factor) := by
  rcases Branches.execute_branch factor (before ++ first :: after) out ho with ⟨ha, he⟩ | ⟨ha, hi⟩
  · refine ⟨first, after ++ [factor], ?_, Or.inl rfl⟩
    simpa only [List.append_assoc, List.cons_append] using he
  · exact insertion_small_cut before first factor after out hne hh hroot hf hb hc hi

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.SmallInsertionIntervalOrderSupport
