import Alexander313.Wilken.SourceOneNativeMultiplicativeTrackingOrder
import Alexander313.Wilken.SourceOneNativeAdditiveTrackingBounds
import Mathlib.Data.List.Forall2

/-!
# Actual covered-prefix retention by original source-one insertion

The real greatest transition scan keeps every written head through any
passing transition, including when a later transition takes priority.
Actual sequential replacement executions and their genuine ordinal bounds
derive such a transition after a covered prefix. The original check-zero
parser and raw mu are retained; no insertion index or returned word is an
oracle. The complete assignment induction is a separate consumer.
Uncompiled source candidates.
-/

noncomputable section

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.CoverPrefixSupport

open InsertionSupport (Row)
open Insertion (Candidate)
open NativeContext.SourceTrackingSequences (lastCode lastCode_mem lastCode_append_singleton)
open Hereditary.FinePredecessor (stripLast stripLast_split)

theorem high_multiplicative (b : Nat) (hb : rootCheck b = true) :
    SourceMultiplicativePrincipal.inputCheck b = true := by
  have he := root_epsilon b hb
  have hp := EpsilonOffsets.epsilon_one_lt he
  have hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 b) := by
    apply (MultiplicativePrincipalArithmetic.multiplicativePrincipal_iff _).mpr
    refine Or.inr ⟨interpretation 0 b, ?_⟩
    exact he.symm.trans (congrArg (fun x : Ordinal.{0} => Ordinal.omega0 ^ x) he.symm)
  exact (SourceMultiplicativePrincipal.inputCheck_exact b).mpr ⟨root_low b hb, hp.le, hm⟩

/-- An actual multiplicative leaf word is strictly increasing through
its literal final input; the proper entries lie strictly below that input. -/
theorem high_word_strict (b : Nat) (hb : rootCheck b = true) :
    ((SourceMultiplicativeTracking.rawWord b).map (interpretation 0)).Pairwise (· < ·) := by
  have hm := high_multiplicative b hb
  have ho := Assignment.execute_multiplicative b hm
  have ht := (SourceTrackingRaw.trackingCheck_exact _).mp (Assignment.execute_tracking b _ ho)
  obtain ⟨last, he, hh⟩ := stripLast_split (SourceMultiplicativeTracking.rawWord b) ht.1
  have hlast : last = b := by
    calc
      last = lastCode (SourceMultiplicativeTracking.rawWord b) := by
        rw [he, lastCode_append_singleton]
      _ = b := SourceMultiplicativeTracking.rawWord_last b
  rw [he, List.map_append, List.map_singleton]
  apply List.pairwise_append.mpr
  refine ⟨ht.2.1.strict, List.pairwise_singleton _ _, ?_⟩
  intro x hx y hy
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
  rw [List.mem_singleton.mp hy, hlast]
  exact ProperPrefix.multiplicative_prefix_lt b hm d hd

/-- If the covered prefix fills the whole child word, its actual strict
epsilon FINAL and real mu bound force the printed append branch. -/
theorem append_of_high_word_values (b : Nat) (hb : rootCheck b = true)
    (heads : List Nat) (hh : SourceTrackingRaw.trackingCheck heads = true)
    (hvalues : heads.map (interpretation 0) =
      (SourceMultiplicativeTracking.rawWord b).map (interpretation 0))
    (factor : Nat) (hf : lowCheckCode 0 factor = true)
    (hcover : interpretation 0 factor ≤ Mu.sourceValue b) :
    BranchesSupport.appendCheck factor heads = true := by
  have ht := (SourceTrackingRaw.trackingCheck_exact heads).mp hh
  have hlast : interpretation 0 (lastCode heads) = interpretation 0 b :=
    (Hereditary.SourceAdditiveTrackingWordBounds.lastCode_values_eq _ _ heads _ ht.1 hvalues).trans
      (congrArg (interpretation 0) (SourceMultiplicativeTracking.rawWord_last b))
  have hroot : SourceTrackingRaw.Support.inputCheck (lastCode heads) = true :=
    (SourceTrackingRaw.Support.inputCheck_exact _).mpr
      ⟨ht.2.2.1, by rw [hlast]; exact EpsilonOffsets.epsilon_one_lt (root_epsilon b hb),
        by rw [hlast]; exact root_epsilon b hb⟩
  have hmu := SourceTrackingRaw.Support.muValue_eq (lastCode heads) b hroot hb hlast
  apply (BranchesSupport.appendCheck_exact factor heads hh).mpr
  refine ⟨hroot, ?_, hf, by rw [hmu]; exact hcover⟩
  have hstrict : (heads.map (interpretation 0)).Pairwise (· < ·) := by
    rw [hvalues]
    exact high_word_strict b hb
  by_cases he : stripLast heads = []
  · rw [if_pos he, hlast]
    exact EpsilonOffsets.epsilon_one_lt (root_epsilon b hb)
  · rw [if_neg he]
    obtain ⟨last, hsplit, hh⟩ := stripLast_split heads ht.1
    have hl : lastCode heads = last := by rw [hsplit, lastCode_append_singleton]
    rw [hsplit, List.map_append, List.map_singleton] at hstrict
    rw [hl]
    exact (List.pairwise_append.mp hstrict).2.2 _
      (List.mem_map.mpr ⟨lastCode (stripLast heads), lastCode_mem _ he, rfl⟩)
      _ List.mem_cons_self

theorem choose_cons_some (a : Row) (rows : List Row) (selected : Candidate)
    (hs : Insertion.choose rows = some selected) :
    Insertion.choose (a :: rows) = some (selected.1 + 1, selected.2) := by
  cases rows with
  | nil => simp only [Insertion.choose_nil, Option.none_ne_some] at hs
  | cons b rest => rw [Insertion.choose_pair, hs]

theorem word_cons_some (a : Row) (rows : List Row) (selected : Candidate)
    (hs : Insertion.choose rows = some selected) :
    Insertion.word (a :: rows) = a.1 :: Insertion.word rows := by
  change (match Insertion.choose (a :: rows) with
    | none => ((a :: rows).head?.getD (0, [])).2
    | some c => ((a :: rows).take c.1).map Prod.fst ++ c.2) = _
  rw [choose_cons_some a rows selected hs]
  change ((a :: rows).take (selected.1 + 1)).map Prod.fst ++ selected.2 = _
  rw [List.take_succ_cons, List.map_cons, List.cons_append]
  rw [Insertion.word, hs]

/-- Any genuinely passing transition forces the computed greatest
selection to retain the written prefix through its predecessor. -/
theorem passing_transition_prefix (before : List Row) (a b : Row) (after : List Row)
    (hc : Insertion.coverCheck a.1 (Insertion.firstCode b.2) = true) :
    (before.map Prod.fst ++ [a.1]).IsPrefix
      (Insertion.word (before ++ a :: b :: after)) ∧
      ∃ selected, Insertion.choose (before ++ a :: b :: after) = some selected := by
  induction before with
  | nil =>
    cases hs : Insertion.choose (b :: after) with
    | none =>
      have hchoose : Insertion.choose (a :: b :: after) = some (1, b.2) := by
        rw [Insertion.choose_pair, hs, hc, Bool.cond_true]
      have hword : Insertion.word (a :: b :: after) = [a.1] ++ b.2 := by
        simp only [Insertion.word, hchoose, List.take_succ_cons, List.take_zero,
          List.map_cons, List.map_nil]
      exact ⟨⟨b.2, by simpa only [List.map_nil, List.nil_append] using hword.symm⟩,
        (1, b.2), hchoose⟩
    | some selected =>
      have hword := word_cons_some a (b :: after) selected hs
      refine ⟨⟨Insertion.word (b :: after), ?_⟩,
        (selected.1 + 1, selected.2), choose_cons_some a _ selected hs⟩
      simpa only [List.map_nil, List.nil_append, List.cons_append] using hword.symm
  | cons x before ih =>
    obtain ⟨hp, selected, hs⟩ := ih
    obtain ⟨tail, he⟩ := hp
    refine ⟨⟨tail, ?_⟩, (selected.1 + 1, selected.2),
      choose_cons_some x _ selected hs⟩
    rw [List.cons_append, word_cons_some x _ selected hs]
    simpa only [List.map_cons, List.cons_append] using congrArg (List.cons x.1) he

/-- The actual sequential relation identifies the two rows at a literal
adjacent cut while retaining the exact preceding head spellings. -/
theorem rows_at_cut (factor : Nat) (before : List Nat) (d next : Nat)
    (after : List Nat) (rows : List Row)
    (hr : List.Forall₂ (InsertionSupport.Matches factor) (before ++ d :: next :: after) rows) :
    ∃ prefix a b rest, rows = prefix ++ a :: b :: rest ∧ prefix.map Prod.fst = before ∧
      a.1 = d ∧ b.1 = next ∧ b.2 ∈ ConditionalReplacement.execute next factor := by
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

/-- Every replacement FIRST is genuinely admitted LOW, as a consequence
of its actual execution, rather than a supplied replacement caller. -/
theorem replacement_first_low (heads : List Nat)
    (hh : SourceTrackingRaw.trackingCheck heads = true) (head factor : Nat)
    (hhead : head ∈ heads) (hf : lowCheckCode 0 factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor))
    (hb : interpretation 0 factor ≤ interpretation 0 (NativeContext.SourceTrackingSequences.lastCode heads))
    (out : List Nat) (ho : out ∈ ConditionalReplacement.execute head factor) :
    out ≠ [] ∧ Insertion.firstCode out ∈ out ∧ lowCheckCode 0 (Insertion.firstCode out) = true := by
  have hs := ConditionalReplacement.execute_spec heads hh head factor hhead hf hm hb out ho
  have hmem : Insertion.firstCode out ∈ out := by
    cases he : out with
    | nil => exact False.elim (hs.1 he)
    | cons a rest =>
      simp only [Insertion.firstCode, he, List.head?_cons, Option.getD_some]
      exact List.mem_cons_self
  exact ⟨hs.1, hmem, ((Theta.acceptedLowCode_iff 0 _).mp (hs.2.1 _ hmem)).1⟩

/-- A real cut whose predecessor covers the computed prefix product is
retained literally by the executing insertion. Actual conditional bounds
derive the FIRST cover; actual rows derive its numerical position. -/
theorem insertion_retains_cut (heads : List Nat)
    (hh : SourceTrackingRaw.trackingCheck heads = true) (factor : Nat)
    (hf : lowCheckCode 0 factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor))
    (hb : interpretation 0 factor ≤ interpretation 0 (NativeContext.SourceTrackingSequences.lastCode heads))
    (prefix : Ordinal.{0}) (hp : 0 < prefix)
    (hbound : ∀ head ∈ heads, interpretation 0 head ≤ prefix)
    (before : List Nat) (d next : Nat) (after : List Nat)
    (he : heads = before ++ d :: next :: after)
    (hd : SourceTrackingRaw.Support.inputCheck d = true)
    (hcover : prefix * interpretation 0 factor ≤ SourceTrackingRaw.Support.muValue d)
    (out : List Nat) (ho : out ∈ Insertion.execute (factor, heads)) :
    (before ++ [d]).IsPrefix out := by
  obtain ⟨rows, hr, hout⟩ := (Part.mem_map_iff Insertion.word).mp ho
  have hrel := InsertionSupport.executeRows_relation factor heads rows hr
  rw [he] at hrel
  obtain ⟨prefixRows, a, b, rest, hrows, hprefix, ha, hbrow, hcall⟩ :=
    rows_at_cut factor before d next after rows hrel
  have hnext : next ∈ heads := by
    rw [he]
    exact List.mem_append_right _ (List.mem_cons_of_mem d List.mem_cons_self)
  have hfirst := replacement_first_low heads hh next factor hnext hf hm hb b.2 hcall
  have hvalues := Bounds.conditional_bounds heads hh next factor hnext hf hm hb prefix hp
    (hbound next hnext) b.2 hcall
  have hpass : Insertion.coverCheck a.1 (Insertion.firstCode b.2) = true := by
    rw [ha]
    exact (Insertion.coverCheck_exact _ _).mpr
      ⟨hd, hfirst.2.2, (hvalues.2.2 _ hfirst.2.1).trans hcover⟩
  have hretained := (passing_transition_prefix prefixRows a b rest hpass).1
  rw [← hrows, hprefix, ha, hout] at hretained
  exact hretained

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.CoverPrefixSupport
