import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingConditionalOrderSupport
import Mathlib.Data.List.Forall2

/-!
# Actual insertion preserves factor order at the same written headword

The larger-factor conditional FIRST is never below the smaller FIRST, so
each transition retained by the larger-factor table is also retained by
the smaller table. If both tables retain a head, the concrete scan recurses
under that common head. If only the smaller retains it, the larger actual
replacement FIRST is strictly above the retained head. Actual replacement
executions derive every row relation; no selected position is supplied.
This is a same-child frame kernel, not full non-M inter-input order.
Source-only uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.InsertionOrderSupport

open PublicEpsilonUnboundedIota SourceTrackingSequences
open InsertionSupport (Row)

def RowOrder (q : Nat) (a b : Row) : Prop :=
  a.1 = b.1 ∧ a.2 ≠ [] ∧ b.2 ≠ [] ∧
    List.Lex (· < ·) (a.2.map (interpretation q)) (b.2.map (interpretation q)) ∧
      interpretation q b.1 < interpretation q (Insertion.firstCode b.2) ∧
        ∀ previous, Insertion.coverCheck q previous (Insertion.firstCode b.2) = true →
          Insertion.coverCheck q previous (Insertion.firstCode a.2) = true

/-- A real selected word starts with the unchanged first head, since its
retained prefix is nonempty. -/
theorem word_selected_cons (q : Nat) (a : Row) (rest : List Row)
    (c : Insertion.Candidate) (hc : Insertion.choose q (a :: rest) = some c) :
    ∃ tail, Insertion.word q (a :: rest) = a.1 :: tail := by
  obtain ⟨before, current, after, hne, he, hw, hcover, hnone⟩ :=
    Insertion.word_selected q (a :: rest) c.1 c.2 hc
  cases before with
  | nil => exact False.elim (hne rfl)
  | cons first prefix =>
    have hf : a = first := (List.cons.inj he).1
    refine ⟨prefix.map Prod.fst ++ current.2, ?_⟩
    simpa only [List.map_cons, List.cons_append, ← hf] using hw

theorem word_pair_selected_tail (q : Nat) (a b : Row) (rest : List Row)
    (c : Insertion.Candidate) (hc : Insertion.choose q (b :: rest) = some c) :
    Insertion.word q (a :: b :: rest) = a.1 :: Insertion.word q (b :: rest) := by
  simp only [Insertion.word, Insertion.choose_pair, hc, List.take_succ_cons,
    List.map_cons, List.cons_append]

theorem word_pair_default_tail (q : Nat) (a b : Row) (rest : List Row)
    (hc : Insertion.choose q (b :: rest) = none) :
    Insertion.word q (a :: b :: rest) =
      cond (Insertion.coverCheck q a.1 (Insertion.firstCode b.2))
        (a.1 :: b.2) a.2 := by
  cases hcover : Insertion.coverCheck q a.1 (Insertion.firstCode b.2) <;>
    simp only [Insertion.word, Insertion.choose_pair, hc, hcover, Bool.cond_true,
      Bool.cond_false, List.take_succ_cons, List.take_zero, List.map_cons,
      List.map_nil, List.nil_append, List.cons_append, List.head?_cons, Option.getD_some]

/-- Every larger-factor passing adjacency also passes in the smaller
table. Thus a smaller table with no passing transition forces the larger
table to have none, without a supplied numeric selected position. -/
theorem choose_none_monotone (q : Nat) (xs ys : List Row)
    (hr : List.Forall₂ (RowOrder q) xs ys)
    (hx : Insertion.choose q xs = none) : Insertion.choose q ys = none := by
  revert hx
  induction hr with
  | nil => intro hx; rfl
  | @cons a b as bs hab ht ih =>
    intro hx
    cases as with
    | nil =>
      have hb : bs = [] := List.forall₂_nil_left_iff.mp ht
      simpa only [hb] using Insertion.choose_singleton q b
    | cons c cs =>
      obtain ⟨d, ds, hcd, hrest, hbs⟩ := List.forall₂_cons_left_iff.mp ht
      subst bs
      have hn := (Insertion.choose_none q (a :: c :: cs)).mp hx
      change Insertion.coverCheck q a.1 (Insertion.firstCode c.2) = false ∧
        Insertion.NoCover q (c :: cs) at hn
      have htail := ih ((Insertion.choose_none q (c :: cs)).mpr hn.2)
      apply (Insertion.choose_none q (b :: d :: ds)).mpr
      change Insertion.coverCheck q b.1 (Insertion.firstCode d.2) = false ∧
        Insertion.NoCover q (d :: ds)
      refine ⟨?_, (Insertion.choose_none q (d :: ds)).mp htail⟩
      cases hc : Insertion.coverCheck q b.1 (Insertion.firstCode d.2) with
      | false => rfl
      | true =>
        have hl := hcd.2.2.2.2.2 b.1 hc
        have hf : Insertion.coverCheck q a.1 (Insertion.firstCode c.2) = true := by
          simpa only [hab.1] using hl
        rw [hn.1] at hf
        cases hf

theorem cons_lt_replacement (q head : Nat) (tail replacement : List Nat)
    (hne : replacement ≠ [])
    (hlt : interpretation q head < interpretation q (Insertion.firstCode replacement)) :
    List.Lex (· < ·) ((head :: tail).map (interpretation q))
      (replacement.map (interpretation q)) := by
  cases he : replacement with
  | nil => exact False.elim (hne he)
  | cons a as =>
    simp only [List.map_cons]
    exact List.Lex.rel (by simpa only [Insertion.firstCode, he,
      List.head?_cons, Option.getD_some] using hlt)

/-- The actual right-priority recursion compares the full words. A
larger retained transition implies the smaller retains there or later;
only-smaller retention is strictly below the larger replacement FIRST. -/
theorem words_lex (q : Nat) (xs ys : List Row)
    (hr : List.Forall₂ (RowOrder q) xs ys) (hne : xs ≠ []) :
    List.Lex (· < ·) ((Insertion.word q xs).map (interpretation q))
      ((Insertion.word q ys).map (interpretation q)) := by
  revert hne
  induction hr with
  | nil => intro hne; exact False.elim (hne rfl)
  | @cons a b as bs hab ht ih =>
    intro hne
    cases as with
    | nil =>
      have hb : bs = [] := List.forall₂_nil_left_iff.mp ht
      simp only [hb, Insertion.word, Insertion.choose_singleton,
        List.head?_cons, Option.getD_some]
      exact hab.2.2.2.1
    | cons c cs =>
      obtain ⟨d, ds, hcd, hrest, hbs⟩ := List.forall₂_cons_left_iff.mp ht
      subst bs
      have htail := ih (List.cons_ne_nil c cs)
      cases hl : Insertion.choose q (c :: cs) with
      | none =>
        have hrnone := choose_none_monotone q (c :: cs) (d :: ds) ht hl
        have hwleft := word_pair_default_tail q a c cs hl
        have hwright := word_pair_default_tail q b d ds hrnone
        cases hc : Insertion.coverCheck q b.1 (Insertion.firstCode d.2) with
        | true =>
          have hsmall : Insertion.coverCheck q a.1 (Insertion.firstCode c.2) = true := by
            simpa only [hab.1] using hcd.2.2.2.2.2 b.1 hc
          simp only [hwleft, hwright, hc, hsmall, Bool.cond_true, List.map_cons]
          rw [hab.1]
          exact List.Lex.cons hcd.2.2.2.1
        | false =>
          cases hs : Insertion.coverCheck q a.1 (Insertion.firstCode c.2) with
          | false =>
            simpa only [hwleft, hwright, hc, hs, Bool.cond_false] using hab.2.2.2.1
          | true =>
            simp only [hwleft, hwright, hc, hs, Bool.cond_false, Bool.cond_true]
            exact cons_lt_replacement q a.1 c.2 b.2 hab.2.2.1
              (by simpa only [hab.1] using hab.2.2.2.2.1)
      | some e =>
        have hwleft := word_pair_selected_tail q a c cs e hl
        cases hg : Insertion.choose q (d :: ds) with
        | some f =>
          have hwright := word_pair_selected_tail q b d ds f hg
          simp only [hwleft, hwright, List.map_cons]
          rw [hab.1]
          exact List.Lex.cons htail
        | none =>
          have hwright := word_pair_default_tail q b d ds hg
          cases hc : Insertion.coverCheck q b.1 (Insertion.firstCode d.2) with
          | true =>
            have hd := (Insertion.word_default q d ds hg).1
            simp only [hwleft, hwright, hc, Bool.cond_true, List.map_cons]
            rw [hab.1]
            exact List.Lex.cons (by simpa only [hd] using htail)
          | false =>
            simp only [hwleft, hwright, hc, Bool.cond_false]
            exact cons_lt_replacement q a.1 (Insertion.word q (c :: cs)) b.2 hab.2.2.1
              (by simpa only [hab.1] using hab.2.2.2.2.1)

/-- Pair the two real finite execution relations at their identical
literal original head list. Every row comparison and cover implication
is derived from the actual conditional procedure. -/
theorem actual_rows_order (q : Nat) (heads : List Nat)
    (hh : SourceTrackingRaw.trackingCheck q heads = true) (left right : Nat)
    (hl : lowCheckCode q left = true) (hr : lowCheckCode q right = true)
    (hml : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q left))
    (hmr : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q right))
    (hone : 1 < interpretation q right)
    (hbl : interpretation q left ≤ interpretation q (lastCode heads))
    (hbr : interpretation q right ≤ interpretation q (lastCode heads))
    (hlt : interpretation q left < interpretation q right)
    (xs ys : List Row)
    (hx : List.Forall₂ (InsertionSupport.Matches q left) heads xs)
    (hy : List.Forall₂ (InsertionSupport.Matches q right) heads ys) :
    List.Forall₂ (RowOrder q) xs ys := by
  have hp : ∀ (pending : List Nat) (as bs : List Row),
      List.Forall₂ (InsertionSupport.Matches q left) pending as →
      List.Forall₂ (InsertionSupport.Matches q right) pending bs →
      (∀ h ∈ pending, h ∈ heads) → List.Forall₂ (RowOrder q) as bs := by
    intro pending as bs hleft
    revert bs
    induction hleft with
    | nil =>
      intro bs hright hmem
      have he : bs = [] := List.forall₂_nil_left_iff.mp hright
      rw [he]
      exact .nil
    | @cons head x rest as hx ht ih =>
      intro bs hright hmem
      obtain ⟨y, bs, hy, hyt, rfl⟩ := List.forall₂_cons_left_iff.mp hright
      have hm := hmem head List.mem_cons_self
      have hxout : x.2 ∈ ConditionalReplacement.execute q head left := hx.2
      have hyout : y.2 ∈ ConditionalReplacement.execute q head right := hy.2
      have hsx := ConditionalReplacement.execute_spec q heads hh head left hm hl hml hbl x.2 hxout
      have hsy := FrameOrderSupport.replacement_first_gt_head q heads hh head right hm
        hr hmr hone hbr y.2 hyout
      refine .cons ?_ (ih bs hyt (fun h hm => hmem h (List.mem_cons_of_mem _ hm)))
      refine ⟨hx.1.trans hy.1.symm, hsx.1, hsy.1, ?_, ?_, ?_⟩
      · exact ConditionalOrderSupport.conditional_replacements_lex q heads hh head left right hm
          hl hr hml hmr hbl hbr hlt x.2 y.2 hxout hyout
      · simpa only [hy.1] using hsy.2
      · intro previous hcover
        exact ConditionalOrderSupport.cover_smaller_replacement q heads hh head left right previous hm
          hl hr hml hmr hbl hbr hlt x.2 y.2 hxout hyout hcover
  exact hp heads xs ys hx hy (fun _ hm => hm)

/-- Same literal heads and two independently executing insertion programs
derive strict full VALUE-word order. No row table, selected position,
replacement word, or FIRST comparison is a caller premise. -/
theorem execute_lex (q : Nat) (heads : List Nat)
    (hh : SourceTrackingRaw.trackingCheck q heads = true) (left right : Nat)
    (hl : lowCheckCode q left = true) (hr : lowCheckCode q right = true)
    (hml : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q left))
    (hmr : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q right))
    (hone : 1 < interpretation q right)
    (hbl : interpretation q left ≤ interpretation q (lastCode heads))
    (hbr : interpretation q right ≤ interpretation q (lastCode heads))
    (hlt : interpretation q left < interpretation q right) (xs ys : List Nat)
    (hx : xs ∈ Insertion.execute ((q, left), heads))
    (hy : ys ∈ Insertion.execute ((q, right), heads)) :
    List.Lex (· < ·) (xs.map (interpretation q)) (ys.map (interpretation q)) := by
  obtain ⟨as, ha, hax⟩ := (Part.mem_map_iff _).mp hx
  obtain ⟨bs, hb, hby⟩ := (Part.mem_map_iff _).mp hy
  have har := InsertionSupport.executeRows_relation q left heads as ha
  have hbrs := InsertionSupport.executeRows_relation q right heads bs hb
  have hne : as ≠ [] := by
    intro he
    have hn := ((SourceTrackingRaw.trackingCheck_conditions q heads).mp hh).1
    exact hn (by simpa only [he, List.map_nil] using
      (InsertionSupport.relation_heads q left har).symm)
  have hs := words_lex q as bs
    (actual_rows_order q heads hh left right hl hr hml hmr hone hbl hbr hlt as bs har hbrs) hne
  simpa only [hax, hby] using hs

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.InsertionOrderSupport
