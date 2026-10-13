import Alexander313.Wilken.SourceOneNativeAdditiveTrackingConditionalOrderSupport

/-!
# Strict order of real original source-one insertion at one headword

Actual conditional executions give paired rows with equal unchanged heads,
strict replacement VALUE order and monotone passing covers. The real scan
retains the common head whenever the larger-factor scan retains it. When
both retain, the comparison descends to their actual tails; when only the
smaller retains, the greater replacement FIRST exceeds that old head.
When neither retains, the genuine replacement comparison applies directly.
No selected numerical position or insertion word is supplied. Original
check zero is retained; no Native base-one parser. Full inter-input order
remains separate. Source-only and uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.InsertionOrderSupport

open InsertionSupport (Row)
open NativeContext.SourceTrackingSequences (lastCode)

def RowOrder (a b : Row) : Prop :=
  a.1 = b.1 ∧ a.2 ≠ [] ∧ b.2 ≠ [] ∧
    List.Lex (· < ·) (a.2.map (interpretation 0)) (b.2.map (interpretation 0)) ∧
    interpretation 0 a.1 < interpretation 0 (Insertion.firstCode b.2) ∧
    ∀ previous : Nat, Insertion.coverCheck previous (Insertion.firstCode b.2) = true →
      Insertion.coverCheck previous (Insertion.firstCode a.2) = true

/-- A current passing transition retains its literal head and the actual
tail word, even when a later transition independently takes priority. -/
theorem word_cons_pass (a b : Row) (rest : List Row)
    (hc : Insertion.coverCheck a.1 (Insertion.firstCode b.2) = true) :
    Insertion.word (a :: b :: rest) = a.1 :: Insertion.word (b :: rest) := by
  cases ht : Insertion.choose (b :: rest) with
  | some e => exact CoverPrefixSupport.word_cons_some a (b :: rest) e ht
  | none =>
    have hs : Insertion.choose (a :: b :: rest) = some (1, b.2) := by
      simp only [Insertion.choose_pair, ht, hc, Bool.cond_true]
    simp only [Insertion.word, hs, ht, List.take_succ_cons, List.take_zero,
      List.map_cons, List.map_nil, List.singleton_append, List.head?_cons, Option.getD_some]

/-- If the actual tail has no passing transition and the current pair
fails, the independently computed word is exactly the first replacement. -/
theorem word_cons_fail (a b : Row) (rest : List Row)
    (ht : Insertion.choose (b :: rest) = none)
    (hc : Insertion.coverCheck a.1 (Insertion.firstCode b.2) = false) :
    Insertion.word (a :: b :: rest) = a.2 := by
  have hs : Insertion.choose (a :: b :: rest) = none := by
    simp only [Insertion.choose_pair, ht, hc, Bool.cond_false]
  exact (Insertion.word_default a (b :: rest) hs).1

/-- Each actual larger-factor passing transition also passes at the
smaller factor; hence a real larger selection gives a real smaller one. -/
theorem choose_left_of_right {xs ys : List Row} (hr : List.Forall₂ RowOrder xs ys) :
    ∀ e : Insertion.Candidate, Insertion.choose ys = some e →
      ∃ d : Insertion.Candidate, Insertion.choose xs = some d := by
  induction hr with
  | nil => intro e he; simp only [Insertion.choose_nil, Option.none_ne_some] at he
  | @cons a b as bs hab htail ih =>
    cases htail with
    | nil => intro e he; simp only [Insertion.choose_singleton, Option.none_ne_some] at he
    | @cons c d cs ds hcd hrest =>
      intro e he
      cases ht : Insertion.choose (d :: ds) with
      | some later =>
        obtain ⟨chosen, hc⟩ := ih later ht
        exact ⟨(chosen.1 + 1, chosen.2), CoverPrefixSupport.choose_cons_some a _ chosen hc⟩
      | none =>
        have hp : Insertion.coverCheck b.1 (Insertion.firstCode d.2) = true := by
          cases hp : Insertion.coverCheck b.1 (Insertion.firstCode d.2) with
          | true => rfl
          | false =>
            simp only [Insertion.choose_pair, ht, hp, Bool.cond_false, Option.none_ne_some] at he
        have hpl : Insertion.coverCheck a.1 (Insertion.firstCode c.2) = true := by
          rw [hab.1]
          exact hcd.2.2.2.2.2 b.1 hp
        cases hl : Insertion.choose (c :: cs) with
        | some chosen =>
          exact ⟨(chosen.1 + 1, chosen.2), CoverPrefixSupport.choose_cons_some a _ chosen hl⟩
        | none =>
          exact ⟨(1, c.2), by simp only [Insertion.choose_pair, hl, hpl, Bool.cond_true]⟩

theorem retained_first_lex (head : Nat) (tail target : List Nat)
    (ht : target ≠ [])
    (hlt : interpretation 0 head < interpretation 0 (Insertion.firstCode target)) :
    List.Lex (· < ·) ((head :: tail).map (interpretation 0))
      (target.map (interpretation 0)) := by
  cases he : target with
  | nil => exact False.elim (ht he)
  | cons b bs =>
    simp only [List.map_cons]
    exact List.Lex.rel (by
      simpa only [he, Insertion.firstCode, List.head?_cons, Option.getD_some] using hlt)

/-- The real right-priority words of paired actual rows are strictly
ordered. The proof derives every retention and default directly from
choose; it assumes no selected location or chosen prefix. -/
theorem rows_word_lex {xs ys : List Row} (hr : List.Forall₂ RowOrder xs ys)
    (hne : xs ≠ []) :
    List.Lex (· < ·) ((Insertion.word xs).map (interpretation 0))
      ((Insertion.word ys).map (interpretation 0)) := by
  revert hne
  induction hr with
  | nil => intro hne; exact False.elim (hne rfl)
  | @cons a b as bs hab htail ih =>
    intro hne
    cases htail with
    | nil =>
      simpa only [Insertion.word, Insertion.choose_singleton, List.head?_cons,
        Option.getD_some] using hab.2.2.2.1
    | @cons c d cs ds hcd hrest =>
      have hlex := ih (List.cons_ne_nil _ _)
      cases ht : Insertion.choose (d :: ds) with
      | some selected =>
        obtain ⟨chosen, hc⟩ := choose_left_of_right (List.Forall₂.cons hcd hrest) selected ht
        rw [CoverPrefixSupport.word_cons_some a _ chosen hc,
          CoverPrefixSupport.word_cons_some b _ selected ht, List.map_cons, List.map_cons, hab.1]
        exact List.Lex.cons hlex
      | none =>
        cases hp : Insertion.coverCheck b.1 (Insertion.firstCode d.2) with
        | true =>
          have hpl : Insertion.coverCheck a.1 (Insertion.firstCode c.2) = true := by
            rw [hab.1]
            exact hcd.2.2.2.2.2 b.1 hp
          rw [word_cons_pass a c cs hpl, word_cons_pass b d ds hp,
            List.map_cons, List.map_cons, hab.1]
          exact List.Lex.cons hlex
        | false =>
          rw [word_cons_fail b d ds ht hp]
          cases hl : Insertion.choose (c :: cs) with
          | some selected =>
            rw [CoverPrefixSupport.word_cons_some a _ selected hl]
            exact retained_first_lex a.1 _ b.2 hab.2.2.1 hab.2.2.2.2.1
          | none =>
            cases hpl : Insertion.coverCheck a.1 (Insertion.firstCode c.2) with
            | true =>
              rw [word_cons_pass a c cs hpl]
              exact retained_first_lex a.1 _ b.2 hab.2.2.1 hab.2.2.2.2.1
            | false =>
              rw [word_cons_fail a c cs hl hpl]
              exact hab.2.2.2.1

/-- The exact actual original conditional callers give RowOrder for two
independent row executions at the same unchanged written head. -/
theorem actual_row_order (heads : List Nat)
    (hh : SourceTrackingRaw.trackingCheck heads = true) (head left right : Nat)
    (hhead : head ∈ heads)
    (hl : lowCheckCode 0 left = true) (hr : lowCheckCode 0 right = true)
    (hml : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 left))
    (hmr : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 right))
    (hbl : interpretation 0 left ≤ interpretation 0 (lastCode heads))
    (hbr : interpretation 0 right ≤ interpretation 0 (lastCode heads))
    (hlt : interpretation 0 left < interpretation 0 right)
    (a b : Row) (ha : InsertionSupport.Matches left head a)
    (hb : InsertionSupport.Matches right head b) : RowOrder a b := by
  have hsx := ConditionalReplacement.execute_spec heads hh head left hhead hl hml hbl a.2 ha.2
  have hsy := ConditionalReplacement.execute_spec heads hh head right hhead hr hmr hbr b.2 hb.2
  have hone : 1 < interpretation 0 right := (Order.one_le_iff_pos.mpr hml.1).trans_lt hlt
  refine ⟨ha.1.trans hb.1.symm, hsx.1, hsy.1,
    ConditionalOrderSupport.conditional_replacements_lex heads hh head left right hhead
      hl hr hml hmr hbl hbr hlt a.2 b.2 ha.2 hb.2, ?_, ?_⟩
  · rw [ha.1]
    exact (FrameOrderSupport.conditional_first_strict heads hh head right hhead hr hmr
      hone hbr b.2 hb.2).2
  · intro previous hc
    exact ConditionalOrderSupport.cover_smaller_replacement heads hh head left right previous
      hhead hl hr hml hmr hbl hbr hlt a.2 b.2 ha.2 hb.2 hc

theorem matched_rows_order {heads : List Nat} {xs ys : List Row}
    (left right : Nat) (hx : List.Forall₂ (InsertionSupport.Matches left) heads xs)
    (hy : List.Forall₂ (InsertionSupport.Matches right) heads ys)
    (hc : ∀ head ∈ heads, ∀ a b : Row, InsertionSupport.Matches left head a →
      InsertionSupport.Matches right head b → RowOrder a b) : List.Forall₂ RowOrder xs ys := by
  revert ys hy hc
  induction hx with
  | nil =>
    intro ys hy hc
    have he : ys = [] := List.forall₂_nil_left_iff.mp hy
    subst ys
    exact .nil
  | @cons head a tail rest ha ht ih =>
    intro ys hy hc
    obtain ⟨b, more, hb, hr, rfl⟩ := List.forall₂_cons_left_iff.mp hy
    exact .cons (hc head List.mem_cons_self a b ha hb)
      (ih hr (fun d hd x y hx hy => hc d (List.mem_cons_of_mem _ hd) x y hx hy))

/-- Both actual finite replacement-table executions at the same literal
headword give genuinely paired ordered rows, with all original callers
and passing-cover implications derived from the actual executions. -/
theorem executeRows_order (heads : List Nat)
    (hh : SourceTrackingRaw.trackingCheck heads = true) (left right : Nat)
    (hl : lowCheckCode 0 left = true) (hr : lowCheckCode 0 right = true)
    (hml : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 left))
    (hmr : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 right))
    (hbl : interpretation 0 left ≤ interpretation 0 (lastCode heads))
    (hbr : interpretation 0 right ≤ interpretation 0 (lastCode heads))
    (hlt : interpretation 0 left < interpretation 0 right) (xs ys : List Row)
    (hx : xs ∈ InsertionSupport.executeRows left heads)
    (hy : ys ∈ InsertionSupport.executeRows right heads) : List.Forall₂ RowOrder xs ys := by
  exact matched_rows_order left right
    (InsertionSupport.executeRows_relation left heads xs hx)
    (InsertionSupport.executeRows_relation right heads ys hy)
    (fun head hhead a b ha hb => actual_row_order heads hh head left right hhead
      hl hr hml hmr hbl hbr hlt a b ha hb)

/-- The independent insertion procedures at one original checked
headword are strictly ordered by their actual multiplicative factors. -/
theorem execute_insertion_lex (heads : List Nat)
    (hh : SourceTrackingRaw.trackingCheck heads = true) (left right : Nat)
    (hl : lowCheckCode 0 left = true) (hr : lowCheckCode 0 right = true)
    (hml : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 left))
    (hmr : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 right))
    (hbl : interpretation 0 left ≤ interpretation 0 (lastCode heads))
    (hbr : interpretation 0 right ≤ interpretation 0 (lastCode heads))
    (hlt : interpretation 0 left < interpretation 0 right) (xs ys : List Nat)
    (hx : xs ∈ Insertion.execute (left, heads))
    (hy : ys ∈ Insertion.execute (right, heads)) :
    List.Lex (· < ·) (xs.map (interpretation 0)) (ys.map (interpretation 0)) := by
  obtain ⟨xrows, hxr, hxe⟩ := (Part.mem_map_iff Insertion.word).mp hx
  obtain ⟨yrows, hyr, hye⟩ := (Part.mem_map_iff Insertion.word).mp hy
  have hrel := executeRows_order heads hh left right hl hr hml hmr hbl hbr hlt
    xrows yrows hxr hyr
  have hne : xrows ≠ [] := by
    intro he
    have hp := InsertionSupport.relation_heads left
      (InsertionSupport.executeRows_relation left heads xrows hxr)
    have hn : heads = [] := hp.symm.trans (by simp only [he, List.map_nil])
    exact ((SourceTrackingRaw.trackingCheck_exact heads).mp hh).1 hn
  rw [← hxe, ← hye]
  exact rows_word_lex hrel hne

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.InsertionOrderSupport
