import Alexander313.Wilken.SourceOneNativeMultiplicativeTrackingOrderSupport

/-!
# Original source-one multiplicative assignment lexicographic order

Actual greatest-cover recursion and genuine covered VALUE prefixes give
strict lexicographic comparison of independently computed multiplicative
words. The original RAW multiplicative guard and complete assignment
execution specialize this to the multiplicative part of Lemma3.22.
This does not assert the nonmultiplicative factor/raised-word comparison.
Original check zero, arbitrary admitted spellings and the value-one base
are retained; no Native base-one parser or order oracle. Uncompiled.
-/

noncomputable section

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceMultiplicativeTracking.Order

open Support Prefix OrderSupport

/-- The actual multiplicative procedure compares literal original Nodes
by their ordinal values. All selected recursive callers are derived. -/
theorem word_values_lex (left right : Nat)
    (hl : Localization.inputCheck 0 left = true) (hr : Localization.inputCheck 0 right = true)
    (hlt : interpretation 0 left < interpretation 0 right) :
    List.Lex (· < ·) ((word left).map (interpretation 0)) ((word right).map (interpretation 0)) := by
  have aux : ∀ n : Nat, ∀ right : Nat, (properPrefix right).length = n →
      Localization.inputCheck 0 right = true → ∀ left : Nat,
      Localization.inputCheck 0 left = true → interpretation 0 left < interpretation 0 right →
      List.Lex (· < ·) ((word left).map (interpretation 0)) ((word right).map (interpretation 0)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro right hn hr left hl hlt
      cases hs : select right (table (properPrefix right)) with
      | none =>
        have hw := Recurrence.word_none right hs
        cases he : word left with
        | nil =>
          exact False.elim ((extend_ne_nil left _) (by simpa only [word] using he))
        | cons a as =>
          rw [hw, he, List.map_cons, List.map_singleton]
          exact List.Lex.rel ((word_value_bound left hl _
            (List.mem_map.mpr ⟨a, by rw [he]; exact List.mem_cons_self, rfl⟩)).trans_lt hlt)
      | some e =>
        have hselected := Recurrence.selected_node right right e hr hs
        have hei := rootCheck_node_input e.1 hselected.2.1
        have hlen : (properPrefix e.1).length < n := by
          simpa only [hn] using Recurrence.selected_prefix_shorter right right e hr hs
        have hw := Recurrence.word_some_values right e hr hs
        rw [hw]
        rcases lt_trichotomy (interpretation 0 left) (interpretation 0 e.1) with hle | heq | hel
        · exact List.Lex.append_right (· < ·) [interpretation 0 right]
            (ih _ hlen e.1 rfl hei left hl hle)
        · rw [Spelling.word_values_eq left e.1 hl hei heq]
          simpa only [List.append_nil] using
            List.Lex.append_left (· < ·)
              (List.Lex.nil : List.Lex (· < ·) ([] : List Ordinal.{0}) [interpretation 0 right])
              ((word e.1).map (interpretation 0))
        · exact prefix_singleton_lex _ _ _
            (covered_word_prefix left e.1 hl hselected.2.1 hel (hlt.le.trans hselected.2.2))
            (fun v hv => (word_value_bound left hl v hv).trans_lt hlt)
  exact aux _ right rfl hr left hl hlt

/-- Genuine raw principal spellings are compared through their actual
last-atom roots; no written root or support equality is assumed. -/
theorem rawWord_values_lex (left right : Nat)
    (hl : SourceLocalization.RootAdapter.inputCheck left = true)
    (hr : SourceLocalization.RootAdapter.inputCheck right = true)
    (hlt : interpretation 0 left < interpretation 0 right) :
    List.Lex (· < ·) ((rawWord left).map (interpretation 0)) ((rawWord right).map (interpretation 0)) := by
  rw [rawWord_values_root left hl, rawWord_values_root right hr]
  apply word_values_lex _ _ (SourceLocalization.RootAdapter.rootInput left hl)
    (SourceLocalization.RootAdapter.rootInput right hr)
  rw [SourceLocalization.RootAdapter.rootCode_value left hl,
    SourceLocalization.RootAdapter.rootCode_value right hr]
  exact hlt

/-- The actual complete original-source-one procedure realizes the
multiplicative-input part of Lemma3.22, including the base-one endpoint. -/
theorem execute_multiplicative_lex (left right : Nat) (xs ys : List Nat)
    (hx : xs ∈ SourceAdditiveTracking.Assignment.execute left)
    (hy : ys ∈ SourceAdditiveTracking.Assignment.execute right)
    (hl : SourceMultiplicativePrincipal.inputCheck left = true)
    (hr : SourceMultiplicativePrincipal.inputCheck right = true)
    (hlt : interpretation 0 left < interpretation 0 right) :
    List.Lex (· < ·) (xs.map (interpretation 0)) (ys.map (interpretation 0)) := by
  have he := Part.mem_unique hx (SourceAdditiveTracking.Assignment.execute_multiplicative left hl)
  have hf := Part.mem_unique hy (SourceAdditiveTracking.Assignment.execute_multiplicative right hr)
  rw [he, hf]
  exact rawWord_values_lex left right (SourceMultiplicativePrincipal.rootAdapter_input left hl)
    (SourceMultiplicativePrincipal.rootAdapter_input right hr) hlt

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceMultiplicativeTracking.Order
