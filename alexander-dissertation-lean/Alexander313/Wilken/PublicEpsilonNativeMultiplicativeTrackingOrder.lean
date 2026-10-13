import Alexander313.Wilken.PublicEpsilonNativeMultiplicativeTrackingOrderSupport
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingAssignment

/-!
# Genuine lexical order of the actual relative M assignment

At a genuine greater original Node, the actual greatest covered table
either returns a singleton or a shorter selected endpoint word followed
by the greater value. If the smaller input precedes that selected endpoint,
strict real localization length gives the comparison recursively. If it
lies above the selected endpoint, the actual direct mu cover derives an
independently computed prefix and the original whole-word upper bound
gives the first differing strict comparison. The generic localized-word
statement is about that concrete procedure, not the additive assignment
on nonM inputs. Only actual M executions are identified with source3.22.
No lexicographic word, prefix, cover or recursion oracle. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceMultiplicativeTracking.Order

open PublicEpsilonUnboundedIota Support OrderSupport SourceLocalization

/-- A true original HIGH epsilon directly covering a genuine raw M
input has its independently computed raw word as a VALUE prefix of that
input's independently computed raw M word. -/
theorem rawWord_direct_cover_prefix (q b current : Nat)
    (hb : Mu.inputCheck q b = true)
    (hc : SourceMultiplicativePrincipal.inputCheck q current = true)
    (hbc : interpretation q b < interpretation q current)
    (hcover : interpretation q current ≤ Mu.sourceValue q b) :
    ((rawWord q b).map (interpretation q)).IsPrefix
      ((rawWord q current).map (interpretation q)) := by
  have hbi := high_node_input q b hb
  have hci := SourceMultiplicativePrincipal.rootAdapter_input q current hc
  have hv := (RootAdapter.rootCode_spec q current hci).2
  rw [RawRecurrence.rawWord_values_word q b hbi, rawWord_root_values q current hci]
  exact word_direct_cover_prefix q b (RootAdapter.rootCode q current) hb
    (SourceMultiplicativePrincipal.rootInput q current hc)
    (by simpa only [hv] using hbc) (by simpa only [hv] using hcover)

/-- The independently computed covered ordinary-localization word is
strictly ordered on all genuine original Nodes. It is not Definition3.20's
nonmultiplicative factor/insertion assignment. -/
theorem word_lex (q left right : Nat)
    (hl : SourceLocalization.inputCheck q left = true)
    (hr : SourceLocalization.inputCheck q right = true)
    (horder : interpretation q left < interpretation q right) :
    List.Lex (· < ·) ((word q left).map (interpretation q))
      ((word q right).map (interpretation q)) := by
  let P : Nat → Prop := fun n => ∀ right,
    (properPrefix q right).length = n → SourceLocalization.inputCheck q right = true →
      ∀ left, SourceLocalization.inputCheck q left = true →
        interpretation q left < interpretation q right →
          List.Lex (· < ·) ((word q left).map (interpretation q))
            ((word q right).map (interpretation q))
  have hall : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro right hn hr left hl horder
      cases hs : select q right (table q (properPrefix q right)) with
      | none =>
        have hw : word q right = [right] := by simp only [word, extend, hs]
        rw [hw, List.map_cons, List.map_nil]
        cases hx : (word q left).map (interpretation q) with
        | nil => exact False.elim (word_values_ne_nil q left hx)
        | cons a xs =>
          apply List.Lex.rel
          have ha : a ∈ (word q left).map (interpretation q) := by rw [hx]; exact List.mem_cons_self
          exact (word_values_bound q left hl a ha).trans_lt horder
      | some e =>
        have he := Recurrence.selected_node q right right e hr hs
        have hei := high_node_input q e.1 he.2.1
        have hw := Recurrence.word_some_values q right e hr hs
        rw [hw]
        by_cases hbefore : interpretation q left < interpretation q e.1
        · have hlt := (Recurrence.selected_prefix_shorter q right right e hr hs).trans_eq hn
          exact List.Lex.append_right (· < ·) [interpretation q right]
            (ih _ hlt e.1 rfl hei left hl hbefore)
        · have hel : interpretation q e.1 ≤ interpretation q left := le_of_not_gt hbefore
          by_cases heq : interpretation q left = interpretation q e.1
          · rw [Spelling.word_values_eq q left e.1 hl hei heq]
            exact prefix_lex_singleton _ _ _ (List.prefix_refl _) (fun a ha =>
              (word_values_bound q e.1 hei a ha).trans_lt
                (SourceAdditiveTracking.ProperPrefix.properPrefix_lt_root q right hr e.1 he.1))
          · have helt : interpretation q e.1 < interpretation q left :=
              lt_of_le_of_ne hel (Ne.symm heq)
            have hp := word_direct_cover_prefix q e.1 left he.2.1 hl helt (horder.le.trans he.2.2)
            exact prefix_lex_singleton _ _ _ hp
              (fun a ha => (word_values_bound q left hl a ha).trans_lt horder)
  exact hall _ right rfl hr left hl horder

/-- On its exact original admitted M domain, the raw numerical procedure
has strict lexical VALUE order, including the original base singleton. -/
theorem rawWord_multiplicative_lex (q left right : Nat)
    (hl : SourceMultiplicativePrincipal.inputCheck q left = true)
    (hr : SourceMultiplicativePrincipal.inputCheck q right = true)
    (horder : interpretation q left < interpretation q right) :
    List.Lex (· < ·) ((rawWord q left).map (interpretation q))
      ((rawWord q right).map (interpretation q)) := by
  have hla := SourceMultiplicativePrincipal.rootAdapter_input q left hl
  have hra := SourceMultiplicativePrincipal.rootAdapter_input q right hr
  let lroot := RootAdapter.rootCode q left
  let rroot := RootAdapter.rootCode q right
  have hli := SourceMultiplicativePrincipal.rootInput q left hl
  have hri := SourceMultiplicativePrincipal.rootInput q right hr
  have hlv := (RootAdapter.rootCode_spec q left hla).2
  have hrv := (RootAdapter.rootCode_spec q right hra).2
  rw [rawWord_root_values q left hla, rawWord_root_values q right hra]
  exact word_lex q lroot rroot hli hri (by simpa only [lroot, rroot, hlv, hrv] using horder)

/-- Actual independently executing full assignments at two original M
inputs satisfy the M subcase of source Lemma3.22. The nonM factor case is
explicitly not inferred from the wider localized-word comparison. -/
theorem execute_multiplicative_lex (q left right : Nat) (leftOut rightOut : List Nat)
    (hl : SourceMultiplicativePrincipal.inputCheck q left = true)
    (hr : SourceMultiplicativePrincipal.inputCheck q right = true)
    (horder : interpretation q left < interpretation q right)
    (hlo : leftOut ∈ SourceAdditiveTracking.Assignment.execute q left)
    (hro : rightOut ∈ SourceAdditiveTracking.Assignment.execute q right) :
    List.Lex (· < ·) (leftOut.map (interpretation q)) (rightOut.map (interpretation q)) := by
  have hle := Part.mem_unique hlo (SourceAdditiveTracking.Assignment.execute_multiplicative q left hl)
  have hre := Part.mem_unique hro (SourceAdditiveTracking.Assignment.execute_multiplicative q right hr)
  rw [hle, hre]
  exact rawWord_multiplicative_lex q left right hl hr horder

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceMultiplicativeTracking.Order
