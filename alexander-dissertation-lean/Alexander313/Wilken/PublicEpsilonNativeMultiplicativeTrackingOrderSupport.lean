import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingLocalizationSupport
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingProperPrefix
import Alexander313.Wilken.PublicEpsilonNativeMultiplicativeTrackingRawRecurrence
import Alexander313.Wilken.PublicEpsilonNativeUnboundedMuSuccessorIntervals
import Mathlib.Data.List.Lex

/-!
# Genuine direct mu covers extend the independently computed M word

The real original argument-successor interval puts the covering epsilon
on the covered input's actual localization. Greatest covered selection
cannot precede that epsilon. When it goes further, the SAME direct cover
licenses the selected shorter localization, so genuine finite path length
proves the independent word extension. No covered-word prefix, selected
support, numerical recursion bound or tracking assignment is supplied.
The localized word procedure is used on genuine original theta-zero Nodes;
the raw M/full assignment adapters are separate. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceMultiplicativeTracking.OrderSupport

open PublicEpsilonUnboundedIota SourceTrackingSequences Support
open SourceLocalization SourceAdditiveTracking.LocalizationSupport
open Hereditary.FinePredecessor (stripLast stripLast_split)

theorem high_node_input (q b : Nat) (hb : Mu.inputCheck q b = true) :
    SourceLocalization.inputCheck q b = true := by
  obtain ⟨a, he, hc, hn, _⟩ := (RootLowCollapse.rootCheck_exact q b).mp hb
  exact (SourceLocalization.inputCheck_exact q b).mpr ⟨a, he, hc, hn⟩

theorem source_mu_lt_endpoint (q b : Nat) (hb : Mu.inputCheck q b = true) :
    Mu.sourceValue q b < Enclosure.sourceAlphaPlus q b := by
  exact ((Mu.muCode_spec q b hb).2.2).symm.trans_lt
    (Mu.SuccessorIntervals.muCode_lt_sourceAlphaPlus q b hb)

private theorem order_endpoint_append_singleton (xs : List Nat) (d : Nat) :
    endpoint (xs ++ [d]) = d := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases xs with
    | nil => rfl
    | cons b xs => exact ih

/-- A strictly internal path VALUE has an actual written proper-prefix
representative. The original root or covering code is never substituted
for that written representative. -/
theorem properPrefix_value_mem (q root : Nat)
    (hr : SourceLocalization.inputCheck q root = true) (v : Ordinal.{0})
    (hv : v ∈ (nativePath q root).map (interpretation q))
    (hb : base q < v) (ht : v < interpretation q root) :
    ∃ d ∈ properPrefix q root, interpretation q d = v := by
  obtain ⟨tail, he⟩ := nativePath_head q root
  obtain ⟨d, hd, hdv⟩ := List.mem_map.mp hv
  have hq := node_baseCheck q root ((SourceLocalization.inputCheck_exact q root).mp hr)
  rw [he] at hd
  rcases List.mem_cons.mp hd with hbase | hd
  · subst d
    have hvalue := baseRaw_value q hq
    have heq : v = base q := hdv.symm.trans (by simpa only [value] using hvalue)
    exact False.elim (hb.ne heq.symm)
  · have hn : tail ≠ [] := fun hn => by rw [hn] at hd; exact List.not_mem_nil hd
    obtain ⟨last, hs, _⟩ := stripLast_split tail hn
    have hend : endpoint (nativePath q root) = last := by
      rw [he, hs]
      change endpoint ((baseRaw q :: stripLast tail) ++ [last]) = last
      exact order_endpoint_append_singleton _ _
    have hlast : interpretation q last = interpretation q root := by
      simpa only [hend, value] using nativePath_end q root hr
    rw [hs] at hd
    rcases List.mem_append.mp hd with hd | hd
    · refine ⟨d, ?_, hdv⟩
      simpa only [properPrefix, he, List.tail_cons] using hd
    · have heq : d = last := List.mem_singleton.mp hd
      exact False.elim (ht.ne (by rw [← hdv, heq, hlast]))

/-- The real direct cover yields a written eligible support record with
the covering root's value and the SAME independently computed mu value. -/
theorem covered_candidate (q b root : Nat) (hb : Mu.inputCheck q b = true)
    (hr : SourceLocalization.inputCheck q root = true)
    (hbr : interpretation q b < interpretation q root)
    (hcover : interpretation q root ≤ Mu.sourceValue q b) :
    ∃ d ∈ properPrefix q root, interpretation q d = interpretation q b ∧
      interpretation q root ≤ Mu.sourceValue q d := by
  have hbi := high_node_input q b hb
  have hp := nativePath_interval_mem q root b hr
    ((SourceLocalization.inputCheck_exact q b).mp hbi) (Mu.root_base_lt q b hb)
    hbr.le (hcover.trans_lt (source_mu_lt_endpoint q b hb))
  obtain ⟨d, hd, he⟩ := properPrefix_value_mem q root hr _ hp (Mu.root_base_lt q b hb) hbr
  have hdh := properPrefix_roots q root hr d hd
  have hmu := Mu.ValueInvariance.sourceValue_eq q b d hb hdh he.symm
  exact ⟨d, hd, he, by rwa [← hmu]⟩

/-- Actual greatest covered selection is present and lies at or above
the direct covering root; no selected record is an input premise. -/
theorem covered_selection (q b root : Nat) (hb : Mu.inputCheck q b = true)
    (hr : SourceLocalization.inputCheck q root = true)
    (hbr : interpretation q b < interpretation q root)
    (hcover : interpretation q root ≤ Mu.sourceValue q b) :
    ∃ e, select q root (table q (properPrefix q root)) = some e ∧
      interpretation q b ≤ interpretation q e.1 := by
  obtain ⟨d, hd, hv, hc⟩ := covered_candidate q b root hb hr hbr hcover
  have hl := node_low q root ((SourceLocalization.inputCheck_exact q root).mp hr)
  cases hs : select q root (table q (properPrefix q root)) with
  | none =>
    have hn := (Recurrence.selected_none_iff_no_cover q root root hr hl).mp hs
    exact False.elim ((hn d hd).not_ge hc)
  | some e =>
    exact ⟨e, hs, by simpa only [hv] using Recurrence.selected_greatest q root root e hr hl hs d hd hc⟩

/-- Every independently computed genuine localized word directly
covered by an earlier epsilon extends that epsilon's independently
computed word in ordinal VALUES. Strict actual localization length is
solely a proof measure, never a numerical bound or supplied prefix. -/
theorem word_direct_cover_prefix (q b root : Nat) (hb : Mu.inputCheck q b = true)
    (hr : SourceLocalization.inputCheck q root = true)
    (hbr : interpretation q b < interpretation q root)
    (hcover : interpretation q root ≤ Mu.sourceValue q b) :
    ((word q b).map (interpretation q)).IsPrefix ((word q root).map (interpretation q)) := by
  let P : Nat → Prop := fun n => ∀ root,
    (properPrefix q root).length = n → SourceLocalization.inputCheck q root = true →
      ∀ b, Mu.inputCheck q b = true → interpretation q b < interpretation q root →
        interpretation q root ≤ Mu.sourceValue q b →
          ((word q b).map (interpretation q)).IsPrefix ((word q root).map (interpretation q))
  have hall : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro root hn hr b hb hbr hcover
      obtain ⟨e, hs, hbe⟩ := covered_selection q b root hb hr hbr hcover
      have hes := Recurrence.selected_node q root root e hr hs
      have hei := high_node_input q e.1 hes.2.1
      have her := SourceAdditiveTracking.ProperPrefix.properPrefix_lt_root q root hr e.1 hes.1
      have hw := Recurrence.word_some_values q root e hr hs
      rw [hw]
      by_cases he : interpretation q b = interpretation q e.1
      · rw [Spelling.word_values_eq q b e.1 (high_node_input q b hb) hei he]
        exact List.prefix_append _ _
      · have hbed : interpretation q b < interpretation q e.1 := lt_of_le_of_ne hbe he
        have hlt := (Recurrence.selected_prefix_shorter q root root e hr hs).trans_eq hn
        have hp := ih _ hlt e.1 rfl hei b hb hbed (her.le.trans hcover)
        exact hp.trans (List.prefix_append _ _)
  exact hall _ root rfl hr b hb hbr hcover

theorem word_values_ne_nil (q root : Nat) : (word q root).map (interpretation q) ≠ [] := by
  intro he
  exact extend_ne_nil q root _ (List.map_eq_nil_iff.mp he)

/-- All actual localized word entries remain below their original input
value. Only genuine table membership and the strict written path are used. -/
theorem word_values_bound (q root : Nat) (hr : SourceLocalization.inputCheck q root = true) :
    ∀ v ∈ (word q root).map (interpretation q), v ≤ interpretation q root := by
  intro v hv
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hv
  cases hs : select q root (table q (properPrefix q root)) with
  | none =>
    have hw : word q root = [root] := by simp only [word, extend, hs]
    rw [hw] at hd
    simpa only [List.mem_singleton.mp hd] using (le_refl (interpretation q root))
  | some e =>
    have hw : word q root = e.2 ++ [root] := by simp only [word, extend, hs]
    rw [hw] at hd
    rcases List.mem_append.mp hd with hd | hd
    · have hp := List.mem_reverse.mp (buildRev_word_mem q (properPrefix q root).reverse e
        (select_mem q root _ e hs) d hd)
      exact (SourceAdditiveTracking.ProperPrefix.properPrefix_lt_root q root hr d hp).le
    · simpa only [List.mem_singleton.mp hd] using (le_refl (interpretation q root))

/-- The genuine raw final-atom parser identifies only the independently
computed root-word VALUES; the original raw final spelling is retained. -/
theorem rawWord_root_values (q current : Nat)
    (hi : RootAdapter.inputCheck q current = true) :
    (rawWord q current).map (interpretation q) =
      (word q (RootAdapter.rootCode q current)).map (interpretation q) := by
  let root := RootAdapter.rootCode q current
  have hr := RootAdapter.rootInput q current hi
  have hv := (RootAdapter.rootCode_spec q current hi).2
  exact Values.extend_values q current root (table q (properPrefix q root))
    (table q (properPrefix q root))
    (fun e he => properPrefix_roots q root hr e.1
      (List.mem_reverse.mp (buildRev_code_mem q (properPrefix q root).reverse e he)))
    (fun e he => properPrefix_roots q root hr e.1
      (List.mem_reverse.mp (buildRev_code_mem q (properPrefix q root).reverse e he)))
    ((RootAdapter.inputCheck_exact q current).mp hi).1
    (node_low q root ((SourceLocalization.inputCheck_exact q root).mp hr)) hv.symm rfl

/-- An actual value prefix followed by a value above the entire smaller
word is lexicographically greater, whether the smaller residual is empty. -/
theorem prefix_lex_singleton (prefix xs : List Ordinal.{0}) (v : Ordinal.{0})
    (hp : prefix.IsPrefix xs) (hb : ∀ a ∈ xs, a < v) :
    List.Lex (· < ·) xs (prefix ++ [v]) := by
  obtain ⟨rest, he⟩ := hp
  rw [← he]
  cases rest with
  | nil =>
    simpa only [List.append_nil] using List.Lex.append_left (· < ·)
      (show List.Lex (· < ·) [] [v] from .nil) prefix
  | cons a rest =>
    have ha : a ∈ xs := by rw [← he]; exact List.mem_append.mpr (Or.inr List.mem_cons_self)
    exact List.Lex.append_left (· < ·) (.rel (hb a ha)) prefix

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceMultiplicativeTracking.OrderSupport
