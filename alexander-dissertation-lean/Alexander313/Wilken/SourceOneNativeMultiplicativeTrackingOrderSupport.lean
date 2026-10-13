import Alexander313.Wilken.SourceOneNativeAdditiveTrackingLocalizationSupport
import Alexander313.Wilken.SourceOneNativeAdditiveTrackingProperPrefix
import Alexander313.Wilken.SourceOneNativeMultiplicativeTrackingRawRecurrence
import Mathlib.Data.List.Lex

/-!
# Genuine covered prefixes of original source-one multiplicative words

The actual source-zero adjacent interval places a covered HIGH root on
the independently computed localization path. Its equal-valued path node
passes the real mu test. Greatest-cover selection and strictly shorter
localization prefixes then show that its independently computed word is
a VALUE prefix. No written support membership, assigned word, cover or
prefix oracle is supplied. This concerns the multiplicative procedure;
the complete nonmultiplicative assignment order remains separate.
Uncompiled source candidates.
-/

noncomputable section

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceMultiplicativeTracking.OrderSupport

open Support Prefix RecurrenceSupport
open Hereditary.FinePredecessor (stripLast stripLast_split)

private theorem order_endpoint_append (xs : List Nat) (d : Nat) :
    Localization.endpoint (xs ++ [d]) = d := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases xs with
    | nil => rfl
    | cons b xs => exact ih

theorem rootCheck_node_input (c : Nat) (hc : rootCheck c = true) :
    Localization.inputCheck 0 c = true := by
  obtain ⟨a, he, ha, hn, _⟩ := (rootCheck_exact c).mp hc
  exact (Localization.inputCheck_exact 0 c).mpr ⟨a, he, ha, hn⟩

/-- The real covered HIGH value occurs strictly before the endpoint of
the actual original localization. Its literal spelling need not occur. -/
theorem covered_proper_node (root b : Nat)
    (hi : Localization.inputCheck 0 root = true) (hb : rootCheck b = true)
    (hlt : interpretation 0 b < interpretation 0 root)
    (hcover : interpretation 0 root ≤ Mu.sourceValue b) :
    ∃ d ∈ properPrefix root, interpretation 0 d = interpretation 0 b := by
  have hr := (Localization.inputCheck_exact 0 root).mp hi
  obtain ⟨tail, hhead⟩ := Localization.nativePath_head 0 root
  have hp := Localization.nativePath_source 0 root hi
  rw [hhead] at hp
  have hend := Localization.nativePath_end 0 root hi
  have hstart : Localization.value 0 (Localization.baseRaw 0) < Localization.value 0 b := by
    rw [Localization.baseRaw_value]
    simpa only [finiteBase_zero, Localization.value] using
      EpsilonOffsets.epsilon_one_lt (root_epsilon b hb)
  have hle : Localization.value 0 b ≤
      Localization.value 0 (Localization.endpoint (Localization.baseRaw 0 :: tail)) := by
    rw [← hhead, hend]
    exact hlt.le
  have hbound : Localization.value 0 (Localization.endpoint (Localization.baseRaw 0 :: tail)) <
      Enclosure.sourceAlphaPlus b := by
    rw [← hhead, hend]
    exact hcover.trans_lt (SourceAdditiveTracking.EndpointSupport.mu_lt_endpoint b hb)
  obtain ⟨d, hd, hv⟩ := SourceAdditiveTracking.LocalizationSupport.covered_value_on_path
    hr hb hp hstart hle hbound
  have hne : tail ≠ [] := fun he => by rw [he] at hd; exact List.not_mem_nil hd
  obtain ⟨last, htail, _⟩ := stripLast_split tail hne
  have hlast : interpretation 0 last = interpretation 0 root := by
    have hep : Localization.endpoint (Localization.nativePath 0 root) = last := by
      rw [hhead, htail]
      change Localization.endpoint ((Localization.baseRaw 0 :: stripLast tail) ++ [last]) = last
      exact order_endpoint_append _ _
    simpa only [hep, Localization.value] using hend
  have hm : d ∈ stripLast tail := by
    rw [htail] at hd
    rcases List.mem_append.mp hd with hd | hd
    · exact hd
    · have he : d = last := List.mem_singleton.mp hd
      have heq : interpretation 0 b = interpretation 0 root := by
        exact hv.symm.trans (by simpa only [he] using hlast)
      exact False.elim (heq.not_lt hlt)
  exact ⟨d, by simpa only [properPrefix, hhead, List.tail_cons] using hm, hv⟩

/-- Every value of the actual multiplicative procedure lies below its
original input, directly from finite table membership. -/
theorem word_value_bound (root : Nat) (hi : Localization.inputCheck 0 root = true) :
    ∀ v ∈ (word root).map (interpretation 0), v ≤ interpretation 0 root := by
  intro v hv
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hv
  cases hs : select root (table (properPrefix root)) with
  | none =>
    have he : c = root := by
      simpa only [word, extend, hs, List.mem_singleton] using hc
    exact he ▸ le_rfl
  | some e =>
    have hm : c ∈ e.2 ++ [root] := by simpa only [word, extend, hs] using hc
    rcases List.mem_append.mp hm with hm | hm
    · have hd := List.mem_reverse.mp
        (buildRev_word_mem (properPrefix root).reverse e (select_mem root _ e hs) c hm)
      exact properPrefix_le_root root hi c hd
    · exact List.mem_singleton.mp hm ▸ le_rfl

/-- A genuinely covering original HIGH root supplies an independently
executed VALUE prefix, by greatest-cover descent on real path lengths. -/
theorem covered_word_prefix (root b : Nat)
    (hi : Localization.inputCheck 0 root = true) (hb : rootCheck b = true)
    (hlt : interpretation 0 b < interpretation 0 root)
    (hcover : interpretation 0 root ≤ Mu.sourceValue b) :
    ((word b).map (interpretation 0)).IsPrefix ((word root).map (interpretation 0)) := by
  have aux : ∀ n : Nat, ∀ root : Nat, (properPrefix root).length = n →
      Localization.inputCheck 0 root = true → ∀ b : Nat, rootCheck b = true →
      interpretation 0 b < interpretation 0 root → interpretation 0 root ≤ Mu.sourceValue b →
      ((word b).map (interpretation 0)).IsPrefix ((word root).map (interpretation 0)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro root hn hi b hb hlt hcover
      obtain ⟨d, hd, hv⟩ := covered_proper_node root b hi hb hlt hcover
      have hdhigh := properPrefix_high root hi d hd
      have hmu := Mu.ValueInvariance.sourceValue_eq d b hdhigh hb hv
      have hdcover : interpretation 0 root ≤ Mu.sourceValue d := by rw [hmu]; exact hcover
      have hlow := Localization.node_low 0 root ((Localization.inputCheck_exact 0 root).mp hi)
      cases hs : select root (table (properPrefix root)) with
      | none =>
        have hno := (Recurrence.selected_none_iff_no_cover root root hi hlow).mp hs d hd
        exact False.elim (hno.not_ge hdcover)
      | some e =>
        have he := Recurrence.selected_node root root e hi hs
        have hei := rootCheck_node_input e.1 he.2.1
        have hbe : interpretation 0 b ≤ interpretation 0 e.1 := by
          rw [← hv]
          exact Recurrence.selected_greatest root root e hi hlow hs d hd hdcover
        have hprefix : ((word b).map (interpretation 0)).IsPrefix
            ((word e.1).map (interpretation 0)) := by
          by_cases heq : interpretation 0 b = interpretation 0 e.1
          · rw [Spelling.word_values_eq b e.1 (rootCheck_node_input b hb) hei heq]
            exact List.prefix_refl _
          · have hsmall := Recurrence.selected_prefix_shorter root root e hi hs
            have hlen : (properPrefix e.1).length < n := by simpa only [hn] using hsmall
            exact ih _ hlen e.1 rfl hei b hb (lt_of_le_of_ne hbe heq)
              ((properPrefix_le_root root hi e.1 he.1).trans hcover)
        rw [Recurrence.word_some_values root e hi hs]
        exact hprefix.trans (List.prefix_append _ _)
  exact aux _ root rfl hi b hb hlt hcover

theorem rawWord_values_root (current : Nat)
    (hc : SourceLocalization.RootAdapter.inputCheck current = true) :
    (rawWord current).map (interpretation 0) =
      (word (SourceLocalization.RootAdapter.rootCode current)).map (interpretation 0) := by
  let root := SourceLocalization.RootAdapter.rootCode current
  have hi := SourceLocalization.RootAdapter.rootInput current hc
  have hn := (SourceLocalization.RootAdapter.rootCode_spec current hc).1
  have hp := node_principal_spec root hn
  have hr : SourceLocalization.RootAdapter.inputCheck root = true :=
    (SourceLocalization.RootAdapter.inputCheck_exact root).mpr ⟨hp.1, hp.2.2.2, hp.2.2.1⟩
  exact (Spelling.rawWord_values_eq current root hc hr
    (SourceLocalization.RootAdapter.rootCode_value current hc).symm).trans
      (RawRecurrence.rawWord_values_word root hi)

/-- A pure strict comparison at the first residual entry after a derived
prefix; no relation between two computed assignments is an input. -/
theorem prefix_singleton_lex (xs prefix : List Ordinal.{0}) (bound : Ordinal.{0})
    (hp : prefix.IsPrefix xs) (hb : ∀ v ∈ xs, v < bound) :
    List.Lex (· < ·) xs (prefix ++ [bound]) := by
  obtain ⟨tail, he⟩ := hp
  rw [← he]
  apply List.Lex.append_left (· < ·)
  cases tail with
  | nil => exact List.Lex.nil
  | cons v vs =>
    apply List.Lex.rel
    apply hb v
    rw [← he]
    exact List.mem_append.mpr (Or.inr List.mem_cons_self)

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceMultiplicativeTracking.OrderSupport
