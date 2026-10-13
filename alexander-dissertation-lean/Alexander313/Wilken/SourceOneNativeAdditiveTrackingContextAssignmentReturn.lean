import Alexander313.Wilken.SourceOneNativeAdditiveTrackingReplacementFidelity
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingAssignment

/-!
# Genuine original source-zero return of a whole raised-context assignment

The lower context is the actual epsilon head of an original checked tracker.
Its independently executing assignment supplies every LOW entry and its
bound by the lower input. The original final-value bound puts all entries
below that head's OWN endpoint. Actual raw-root construction and contextual
mu fidelity therefore preserve every proper returned mu, including arbitrary
raw epsilon spellings. The existing literal source-zero return maps the whole
word and yields an original RAW tracker. No equality with an original-source
assignment, branch-composition law or order comparison is asserted here.
Source-only uncompiled candidates; the original source base is literal zero.
-/

noncomputable section

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.ContextAssignmentReturn

open Replacement (EntryMatches)
open NativeContext.SourceTrackingSequences (lastCode lastCode_mem lastCode_singleton)
open SkTracking.Support (stripLast_cons_nonempty lastCode_cons_nonempty)
open Hereditary.FinePredecessor (stripLast)

/-- The actual raw parser supplies the lower HIGH caller. Its value law,
not the raw spelling, licenses the genuine contextual mu return. -/
theorem contextual_raw_entry (root c d : Nat) (ha : Mu.inputCheck root = true)
    (hc : NativeContext.SourceTrackingRaw.Support.inputCheck (alphaCode root) c = true)
    (hd : EntryMatches (alphaCode root) c d)
    (hb : NativeContext.interpretation (alphaCode root) c < Enclosure.sourceAlphaPlus root) :
    SourceTrackingRaw.Support.inputCheck d = true ∧
      SourceTrackingRaw.Support.muValue d =
        NativeContext.SourceTrackingRaw.Support.muValue (alphaCode root) c := by
  have hs := NativeContext.SourceTrackingRaw.Support.rootCode_spec (alphaCode root) c hc
  have hd' : EntryMatches (alphaCode root)
      (NativeContext.SourceTrackingRaw.Support.rootCode (alphaCode root) c) d :=
    ⟨hd.1, hd.2.trans hs.2.2.symm⟩
  have hm := ReplacementFidelity.contextual_entry root _ d ha hs.2.1 hd'
    (hs.2.2.trans_lt hb)
  exact ⟨hm.1, hm.2⟩

private theorem relation_rootWord {r : Nat} {xs ys : List Nat}
    (hrel : List.Forall₂ (EntryMatches r) xs ys)
    (hc : ∀ c ∈ xs, NativeContext.SourceTrackingRaw.Support.inputCheck r c = true) :
    List.Forall₂ (EntryMatches r) (NativeContext.SourceTrackingRaw.Support.rootWord r xs) ys := by
  revert hc
  induction hrel with
  | nil => intro hc; exact .nil
  | @cons c d xs ys hd ht ih =>
    intro hc
    have hs := NativeContext.SourceTrackingRaw.Support.rootCode_spec r c (hc c List.mem_cons_self)
    exact .cons ⟨hd.1, hd.2.trans hs.2.2.symm⟩
      (ih (fun a ha => hc a (List.mem_cons_of_mem _ ha)))

theorem raw_reference_return (root : Nat) (ha : Mu.inputCheck root = true)
    (xs ys : List Nat) (hr : NativeContext.SourceTrackingRaw.Reference (alphaCode root) xs)
    (hrel : List.Forall₂ (EntryMatches (alphaCode root)) xs ys)
    (hb : ∀ c ∈ xs, NativeContext.interpretation (alphaCode root) c < Enclosure.sourceAlphaPlus root) :
    SourceTrackingRaw.Reference ys := by
  apply ReplacementFidelity.reference_return root ha _ ys hr.2
    (relation_rootWord hrel hr.1)
  intro c hc
  obtain ⟨a, hm, rfl⟩ := List.mem_map.mp hc
  exact (NativeContext.SourceTrackingRaw.Support.rootCode_spec _ a (hr.1 a hm)).2.2.trans_lt
    (hb a hm)

private theorem entry_relation_prefix {r : Nat} {xs ys : List Nat}
    (hrel : List.Forall₂ (EntryMatches r) xs ys) :
    List.Forall₂ (EntryMatches r) (stripLast xs) (stripLast ys) := by
  induction hrel with
  | nil => exact .nil
  | @cons c d xs ys hd ht ih =>
    cases xs with
    | nil => cases ht; exact .nil
    | cons a as =>
      cases ht with
      | cons he hrest =>
        rw [stripLast_cons_nonempty c _ (List.cons_ne_nil _ _),
          stripLast_cons_nonempty d _ (List.cons_ne_nil _ _)]
        exact .cons hd ih

private theorem entry_relation_last {r : Nat} {xs ys : List Nat}
    (hrel : List.Forall₂ (EntryMatches r) xs ys) (hne : xs ≠ []) :
    EntryMatches r (lastCode xs) (lastCode ys) := by
  revert hne
  induction hrel with
  | nil => intro hn; exact False.elim (hn rfl)
  | @cons c d xs ys hd ht ih =>
    intro hn
    by_cases hx : xs = []
    · subst xs
      cases ht
      simpa only [lastCode_singleton] using hd
    · have hy : ys ≠ [] := by
        intro hy
        have he := ht.length_eq
        rw [hy, List.length_nil] at he
        exact hx (List.length_eq_zero_iff.mp he)
      rw [lastCode_cons_nonempty c xs hx, lastCode_cons_nonempty d ys hy]
      exact ih hx

theorem raw_tracking_return (root : Nat) (ha : Mu.inputCheck root = true)
    (xs ys : List Nat)
    (hx : NativeContext.SourceTrackingRaw.trackingCheck (alphaCode root) xs = true)
    (hrel : List.Forall₂ (EntryMatches (alphaCode root)) xs ys)
    (hb : ∀ c ∈ xs, NativeContext.interpretation (alphaCode root) c < Enclosure.sourceAlphaPlus root) :
    SourceTrackingRaw.trackingCheck ys = true := by
  have hs := (NativeContext.SourceTrackingRaw.trackingCheck_conditions _ xs).mp hx
  have hne : ys ≠ [] := by
    intro hy
    have he := hrel.length_eq
    rw [hy, List.length_nil] at he
    exact hs.1 (List.length_eq_zero_iff.mp he)
  have hp := entry_relation_prefix hrel
  have hl := entry_relation_last hrel hs.1
  have hr := raw_reference_return root ha _ _ hs.2.1 hp (by
    intro c hc
    exact hb c (Hereditary.FinePredecessor.stripLast_mem _ _ hc))
  apply (SourceTrackingRaw.trackingCheck_exact ys).mpr
  refine ⟨hne, hr, ((Theta.acceptedLowCode_iff 0 _).mp hl.1).1, ?_, ?_, ?_⟩
  · rw [hl.2]; exact hs.2.2.2.1
  · rw [hl.2]; exact hs.2.2.2.2.1
  · by_cases hy : stripLast ys = []
    · have he : stripLast xs = [] := by
        have hh := hp.length_eq
        rw [hy, List.length_nil] at hh
        exact List.length_eq_zero_iff.mp hh
      rw [if_pos hy, hl.2]
      have hbase : 1 ≤ NativeContext.base (alphaCode root) := by
        rw [OrderSupport.alpha_base root ha]
        exact Order.one_le_iff_pos.mpr (root_pos root ha)
      exact hbase.trans (by simpa only [if_pos he] using hs.2.2.2.2.2)
    · have he : stripLast xs ≠ [] := by
        intro he
        have hh := hp.length_eq
        rw [he, List.length_nil] at hh
        exact hy (List.length_eq_zero_iff.mp hh.symm)
      have hm := contextual_raw_entry root (lastCode (stripLast xs)) (lastCode (stripLast ys))
        ha (hs.2.1.nodes _ (lastCode_mem _ he)) (entry_relation_last hp he)
        (hb _ (Hereditary.FinePredecessor.stripLast_mem _ _ (lastCode_mem _ he)))
      rw [if_neg hy, hl.2, hm.2]
      simpa only [if_neg he] using hs.2.2.2.2.2

/-- An independently executed arbitrary lower-head assignment derives all
return and OWN-endpoint callers. Its original return is a real RAW tracker.
This is a complete provenance conclusion, not a context-composition law. -/
theorem assignment_return (word : List Nat) (head input : Nat) (xs : List Nat)
    (hw : SourceTrackingRaw.trackingCheck word = true) (hh : head ∈ stripLast word)
    (ho : xs ∈ NativeContext.SourceAdditiveTracking.Assignment.execute
      (ReplacementSupport.raisedBaseCode head) input)
    (hb : NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) input ≤
      interpretation 0 (lastCode word)) :
    SourceTrackingRaw.trackingCheck (Replacement.returnWord head xs) = true ∧
      List.Forall₂ (EntryMatches (ReplacementSupport.raisedBaseCode head)) xs
        (Replacement.returnWord head xs) ∧
      (Replacement.returnWord head xs).map (interpretation 0) =
        xs.map (NativeContext.interpretation (ReplacementSupport.raisedBaseCode head)) ∧
      ∀ d ∈ Replacement.returnWord head xs, Theta.acceptedLowCode 0 d = true := by
  have ht := (SourceTrackingRaw.trackingCheck_exact word).mp hw
  have hhead := ht.2.1.nodes head hh
  have hroot := (SourceTrackingRaw.Support.rootCode_spec head hhead).2.1
  have he := ReplacementFidelity.raisedBase_eq_alphaCode head hhead
  have hne : stripLast word ≠ [] := by
    intro hn
    rw [hn] at hh
    exact List.not_mem_nil hh
  have hend := EndpointSupport.tracking_final_lt_endpoints word hw hne head hh
  have htrack := NativeContext.SourceAdditiveTracking.Assignment.execute_tracking _ input xs ho
  have hlow := ((NativeContext.SourceTrackingRaw.trackingCheck_exact _ xs).mp htrack).source_domain
  have hall := (NativeContext.SourceAdditiveTracking.Assignment.execute_spec _ input xs ho).2.1.2.1
  have hfinite : ∀ c ∈ xs,
      NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) c < finiteBase 1 := by
    intro c hc
    exact ((hall c hc).trans hb).trans_lt
      (SourceTrackingRaw.Support.original_bound _ ht.2.2.1)
  have hown : ∀ c ∈ xs,
      NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) c <
        Enclosure.sourceAlphaPlus (SourceTrackingRaw.Support.rootCode head) := by
    intro c hc
    exact ((hall c hc).trans hb).trans_lt hend
  have hrel := Replacement.returnWord_relation head xs (fun c hc => (hlow c hc).1) hfinite
  have hreturned := raw_tracking_return (SourceTrackingRaw.Support.rootCode head) hroot xs
    (Replacement.returnWord head xs) (by simpa only [he] using htrack)
    (by simpa only [he] using hrel) (by simpa only [he] using hown)
  exact ⟨hreturned, hrel, Replacement.returnWord_values head xs (fun c hc => (hlow c hc).1) hfinite,
    Replacement.returnWord_checked head xs (fun c hc => (hlow c hc).1) hfinite⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.ContextAssignmentReturn
