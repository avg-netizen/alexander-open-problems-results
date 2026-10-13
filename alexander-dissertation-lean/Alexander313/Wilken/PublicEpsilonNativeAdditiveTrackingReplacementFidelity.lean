import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingReplacement
import Alexander313.Wilken.PublicEpsilonNativeTrackingEndpointSupport
import Alexander313.Wilken.PublicEpsilonNativeContextMuInvariance
import Alexander313.Wilken.PublicEpsilonNativeSkTrackingSupport

/-!
# Original mu callers for actual raised tracking replacements

The actual original reference endpoints are nested. A last-factor bound
by its already checked original headword final value therefore places
EVERY proper raised epsilon below the selected original head's OWN
argument-successor. The genuine contextual mu theorem and same-source
spelling theorem identify its original returned mu. Finite relation
induction then transfers the real raised reference and tracking checks.
No original-q tracker is inferred from value equality alone. Uncompiled.
-/

noncomputable section

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.ReplacementFidelity

open PublicEpsilonUnboundedIota SourceTrackingSequences
open Hereditary.FinePredecessor (stripLast)

abbrev SameEntry (q r c d : Nat) : Prop := SkSourceWord.Support.EntryMatches q (r, c) d

/-- A genuine alpha-context HIGH root below alpha's OWN endpoint has the
same actual mu at every original LOW returned spelling of that value. -/
theorem contextual_entry (q alpha c d : Nat)
    (ha : RootLowCollapse.rootCheck q alpha = true)
    (hc : RootLowCollapse.rootCheck (betaCode q alpha) c = true)
    (hd : SameEntry q (betaCode q alpha) c d)
    (hb : interpretation (betaCode q alpha) c < Enclosure.sourceAlphaPlus q alpha) :
    SourceTrackingRaw.Support.inputCheck q d = true ∧
      SourceTrackingRaw.Support.muValue q d = Mu.sourceValue (betaCode q alpha) c := by
  have hr := ContextTranslation.Return.returnedRoot_spec q alpha c ha hc
  have hraw : SourceTrackingRaw.Support.inputCheck q d = true :=
    (SourceTrackingRaw.Support.inputCheck_exact q d).mpr
      ⟨hd.1, by
        rw [hd.2.2]
        exact (root_base_lt q alpha ha).trans (by
          rw [← beta_base q alpha ha]
          exact root_base_lt _ c hc), by
        rw [hd.2.2]
        exact RootLowCollapse.root_epsilon _ c hc⟩
  have hm := SourceTrackingRaw.Support.muValue_eq q d
    (ContextTranslation.Return.returnedRoot q alpha c) hraw hr.1
    (hd.2.2.trans hr.2.symm)
  exact ⟨hraw, hm.trans
    (ContextTranslation.MuInvariance.returned_sourceValue_eq q alpha c ha hc hb)⟩

/-- Literal context identity comes from the actual SAME-q canonical
public returns of the original raw head and its constructed root atom. -/
theorem raisedBase_eq_betaCode (q head : Nat)
    (hh : SourceTrackingRaw.Support.inputCheck q head = true) :
    ReplacementSupport.raisedBaseCode q head =
      betaCode q (SourceTrackingRaw.Support.rootCode q head) := by
  have hs := SourceTrackingRaw.Support.rootCode_spec q head hh
  exact UniformPublicReturn.publicCode_value_invariant q q head _
    ((UniformPublicReturn.inputCheck_exact q head).mpr hs.1)
    ((UniformPublicReturn.inputCheck_exact q _).mpr (RootLowCollapse.root_low q _ hs.2.1))
    hs.2.2.symm

/-- The actual returned finite relation preserves genuine references once
EVERY original contextual caller is derived from the stated own interval. -/
theorem reference_return (q alpha : Nat) (ha : RootLowCollapse.rootCheck q alpha = true)
    (xs ys : List Nat) (hr : Reference (betaCode q alpha) xs)
    (hrel : List.Forall₂ (SameEntry q (betaCode q alpha)) xs ys)
    (hb : ∀ c ∈ xs, interpretation (betaCode q alpha) c < Enclosure.sourceAlphaPlus q alpha) :
    SourceTrackingRaw.Reference q ys := by
  revert ys hb
  induction hr with
  | nil =>
    intro ys hrel hb
    cases hrel
    exact ⟨fun c hc => False.elim (List.not_mem_nil hc), .nil⟩
  | one c hc =>
    intro ys hrel hb
    cases hrel with
    | cons hd ht =>
      cases ht
      exact SkTracking.Support.reference_one q _
        (contextual_entry q alpha c _ ha hc hd (hb c (by simp))).1
  | cons a b xs hroot hab hcover tail ih =>
    intro ys hrel hb
    cases hrel with
    | cons hd ht =>
      have htail := ih _ ht (fun c hc => hb c (List.mem_cons_of_mem _ hc))
      cases ht with
      | cons he hrest =>
        have hm := contextual_entry q alpha a _ ha hroot hd (hb a (by simp))
        have hn := contextual_entry q alpha b _ ha tail.first he (hb b (by simp))
        exact SkTracking.Support.reference_prepend q _ _ _ hm.1 hn.1
          (by rw [hd.2.2, he.2.2]; exact hab)
          (by rw [he.2.2, hm.2]; exact hcover) htail

private theorem relation_prefix {q r : Nat} {xs ys : List Nat}
    (hrel : List.Forall₂ (SameEntry q r) xs ys) :
    List.Forall₂ (SameEntry q r) (stripLast xs) (stripLast ys) := by
  induction hrel with
  | nil => exact .nil
  | @cons c d xs ys hd ht ih =>
    cases xs with
    | nil =>
      cases ht
      exact .nil
    | cons a as =>
      cases ht with
      | cons he hrest =>
        rw [SkTracking.Support.stripLast_cons_nonempty c _ (List.cons_ne_nil _ _),
          SkTracking.Support.stripLast_cons_nonempty d _ (List.cons_ne_nil _ _)]
        exact .cons hd ih

private theorem relation_last {q r : Nat} {xs ys : List Nat}
    (hrel : List.Forall₂ (SameEntry q r) xs ys) (hne : xs ≠ []) :
    SameEntry q r (lastCode xs) (lastCode ys) := by
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
      rw [SkTracking.Support.lastCode_cons_nonempty c xs hx,
        SkTracking.Support.lastCode_cons_nonempty d ys hy]
      exact ih hx

/-- Original own-interval callers identify every proper returned mu and
therefore transfer the whole actual raised tracking condition to q. -/
theorem tracking_return (q alpha : Nat) (ha : RootLowCollapse.rootCheck q alpha = true)
    (xs ys : List Nat) (hx : trackingCheck (betaCode q alpha) xs = true)
    (hrel : List.Forall₂ (SameEntry q (betaCode q alpha)) xs ys)
    (hb : ∀ c ∈ xs, interpretation (betaCode q alpha) c < Enclosure.sourceAlphaPlus q alpha) :
    SourceTrackingRaw.trackingCheck q ys = true := by
  have hs := (trackingCheck_exact _ xs).mp hx
  have hne : ys ≠ [] := by
    intro hy
    have he := hrel.length_eq
    rw [hy, List.length_nil] at he
    exact hs.1 (List.length_eq_zero_iff.mp he)
  have hp := relation_prefix hrel
  have hl := relation_last hrel hs.1
  have hprefix := reference_return q alpha ha _ _ hs.2.1 hp (by
    intro c hc
    exact hb c (Hereditary.FinePredecessor.stripLast_mem _ _ hc))
  apply (SourceTrackingRaw.trackingCheck_conditions q ys).mpr
  refine ⟨hne, hprefix, hl.1, ?_, ?_, ?_⟩
  · rw [hl.2.2]; exact hs.2.2.2.1
  · rw [hl.2.2]; exact hs.2.2.2.2.1
  · by_cases hy : stripLast ys = []
    · have he : stripLast xs = [] := by
        have hh := hp.length_eq
        rw [hy, List.length_nil] at hh
        exact List.length_eq_zero_iff.mp hh
      rw [if_pos hy, hl.2.2]
      have hbase := root_base_le q alpha ha
      rw [← beta_base q alpha ha] at hbase
      exact hbase.trans (by simpa only [if_pos he] using hs.2.2.2.2.2)
    · have he : stripLast xs ≠ [] := by
        intro he
        have hh := hp.length_eq
        rw [he, List.length_nil] at hh
        exact hy (List.length_eq_zero_iff.mp hh.symm)
      have hm := contextual_entry q alpha (lastCode (stripLast xs))
        (lastCode (stripLast ys)) ha (hs.2.1.nodes _ (lastCode_mem _ he))
        (relation_last hp he)
        (hb _ (Hereditary.FinePredecessor.stripLast_mem _ _ (lastCode_mem _ he)))
      rw [if_neg hy, hl.2.2, hm.2]
      simpa only [if_neg he] using hs.2.2.2.2.2

/-- The factor bound by the final original headword value and actual
endpoint nesting derive EVERY contextual mu caller for the raised word.
No original tracker or interval is added as an output hypothesis. -/
theorem raisedReplacement_tracking (q head factor : Nat) (word out : List Nat)
    (hw : SourceTrackingRaw.trackingCheck q word = true)
    (hh : head ∈ stripLast word)
    (hf : lowCheckCode q factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q factor))
    (hlt : interpretation q head < interpretation q factor)
    (hfactor : interpretation q factor ≤ interpretation q (lastCode word))
    (ho : out ∈ Replacement.raisedReplacement q head factor) :
    SourceTrackingRaw.trackingCheck q out = true := by
  have ht := (SourceTrackingRaw.trackingCheck_exact q word).mp hw
  have hhead := ht.2.1 head hh
  have hroot := (SourceTrackingRaw.Support.rootCode_spec q head hhead).2.1
  have he := raisedBase_eq_betaCode q head hhead
  have hne : stripLast word ≠ [] := by
    intro hnil
    rw [hnil] at hh
    exact List.not_mem_nil hh
  have hend := EndpointSupport.tracking_final_lt_endpoints q word hw hne head hh
  obtain ⟨raised, hr, hreturned⟩ := Part.mem_bind_iff.mp ho
  have hs := ReplacementSupport.raisedWord_spec q head factor raised hhead hf hm hlt hr
  have hrel := Replacement.returnWord_relation q _ raised out hreturned
    (fun c hc => (hs.2.2 c hc).1)
  have hpair : List.Forall₂ (SameEntry q (ReplacementSupport.raisedBaseCode q head)) raised out := by
    simpa only [Replacement.contextWord, List.forall₂_map_left_iff] using hrel
  have hbound : ∀ c ∈ raised, interpretation (ReplacementSupport.raisedBaseCode q head) c <
      Enclosure.sourceAlphaPlus q (SourceTrackingRaw.Support.rootCode q head) := by
    intro c hc
    exact ((hs.2.2 c hc).2.trans hfactor).trans_lt hend
  rw [he] at hs hpair hbound
  exact tracking_return q _ hroot raised out hs.1 hpair hbound

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.ReplacementFidelity
