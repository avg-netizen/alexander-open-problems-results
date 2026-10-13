import Alexander313.Wilken.SourceOneNativeAdditiveTrackingReplacement
import Alexander313.Wilken.SourceOneNativeTrackingEndpointSupport

/-!
# Original source-one mu fidelity for complete raised replacements

The checked original headword bounds its final value below every proper
root's own original endpoint. Under the honestly explicit last-factor
bound by that final value, every raised replacement entry is in the
selected original own interval. The actual source-one contextual return
and real RAW mu spelling theorem then identify every proper returned mu.
Finite relation induction transfers the whole genuine raised tracker to
the original check-zero dictionary. No value-only mu/Par inference,
Native base-one parser or tracking-assignment oracle. Uncompiled.
-/

noncomputable section

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.ReplacementFidelity

open Replacement (EntryMatches)
open NativeContext.SourceTrackingSequences (lastCode lastCode_singleton lastCode_mem)
open SkTracking.Support (stripLast_cons_nonempty lastCode_cons_nonempty)
open Hereditary.FinePredecessor (stripLast)

theorem contextual_entry (root c d : Nat) (ha : Mu.inputCheck root = true)
    (hc : NativeContext.PublicEpsilonUnboundedIota.Mu.inputCheck (alphaCode root) c = true)
    (hd : EntryMatches (alphaCode root) c d)
    (hb : NativeContext.interpretation (alphaCode root) c < Enclosure.sourceAlphaPlus root) :
    SourceTrackingRaw.Support.inputCheck d = true ∧
      SourceTrackingRaw.Support.muValue d =
        NativeContext.PublicEpsilonUnboundedIota.Mu.sourceValue (alphaCode root) c := by
  have hs := SkContextFidelity.sourceRoot_spec root c ha hc hb
  have he := NativeContext.RootLowCollapse.root_epsilon _ c hc
  have hr := (SourceTrackingRaw.Support.inputCheck_exact d).mpr
    ⟨((Theta.acceptedLowCode_iff 0 d).mp hd.1).1,
      by rw [hd.2]; exact EpsilonOffsets.epsilon_one_lt he,
      by rw [hd.2]; exact he⟩
  have hm := SourceTrackingRaw.Support.muValue_eq d (SkContextFidelity.sourceRoot root c)
    hr hs.1 (hd.2.trans hs.2.1.symm)
  exact ⟨hr, hm.trans hs.2.2.2⟩

theorem raisedBase_eq_alphaCode (head : Nat)
    (hh : SourceTrackingRaw.Support.inputCheck head = true) :
    ReplacementSupport.raisedBaseCode head = alphaCode (SourceTrackingRaw.Support.rootCode head) := by
  have hs := SourceTrackingRaw.Support.rootCode_spec head hh
  have hp := SourceTrackingRaw.Support.publicCode_spec head hs.1
  have hr := alphaCode_spec _ hs.2.1
  exact Canonical.check_value_injective _ _ hp.1 hr.1
    (hp.2.trans (hs.2.2.symm.trans hr.2.symm))

theorem reference_return (root : Nat) (ha : Mu.inputCheck root = true)
    (xs ys : List Nat) (hr : NativeContext.SourceTrackingSequences.Reference (alphaCode root) xs)
    (hrel : List.Forall₂ (EntryMatches (alphaCode root)) xs ys)
    (hb : ∀ c ∈ xs, NativeContext.interpretation (alphaCode root) c < Enclosure.sourceAlphaPlus root) :
    SourceTrackingRaw.Reference ys := by
  revert ys hb
  induction hr with
  | nil => intro ys hrel hb; cases hrel; exact .nil
  | one c hc =>
    intro ys hrel hb
    cases hrel with
    | cons hd ht =>
      cases ht
      exact .one _ (contextual_entry root c _ ha hc hd (hb c (List.mem_singleton_self c))).1
  | cons a b xs hc hab hcover tail ih =>
    intro ys hrel hb
    cases hrel with
    | cons hd ht =>
      have htail := ih _ ht (fun c hm => hb c (List.mem_cons_of_mem _ hm))
      cases ht with
      | cons he hrest =>
        have hm := contextual_entry root a _ ha hc hd (hb a List.mem_cons_self)
        exact .cons _ _ _ hm.1
          (by rw [hd.2, he.2]; exact hab)
          (by rw [he.2, hm.2]; exact hcover) htail

private theorem relation_prefix {r : Nat} {xs ys : List Nat}
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

private theorem relation_last {r : Nat} {xs ys : List Nat}
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

theorem tracking_return (root : Nat) (ha : Mu.inputCheck root = true)
    (xs ys : List Nat)
    (hx : NativeContext.SourceTrackingSequences.trackingCheck (alphaCode root) xs = true)
    (hrel : List.Forall₂ (EntryMatches (alphaCode root)) xs ys)
    (hb : ∀ c ∈ xs, NativeContext.interpretation (alphaCode root) c < Enclosure.sourceAlphaPlus root) :
    SourceTrackingRaw.trackingCheck ys = true := by
  have hs := (NativeContext.SourceTrackingSequences.trackingCheck_exact _ xs).mp hx
  have hne : ys ≠ [] := by
    intro hy
    have he := hrel.length_eq
    rw [hy, List.length_nil] at he
    exact hs.1 (List.length_eq_zero_iff.mp he)
  have hp := relation_prefix hrel
  have hl := relation_last hrel hs.1
  have hr := reference_return root ha _ _ hs.2.1 hp (by
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
      have hm := contextual_entry root (lastCode (stripLast xs)) (lastCode (stripLast ys))
        ha (hs.2.1.nodes _ (lastCode_mem _ he)) (relation_last hp he)
        (hb _ (Hereditary.FinePredecessor.stripLast_mem _ _ (lastCode_mem _ he)))
      rw [if_neg hy, hl.2, hm.2]
      simpa only [if_neg he] using hs.2.2.2.2.2

/-- Every original raised return is a genuine original RAW tracking word
once the joint factor<=computed-headword-final inequality is supplied.
All contextual mu/endpoint callers are conclusions of real execution. -/
theorem raisedReplacement_tracking (head factor : Nat) (word out : List Nat)
    (hw : SourceTrackingRaw.trackingCheck word = true)
    (hh : head ∈ stripLast word) (hf : lowCheckCode 0 factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor))
    (hlt : interpretation 0 head < interpretation 0 factor)
    (hfactor : interpretation 0 factor ≤ interpretation 0 (lastCode word))
    (ho : out ∈ Replacement.raisedReplacement head factor) :
    SourceTrackingRaw.trackingCheck out = true := by
  have ht := (SourceTrackingRaw.trackingCheck_exact word).mp hw
  have hhead := ht.2.1.nodes head hh
  have hroot := (SourceTrackingRaw.Support.rootCode_spec head hhead).2.1
  have he := raisedBase_eq_alphaCode head hhead
  have hne : stripLast word ≠ [] := by
    intro hnil
    rw [hnil] at hh
    exact List.not_mem_nil hh
  have hend := EndpointSupport.tracking_final_lt_endpoints word hw hne head hh
  obtain ⟨raised, hr, rfl⟩ := (Part.mem_map_iff _).mp ho
  have hs := ReplacementSupport.raisedWord_spec head factor raised hhead hf hm hlt hr
  have hrel := Replacement.returnWord_relation head raised
    (fun c hc => (hs.2.2 c hc).1) (fun c hc => (hs.2.2 c hc).2.2)
  have hb : ∀ c ∈ raised, NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) c <
      Enclosure.sourceAlphaPlus (SourceTrackingRaw.Support.rootCode head) := by
    intro c hc
    exact ((hs.2.2 c hc).2.1.trans hfactor).trans_lt hend
  rw [he] at hs hrel hb
  exact tracking_return _ hroot raised _ hs.1 hrel hb

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.ReplacementFidelity
