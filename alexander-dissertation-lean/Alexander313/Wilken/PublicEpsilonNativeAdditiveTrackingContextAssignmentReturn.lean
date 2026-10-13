import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingReplacementFidelity
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingAssignment

/-!
# Genuine original-q return of an arbitrary lower-head RAW assignment

The original checked tracker supplies the actual epsilon head and its own
nested endpoint. The independently executing lower-context assignment
supplies every LOW entry and its actual bound by the lower input. Bounding
that input by the original tracker final value derives every return and
contextual mu caller. The real raw-root parser and finite return relation
then transfer the complete RAW reference and tracker, retaining all VALUES.
No equality with an original-q assignment or branch-composition law follows
from this provenance theorem. Source-only uncompiled candidates.
-/

noncomputable section

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.ContextAssignmentReturn

open PublicEpsilonUnboundedIota
open ReplacementFidelity (SameEntry)
open SourceTrackingSequences (lastCode lastCode_mem lastCode_singleton)
open SkTracking.Support (stripLast_cons_nonempty lastCode_cons_nonempty)
open Hereditary.FinePredecessor (stripLast)

/-- Actual raw-root construction licenses the genuine own-interval mu
theorem without identifying different written source spellings. -/
theorem contextual_raw_entry (q alpha c d : Nat)
    (ha : RootLowCollapse.rootCheck q alpha = true)
    (hc : SourceTrackingRaw.Support.inputCheck (betaCode q alpha) c = true)
    (hd : SameEntry q (betaCode q alpha) c d)
    (hb : interpretation (betaCode q alpha) c < Enclosure.sourceAlphaPlus q alpha) :
    SourceTrackingRaw.Support.inputCheck q d = true ∧
      SourceTrackingRaw.Support.muValue q d =
        SourceTrackingRaw.Support.muValue (betaCode q alpha) c := by
  have hs := SourceTrackingRaw.Support.rootCode_spec (betaCode q alpha) c hc
  have hd' : SameEntry q (betaCode q alpha)
      (SourceTrackingRaw.Support.rootCode (betaCode q alpha) c) d :=
    ⟨hd.1, hd.2.1, hd.2.2.trans hs.2.2.symm⟩
  have hm := ReplacementFidelity.contextual_entry q alpha _ d ha hs.2.1 hd'
    (hs.2.2.trans_lt hb)
  exact ⟨hm.1, hm.2⟩

private theorem context_relation_roots {q r : Nat} {xs ys : List Nat}
    (hrel : List.Forall₂ (SameEntry q r) xs ys)
    (hc : ∀ c ∈ xs, SourceTrackingRaw.Support.inputCheck r c = true) :
    List.Forall₂ (SameEntry q r) (SourceTrackingRaw.Support.rootWord r xs) ys := by
  revert hc
  induction hrel with
  | nil => intro hc; exact .nil
  | @cons c d xs ys hd ht ih =>
    intro hc
    have hs := SourceTrackingRaw.Support.rootCode_spec r c (hc c List.mem_cons_self)
    exact .cons ⟨hd.1, hd.2.1, hd.2.2.trans hs.2.2.symm⟩
      (ih (fun a ha => hc a (List.mem_cons_of_mem _ ha)))

theorem raw_reference_return (q alpha : Nat)
    (ha : RootLowCollapse.rootCheck q alpha = true)
    (xs ys : List Nat) (hr : SourceTrackingRaw.Reference (betaCode q alpha) xs)
    (hrel : List.Forall₂ (SameEntry q (betaCode q alpha)) xs ys)
    (hb : ∀ c ∈ xs, interpretation (betaCode q alpha) c < Enclosure.sourceAlphaPlus q alpha) :
    SourceTrackingRaw.Reference q ys := by
  apply ReplacementFidelity.reference_return q alpha ha _ ys hr.2
    (context_relation_roots hrel hr.1)
  intro c hc
  obtain ⟨a, hm, rfl⟩ := List.mem_map.mp hc
  exact (SourceTrackingRaw.Support.rootCode_spec _ a (hr.1 a hm)).2.2.trans_lt (hb a hm)

private theorem context_relation_prefix {q r : Nat} {xs ys : List Nat}
    (hrel : List.Forall₂ (SameEntry q r) xs ys) :
    List.Forall₂ (SameEntry q r) (stripLast xs) (stripLast ys) := by
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

private theorem context_relation_last {q r : Nat} {xs ys : List Nat}
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
      rw [lastCode_cons_nonempty c xs hx, lastCode_cons_nonempty d ys hy]
      exact ih hx

/-- Both recognizers have genuine RAW domains. Normalization is used only
to derive the reference roots and their actual contextual mu equations. -/
theorem raw_tracking_return (q alpha : Nat)
    (ha : RootLowCollapse.rootCheck q alpha = true)
    (xs ys : List Nat) (hx : SourceTrackingRaw.trackingCheck (betaCode q alpha) xs = true)
    (hrel : List.Forall₂ (SameEntry q (betaCode q alpha)) xs ys)
    (hb : ∀ c ∈ xs, interpretation (betaCode q alpha) c < Enclosure.sourceAlphaPlus q alpha) :
    SourceTrackingRaw.trackingCheck q ys = true := by
  have hs := (SourceTrackingRaw.trackingCheck_conditions _ xs).mp hx
  have hne : ys ≠ [] := by
    intro hy
    have he := hrel.length_eq
    rw [hy, List.length_nil] at he
    exact hs.1 (List.length_eq_zero_iff.mp he)
  have hp := context_relation_prefix hrel
  have hl := context_relation_last hrel hs.1
  have hr := raw_reference_return q alpha ha _ _ hs.2.1 hp (by
    intro c hc
    exact hb c (Hereditary.FinePredecessor.stripLast_mem _ _ hc))
  apply (SourceTrackingRaw.trackingCheck_conditions q ys).mpr
  refine ⟨hne, hr, hl.1, ?_, ?_, ?_⟩
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
      have hm := contextual_raw_entry q alpha (lastCode (stripLast xs)) (lastCode (stripLast ys))
        ha (hs.2.1.nodes _ (lastCode_mem _ he)) (context_relation_last hp he)
        (hb _ (Hereditary.FinePredecessor.stripLast_mem _ _ (lastCode_mem _ he)))
      rw [if_neg hy, hl.2.2, hm.2]
      simpa only [if_neg he] using hs.2.2.2.2.2

/-- Actual lower Assignment bounds derive every own-interval mu caller
for the original partial return of its entire RAW word. -/
theorem assignment_return_spec (q : Nat) (word : List Nat) (head input : Nat) (xs out : List Nat)
    (hw : SourceTrackingRaw.trackingCheck q word = true) (hh : head ∈ stripLast word)
    (ho : xs ∈ Assignment.execute (ReplacementSupport.raisedBaseCode q head) input)
    (hb : interpretation (ReplacementSupport.raisedBaseCode q head) input ≤
      interpretation q (lastCode word))
    (hreturned : out ∈ Replacement.returnWord q (ReplacementSupport.raisedBaseCode q head) xs) :
    SourceTrackingRaw.trackingCheck q out = true ∧
      List.Forall₂ (SameEntry q (ReplacementSupport.raisedBaseCode q head)) xs out ∧
      out.map (interpretation q) = xs.map (interpretation (ReplacementSupport.raisedBaseCode q head)) ∧
      ∀ d ∈ out, lowCheckCode q d = true ∧ Comparison.acceptedCode q d = true := by
  have ht := (SourceTrackingRaw.trackingCheck_conditions q word).mp hw
  have hhead := ht.2.1.nodes head hh
  have hroot := (SourceTrackingRaw.Support.rootCode_spec q head hhead).2.1
  have he := ReplacementFidelity.raisedBase_eq_betaCode q head hhead
  have hne : stripLast word ≠ [] := by
    intro hn
    rw [hn] at hh
    exact List.not_mem_nil hh
  have hend := EndpointSupport.tracking_final_lt_endpoints q word hw hne head hh
  have htrack := Assignment.execute_tracking _ input xs ho
  have hlow := ((SourceTrackingRaw.trackingCheck_exact _ xs).mp htrack).source_domain
  have hall := (Assignment.execute_spec _ input xs ho).2.1.2.1
  have hown : ∀ c ∈ xs, interpretation (ReplacementSupport.raisedBaseCode q head) c <
      Enclosure.sourceAlphaPlus q (SourceTrackingRaw.Support.rootCode q head) := by
    intro c hc
    exact ((hall c hc).trans hb).trans_lt hend
  have hrel := Replacement.returnWord_relation q _ xs out hreturned (fun c hc => (hlow c hc).1)
  have hpair : List.Forall₂ (SameEntry q (ReplacementSupport.raisedBaseCode q head)) xs out := by
    simpa only [Replacement.contextWord, List.forall₂_map_left_iff] using hrel
  have hreturnedTrack := raw_tracking_return q _ hroot xs out
    (by simpa only [he] using htrack) (by simpa only [he] using hpair)
    (by simpa only [he] using hown)
  have hs := Replacement.returnWord_spec q _ xs out hreturned (fun c hc => (hlow c hc).1)
  exact ⟨hreturnedTrack, hpair, hs.2.1, hs.1⟩

/-- Original final LOW admission and actual Assignment ALL bounds derive
termination of every real returning search, without a program fuel bound. -/
theorem assignment_return_returns (q : Nat) (word : List Nat) (head input : Nat) (xs : List Nat)
    (hw : SourceTrackingRaw.trackingCheck q word = true) (hh : head ∈ stripLast word)
    (ho : xs ∈ Assignment.execute (ReplacementSupport.raisedBaseCode q head) input)
    (hb : interpretation (ReplacementSupport.raisedBaseCode q head) input ≤
      interpretation q (lastCode word)) :
    ∃ out, out ∈ Replacement.returnWord q (ReplacementSupport.raisedBaseCode q head) xs ∧
      SourceTrackingRaw.trackingCheck q out = true ∧
      out.map (interpretation q) = xs.map (interpretation (ReplacementSupport.raisedBaseCode q head)) := by
  have ht := (SourceTrackingRaw.trackingCheck_conditions q word).mp hw
  have hq := (HeightBoundary.input_spec q _ ht.2.2.1).2.1
  have hlow := ((SourceTrackingRaw.trackingCheck_exact _ xs).mp
    (Assignment.execute_tracking _ input xs ho)).source_domain
  have hall := (Assignment.execute_spec _ input xs ho).2.1.2.1
  obtain ⟨out, hr⟩ := Replacement.returnWord_returns q _ xs hq (by
    intro c hc
    exact ⟨(hlow c hc).1, ((hall c hc).trans hb).trans_lt
      (checked_low_bound q _ ht.2.2.1)⟩)
  have hs := assignment_return_spec q word head input xs out hw hh ho hb hr
  exact ⟨out, hr, hs.1, hs.2.2.1⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.ContextAssignmentReturn
