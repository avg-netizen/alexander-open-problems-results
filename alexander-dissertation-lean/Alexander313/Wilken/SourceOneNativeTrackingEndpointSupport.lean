import Alexander313.Wilken.SourceOneNativeTrackingRaw
import Alexander313.Wilken.SourceOneNativeMuBounds
import Alexander313.Wilken.PublicEpsilonNativeMultiplicativeTracking
import Alexander313.Wilken.SourceCollapseSuccessorIntervals

/-!
# Genuine endpoint nesting in the original source-one dictionary

The original check-zero HIGH roots supply their actual sorted global
arguments. The adjacent-collapse interval theorem keeps each successor
endpoint inside its predecessor's endpoint. Actual original mu is below
that own endpoint. Induction on the real RAW reference recurrence therefore
bounds a covered final tracking value by every preceding root's endpoint.
The original source base is one; no Native base-one parser is used.
These statements concern checked words, not a tracking assignment. Uncompiled.
-/

noncomputable section

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.EndpointSupport

open NativeContext.SourceTrackingSequences (lastCode)

theorem argument_spec (root : Nat) (ha : rootCheck root = true) :
    GlobalNotation (finiteBase 0) 1 (interpretation 0 (Lambda.argumentCode root)) ∧
      interpretation 0 (Lambda.argumentCode root) < omegaSequence (finiteBase 0) 2 ∧
      interpretation 0 root = globalCollapse (finiteBase 0) 0
        (interpretation 0 (Lambda.argumentCode root)) := by
  obtain ⟨t, he, ht, hn, hh⟩ := (rootCheck_exact root).mp ha
  have hc := SourceFixedPoint.checked_theta_argument 0 0 t ht
  refine ⟨?_, ?_, ?_⟩
  · simpa only [OmegaQuotient.argumentCode, he, Localization.argumentCode_theta,
      interpretation_code] using SourceFixedPoint.checked_notation_at 0 t hc 1
  · simpa only [OmegaQuotient.argumentCode, he, Localization.argumentCode_theta,
      interpretation_code] using SourceFixedPoint.checked_theta_sort 0 0 t ht
  · simpa only [OmegaQuotient.argumentCode, he, Localization.argumentCode_theta,
      interpretation_code] using
      (rfl : denote 0 (.theta 0 t) = globalCollapse (finiteBase 0) 0 (denote 0 t))

theorem mu_lt_endpoint (root : Nat) (ha : Mu.inputCheck root = true) :
    Mu.sourceValue root < Enclosure.sourceAlphaPlus root := by
  have hs := Mu.Bounds.muCode_lt_source_alphaPlus root ha
  rw [(Mu.muCode_spec root ha).2.2] at hs
  exact hs

theorem endpoint_nested (alpha beta : Nat)
    (ha : rootCheck alpha = true) (hb : rootCheck beta = true)
    (hlt : interpretation 0 alpha < interpretation 0 beta)
    (hbound : interpretation 0 beta < Enclosure.sourceAlphaPlus alpha) :
    Enclosure.sourceAlphaPlus beta < Enclosure.sourceAlphaPlus alpha := by
  have hA := argument_spec alpha ha
  have hB := argument_spec beta hb
  let a : GlobalNotationOrdinal (finiteBase 0) 1 :=
    ⟨interpretation 0 (Lambda.argumentCode alpha), hA.1⟩
  let b : GlobalNotationOrdinal (finiteBase 0) 1 :=
    ⟨interpretation 0 (Lambda.argumentCode beta), hB.1⟩
  have hab : globalCollapse (finiteBase 0) 0 a.val <
      globalCollapse (finiteBase 0) 0 b.val := by
    simpa only [a, b, ← hA.2.2, ← hB.2.2] using hlt
  have hbs : globalCollapse (finiteBase 0) 0 b.val <
      globalCollapse (finiteBase 0) 0 (a.val + 1) := by
    simpa only [a, b, ← hB.2.2, Enclosure.sourceAlphaPlus] using hbound
  have hs := SourceCollapseSuccessorIntervals.global_adjacent_successor_lt_endpoint
    (finiteBase 0) (finiteBase_pos 0) 0 a b hA.2.1 hB.2.1 hab hbs
  simpa only [a, b, Enclosure.sourceAlphaPlus] using hs

theorem raw_mu_lt_endpoint (c : Nat)
    (hc : SourceTrackingRaw.Support.inputCheck c = true) :
    SourceTrackingRaw.Support.muValue c <
      Enclosure.sourceAlphaPlus (SourceTrackingRaw.Support.rootCode c) :=
  mu_lt_endpoint _ (SourceTrackingRaw.Support.rootCode_spec c hc).2.1

theorem raw_endpoint_nested (a b : Nat)
    (ha : SourceTrackingRaw.Support.inputCheck a = true)
    (hb : SourceTrackingRaw.Support.inputCheck b = true)
    (hlt : interpretation 0 a < interpretation 0 b)
    (hbound : interpretation 0 b <
      Enclosure.sourceAlphaPlus (SourceTrackingRaw.Support.rootCode a)) :
    Enclosure.sourceAlphaPlus (SourceTrackingRaw.Support.rootCode b) <
      Enclosure.sourceAlphaPlus (SourceTrackingRaw.Support.rootCode a) := by
  have hA := SourceTrackingRaw.Support.rootCode_spec a ha
  have hB := SourceTrackingRaw.Support.rootCode_spec b hb
  exact endpoint_nested _ _ hA.2.1 hB.2.1
    (by rw [hA.2.2, hB.2.2]; exact hlt)
    (by rw [hB.2.2]; exact hbound)

theorem reference_cover_endpoints (xs : List Nat)
    (hr : SourceTrackingRaw.Reference xs) (hne : xs ≠ []) (xi : Ordinal.{0})
    (hcover : xi ≤ SourceTrackingRaw.Support.muValue (lastCode xs)) :
    ∀ c ∈ xs, xi < Enclosure.sourceAlphaPlus (SourceTrackingRaw.Support.rootCode c) := by
  revert hne xi
  induction hr with
  | nil => intro hne; exact False.elim (hne rfl)
  | one a ha =>
    intro hne xi hcover c hc
    have he : c = a := List.mem_singleton.mp hc
    subst c
    have hle : xi ≤ SourceTrackingRaw.Support.muValue a := by
      simpa only [lastCode, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.head?_cons, Option.getD_some] using hcover
    exact hle.trans_lt (raw_mu_lt_endpoint a ha)
  | cons a b xs ha hab hcovered tail ih =>
    intro hne xi hcover c hc
    have htail : xi ≤ SourceTrackingRaw.Support.muValue (lastCode (b :: xs)) := by
      simpa only [NativeContext.SourceMultiplicativeTracking.lastCode_cons_nonempty
        a (b :: xs) (by simp)] using hcover
    have hbelow := ih (by simp) xi htail
    rcases List.mem_cons.mp hc with rfl | hc
    · have hb := tail.first
      have hn := raw_endpoint_nested a b ha hb hab
        (hcovered.trans_lt (raw_mu_lt_endpoint a ha))
      exact (hbelow b List.mem_cons_self).trans hn
    · exact hbelow c hc

/-- The real final covering clause supplies every original own-endpoint
bound needed by a contextual return along the proper RAW epsilon prefix. -/
theorem tracking_final_lt_endpoints (word : List Nat)
    (hw : SourceTrackingRaw.trackingCheck word = true)
    (hne : Hereditary.FinePredecessor.stripLast word ≠ []) :
    ∀ c ∈ Hereditary.FinePredecessor.stripLast word,
      interpretation 0 (lastCode word) <
        Enclosure.sourceAlphaPlus (SourceTrackingRaw.Support.rootCode c) := by
  have ht := (SourceTrackingRaw.trackingCheck_exact word).mp hw
  have hfinal := ht.2.2.2.2.2
  rw [if_neg hne] at hfinal
  exact reference_cover_endpoints _ ht.2.1 hne _ hfinal.2

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.EndpointSupport
