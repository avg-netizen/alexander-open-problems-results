import Alexander313.Wilken.PublicEpsilonNativeTrackingRaw
import Alexander313.Wilken.PublicEpsilonNativeMultiplicativeTracking
import Alexander313.Wilken.PublicEpsilonNativeUnboundedMuSuccessorIntervals
import Alexander313.Wilken.SourceCollapseSuccessorIntervals

/-!
# Genuine nested original endpoints of a tracking reference prefix

The original adjacent-collapse interval theorem bounds the true argument
successor of every HIGH root in that interval. Actual mu outputs lie below
their own original successor endpoint. Induction on the real reference
recurrence therefore bounds its covered final value by EVERY preceding
epsilon root's endpoint. This supplies the contextual mu caller needed
for raised replacements, rather than assuming their interval membership.
No endpoint, covering or assigned tracking word is supplied as an oracle.
The statements concern already checked tracking words. Uncompiled.
-/

noncomputable section

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.EndpointSupport

open PublicEpsilonUnboundedIota
open SourceTrackingSequences

theorem mu_lt_endpoint (q root : Nat) (ha : Mu.inputCheck q root = true) :
    Mu.sourceValue q root < Enclosure.sourceAlphaPlus q root := by
  have hs := Mu.SuccessorIntervals.muCode_lt_sourceAlphaPlus q root ha
  rwa [(Mu.muCode_spec q root ha).2.2] at hs

/-- The actual original-source adjacent interval is closed under the true
argument-successor endpoint. Both sorted notation callers are derived. -/
theorem endpoint_nested (q alpha beta : Nat)
    (ha : RootLowCollapse.rootCheck q alpha = true)
    (hb : RootLowCollapse.rootCheck q beta = true)
    (hlt : interpretation q alpha < interpretation q beta)
    (hbound : interpretation q beta < Enclosure.sourceAlphaPlus q alpha) :
    Enclosure.sourceAlphaPlus q beta < Enclosure.sourceAlphaPlus q alpha := by
  let a : GlobalNotationOrdinal (base q) 1 :=
    ⟨interpretation q (RootEndpointCollapse.argumentCode alpha),
      RootEndpointCollapse.argument_notation q alpha ha⟩
  let b : GlobalNotationOrdinal (base q) 1 :=
    ⟨interpretation q (RootEndpointCollapse.argumentCode beta),
      RootEndpointCollapse.argument_notation q beta hb⟩
  have hq := (HeightBoundary.input_spec q alpha (RootLowCollapse.root_low q alpha ha)).2.1
  have hab : globalCollapse (base q) 0 a.val < globalCollapse (base q) 0 b.val := by
    simpa only [a, b, ← RootEndpointCollapse.root_value q alpha ha,
      ← RootEndpointCollapse.root_value q beta hb] using hlt
  have hbs : globalCollapse (base q) 0 b.val < globalCollapse (base q) 0 (a.val + 1) := by
    simpa only [a, b, ← RootEndpointCollapse.root_value q beta hb,
      Enclosure.sourceAlphaPlus, RootEndpointCollapse.argumentCode] using hbound
  have hs := SourceCollapseSuccessorIntervals.global_adjacent_successor_lt_endpoint
    (base q) (base_pos q hq) 0 a b
    (RootEndpointCollapse.argument_sorted q alpha ha)
    (RootEndpointCollapse.argument_sorted q beta hb) hab hbs
  simpa only [a, b, Enclosure.sourceAlphaPlus, RootEndpointCollapse.argumentCode] using hs

/-- A value covered by the final reference root lies below the own original
endpoint of every earlier reference root, with the nested callers derived
from the real adjacent mu inequalities. -/
theorem reference_cover_endpoints (q : Nat) (xs : List Nat)
    (hr : Reference q xs) (hne : xs ≠ []) (xi : Ordinal.{0})
    (hcover : xi ≤ Mu.sourceValue q (lastCode xs)) :
    ∀ c ∈ xs, xi < Enclosure.sourceAlphaPlus q c := by
  revert hne xi
  induction hr with
  | nil => intro hne; exact False.elim (hne rfl)
  | one a ha =>
    intro hne xi hcover c hc
    have he : c = a := List.mem_singleton.mp hc
    subst c
    have hle : xi ≤ Mu.sourceValue q a := by
      simpa only [lastCode, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.head?_cons, Option.getD_some] using hcover
    exact hle.trans_lt (mu_lt_endpoint q a ha)
  | cons a b xs ha hab hcovered tail ih =>
    intro hne xi hcover c hc
    have htail : xi ≤ Mu.sourceValue q (lastCode (b :: xs)) := by
      simpa only [SourceMultiplicativeTracking.lastCode_cons_nonempty a (b :: xs)
        (by simp)] using hcover
    have hbelow := ih (by simp) xi htail
    rcases List.mem_cons.mp hc with rfl | hc
    · have hb := tail.first
      have hn := endpoint_nested q a b ha hb hab
        (hcovered.trans_lt (mu_lt_endpoint q a ha))
      exact (hbelow b List.mem_cons_self).trans hn
    · exact hbelow c hc

/-- Every proper raw epsilon prefix bounds the original final headword
value by its genuine own endpoint. All literal root atoms are constructed
by the checked raw reference parser. -/
theorem tracking_final_lt_endpoints (q : Nat) (word : List Nat)
    (hw : SourceTrackingRaw.trackingCheck q word = true)
    (hne : Hereditary.FinePredecessor.stripLast word ≠ []) :
    ∀ c ∈ Hereditary.FinePredecessor.stripLast word,
      interpretation q (lastCode word) <
        Enclosure.sourceAlphaPlus q (SourceTrackingRaw.Support.rootCode q c) := by
  have ht := (SourceTrackingRaw.trackingCheck_exact q word).mp hw
  have hr := (SourceTrackingRaw.referenceCheck_exact q _).mp
    (SourceTrackingRaw.tracking_erasure q word hw)
  have hfinal := ht.final_conditions
  rw [if_neg hne] at hfinal
  have hrootne := SourceTrackingRaw.rootWord_ne_nil q _ hne
  have hc : interpretation q (lastCode word) ≤ Mu.sourceValue q
      (lastCode (SourceTrackingRaw.Support.rootWord q (Hereditary.FinePredecessor.stripLast word))) := by
    rw [SourceTrackingRaw.rootWord_lastCode q _ hne]
    exact hfinal.2.2.2.2
  have hs := reference_cover_endpoints q _ hr.2 hrootne _ hc
  intro c hm
  exact hs _ (List.mem_map.mpr ⟨c, hm, rfl⟩)

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.EndpointSupport
