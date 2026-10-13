import Alexander313.Wilken.SourceOneNativeTrackingEndpointSupport
import Alexander313.Wilken.SourceOneNativeLocalizationRootAdapter
import Alexander313.Wilken.HereditaryLocalizationOrder
import Alexander313.Wilken.SourceCollapseSuccessors
import Mathlib.Data.List.Sort

/-!
# Covered original source-one roots occur on genuine localization paths

The actual checked source-zero arguments satisfy the adjacent-collapse
interval theorem. A localization step that skipped a covered root would
therefore make its argument both smaller and larger than the selected
argument. First-crossing induction recovers the root's value on the actual
path, even if its written spelling is absent from the original support.
Own-endpoint bounds come from the real RAW mu-cover recurrence. Strictly
ordered value lists then give a genuine subsequence. No Native base-one
parser, support membership or localization equation is assumed. Uncompiled.
-/

noncomputable section

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.LocalizationSupport

open Localization Localization.Refinements Localization.OrderSupport
open NativeContext.SourceTrackingSequences (lastCode lastCode_append_singleton)

/-- Every actual original checked theta-zero node supplies its sorted
global argument, including non-epsilon final principals. -/
theorem node_argument_spec (c : Nat) (hc : Localization.Node 0 c) :
    GlobalNotation (finiteBase 0) 1 (Localization.argumentValue 0 c) ∧
      Localization.argumentValue 0 c < omegaSequence (finiteBase 0) 2 ∧
      Localization.value 0 c = globalCollapse (finiteBase 0) 0
        (Localization.argumentValue 0 c) := by
  obtain ⟨a, rfl, ha, hn⟩ := hc
  have hac := SourceFixedPoint.checked_theta_argument 0 0 a ha
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Localization.argumentValue, Localization.argumentCode_theta,
      interpretation_code] using SourceFixedPoint.checked_notation_at 0 a hac 1
  · simpa only [Localization.argumentValue, Localization.argumentCode_theta,
      interpretation_code] using SourceFixedPoint.checked_theta_sort 0 0 a ha
  · simpa only [Localization.value, Localization.argumentValue,
      Localization.argumentCode_theta, interpretation_code] using
      (rfl : denote 0 (.theta 0 a) = globalCollapse (finiteBase 0) 0 (denote 0 a))

/-- The genuine adjacent interval reverses the arguments of any two
original checked nodes strictly between a root and its own successor. -/
theorem argument_lt_of_adjacent (a b : Nat) (ha : rootCheck a = true)
    (hb : Localization.Node 0 b)
    (hlt : Localization.value 0 a < Localization.value 0 b)
    (hbound : Localization.value 0 b < Enclosure.sourceAlphaPlus a) :
    Localization.argumentValue 0 b < Localization.argumentValue 0 a := by
  obtain ⟨t, he, ht, hn, hh⟩ := (rootCheck_exact a).mp ha
  have han : Localization.Node 0 a := ⟨t, he, ht, hn⟩
  have hA := node_argument_spec a han
  have hB := node_argument_spec b hb
  let A : GlobalNotationOrdinal (finiteBase 0) 1 :=
    ⟨Localization.argumentValue 0 a, hA.1⟩
  let B : GlobalNotationOrdinal (finiteBase 0) 1 :=
    ⟨Localization.argumentValue 0 b, hB.1⟩
  have hab : globalCollapse (finiteBase 0) 0 A.val < globalCollapse (finiteBase 0) 0 B.val := by
    exact hA.2.2.symm.trans_lt (hlt.trans_eq hB.2.2)
  have hbs : globalCollapse (finiteBase 0) 0 B.val <
      globalCollapse (finiteBase 0) 0 (A.val + 1) := by
    calc
      globalCollapse (finiteBase 0) 0 B.val = Localization.value 0 b := hB.2.2.symm
      _ < Enclosure.sourceAlphaPlus a := hbound
      _ = globalCollapse (finiteBase 0) 0 (A.val + 1) := rfl
  exact SourceCollapseSuccessors.global_adjacent_argument_lt
    (finiteBase 0) (finiteBase_pos 0) 0 A B hA.2.1 hB.2.1 hab hbs

/-- A true localization path cannot cross a covered original HIGH root
without containing its value. No literal support membership is required. -/
theorem covered_value_on_path {root a current : Nat} {tail : List Nat}
    (hr : Localization.Node 0 root) (ha : rootCheck a = true)
    (hp : Localization.SourcePath 0 (Localization.support root) (current :: tail))
    (hstart : Localization.value 0 current < Localization.value 0 a)
    (hle : Localization.value 0 a ≤ Localization.value 0 (Localization.endpoint (current :: tail)))
    (hbound : Localization.value 0 (Localization.endpoint (current :: tail)) <
      Enclosure.sourceAlphaPlus a) :
    ∃ d ∈ tail, Localization.value 0 d = Localization.value 0 a := by
  obtain ⟨t, he, ht, hn, hh⟩ := (rootCheck_exact a).mp ha
  have han : Localization.Node 0 a := ⟨t, he, ht, hn⟩
  revert hstart hle hbound
  induction hp with
  | stop c hc hmax =>
    intro hstart hle hbound
    exact False.elim (hstart.not_ge (by simpa only [Localization.endpoint] using hle))
  | next c d tail hc hcd hds harg hrest ih =>
    intro hstart hle hbound
    rcases lt_trichotomy (Localization.value 0 d) (Localization.value 0 a) with hda | heq | had
    · obtain ⟨e, hem, hev⟩ := ih hda
        (by simpa only [Localization.endpoint] using hle)
        (by simpa only [Localization.endpoint] using hbound)
      exact ⟨e, List.mem_cons_of_mem _ hem, hev⟩
    · exact ⟨d, List.mem_cons_self, heq⟩
    · have hpfull := Localization.SourcePath.next c d tail hc hcd hds harg hrest
      have hd := hrest.nodes d List.mem_cons_self
      have hforward := Localization.Refinements.sourcePath_interval_argument_lt
        hr hpfull a han hstart had
      have hbelow : Localization.value 0 d < Enclosure.sourceAlphaPlus a :=
        (hrest.le_endpoint d List.mem_cons_self).trans_lt
          (by simpa only [Localization.endpoint] using hbound)
      have hreverse := argument_lt_of_adjacent a d ha hd had hbelow
      exact False.elim (lt_asymm hforward hreverse)

/-- Membership in two strict ordinal orders is enough to determine an
actual subsequence, with no equality of underlying code spellings. -/
theorem strict_values_sublist (xs ys : List Ordinal.{0})
    (hx : xs.Pairwise (· < ·)) (hy : ys.Pairwise (· < ·))
    (hmem : ∀ x ∈ xs, x ∈ ys) : xs.Sublist ys := by
  have hp : List.Subperm xs ys := List.subperm_of_subset hx.nodup hmem
  exact List.sublist_of_subperm_of_pairwise (r := (· ≤ ·)) hp
    (hx.imp (fun {_ _} h => h.le)) (hy.imp (fun {_ _} h => h.le))

/-- A real strictly increasing RAW mu-covered word is a VALUE
subsequence of its final principal's independently computed localization. -/
theorem reference_localization_subsequence (before : List Nat) (current : Nat)
    (hr : SourceTrackingRaw.Reference before) (hne : before ≠ [])
    (hc : SourceLocalization.RootAdapter.inputCheck current = true)
    (hcover : interpretation 0 current ≤ SourceTrackingRaw.Support.muValue (lastCode before))
    (hstrict : ((before ++ [current]).map (interpretation 0)).Pairwise (· < ·)) :
    ((before ++ [current]).map (interpretation 0)).Sublist
      ((Localization.nativePath 0 (SourceLocalization.RootAdapter.rootCode current)).map
        (Localization.value 0)) := by
  let root := SourceLocalization.RootAdapter.rootCode current
  have hroot := (SourceLocalization.RootAdapter.rootCode_spec current hc).1
  have hi := SourceLocalization.RootAdapter.rootInput current hc
  have hend := SourceLocalization.RootAdapter.localization_endpoint_value current hc
  have hp := Localization.nativePath_source 0 root hi
  have hs := Localization.nativePath_strict 0 root hi
  have hb := EndpointSupport.reference_cover_endpoints before hr hne
    (interpretation 0 current) hcover
  have hcross := List.pairwise_append.mp (show
    (before.map (interpretation 0) ++ [interpretation 0 current]).Pairwise (· < ·) from
    by simpa only [List.map_append, List.map_singleton] using hstrict)
  obtain ⟨tail, hhead⟩ := Localization.nativePath_head 0 root
  have hphead : Localization.SourcePath 0 (Localization.support root) (Localization.baseRaw 0 :: tail) := by
    rw [← hhead]
    exact hp
  have hmem : ∀ v ∈ (before ++ [current]).map (interpretation 0),
      v ∈ (Localization.nativePath 0 root).map (Localization.value 0) := by
    intro v hv
    obtain ⟨c, hm, rfl⟩ := List.mem_map.mp hv
    rcases List.mem_append.mp hm with hm | hm
    · have hraw := SourceTrackingRaw.Support.rootCode_spec c (hr.nodes c hm)
      have ha := hraw.2.1
      have hval := hraw.2.2
      have hstart : Localization.value 0 (Localization.baseRaw 0) <
          Localization.value 0 (SourceTrackingRaw.Support.rootCode c) := by
        rw [Localization.baseRaw_value]
        change finiteBase 0 < interpretation 0 (SourceTrackingRaw.Support.rootCode c)
        rw [finiteBase_zero, hval]
        exact (hr.epsilons c hm).2.1
      have hcle : interpretation 0 c ≤ interpretation 0 current :=
        (hcross.2.2 _ (List.mem_map.mpr ⟨c, hm, rfl⟩) _ List.mem_cons_self).le
      have hle : Localization.value 0 (SourceTrackingRaw.Support.rootCode c) ≤
          Localization.value 0 (Localization.endpoint (Localization.baseRaw 0 :: tail)) := by
        rw [← hhead]
        change interpretation 0 (SourceTrackingRaw.Support.rootCode c) ≤ _
        rw [hval, hend]
        exact hcle
      have hbound : Localization.value 0 (Localization.endpoint (Localization.baseRaw 0 :: tail)) <
          Enclosure.sourceAlphaPlus (SourceTrackingRaw.Support.rootCode c) := by
        rw [← hhead, hend]
        exact hb c hm
      obtain ⟨d, hd, he⟩ := covered_value_on_path hroot ha hphead hstart hle hbound
      apply List.mem_map.mpr
      refine ⟨d, ?_, ?_⟩
      · rw [hhead]
        exact List.mem_cons_of_mem _ hd
      · exact he.trans hval
    · have he : c = current := List.mem_singleton.mp hm
      subst c
      have hm : Localization.endpoint (Localization.nativePath 0 root) ∈
          Localization.nativePath 0 root := by
        rw [hhead]
        exact Localization.endpoint_mem _ _
      exact List.mem_map.mpr ⟨Localization.endpoint (Localization.nativePath 0 root), hm, hend⟩
  exact strict_values_sublist _ _ hstrict hs hmem

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.LocalizationSupport
