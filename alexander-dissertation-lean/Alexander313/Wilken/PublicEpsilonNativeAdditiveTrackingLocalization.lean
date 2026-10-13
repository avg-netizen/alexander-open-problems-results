import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingLocalizationSupport
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingAssignment

/-!
# Genuine localization clause of source Lemma 3.21.4

Every original adjacent mu cover follows from the independently checked
RAW tracker. When the adjacent entries increase, real reference prefix
and endpoint nesting place every earlier epsilon inside its own genuine
successor interval at the current principal. The actual first-crossing
lemma recovers all those values in the current principal's localization;
strict finite order turns membership into a complete VALUE subsequence.
The final principal may be non-epsilon. No support, assigned prefix,
literal-code equality or localization-subsequence premise is supplied.
Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.Localization

open SourceLocalization LocalizationSupport
open Hereditary.FinePredecessor (stripLast)
open SourceTrackingSequences (lastCode lastCode_mem lastCode_append_singleton)

/-- A checked raw tracking cut that increases at its final entry derives
the original final Node and the complete genuine localization subsequence. -/
theorem tracking_prefix_sublist (q : Nat) (word prefix : List Nat) (d : Nat) (after : List Nat)
    (hw : SourceTrackingRaw.trackingCheck q word = true)
    (he : word = prefix ++ d :: after) (hne : prefix ≠ [])
    (hstrict : interpretation q (lastCode prefix) < interpretation q d) :
    RootAdapter.inputCheck q d = true ∧
      interpretation q d ≤ SourceTrackingRaw.Support.muValue q (lastCode prefix) ∧
        ((prefix ++ [d]).map (interpretation q)).Sublist
          ((nativePath q (RootAdapter.rootCode q d)).map (interpretation q)) := by
  have hr := InsertionFidelitySupport.tracking_prefix_reference q word prefix d after hw he
  have hmember : d ∈ word := by rw [he]; exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  have hd := ConditionalReplacement.tracking_member_principal q word hw d hmember
  have hlast := hr.epsilons (lastCode prefix) (lastCode_mem prefix hne)
  have hb : base q ≤ interpretation q d := hlast.2.1.le.trans hstrict.le
  have hi : RootAdapter.inputCheck q d = true :=
    (RootAdapter.inputCheck_exact q d).mpr ⟨hd.1, hb, hd.2.2⟩
  have hs := RootAdapter.rootCode_spec q d hi
  have hroot := RootAdapter.rootInput q d hi
  have hcover := tracking_cut_cover q word prefix d after hw he hne
  have hone : 1 < interpretation q d :=
    (EpsilonOffsets.epsilon_one_lt hlast.2.2.1).trans hstrict
  have hcut := InsertionFidelitySupport.tracking_append_singleton q prefix d hr hne
    hd.1 hd.2.1 hd.2.2 hone hcover
  have hcutne : stripLast (prefix ++ [d]) ≠ [] := by
    simpa only [SourceTrackingSequences.stripLast_append_singleton] using hne
  have hends := EndpointSupport.tracking_final_lt_endpoints q (prefix ++ [d]) hcut hcutne
  have hbelow : ∀ c ∈ prefix, interpretation q c < interpretation q d := fun c hc =>
    (reference_le_last q prefix hr hne c hc).trans_lt hstrict
  have hmem : ∀ c ∈ prefix, interpretation q c ∈
      (nativePath q (RootAdapter.rootCode q d)).map (interpretation q) := by
    intro c hc
    have heps := hr.epsilons c hc
    have hp := EpsilonOffsets.epsilon_pos_principal heps.2.2.1
    have hci : RootAdapter.inputCheck q c = true :=
      (RootAdapter.inputCheck_exact q c).mpr ⟨heps.1, heps.2.1.le, hp.2⟩
    have hcs := RootAdapter.rootCode_spec q c hci
    have hendpoint : value q (RootAdapter.rootCode q d) <
        PublicEpsilonUnboundedIota.Enclosure.sourceAlphaPlus q (RootAdapter.rootCode q c) := by
      have he := hends c (by
        simpa only [SourceTrackingSequences.stripLast_append_singleton] using hc)
      simpa only [lastCode_append_singleton, value, hs.2] using he
    have hm := nativePath_interval_mem q (RootAdapter.rootCode q d) (RootAdapter.rootCode q c)
      hroot hcs.1 (by simpa only [value, hcs.2] using heps.2.1)
      (by simpa only [value, hs.2, hcs.2] using (hbelow c hc).le) hendpoint
    simpa only [value, hcs.2] using hm
  have hend : interpretation q d ∈
      (nativePath q (RootAdapter.rootCode q d)).map (interpretation q) := by
    obtain ⟨tail, ht⟩ := nativePath_head q (RootAdapter.rootCode q d)
    have he := nativePath_end q (RootAdapter.rootCode q d) hroot
    have hm : endpoint (nativePath q (RootAdapter.rootCode q d)) ∈
        nativePath q (RootAdapter.rootCode q d) := by rw [ht]; exact endpoint_mem _ _
    exact List.mem_map.mpr ⟨_, hm, by simpa only [value, hs.2] using he⟩
  have hordered : ((prefix ++ [d]).map (interpretation q)).Pairwise (· < ·) := by
    rw [List.map_append, List.map_singleton]
    apply List.pairwise_append.mpr
    refine ⟨hr.strict, by simp, ?_⟩
    intro a ha b hb
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
    have he : b = interpretation q d := List.mem_singleton.mp hb
    rw [he]
    exact hbelow c hc
  refine ⟨hi, hcover, strict_sublist_of_subset _ _ hordered (nativePath_strict q _ hroot) ?_⟩
  intro a ha
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
  rcases List.mem_append.mp hc with hc | hc
  · exact hmem c hc
  · simpa only [List.mem_singleton.mp hc] using hend

/-- Exact source3.21.4 at every actual adjacent written decomposition.
The real original tracker derives the cover; the increasing case derives
a genuine VALUE subsequence of the original localization at that endpoint. -/
theorem execute_localization (q current : Nat) (out before : List Nat) (a b : Nat) (after : List Nat)
    (ho : out ∈ Assignment.execute q current)
    (he : out = before ++ a :: b :: after) :
    interpretation q b ≤ SourceTrackingRaw.Support.muValue q a ∧
      (interpretation q a < interpretation q b →
        RootAdapter.inputCheck q b = true ∧
          ((before ++ [a, b]).map (interpretation q)).Sublist
            ((nativePath q (RootAdapter.rootCode q b)).map (interpretation q))) := by
  have hw := Assignment.execute_tracking q current out ho
  have hprefix : before ++ [a] ≠ [] := by simp
  have hcut : out = (before ++ [a]) ++ b :: after := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using he
  have hc := tracking_cut_cover q out (before ++ [a]) b after hw hcut hprefix
  refine ⟨by simpa only [lastCode_append_singleton] using hc, ?_⟩
  intro hab
  have ht := tracking_prefix_sublist q out (before ++ [a]) b after hw hcut hprefix
    (by simpa only [lastCode_append_singleton] using hab)
  exact ⟨ht.1, by simpa only [List.append_assoc, List.cons_append, List.nil_append] using ht.2.2⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.Localization
