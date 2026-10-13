import Alexander313.Wilken.HereditaryGlobalAdditiveTrackingRelativeSupport

/-!
# Independently computed original assignment outputs are public trackers

The actual original RAW condition derives every public return and same-source
mu caller. Concrete public emissions preserve both the reference prefix and
the unchanged original final principal value. The independently defined public
relative Tracking predicate is a conclusion. Global upsilon prefixes and the
endpoint extension of mu are separate. Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.GlobalAdditiveTracking.RelativeCertificate

open NativeContext.SourceTrackingSequences (lastCode lastCode_mem)
open Hereditary.FinePredecessor (stripLast)
open MuPublicDictionary.Agreement (positivePublicCode sourceOnePublicCode)

theorem source_one_tracking (word : List Nat)
    (hw : SourceOneIota.SourceTrackingRaw.trackingCheck word = true) :
    PublicTrackingSequences.Tracking (word.map sourceOnePublicCode) := by
  have ht := (SourceOneIota.SourceTrackingRaw.trackingCheck_exact word).mp hw
  have hl := Return.source_one_word_low word hw
  have hp (c : Nat) (hc : c ∈ word) := SourceOneIota.SourceTrackingRaw.Support.publicCode_spec c (hl c hc)
  have hn : word.map sourceOnePublicCode ≠ [] := fun h => ht.1 (List.map_eq_nil_iff.mp h)
  have hf := hp (lastCode word) (lastCode_mem word ht.1)
  have hlast := lastCode_map sourceOnePublicCode word ht.1
  refine ⟨hn, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    exact (hp d hd).1
  · rw [stripLast_map]
    exact source_one_reference ht.2.1
  · rw [hlast, hf.2]
    exact ht.2.2.2.1
  · rw [hlast, hf.2]
    exact ht.2.2.2.2.1
  · by_cases he : stripLast word = []
    · have hem : stripLast (word.map sourceOnePublicCode) = [] := by
        rw [stripLast_map, he, List.map_nil]
      rw [if_pos hem, hlast, hf.2]
      simpa only [if_pos he] using ht.2.2.2.2.2
    · have hem : stripLast (word.map sourceOnePublicCode) ≠ [] := by
        rw [stripLast_map]
        exact fun h => he (List.map_eq_nil_iff.mp h)
      have hg := ht.2.1.nodes _ (lastCode_mem (stripLast word) he)
      have hbound : 1 < interpretation 0 (lastCode word) ∧
          interpretation 0 (lastCode word) ≤ SourceOneIota.SourceTrackingRaw.Support.muValue (lastCode (stripLast word)) := by
        simpa only [if_neg he] using ht.2.2.2.2.2
      rw [if_neg hem, hlast, hf.2, stripLast_map, lastCode_map sourceOnePublicCode _ he]
      exact ⟨hbound.1, by simpa only [SkPublicRecurrence.muValue,
        MuPublicDictionary.Agreement.source_one_public_mu _ hg] using hbound.2⟩

theorem native_tracking (s : Nat) (word : List Nat)
    (hw : NativeContext.SourceTrackingRaw.trackingCheck (NativePublicBridge.contextCode s) word = true) :
    PublicTrackingSequences.Tracking (word.map (positivePublicCode s)) := by
  let q := NativePublicBridge.contextCode s
  have ht := (NativeContext.SourceTrackingRaw.trackingCheck_conditions q word).mp hw
  have hl := Return.native_word_low q word hw
  have hp (c : Nat) (hc : c ∈ word) := NativeContext.UniformPublicReturn.publicCode_spec q c
    ((NativeContext.UniformPublicReturn.inputCheck_exact q c).mpr (hl c hc))
  have hn : word.map (positivePublicCode s) ≠ [] := fun h => ht.1 (List.map_eq_nil_iff.mp h)
  have hf := hp (lastCode word) (lastCode_mem word ht.1)
  have hlast := lastCode_map (positivePublicCode s) word ht.1
  refine ⟨hn, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    exact (hp d hd).1
  · rw [stripLast_map]
    exact native_reference s _ ht.2.1
  · rw [hlast]
    change 0 < unionInterpretation (NativeContext.UniformPublicReturn.publicCode q (lastCode word))
    rw [hf.2]
    exact ht.2.2.2.1
  · rw [hlast]
    change Ordinal.IsPrincipal (· + ·)
      (unionInterpretation (NativeContext.UniformPublicReturn.publicCode q (lastCode word)))
    rw [hf.2]
    exact ht.2.2.2.2.1
  · by_cases he : stripLast word = []
    · have hem : stripLast (word.map (positivePublicCode s)) = [] := by
        rw [stripLast_map, he, List.map_nil]
      rw [if_pos hem, hlast]
      change 1 ≤ unionInterpretation (NativeContext.UniformPublicReturn.publicCode q (lastCode word))
      rw [hf.2]
      have hb : NativeContext.base q ≤ NativeContext.interpretation q (lastCode word) := by
        simpa only [if_pos he] using ht.2.2.2.2.2
      exact (Order.one_le_iff_pos.mpr
        (NativeContext.base_pos q (NativePublicBridge.contextCode_checked s))).trans hb
    · have hem : stripLast (word.map (positivePublicCode s)) ≠ [] := by
        rw [stripLast_map]
        exact fun h => he (List.map_eq_nil_iff.mp h)
      have hg := ht.2.1.nodes _ (lastCode_mem (stripLast word) he)
      have hbound : 1 < NativeContext.interpretation q (lastCode word) ∧
          NativeContext.interpretation q (lastCode word) ≤
            NativeContext.SourceTrackingRaw.Support.muValue q (lastCode (stripLast word)) := by
        simpa only [if_neg he] using ht.2.2.2.2.2
      rw [if_neg hem, hlast, stripLast_map, lastCode_map (positivePublicCode s) _ he]
      have hmu := MuPublicDictionary.Agreement.positive_public_mu s _ hg
      rw [SkPublicRecurrence.muValue, hmu]
      simpa only [SkPublicDictionary.PositiveAgreement.publicCode, hf.2] using hbound

theorem sourceOneExecute_tracking (alpha : Nat) (codes : List Nat)
    (ho : codes ∈ Return.sourceOneExecute alpha) : PublicTrackingSequences.Tracking codes := by
  obtain ⟨word, hw, rfl⟩ := (Part.mem_map_iff Return.sourceOneWord).mp ho
  exact source_one_tracking word (SourceOneIota.SourceAdditiveTracking.Assignment.execute_tracking _ word hw)

theorem nativeExecute_tracking (alpha : Nat) (codes : List Nat)
    (ho : codes ∈ Return.nativeExecute alpha) : PublicTrackingSequences.Tracking codes := by
  obtain ⟨word, hw, rfl⟩ := (Part.mem_map_iff (Return.nativeWord alpha)).mp ho
  exact native_tracking (Source.sourceIndex alpha) word
    (NativeContext.SourceAdditiveTracking.Assignment.execute_tracking _ _ word hw)

theorem sourceOneExecute_trackingCheck (alpha : Nat) (codes : List Nat)
    (ho : codes ∈ Return.sourceOneExecute alpha) : PublicTrackingSequences.trackingCheck codes = true :=
  (PublicTrackingSequences.trackingCheck_exact _).mpr (sourceOneExecute_tracking alpha codes ho)

theorem nativeExecute_trackingCheck (alpha : Nat) (codes : List Nat)
    (ho : codes ∈ Return.nativeExecute alpha) : PublicTrackingSequences.trackingCheck codes = true :=
  (PublicTrackingSequences.trackingCheck_exact _).mpr (nativeExecute_tracking alpha codes ho)

end Alexander313.Wilken.RelativeTerm.Hereditary.GlobalAdditiveTracking.RelativeCertificate
