import Alexander313.Wilken.HereditaryEvaluationSourceOneFinalHeight

/-!
# Complete actual source-one length word when the proper tail is empty

The genuine maximal segment scan, its literal zero index and empty proper
tail derive the actual initial previous code. The actual component graph
then contains only the independently executing final component. Its original
LOW target height bounds the optional second-factor append and hence the
entire positive chronological length word. This covers arbitrary final
principals strictly below the first grammar ceiling. Positive segments,
the genuine grammar ceiling and recursive evaluation descent are separate.
Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationSourceOneEmptyTailLength

open GlobalTrackingSequences EvaluationComponents.Support
open Hereditary.FinePredecessor (stripLast)
open NativeContext.SourceTrackingSequences (lastCode)
open EvaluationSourceOneFinalHeightSupport (sourceHeight)

theorem previous_code (codes : List Nat) (ht : Tracking codes)
    (hn : properTail codes = []) (hm : segmentIndex (stripLast codes) = 0) :
    EvaluationFinalComponent.previousCode codes = endpointCode 0 := by
  have hs := tracking_segment codes ht
  have he : stripLast codes = [] := by
    simpa only [hm, hn, GlobalAdditiveTracking.Source.baseWord, List.range_zero,
      List.map_nil, List.append_nil] using hs.1
  simp only [EvaluationFinalComponent.previousCode, he, List.isEmpty_nil, Bool.cond_true]

theorem execute_component_bounds (codes : List Nat) (out : List EvaluationBlocks.Block)
    (ho : out ∈ EvaluationComponents.execute codes)
    (hn : properTail codes = []) (hm : segmentIndex (stripLast codes) = 0)
    (hb : unionInterpretation (lastCode codes) < finiteBase 1) :
    out.length ≤ sourceHeight (lastCode codes) + 1 ∧
      ∀ word ∈ out, word.length ≤ sourceHeight (lastCode codes) + 1 := by
  obtain ⟨ht, words, final, ha, hf, hout⟩ := (EvaluationComponents.execute_graph codes out).mp ho
  have he := previous_code codes ht hn hm
  have hfinal : final ∈ EvaluationFinalComponent.execute (endpointCode 0) (lastCode codes) := by
    simpa only [EvaluationComponents.finalExecute, he] using hf
  have hlen := EvaluationSourceOneFinalHeight.execute_length_bound _ final hfinal hb
  rw [hn] at ha
  cases ha
  have hout : out = [final] := by simpa only [List.nil_append] using hout
  rw [hout]
  refine ⟨?_, ?_⟩
  · simp only [List.length_singleton]; omega
  · intro word hw
    rw [List.mem_singleton.mp hw]
    exact hlen

theorem executeLengths_bounded (codes ns : List Nat)
    (ho : ns ∈ EvaluationComponents.executeLengths codes)
    (hn : properTail codes = []) (hm : segmentIndex (stripLast codes) = 0)
    (hb : unionInterpretation (lastCode codes) < finiteBase 1) :
    ns.length ≤ sourceHeight (lastCode codes) + 1 ∧
      ∀ n ∈ ns, 0 < n ∧ n ≤ sourceHeight (lastCode codes) + 1 := by
  obtain ⟨words, hw, he⟩ := (EvaluationComponents.executeLengths_graph codes ns).mp ho
  have hlength := execute_component_bounds codes words hw hn hm hb
  have hpositive := (EvaluationComponents.executeLengths_spec codes ns ho).2
  refine ⟨?_, ?_⟩
  · rw [← he, EvaluationBlocks.lengths, List.length_map]
    exact hlength.1
  · intro n hmem
    have hh := hmem
    rw [← he, EvaluationBlocks.lengths] at hh
    obtain ⟨word, hword, rfl⟩ := List.mem_map.mp hh
    exact ⟨hpositive _ hmem, hlength.2 word hword⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationSourceOneEmptyTailLength
