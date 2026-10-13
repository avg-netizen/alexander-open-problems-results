import Alexander313.Wilken.HereditaryEvaluationPositiveFinalHeight

/-!
# Complete actual positive-endpoint length word with an empty proper tail

The computed segment scan and empty proper tail identify the literal base
word and its actual last endpoint. The genuine component graph has only its
independently executing final component. The computed original positive
source height of the final target bounds the whole positive length word,
including the real optional second-factor append. Strict upper-grammar
admission remains explicit; recursive evaluation descent is separate.
Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationPositiveEmptyTailLength

open GlobalTrackingSequences EvaluationComponents.Support
open Hereditary.FinePredecessor (stripLast)
open NativeContext.SourceTrackingSequences (lastCode)
open EvaluationPositiveFinalHeightSupport (sourceHeight)

theorem previous_code (s : Nat) (codes : List Nat) (ht : Tracking codes)
    (hn : properTail codes = []) (hm : segmentIndex (stripLast codes) = s + 1) :
    EvaluationFinalComponent.previousCode codes = endpointCode (s + 1) := by
  have hs := tracking_segment codes ht
  have he : stripLast codes = GlobalAdditiveTracking.Source.baseWord (s + 1) := by
    simpa only [hm, hn, List.append_nil] using hs.1
  have hne := GlobalTrackingSequences.AssignmentSupport.baseWord_ne_nil (s + 1) (by omega)
  simp only [EvaluationFinalComponent.previousCode, he,
    List.isEmpty_eq_false_iff.mpr hne, Bool.cond_false,
    GlobalTrackingSequences.AssignmentSupport.baseWord_last]

theorem execute_component_bounds (s : Nat) (codes : List Nat) (out : List EvaluationBlocks.Block)
    (ho : out ∈ EvaluationComponents.execute codes)
    (hn : properTail codes = []) (hm : segmentIndex (stripLast codes) = s + 1)
    (hb : unionInterpretation (lastCode codes) < finiteBase ((s + 1) + 1)) :
    out.length ≤ sourceHeight s (lastCode codes) + 1 ∧
      ∀ word ∈ out, word.length ≤ sourceHeight s (lastCode codes) + 1 := by
  obtain ⟨ht, words, final, ha, hf, hout⟩ := (EvaluationComponents.execute_graph codes out).mp ho
  have he := previous_code s codes ht hn hm
  have hfinal : final ∈ EvaluationFinalComponent.execute (endpointCode (s + 1)) (lastCode codes) := by
    simpa only [EvaluationComponents.finalExecute, he] using hf
  have hlen := EvaluationPositiveFinalHeight.execute_length_bound s _ final hfinal hb
  rw [hn] at ha
  cases ha
  have hout : out = [final] := by simpa only [List.nil_append] using hout
  rw [hout]
  refine ⟨?_, ?_⟩
  · simp only [List.length_singleton]; omega
  · intro word hw
    rw [List.mem_singleton.mp hw]
    exact hlen

theorem executeLengths_bounded (s : Nat) (codes ns : List Nat)
    (ho : ns ∈ EvaluationComponents.executeLengths codes)
    (hn : properTail codes = []) (hm : segmentIndex (stripLast codes) = s + 1)
    (hb : unionInterpretation (lastCode codes) < finiteBase ((s + 1) + 1)) :
    ns.length ≤ sourceHeight s (lastCode codes) + 1 ∧
      ∀ n ∈ ns, 0 < n ∧ n ≤ sourceHeight s (lastCode codes) + 1 := by
  obtain ⟨words, hw, he⟩ := (EvaluationComponents.executeLengths_graph codes ns).mp ho
  have hlength := execute_component_bounds s codes words hw hn hm hb
  have hpositive := (EvaluationComponents.executeLengths_spec codes ns ho).2
  refine ⟨?_, ?_⟩
  · rw [← he, EvaluationBlocks.lengths, List.length_map]
    exact hlength.1
  · intro n hmem
    have hh := hmem
    rw [← he, EvaluationBlocks.lengths] at hh
    obtain ⟨word, hword, rfl⟩ := List.mem_map.mp hh
    exact ⟨hpositive _ hmem, hlength.2 word hword⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationPositiveEmptyTailLength
