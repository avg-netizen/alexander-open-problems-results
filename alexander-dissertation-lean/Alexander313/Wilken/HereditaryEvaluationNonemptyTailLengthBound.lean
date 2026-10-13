import Alexander313.Wilken.HereditaryEvaluationFinalComponentProperLength

/-!
# The complete actual length word is bounded when the proper tail is nonempty

The maximal endpoint scan supplies the genuine proper tail and finite gap.
Its real last entry is the final component's actual previous epsilon, so
the independent global tracker derives the final mu caller and the previous
height bound. All real proper components and the optional final append now
obey the common computed initial height plus one, as does their count.
The actual chronological length program therefore belongs to the printed
finite bounded alphabet on this nonempty-tail domain. The empty-tail height
adapter and recursive lexical descent remain separate. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationNonemptyTailLengthBound

open GlobalTrackingSequences
open EvaluationComponents.Support
open EvaluationInitialReferenceHeight
open Hereditary.FinePredecessor (stripLast)
open NativeContext.SourceTrackingSequences (lastCode lastCode_mem)
open NativeContext.SourceAdditiveTracking.Insertion (firstCode)

theorem previous_data (codes : List Nat) (ht : Tracking codes) (first : Nat) (rest : List Nat)
    (hfirst : properTail codes = first :: rest) :
    MuPublicDictionary.Support.inputCheck (EvaluationFinalComponent.previousCode codes) = true ∧
      TailGap (segmentIndex (stripLast codes)) [EvaluationFinalComponent.previousCode codes] ∧
        initialHeight (EvaluationFinalComponent.previousCode codes) ≤ initialHeight first := by
  have hs := tracking_segment codes ht
  rw [hfirst] at hs
  have hp := SmallHSupport.epsilonReference_in_gap _ (first :: rest) hs.2.1 hs.2.2
  have hm := lastCode_mem (first :: rest) (List.cons_ne_nil _ _)
  have hstrip : stripLast codes ≠ [] := by
    intro he
    have hc : lastCode (first :: rest) ∈ stripLast codes := by
      rw [hs.1]
      exact List.mem_append.mpr (Or.inr hm)
    rw [he] at hc
    exact List.not_mem_nil hc
  have hb : (stripLast codes).isEmpty = false := List.isEmpty_eq_false_iff.mpr hstrip
  have he : EvaluationFinalComponent.previousCode codes = lastCode (first :: rest) := by
    rw [EvaluationFinalComponent.previousCode, hb, Bool.cond_false, hs.1]
    exact AssignmentSupport.lastCode_append_nonempty _ _ (List.cons_ne_nil _ _)
  rw [he]
  exact ⟨hp.1.nodes _ hm, (hp.2 _ hm).1,
    EvaluationInitialHeightCoveredMonotonicity.global_tail_height_bound _ first rest hs.2.1 hs.2.2 _ hm⟩

theorem final_length_bound (codes : List Nat) (ht : Tracking codes) (first : Nat) (rest : List Nat)
    (hfirst : properTail codes = first :: rest) (final : List Nat)
    (hf : final ∈ EvaluationComponents.finalExecute codes) :
    final.length ≤ initialHeight first + 1 := by
  have hp := previous_data codes ht first rest hfirst
  have hs := tracking_segment codes ht
  have hstrip : stripLast codes ≠ [] := by
    intro he
    rw [he] at hs
    have hn := (List.append_eq_nil_iff.mp hs.1.symm).2
    rw [hfirst] at hn
    exact List.cons_ne_nil _ _ hn
  have hb : (stripLast codes).isEmpty = false := List.isEmpty_eq_false_iff.mpr hstrip
  have he : EvaluationFinalComponent.previousCode codes = lastCode (stripLast codes) := by
    simp only [EvaluationFinalComponent.previousCode, hb, Bool.cond_false]
  have hcover : unionInterpretation (EvaluationFinalComponent.previousCode codes) <
      unionInterpretation (lastCode codes) →
        EvaluationRelativeCallers.blockInputCheck (EvaluationFinalComponent.previousCode codes) (lastCode codes) = true := by
    intro hgt
    simpa only [he] using EvaluationRelativeCallers.tracking_final_caller codes ht hstrip
      (by simpa only [he] using hgt.le)
  have hlen := EvaluationFinalComponentProperLength.execute_length_le_previous _ _ _ final
    hp.1 hp.2.1 hf hcover
  exact hlen.trans (Nat.add_le_add_right hp.2.2 1)

theorem execute_component_bounds (codes : List Nat) (out : List EvaluationBlocks.Block)
    (ho : out ∈ EvaluationComponents.execute codes) (first : Nat) (rest : List Nat)
    (hfirst : properTail codes = first :: rest) :
    out.length ≤ initialHeight first + 1 ∧
      ∀ word ∈ out, word.length ≤ initialHeight first + 1 := by
  obtain ⟨ht, words, final, ha, hf, hout⟩ := (EvaluationComponents.execute_graph codes out).mp ho
  have hs := tracking_segment codes ht
  rw [hfirst] at hs ha
  have hw := EvaluationProperComponentLengths.global_lengths _ first rest words hs.2.1 hs.2.2 ha
  have hfinal := final_length_bound codes ht first rest hfirst final hf
  have hcount := global_component_count_le _ first rest hs.2.1 hs.2.2
  have hc := EvaluationComponents.execute_count codes out ho
  rw [hfirst] at hc
  refine ⟨hc.le.trans hcount, ?_⟩
  intro word hm
  rw [hout] at hm
  rcases List.mem_append.mp hm with hm | hm
  · exact (hw word hm).trans (Nat.le_add_right _ _)
  · rw [List.mem_singleton.mp hm]; exact hfinal

/-- The sole added domain guard is nonempty actual proper tail. Both the
height and every chronological length are the real computed artifacts. -/
theorem executeLengths_bounded (codes ns : List Nat)
    (ho : ns ∈ EvaluationComponents.executeLengths codes) (hne : properTail codes ≠ []) :
    ns.length ≤ initialHeight (firstCode (properTail codes)) + 1 ∧
      ∀ n ∈ ns, 0 < n ∧ n ≤ initialHeight (firstCode (properTail codes)) + 1 := by
  obtain ⟨first, rest, hfirst⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨words, hw, he⟩ := (EvaluationComponents.executeLengths_graph codes ns).mp ho
  have hb := execute_component_bounds codes words hw first rest hfirst
  have hp := (EvaluationComponents.executeLengths_spec codes ns ho).2
  have hh : firstCode (properTail codes) = first := by
    simp only [hfirst, firstCode, List.head?_cons, Option.getD_some]
  rw [hh]
  refine ⟨?_, ?_⟩
  · rw [← he, EvaluationBlocks.lengths, List.length_map]; exact hb.1
  · intro n hn
    have hm := hn
    rw [← he, EvaluationBlocks.lengths] at hm
    obtain ⟨word, hword, rfl⟩ := List.mem_map.mp hm
    exact ⟨hp _ hn, hb.2 word hword⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationNonemptyTailLengthBound
