import Alexander313.Wilken.HereditaryEvaluationEpsilonComponentIntervals

/-!
# Every genuine proper component obeys the common computed initial height

The actual Assigned graph identifies each literal previous base and target.
An independently defined proper reference in its real finite gap derives
every target's proper admission, gap and initial-height bound. The actual
epsilon-block interval theorem then bounds each whole component by that
common computed height. The concrete evaluation graph supplies all these
premises from global Tracking and the actual maximal initial endpoint scan.
No component length or chosen height list is an input to the global bound.
The final MNF component and recursive lexical descent remain separate.
Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationProperComponentLengths

open GlobalTrackingSequences EvaluationBlocks
open EvaluationInitialReferenceHeight

theorem initial_floor (m : Nat) :
    sourceUpsilon (m : Ordinal.{0}) ≤ unionInterpretation (endpointCode m) := by
  cases m with
  | zero =>
    simp only [Nat.cast_zero, sourceUpsilon_zero,
      PublicEpsilonSourceDictionary.endpointCode_value, finiteBase_zero]
    exact bot_le
  | succ n =>
    simp only [PublicEpsilonSourceDictionary.endpointCode_value,
      PublicUpsilonSegment.successor_value]
    exact le_rfl

/-- The explicit target-height bounds in this induction helper are
discharged from the genuine reference in global_lengths below. -/
theorem assigned_lengths (m bound : Nat) {gamma : Nat} {inputs : List Nat}
    {words : List Block} (ha : Assigned gamma inputs words)
    (hfloor : sourceUpsilon (m : Ordinal.{0}) ≤ unionInterpretation gamma)
    (hi : ∀ beta ∈ inputs, MuPublicDictionary.Support.inputCheck beta = true ∧
      TailGap m [beta] ∧ initialHeight beta ≤ bound) :
    ∀ word ∈ words, word.length ≤ bound := by
  revert hfloor hi
  induction ha with
  | nil gamma =>
    intro hfloor hi word hw
    exact False.elim (List.not_mem_nil hw)
  | cons gamma beta rest word words hw ht ih =>
    intro hfloor hi current hc
    have hb := hi beta List.mem_cons_self
    rcases List.mem_cons.mp hc with rfl | hc
    · exact (EvaluationEpsilonComponentIntervals.block_length_le_target m gamma beta word
        hw hb.1 hfloor hb.2.1).trans hb.2.2
    · exact ih hb.2.1.1.le
        (fun a ha => hi a (List.mem_cons_of_mem _ ha)) current hc

theorem global_lengths (m first : Nat) (rest : List Nat) (words : List Block)
    (hr : EpsilonReference (first :: rest)) (hg : TailGap m (first :: rest))
    (ha : Assigned (endpointCode m) (first :: rest) words) :
    ∀ word ∈ words, word.length ≤ initialHeight first := by
  have hp := SmallHSupport.epsilonReference_in_gap m (first :: rest) hr hg
  have hh := EvaluationInitialHeightCoveredMonotonicity.global_tail_height_bound m first rest hr hg
  apply assigned_lengths m (initialHeight first) ha (initial_floor m)
  intro beta hb
  exact ⟨hp.1.nodes beta hb, (hp.2 beta hb).1, hh beta hb⟩

/-- Actual evaluation execution supplies the genuine chronological words,
true source gap and literal first proper epsilon. -/
theorem execute_proper_lengths (codes : List Nat) (out : List Block)
    (ho : out ∈ EvaluationComponents.execute codes) (first : Nat) (rest : List Nat)
    (hfirst : EvaluationComponents.Support.properTail codes = first :: rest) :
    ∃ words final, out = words ++ [final] ∧
      (∀ word ∈ words, word.length ≤ initialHeight first) ∧
        words.length = (first :: rest).length := by
  obtain ⟨ht, words, final, ha, hf, hout⟩ := (EvaluationComponents.execute_graph codes out).mp ho
  have hs := EvaluationComponents.Support.tracking_segment codes ht
  rw [hfirst] at ha hs
  exact ⟨words, final, hout,
    global_lengths _ first rest words hs.2.1 hs.2.2 ha, assigned_length ha⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationProperComponentLengths
