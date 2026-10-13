import Alexander313.Wilken.HereditaryEvaluationPrefixBlocks
import Alexander313.Wilken.HereditaryEvaluationFiniteLengthOrder

/-!
# The actual evaluation prefix call strictly decreases lSeq

The executing proper components are split at their real last input. The
computed endpoint scan survives that prefix, whose final epsilon component
is precisely the last proper component of the original execution. The
whole prefix therefore independently executes the original proper blocks.
Its chronological length word is the literal original word with the final
entry deleted. Strict lexical descent and membership in the same originally
computed finite height domain follow, without a recursive-output or descent
oracle. The h/sk calls in the other source clauses remain separate.
Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationPrefixLengthDescent

open GlobalTrackingSequences EvaluationComponents.Support EvaluationBlocks
open GlobalAdditiveTracking.Source (baseWord)
open Hereditary.FinePredecessor (stripLast stripLast_split)
open NativeContext.SourceTrackingSequences (lastCode lastCode_append_singleton stripLast_append_singleton)

/-- The real original execution supplies the entire independently
executing prefix word, including its actual final epsilon component. -/
theorem execute_prefix_components (codes : List Nat) (out : List Block)
    (ho : out ∈ EvaluationComponents.execute codes) (hne : properTail codes ≠ []) :
    ∃ next final, next ∈ EvaluationComponents.execute (stripLast codes) ∧ out = next ++ [final] := by
  obtain ⟨ht, words, final, hw, hf, hout⟩ := (EvaluationComponents.execute_graph codes out).mp ho
  let m := segmentIndex (stripLast codes)
  let before := stripLast (properTail codes)
  obtain ⟨a, htail, hreverse⟩ := stripLast_split (properTail codes) hne
  have htail' : properTail codes = before ++ [a] := htail
  have hseg := tracking_segment codes ht
  have hprefix : stripLast codes = (baseWord m ++ before) ++ [a] := by
    have hs := hseg.1
    rw [htail'] at hs
    simpa only [m, List.append_assoc] using hs
  have hr : EpsilonReference (before ++ [a]) := by
    have hs := hseg.2.1
    rw [htail'] at hs
    exact hs
  have hg : TailGap m (before ++ [a]) := by
    have hs := hseg.2.2
    rw [htail'] at hs
    exact hs
  have hassigned : Assigned (endpointCode m) (before ++ [a]) words := by
    have hs : Assigned (endpointCode m) (properTail codes) words := hw
    rw [htail'] at hs
    exact hs
  obtain ⟨prefixWords, lastWord, hbefore, hlastWord, hwords⟩ :=
    EvaluationPrefixBlocks.assigned_snoc_split (endpointCode m) a before words hassigned
  have hprefixNe : stripLast codes ≠ [] := by
    intro he
    have hh := (List.append_eq_nil_iff.mp (hprefix.symm.trans he)).2
    exact List.cons_ne_nil _ _ hh
  have htPrefix := EvaluationPrefixSupport.stripLast_tracking codes ht hprefixNe
  have hstrip : stripLast (stripLast codes) = baseWord m ++ before := by
    rw [hprefix, stripLast_append_singleton]
  have hindex : segmentIndex (stripLast (stripLast codes)) = m := by
    rw [hstrip]
    exact (EvaluationPrefixSegment.prefix_segment m a before hr hg).1
  have hproper : properTail (stripLast codes) = before := by
    rw [hprefix]
    exact (EvaluationPrefixSegment.prefix_segment m a before hr hg).2
  have hlast : lastCode (stripLast codes) = a := by
    rw [hprefix, lastCode_append_singleton]
  have hprevious : EvaluationFinalComponent.previousCode (stripLast codes) =
      EvaluationPrefixBlocks.previous (endpointCode m) before := by
    rw [hprefix]
    exact EvaluationPrefixBlocks.previous_global_prefix m a before
  have ha := hr.nodes a (List.mem_append.mpr (Or.inr List.mem_cons_self))
  have hfinal : lastWord ∈ EvaluationComponents.finalExecute (stripLast codes) := by
    rw [EvaluationComponents.finalExecute, hprevious, hlast]
    exact EvaluationPrefixSupport.epsilon_final_block _ a lastWord
      (EvaluationPrefixBlocks.previous_start m a before hr) ha
      (EvaluationPrefixBlocks.previous_lt_final m a before hr hg) hlastWord
  have hnext : words ∈ EvaluationComponents.execute (stripLast codes) := by
    apply (EvaluationComponents.execute_graph _ words).mpr
    refine ⟨htPrefix, prefixWords, lastWord, ?_, hfinal, hwords⟩
    simpa only [hindex, hproper] using hbefore
  exact ⟨words, final, hnext, hout⟩

/-- Genuine chronological length outputs on the actual prefix differ
by deletion of the real final component length, not a chosen witness. -/
theorem executeLengths_prefix (codes ns : List Nat)
    (ho : ns ∈ EvaluationComponents.executeLengths codes) (hne : properTail codes ≠ []) :
    ∃ next n, next ∈ EvaluationComponents.executeLengths (stripLast codes) ∧
      ns = next ++ [n] ∧ 0 < n := by
  obtain ⟨words, hw, he⟩ := (EvaluationComponents.executeLengths_graph codes ns).mp ho
  obtain ⟨nextWords, final, hnext, hwords⟩ := execute_prefix_components codes words hw hne
  have hnonempty := EvaluationComponents.execute_nonempty_components codes words hw final
    (by rw [hwords]; exact List.mem_append.mpr (Or.inr List.mem_cons_self))
  refine ⟨lengths nextWords, final.length, ?_, ?_, List.length_pos_iff.mpr hnonempty⟩
  · exact (EvaluationComponents.executeLengths_graph _ _).mpr ⟨nextWords, hnext, rfl⟩
  · rw [← he, hwords, lengths, List.map_append, List.map_singleton]

/-- The actual prefix step both strictly decreases lSeq and stays inside
the same finite height domain of the original input. No new height bound,
prefix output or strict decrease is a premise. -/
theorem executeLengths_prefix_descent (codes ns : List Nat)
    (ho : ns ∈ EvaluationComponents.executeLengths codes) (hne : properTail codes ≠ []) :
    ∃ next,
      next ∈ EvaluationComponents.executeLengths (stripLast codes) ∧
      List.Lex (· < ·) next ns ∧
      next ∈ EvaluationFiniteLengthOrder.lengthDomain
        (EvaluationCompleteLengthBound.originalHeight codes + 1) ∧
      ns ∈ EvaluationFiniteLengthOrder.lengthDomain
        (EvaluationCompleteLengthBound.originalHeight codes + 1) := by
  obtain ⟨next, n, hnext, he, hn⟩ := executeLengths_prefix codes ns ho hne
  have hbound := EvaluationFiniteLengthOrder.executeLengths_mem codes ns ho
    (fun he => False.elim (hne he))
  have hlex : List.Lex (· < ·) next ns := by
    rw [he]
    simpa only [List.append_nil] using EvaluationFiniteLengthOrder.lex_proper_prefix next [] n
  have hprefixBound : next ∈ EvaluationFiniteLengthOrder.lengthDomain
      (EvaluationCompleteLengthBound.originalHeight codes + 1) := by
    refine ⟨?_, fun a ha => hbound.2 a (by rw [he]; exact List.mem_append.mpr (Or.inl ha))⟩
    have hl := hbound.1
    rw [he, List.length_append, List.length_singleton] at hl
    omega
  exact ⟨next, hnext, hlex, hprefixBound, hbound⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationPrefixLengthDescent
