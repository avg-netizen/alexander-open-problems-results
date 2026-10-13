import Alexander313.Wilken.HereditaryEvaluationPrefixSegment

/-!
# Actual proper-block execution supplies the prefix's final block

The real Assigned recurrence, split at its actual last proper input,
derives every preceding block and the last independently executing block.
Its genuine previous code is exactly the actual final-component previous
code on the literal global prefix. The independent epsilon reference and
open gap derive the strict previous-to-final comparison and start caller.
No block word, decomposition, previous code or caller is supplied to the
eventual whole-execution consumer. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationPrefixBlocks

open GlobalTrackingSequences EvaluationBlocks
open GlobalAdditiveTracking.Source (baseWord)
open Hereditary.FinePredecessor (stripLast)
open NativeContext.SourceTrackingSequences (lastCode lastCode_mem lastCode_singleton stripLast_append_singleton)
open NativeContext.PublicEpsilonUnboundedIota.SkTracking.Support (lastCode_cons_nonempty)

def previous (gamma : Nat) (before : List Nat) : Nat :=
  match before with
  | [] => gamma
  | _ :: _ => lastCode before

private theorem previous_cons (gamma a : Nat) (rest : List Nat) :
    previous gamma (a :: rest) = previous a rest := by
  cases rest with
  | nil => exact lastCode_singleton a
  | cons b rest => exact lastCode_cons_nonempty a (b :: rest) (List.cons_ne_nil _ _)

theorem assigned_snoc_split (gamma a : Nat) (before : List Nat) (words : List Block)
    (ha : Assigned gamma (before ++ [a]) words) :
    ∃ prefix word, Assigned gamma before prefix ∧
      word ∈ EvaluationRelativeCallers.blockExecute (previous gamma before) a ∧
      words = prefix ++ [word] := by
  induction before generalizing gamma words with
  | nil =>
    cases ha with
    | cons gamma a rest word words hw ht =>
      cases ht
      exact ⟨[], word, .nil gamma, hw, rfl⟩
  | cons b rest ih =>
    cases ha with
    | cons gamma b tail first words hw ht =>
      obtain ⟨prefix, word, hp, hl, he⟩ := ih b words ht
      refine ⟨first :: prefix, word, .cons gamma b rest first prefix hw hp, ?_, ?_⟩
      · rw [previous_cons]
        exact hl
      · simpa only [he, List.cons_append]

/-- Literal endpoint algebra derives the previous code actually used by
the prefix's final-component dispatcher. -/
theorem previous_global_prefix (m a : Nat) (before : List Nat) :
    EvaluationFinalComponent.previousCode ((baseWord m ++ before) ++ [a]) =
      previous (endpointCode m) before := by
  rw [EvaluationFinalComponent.previousCode, stripLast_append_singleton]
  cases before with
  | nil =>
    rw [List.append_nil]
    cases m with
    | zero => rfl
    | succ n =>
      have hn := AssignmentSupport.baseWord_ne_nil (n + 1) (Nat.succ_ne_zero _)
      rw [List.isEmpty_eq_false_iff.mpr hn, Bool.cond_false, AssignmentSupport.baseWord_last]
      rfl
  | cons b rest =>
    have hn : baseWord m ++ b :: rest ≠ [] := by
      intro he
      exact List.cons_ne_nil _ _ (List.append_eq_nil_iff.mp he).2
    rw [List.isEmpty_eq_false_iff.mpr hn, Bool.cond_false,
      AssignmentSupport.lastCode_append_nonempty _ _ (List.cons_ne_nil _ _)]
    rfl

theorem previous_start (m a : Nat) (before : List Nat)
    (hr : EpsilonReference (before ++ [a])) :
    EvaluationFinalComponent.Support.startCheck (previous (endpointCode m) before) = true := by
  apply (EvaluationFinalComponent.Support.startCheck_exact _).mpr
  cases before with
  | nil =>
    cases m with
    | zero => exact Or.inl rfl
    | succ n => exact Or.inr (GlobalMuDictionary.Support.endpoint_input n)
  | cons b rest =>
    apply Or.inr
    exact hr.nodes _ (List.mem_append.mpr (Or.inl (lastCode_mem _ (List.cons_ne_nil _ _))))

theorem previous_lt_final (m a : Nat) (before : List Nat)
    (hr : EpsilonReference (before ++ [a])) (hg : TailGap m (before ++ [a])) :
    unionInterpretation (previous (endpointCode m) before) < unionInterpretation a := by
  cases before with
  | nil =>
    have ha := (GlobalMuDictionary.Support.inputCheck_exact a).mp (hr.nodes a List.mem_cons_self)
    cases m with
    | zero =>
      simpa only [previous, PublicEpsilonSourceDictionary.endpointCode_value, finiteBase_zero] using
        EpsilonOffsets.epsilon_one_lt ha.2
    | succ n =>
      simpa only [previous, TailGap, List.nil_append,
        PublicEpsilonSourceDictionary.endpointCode_value, PublicUpsilonSegment.successor_value] using hg.1
  | cons b rest =>
    have hstrict := hr.strict
    rw [List.map_append] at hstrict
    exact (List.pairwise_append.mp hstrict).2.2 _
      (List.mem_map.mpr ⟨lastCode (b :: rest), lastCode_mem _ (List.cons_ne_nil _ _), rfl⟩)
      _ (List.mem_map.mpr ⟨a, List.mem_cons_self, rfl⟩)

end Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationPrefixBlocks
