import Alexander313.Wilken.HereditaryEvaluationPrefixLengthDescent

/-!
# Independent execution of every genuine proper component prefix

The actual component graph supplies the complete epsilon reference and its
computed source segment. Literal finite Assignment splitting constructs
all earlier blocks and the block at any observed proper epsilon. That
proper prefix is an independent global Reference, hence a true Tracking
input; its computed segment and genuine final epsilon dispatcher reproduce
exactly the corresponding component prefix. No prefix execution, component
value, source index or evaluator equation is supplied. Uncompiled source.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationComponentPrefix

open GlobalTrackingSequences EvaluationComponents.Support EvaluationBlocks
open GlobalAdditiveTracking.Source (baseWord)
open Hereditary.FinePredecessor (stripLast)
open NativeContext.SourceTrackingSequences (lastCode lastCode_singleton lastCode_append_singleton stripLast_append_singleton)

private theorem previous_cons (gamma a : Nat) (rest : List Nat) :
    EvaluationPrefixBlocks.previous gamma (a :: rest) = EvaluationPrefixBlocks.previous a rest := by
  cases rest with
  | nil => simp only [EvaluationPrefixBlocks.previous, lastCode_singleton]
  | cons b bs =>
    exact NativeContext.PublicEpsilonUnboundedIota.SkTracking.Support.lastCode_cons_nonempty
      a (b :: bs) (List.cons_ne_nil _ _)

theorem assigned_append_split (gamma : Nat) (before rest : List Nat) (words : List Block)
    (ha : Assigned gamma (before ++ rest) words) :
    ∃ prefix suffix, words = prefix ++ suffix ∧ Assigned gamma before prefix ∧
      Assigned (EvaluationPrefixBlocks.previous gamma before) rest suffix := by
  induction before generalizing gamma words with
  | nil => exact ⟨[], words, rfl, .nil gamma, ha⟩
  | cons a before ih =>
    cases ha with
    | cons gamma a inputs word tail hw ht =>
      obtain ⟨prefix, suffix, he, hp, hs⟩ := ih a tail ht
      refine ⟨word :: prefix, suffix, ?_, .cons gamma a before word prefix hw hp, ?_⟩
      · simpa only [List.cons_append] using congrArg (List.cons word) he
      · rw [previous_cons]; exact hs

theorem epsilonReference_prefix (before rest : List Nat)
    (hr : EpsilonReference (before ++ rest)) : EpsilonReference before := by
  revert hr
  induction before with
  | nil => intro hr; exact .nil
  | cons a before ih =>
    intro hr
    cases before with
    | nil => exact .one a (hr.nodes a List.mem_cons_self)
    | cons b before =>
      cases hr with
      | cons a b xs ha hab hc ht => exact .cons a b before ha hab hc (ih ht)

theorem tailGap_prefix (m : Nat) (before rest : List Nat)
    (hg : TailGap m (before ++ rest)) : TailGap m before := by
  cases before with
  | nil => trivial
  | cons a before => exact hg

/-- Every observed proper epsilon component constructs the actual
independently executing global prefix and its complete component word. -/
theorem execute_proper_prefix (codes before : List Nat) (gamma : Nat) (after : List Nat)
    (out : List Block) (ho : out ∈ EvaluationComponents.execute codes)
    (htail : properTail codes = before ++ gamma :: after) :
    ∃ prefix word rest,
      out = prefix ++ word :: rest ∧
      prefix ++ [word] ∈ EvaluationComponents.execute
        ((baseWord (segmentIndex (stripLast codes)) ++ before) ++ [gamma]) := by
  obtain ⟨ht, words, final, hw, hf, hout⟩ := (EvaluationComponents.execute_graph codes out).mp ho
  let m := segmentIndex (stripLast codes)
  have hseg := tracking_segment codes ht
  have hrWhole : EpsilonReference ((before ++ [gamma]) ++ after) := by
    have hr := hseg.2.1
    rw [htail] at hr
    simpa only [List.append_assoc, List.singleton_append] using hr
  have hgWhole : TailGap m ((before ++ [gamma]) ++ after) := by
    have hg := hseg.2.2
    rw [htail] at hg
    simpa only [List.append_assoc, List.singleton_append] using hg
  have hr := epsilonReference_prefix (before ++ [gamma]) after hrWhole
  have hg := tailGap_prefix m (before ++ [gamma]) after hgWhole
  have hassigned : Assigned (endpointCode m) (before ++ gamma :: after) words := by
    simpa only [htail] using hw
  obtain ⟨prefix, suffix, he, hp, hs⟩ := assigned_append_split (endpointCode m) before
    (gamma :: after) words hassigned
  cases hs with
  | cons previous gamma after word rest hword hrest =>
    have hwords : words = prefix ++ word :: rest := he
    let next := (baseWord m ++ before) ++ [gamma]
    have href : Reference next := ⟨m, before ++ [gamma], by
      simp only [next, List.append_assoc], hr, hg⟩
    have hne : next ≠ [] := by
      intro hn
      exact List.cons_ne_nil _ _ (List.append_eq_nil_iff.mp hn).2
    have htNext := EvaluationPrefixSupport.reference_tracking next href hne
    have hstrip : stripLast next = baseWord m ++ before := stripLast_append_singleton _ _
    have hindex : segmentIndex (stripLast next) = m := by
      rw [hstrip]; exact (EvaluationPrefixSegment.prefix_segment m gamma before hr hg).1
    have hproper : properTail next = before :=
      (EvaluationPrefixSegment.prefix_segment m gamma before hr hg).2
    have hlast : lastCode next = gamma := lastCode_append_singleton _ _
    have hprevious : EvaluationFinalComponent.previousCode next =
        EvaluationPrefixBlocks.previous (endpointCode m) before :=
      EvaluationPrefixBlocks.previous_global_prefix m gamma before
    have ha := hr.nodes gamma (List.mem_append.mpr (Or.inr List.mem_cons_self))
    have hfinal : word ∈ EvaluationComponents.finalExecute next := by
      rw [EvaluationComponents.finalExecute, hprevious, hlast]
      exact EvaluationPrefixSupport.epsilon_final_block _ gamma word
        (EvaluationPrefixBlocks.previous_start m gamma before hr) ha
        (EvaluationPrefixBlocks.previous_lt_final m gamma before hr hg) hword
    have hnext : prefix ++ [word] ∈ EvaluationComponents.execute next := by
      apply (EvaluationComponents.execute_graph _ _).mpr
      refine ⟨htNext, prefix, word, ?_, hfinal, rfl⟩
      simpa only [hindex, hproper] using hp
    refine ⟨prefix, word, rest ++ [final], ?_, hnext⟩
    rw [hout, hwords, List.append_assoc, List.cons_append]

end Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationComponentPrefix
