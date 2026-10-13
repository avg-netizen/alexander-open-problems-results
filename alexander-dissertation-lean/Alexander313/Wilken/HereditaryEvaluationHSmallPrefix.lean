import Alexander313.Wilken.HereditaryGlobalHSmall
import Alexander313.Wilken.HereditaryEvaluationComponentPrefix

/-!
# Genuine covered h-small calls expose an executing component prefix

The actual maximal sk path cannot stop at its initial epsilon when that
epsilon covers the cutoff. Its real second entry makes the original last
epsilon a proper node of the new global reference. The actual gap of the
original reference survives the splice and identifies the computed maximal
endpoint scan. Thus the actual component execution on h-small has an
independently executing component prefix at the original reference itself.
No chosen segment, sk extension, prefix execution or component is supplied.
Source-only uncompiled candidates; strict evaluator descent is separate.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationHSmallPrefix

open GlobalTrackingSequences EvaluationComponents.Support EvaluationBlocks
open GlobalAdditiveTracking.Source (baseWord)
open Hereditary.FinePredecessor (stripLast)
open NativeContext.SourceAdditiveTracking.InsertionFidelitySupport (stripLast_append_nonempty)
open NativeContext.PublicEpsilonUnboundedIota.SkTracking.Support (stripLast_cons_nonempty)

/-- The independently executing maximal sk path extends its initial
epsilon exactly as required by a genuine observed mu cover. -/
theorem sk_covered_nontrivial (gamma cutoff : Nat) (codes : List Nat)
    (ho : codes ∈ SkPublicDictionary.execute (gamma, cutoff))
    (hc : unionInterpretation cutoff ≤ SkPublicRecurrence.muValue gamma) :
    ∃ second rest, codes = gamma :: second :: rest := by
  obtain ⟨tail, he, hone⟩ := SkPublicRecurrence.execute_initial gamma cutoff codes ho
  cases tail with
  | nil =>
    have hp := SkPublicRecurrence.execute_path gamma cutoff codes ho
    rw [he] at hp
    cases hp with
    | stop a ha hb => exact False.elim (hb.not_ge hc)
  | cons second rest => exact ⟨second, rest, he⟩

/-- Genuine h-small membership and cover construct its actual nontrivial
sk splice and complete global Tracking. -/
theorem execute_covered_extension (p : GlobalHSmall.Query) (out : List Nat)
    (ho : out ∈ GlobalHSmall.execute p)
    (hc : unionInterpretation p.2.2 ≤ SkPublicRecurrence.muValue p.2.1)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation p.2.2))
    (hone : 1 < unionInterpretation p.2.2) :
    Tracking out ∧ ∃ second rest,
      out = p.1 ++ p.2.1 :: second :: rest ∧
      p.2.1 :: second :: rest ∈ SkPublicDictionary.execute p.2 := by
  have hs := (GlobalHSmall.execute_clauses p out).mp ho
  refine ⟨GlobalHSmall.execute_tracking p out ho hm hone, ?_⟩
  rcases hs.2 with ⟨hcover, codes, hcodes, he⟩ | ⟨hfail, he⟩
  · obtain ⟨second, rest, hshape⟩ := sk_covered_nontrivial _ _ codes hcodes hc
    exact ⟨second, rest, by simpa only [hshape] using he,
      by simpa only [hshape] using hcodes⟩
  · exact False.elim (hfail.not_ge hc)

/-- An actual component execution on a genuinely covered h-small result
constructs the literal component prefix executing the original reference.
The real source segment and intervening component are conclusions. -/
theorem execute_components_prefix (p : GlobalHSmall.Query) (out : List Nat)
    (words : List Block) (ho : out ∈ GlobalHSmall.execute p)
    (hc : unionInterpretation p.2.2 ≤ SkPublicRecurrence.muValue p.2.1)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation p.2.2))
    (hone : 1 < unionInterpretation p.2.2)
    (hw : words ∈ EvaluationComponents.execute out) :
    ∃ prefix word rest,
      words = prefix ++ word :: rest ∧
      prefix ++ [word] ∈ EvaluationComponents.execute (p.1 ++ [p.2.1]) := by
  have hi := (GlobalHSmall.inputCheck_exact p).mp
    ((GlobalHSmall.execute_clauses p out).mp ho).1
  obtain ⟨m, before, hp, hr, hg⟩ := SmallHSupport.proper_last_segment p.1 p.2.1 hi.1 hi.2.1
  obtain ⟨htOut, second, tail, hshape, hsk⟩ := execute_covered_extension p out ho hc hm hone
  have htSk := SkPublicRecurrence.execute_tracking _ _ _ hsk hm hone
  have htRel := PublicHSmall.reference_tracking_splice before p.2.1 (second :: tail) hr htSk
  have hgap : TailGap m (stripLast (before ++ p.2.1 :: second :: tail)) := by
    cases before with
    | nil => exact (SmallHSupport.relative_tracking_in_gap m p.2.1 (second :: tail)
        hi.2.1 htRel hg).1
    | cons a before =>
      have ha := hr.nodes a List.mem_cons_self
      exact (SmallHSupport.relative_tracking_in_gap m a (before ++ p.2.1 :: second :: tail)
        ha htRel hg).1
  have hreference := EpsilonReference.of_relative htRel.2.2.1
  have hrelativeShape : stripLast (before ++ p.2.1 :: second :: tail) =
      before ++ p.2.1 :: stripLast (second :: tail) := by
    rw [stripLast_append_nonempty before _ (List.cons_ne_nil _ _),
      stripLast_cons_nonempty p.2.1 _ (List.cons_ne_nil _ _)]
  have hstrip : stripLast out = baseWord m ++ (before ++ p.2.1 :: stripLast (second :: tail)) := by
    rw [hshape, hp, List.append_assoc,
      stripLast_append_nonempty (baseWord m) _ (by
        intro hn; exact List.cons_ne_nil _ _ (List.append_eq_nil_iff.mp hn).2), hrelativeShape]
  have hindex : segmentIndex (stripLast out) = m := by
    rw [hstrip]
    exact EvaluationPrefixSegment.segmentIndex_on_segment m _
      (by simpa only [hrelativeShape] using hreference)
      (by simpa only [hrelativeShape] using hgap)
  have hproper : properTail out = before ++ p.2.1 :: stripLast (second :: tail) := by
    rw [properTail, hindex, hstrip]
    exact List.drop_left' (baseWord_length m)
  obtain ⟨prefix, word, rest, he, hprefix⟩ :=
    EvaluationComponentPrefix.execute_proper_prefix out before p.2.1 _ words hw hproper
  refine ⟨prefix, word, rest, he, ?_⟩
  simpa only [hindex, hp] using hprefix

end Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationHSmallPrefix
