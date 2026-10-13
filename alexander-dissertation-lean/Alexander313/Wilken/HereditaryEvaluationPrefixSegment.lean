import Alexander313.Wilken.HereditaryEvaluationPrefixSupport

/-!
# The actual maximal endpoint segment survives proper-prefix recursion

An independent epsilon reference and its true open endpoint gap identify
the genuinely computed maximal segment, rather than a supplied numerical
segment index. Removing its last entry preserves both properties. The
actual proper-tail scan therefore computes the literal remaining tail on
the prefix used by evaluation. No assignment decomposition, recursive
output, height or evaluation law is assumed. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationPrefixSegment

open GlobalTrackingSequences EvaluationComponents.Support
open GlobalAdditiveTracking.Source (baseWord)
open Hereditary.FinePredecessor (stripLast)
open NativeContext.SourceTrackingSequences (stripLast_singleton stripLast_append_singleton)
open NativeContext.PublicEpsilonUnboundedIota.SkTracking.Support (stripLast_cons_nonempty)

theorem epsilonReference_stripLast {xs : List Nat} (hr : EpsilonReference xs) :
    EpsilonReference (stripLast xs) := by
  induction hr with
  | nil => exact .nil
  | one a ha => simpa only [stripLast_singleton] using (EpsilonReference.nil)
  | cons a b xs ha hab hcover ht ih =>
    cases xs with
    | nil =>
      have hs : stripLast [a, b] = [a] := stripLast_append_singleton [a] b
      rw [hs]
      exact .one a ha
    | cons c cs =>
      rw [stripLast_cons_nonempty a _ (List.cons_ne_nil _ _),
        stripLast_cons_nonempty b _ (List.cons_ne_nil _ _)]
      exact .cons a b _ ha hab hcover
        (by simpa only [stripLast_cons_nonempty b _ (List.cons_ne_nil _ _)] using ih)

theorem tailGap_stripLast (m : Nat) (xs : List Nat) (hg : TailGap m xs) :
    TailGap m (stripLast xs) := by
  cases xs with
  | nil => trivial
  | cons a xs =>
    cases xs with
    | nil => rw [stripLast_singleton]; trivial
    | cons b xs =>
      simpa only [stripLast_cons_nonempty a _ (List.cons_ne_nil _ _), TailGap] using hg

/-- Both directions use the actual maximal-segment theorem and true
checked segment; no equality with the scan is supplied. -/
theorem segmentIndex_on_segment (m : Nat) (xs : List Nat)
    (hr : EpsilonReference xs) (hg : TailGap m xs) :
    segmentIndex (baseWord m ++ xs) = m := by
  have href : Reference (baseWord m ++ xs) := ⟨m, xs, rfl, hr, hg⟩
  have htake : (baseWord m ++ xs).take m = baseWord m := by
    exact List.take_left' (baseWord_length m)
  have hdrop : (baseWord m ++ xs).drop m = xs := by
    exact List.drop_left' (baseWord_length m)
  have hcheck : segmentCheck (baseWord m ++ xs) m = true :=
    (segmentCheck_exact _ m).mpr ⟨htake, by simpa only [hdrop] using hr,
      by simpa only [hdrop] using hg⟩
  have hactual := segmentIndex_checked _ href
  exact Nat.le_antisymm
    (checked_segment_maximal _ m _ hcheck ((segmentCheck_exact _ _).mp hactual).1)
    (segmentIndex_maximal _ href m htake)

theorem properTail_on_segment (m beta : Nat) (xs : List Nat)
    (hr : EpsilonReference xs) (hg : TailGap m xs) :
    properTail ((baseWord m ++ xs) ++ [beta]) = xs := by
  rw [properTail, stripLast_append_singleton, segmentIndex_on_segment m xs hr hg]
  exact List.drop_left' (baseWord_length m)

/-- Actual scanning on the prefix's proper reference retains the same
maximal endpoint segment while deleting its genuine last proper entry. -/
theorem prefix_segment (m a : Nat) (before : List Nat)
    (hr : EpsilonReference (before ++ [a])) (hg : TailGap m (before ++ [a])) :
    segmentIndex (baseWord m ++ before) = m ∧
      properTail ((baseWord m ++ before) ++ [a]) = before := by
  have hreference : EpsilonReference before := by
    simpa only [stripLast_append_singleton] using epsilonReference_stripLast hr
  have hgap : TailGap m before := by
    simpa only [stripLast_append_singleton] using tailGap_stripLast m _ hg
  exact ⟨segmentIndex_on_segment m before hreference hgap,
    properTail_on_segment m a before hreference hgap⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationPrefixSegment
