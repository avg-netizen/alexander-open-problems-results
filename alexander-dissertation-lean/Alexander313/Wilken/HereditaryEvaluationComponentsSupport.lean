import Alexander313.Wilken.HereditaryEvaluationFinalComponent

/-!
# Computing the genuine maximal initial endpoint chain

The finite original segment checker is scanned by its actual first
passing index. Independent global Reference proves that a row passes;
the actual endpoint gap proves that no longer initial endpoint chain is
possible. Thus the executed index is the maximal m of Definition3.35,
not a supplied decomposition. Actual final-component membership also
derives nonemptiness. Common height and lSeq descent remain separate.
Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationComponents.Support

open GlobalTrackingSequences
open GlobalAdditiveTracking.Source (baseWord baseWord_primrec)
open Hereditary.FinePredecessor (stripLast stripLast_primrec)

def segmentIndex (codes : List Nat) : Nat :=
  (List.range (codes.length + 1)).findIdx (segmentCheck codes)

theorem segmentIndex_primrec : Primrec segmentIndex :=
  Primrec.list_findIdx (Primrec.list_range.comp (Primrec.succ.comp Primrec.list_length))
    segmentCheck_primrec

theorem segmentIndex_checked (codes : List Nat) (hr : Reference codes) :
    segmentCheck codes (segmentIndex codes) = true := by
  have he : (List.range (codes.length + 1)).any (segmentCheck codes) = true :=
    (referenceCheck_exact codes).mpr hr
  have hx := List.any_eq_true.mp he
  have hi := List.findIdx_lt_length_of_exists hx
  have hc := @List.findIdx_getElem Nat (segmentCheck codes)
    (List.range (codes.length + 1)) hi
  simpa only [segmentIndex, List.getElem_range] using hc

theorem segmentIndex_spec (codes : List Nat) (hr : Reference codes) :
    codes = baseWord (segmentIndex codes) ++ codes.drop (segmentIndex codes) ∧
      EpsilonReference (codes.drop (segmentIndex codes)) ∧
        TailGap (segmentIndex codes) (codes.drop (segmentIndex codes)) := by
  have hs := (segmentCheck_exact codes _).mp (segmentIndex_checked codes hr)
  refine ⟨?_, hs.2⟩
  rw [← hs.1]
  exact (List.take_append_drop _ codes).symm

/-- A genuine open first gap excludes every strictly longer initial
endpoint chain, even if it is merely supplied as a literal prefix. -/
theorem checked_segment_maximal (codes : List Nat) (m n : Nat)
    (hm : segmentCheck codes m = true) (hn : codes.take n = baseWord n) : n ≤ m := by
  apply le_of_not_gt
  intro hmn
  have hs := (segmentCheck_exact codes m).mp hm
  have hread : codes[m]? = some (endpointCode (m + 1)) := by
    calc
      codes[m]? = (codes.take n)[m]? := (List.getElem?_take_of_lt hmn).symm
      _ = (baseWord n)[m]? := congrArg (fun xs : List Nat => xs[m]?) hn
      _ = some (endpointCode (m + 1)) := by
        simp only [GlobalAdditiveTracking.Source.baseWord, List.getElem?_map,
          List.getElem?_range hmn, Option.map_some]
  have hsplit : codes = baseWord m ++ codes.drop m := by
    rw [← hs.1]
    exact (List.take_append_drop m codes).symm
  have hfirst : (codes.drop m)[0]? = some (endpointCode (m + 1)) := by
    rw [hsplit, List.getElem?_append_right (by
      simpa only [baseWord_length] using (le_refl m))] at hread
    simpa only [baseWord_length, Nat.sub_self] using hread
  cases hd : codes.drop m with
  | nil => simp [hd] at hfirst
  | cons a rest =>
    have ha : a = endpointCode (m + 1) := by
      simpa only [hd, List.getElem?_cons_zero, Option.some.injEq] using hfirst
    have hg : sourceUpsilon (m : Ordinal.{0}) < unionInterpretation a ∧
        unionInterpretation a < sourceUpsilon ((m + 1 : Nat) : Ordinal.{0}) := by
      simpa only [hd, TailGap] using hs.2.2
    have hgap := hg.2
    have hv : unionInterpretation (endpointCode (m + 1)) =
        sourceUpsilon ((m + 1 : Nat) : Ordinal.{0}) :=
      (PublicEpsilonSourceDictionary.endpointCode_value _).trans
        (PublicUpsilonSegment.successor_value m).symm
    rw [ha, hv] at hgap
    exact (lt_irrefl _ hgap)

theorem segmentIndex_maximal (codes : List Nat) (hr : Reference codes) (n : Nat)
    (hn : codes.take n = baseWord n) : n ≤ segmentIndex codes :=
  checked_segment_maximal codes _ n (segmentIndex_checked codes hr) hn

def properTail (codes : List Nat) : List Nat :=
  (stripLast codes).drop (segmentIndex (stripLast codes))

theorem properTail_primrec : Primrec properTail :=
  Primrec.list_drop.comp (segmentIndex_primrec.comp stripLast_primrec) stripLast_primrec

theorem tracking_segment (codes : List Nat) (ht : Tracking codes) :
    stripLast codes = baseWord (segmentIndex (stripLast codes)) ++ properTail codes ∧
      EpsilonReference (properTail codes) ∧
        TailGap (segmentIndex (stripLast codes)) (properTail codes) :=
  segmentIndex_spec (stripLast codes) ht.2.2.1

theorem finish_nonempty (gamma : Nat) (fs word : List Nat) (hw : word ≠ []) :
    EvaluationFinalComponent.finish gamma fs word ≠ [] := by
  unfold EvaluationFinalComponent.finish
  cases hc : EvaluationFinalComponent.appendCheck gamma fs with
  | false => simpa only [Bool.cond_false] using hw
  | true =>
    simp only [Bool.cond_true]
    intro he
    exact hw (List.append_eq_nil_iff.mp he).1

theorem final_nonempty (gamma beta : Nat) (out : List Nat)
    (ho : out ∈ EvaluationFinalComponent.execute gamma beta) : out ≠ [] := by
  rcases (EvaluationFinalComponent.execute_clauses gamma beta out).mp ho with
    ⟨hi, ⟨hc, rfl⟩ | ⟨hc, fs, word, hf, hw, rfl⟩⟩
  · exact List.cons_ne_nil beta []
  · exact finish_nonempty gamma fs word (EvaluationBlocks.block_tracking gamma _ word hw).1

end Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationComponents.Support
