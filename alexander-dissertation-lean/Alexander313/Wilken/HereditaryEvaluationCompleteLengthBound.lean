import Alexander313.Wilken.HereditaryEvaluationEmptyTailGrammar
import Alexander313.Wilken.HereditaryEvaluationNonemptyTailLengthBound

/-!
# One computed original height bounds actual nonfixed evaluation lengths

The real maximal endpoint scan and proper tail choose the original height:
the selected proper FIRST height, or the original LOW final-target height
when that tail is empty. In the latter case genuine global Tracking derives
strict grammar admission unless the complete input is the next baseWord,
one of the printed fixed points. Actual component lengths belong to the
finite positive bounded alphabet at this computed height. No supplied
decomposition, height estimate or grammar guard is required. Recursive
lexical descent and evaluation remain separate. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationCompleteLengthBound

open GlobalTrackingSequences EvaluationComponents.Support
open Hereditary.FinePredecessor (stripLast stripLast_primrec)
open NativeContext.SourceTrackingSequences (lastCode lastCode_primrec list_isEmpty_primrec)
open NativeContext.SourceAdditiveTracking.Insertion (firstCode firstCode_primrec)

def originalHeight (codes : List Nat) : Nat := cond (properTail codes).isEmpty
  (cond (segmentIndex (stripLast codes) == 0)
    (EvaluationSourceOneFinalHeightSupport.sourceHeight (lastCode codes))
    (EvaluationPositiveFinalHeightSupport.sourceHeight
      (segmentIndex (stripLast codes) - 1) (lastCode codes)))
  (EvaluationInitialReferenceHeight.initialHeight (firstCode (properTail codes)))

theorem originalHeight_primrec : Primrec originalHeight := by
  have hm := segmentIndex_primrec.comp stripLast_primrec
  have hz := Primrec.beq.comp hm (Primrec.const 0)
  have he := list_isEmpty_primrec.comp properTail_primrec
  have hs := EvaluationSourceOneFinalHeightSupport.sourceHeight_primrec.comp lastCode_primrec
  have hp := EvaluationPositiveFinalHeightSupport.sourceHeight_primrec.comp
    (Primrec.nat_sub.comp hm (Primrec.const 1)) lastCode_primrec
  have ht := EvaluationInitialReferenceHeight.initialHeight_primrec.comp
    (firstCode_primrec.comp properTail_primrec)
  exact he.cond (hz.cond hs hp) ht

/-- The exception is exactly an actual evaluation fixed endpoint chain.
The real empty-tail final cover supplies the strict LOW grammar guard. -/
theorem executeLengths_bounded (codes ns : List Nat)
    (ho : ns ∈ EvaluationComponents.executeLengths codes)
    (hf : properTail codes = [] →
      codes ≠ GlobalAdditiveTracking.Source.baseWord (segmentIndex (stripLast codes) + 1)) :
    ns.length ≤ originalHeight codes + 1 ∧
      ∀ n ∈ ns, 0 < n ∧ n ≤ originalHeight codes + 1 := by
  by_cases hn : properTail codes = []
  · obtain ⟨words, hw, he⟩ := (EvaluationComponents.executeLengths_graph codes ns).mp ho
    have ht := ((EvaluationComponents.execute_graph codes words).mp hw).1
    have hb := EvaluationEmptyTailGrammar.nonfixed_target_lt_ceiling codes ht hn (hf hn)
    cases hm : segmentIndex (stripLast codes) with
    | zero =>
      have hbound := EvaluationSourceOneEmptyTailLength.executeLengths_bounded codes ns ho hn hm
        (by simpa only [hm] using hb)
      simpa only [originalHeight, hn, List.isEmpty_nil, Bool.cond_true, hm,
        beq_self_eq_true] using hbound
    | succ s =>
      have hbound := EvaluationPositiveEmptyTailLength.executeLengths_bounded s codes ns ho hn hm
        (by simpa only [hm] using hb)
      have hz : ((s + 1) == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
      simpa only [originalHeight, hn, List.isEmpty_nil, Bool.cond_true, hm,
        hz, Bool.cond_false, Nat.add_sub_cancel] using hbound
  · have hbound := EvaluationNonemptyTailLengthBound.executeLengths_bounded codes ns ho hn
    have he : (properTail codes).isEmpty = false := List.isEmpty_eq_false_iff.mpr hn
    simpa only [originalHeight, he, Bool.cond_false] using hbound

end Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationCompleteLengthBound
