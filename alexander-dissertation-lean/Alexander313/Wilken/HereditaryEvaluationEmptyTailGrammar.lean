import Alexander313.Wilken.HereditaryEvaluationPositiveEmptyTailLength
import Alexander313.Wilken.HereditaryEvaluationSourceOneEmptyTailLength

/-!
# Actual global tracking derives the empty-tail source grammar guard

When the computed proper tail is empty, the real maximal segment gives
the literal original baseWord. Its extended mu bounds the final target
by the next finite endpoint. Equality there makes the complete original
word exactly the next baseWord, one of the printed evaluation fixed points.
Every other such word therefore has strict source grammar admission.
No decomposition or ceiling representative is supplied. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationEmptyTailGrammar

open GlobalTrackingSequences EvaluationComponents.Support
open GlobalAdditiveTracking.Source (baseWord)
open Hereditary.FinePredecessor (stripLast stripLast_split)
open NativeContext.SourceTrackingSequences (lastCode)

theorem target_le_ceiling (codes : List Nat) (ht : Tracking codes)
    (hn : properTail codes = []) :
    unionInterpretation (lastCode codes) ≤ finiteBase (segmentIndex (stripLast codes) + 1) := by
  have hs := tracking_segment codes ht
  have he : stripLast codes = baseWord (segmentIndex (stripLast codes)) := by
    simpa only [hn, List.append_nil] using hs.1
  cases hm : segmentIndex (stripLast codes) with
  | zero =>
    have hnil : stripLast codes = [] := by
      simpa only [hm, GlobalAdditiveTracking.Source.baseWord, List.range_zero, List.map_nil] using he
    have hb := ht.2.2.2.2.2
    rw [if_pos hnil] at hb
    simpa only [hm, PublicUpsilonSegment.successor_value 0] using hb.2
  | succ s =>
    have hne : stripLast codes ≠ [] := by
      rw [he, hm]
      exact AssignmentSupport.baseWord_ne_nil (s + 1) (by omega)
    have hb := ht.2.2.2.2.2
    rw [if_neg hne, he, AssignmentSupport.baseWord_final_cover _ (by rw [hm]; omega)] at hb
    simpa only [hm, PublicUpsilonSegment.successor_value] using hb.2

theorem at_ceiling_is_baseWord (codes : List Nat) (ht : Tracking codes)
    (hn : properTail codes = [])
    (he : unionInterpretation (lastCode codes) = finiteBase (segmentIndex (stripLast codes) + 1)) :
    codes = baseWord (segmentIndex (stripLast codes) + 1) := by
  have hs := tracking_segment codes ht
  have hstrip : stripLast codes = baseWord (segmentIndex (stripLast codes)) := by
    simpa only [hn, List.append_nil] using hs.1
  have hc : lastCode codes = endpointCode (segmentIndex (stripLast codes) + 1) :=
    Canonical.check_value_injective _ _
      (ht.2.1 _ (NativeContext.SourceTrackingSequences.lastCode_mem codes ht.1))
      (PublicEpsilonSourceDictionary.endpointCode_checked _) (he.trans
        (PublicEpsilonSourceDictionary.endpointCode_value _).symm)
  obtain ⟨last, hsplit, hlast⟩ := stripLast_split codes ht.1
  have hl : lastCode codes = last := by
    simp only [lastCode, hlast, Option.getD_some]
  calc
    codes = stripLast codes ++ [lastCode codes] := by simpa only [hl] using hsplit
    _ = baseWord (segmentIndex (stripLast codes)) ++ [endpointCode (segmentIndex (stripLast codes) + 1)] := by
      rw [hstrip, hc]
    _ = baseWord (segmentIndex (stripLast codes) + 1) := (AssignmentSupport.baseWord_succ _).symm

theorem nonfixed_target_lt_ceiling (codes : List Nat) (ht : Tracking codes)
    (hn : properTail codes = [])
    (hf : codes ≠ baseWord (segmentIndex (stripLast codes) + 1)) :
    unionInterpretation (lastCode codes) < finiteBase (segmentIndex (stripLast codes) + 1) := by
  apply lt_of_le_of_ne (target_le_ceiling codes ht hn)
  intro he
  exact hf (at_ceiling_is_baseWord codes ht hn he)

end Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationEmptyTailGrammar
