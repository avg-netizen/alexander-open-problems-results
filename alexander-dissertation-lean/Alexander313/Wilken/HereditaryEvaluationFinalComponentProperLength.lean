import Alexander313.Wilken.HereditaryEvaluationCoveredComponentLength
import Alexander313.Wilken.HereditaryEvaluationProperComponentLengths

/-!
# The actual final component at a proper previous epsilon has the common bound

The no-append branch uses the genuine covered-component height bound.
When the actual second-factor flag passes, the real first factor is an
epsilon strictly above the previous one and under its original public mu.
The previous epsilon's true finite gap and strict mu boundary derive a
proper first-factor caller in that same gap. Its whole epsilon component
costs no extra entry, leaving exactly one for the actual second-factor
append. This proves the printed final length bound with honest original
mu coverage and a real previous gap, without an input length estimate.
The actual global-tracker consumer is separate. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationFinalComponentProperLength

open GlobalTrackingSequences EvaluationRelativeCallers
open EvaluationFinalComponent EvaluationFinalComponent.Support
open EvaluationInitialReferenceHeight EvaluationReferenceHeight

theorem first_factor_gap (m gamma beta first : Nat) (rest : List Nat)
    (hg : MuPublicDictionary.Support.inputCheck gamma = true)
    (hgap : TailGap m [gamma])
    (hi : blockInputCheck gamma beta = true)
    (hf : (first :: rest) ∈ factors beta)
    (hgt : unionInterpretation gamma < unionInterpretation beta)
    (he : GlobalMuDictionary.Support.inputCheck first = true)
    (hstrict : unionInterpretation gamma < unionInterpretation first) :
    MuPublicDictionary.Support.inputCheck first = true ∧ TailGap m [first] ∧
      initialHeight first ≤ initialHeight gamma := by
  have hglobal := ((MuPublicDictionary.Support.inputCheck_exact gamma).mp hg).1
  have hstart : startCheck gamma = true := (startCheck_exact gamma).mpr (Or.inr hglobal)
  have hb := first_factor_bounds gamma beta first rest hstart (factors_spec beta _ hf) hgt
  have hn := epsilon_not_initial gamma hglobal
  have hc : MuCoveredRelativeAssignment.Support.inputCheck gamma beta = true := by
    simpa only [blockInputCheck, hn, Bool.cond_false] using hi
  have hcaller := (MuCoveredRelativeAssignment.Support.inputCheck_exact gamma beta).mp hc
  have hcover : unionInterpretation first ≤ muValue gamma := hb.2.trans hcaller.2.2.2.2.2
  have hlevel := SmallHSupport.level_eq_of_gap m gamma
    ((MuPublicDictionary.Support.inputCheck_image gamma).mp hg).1 hgap
  have hmu : muValue gamma < sourceUpsilon ((m + 1 : Nat) : Ordinal.{0}) := by
    simpa only [muValue, hlevel, PublicUpsilonSegment.successor_value] using
      GlobalMuDictionary.publicCode_proper_bound gamma hg
  have hfirstGap : TailGap m [first] := ⟨hgap.1.trans hstrict, hcover.trans_lt hmu⟩
  have hproper := SmallHSupport.proper_of_gap m first he hfirstGap
  have hpublicCover : unionInterpretation first ≤ publicMuValue gamma := by
    simpa only [muValue, GlobalMuDictionary.publicCode_proper gamma hg, publicMuValue] using hcover
  have hheight := EvaluationInitialHeightCoveredMonotonicity.adjacency_monotone gamma first hg
    ((GlobalMuDictionary.Support.inputCheck_exact first).mp he).1
    ((GlobalMuDictionary.Support.inputCheck_exact first).mp he).2 hstrict hpublicCover
  exact ⟨hproper, hfirstGap, hheight⟩

/-- Actual output membership and the independent numerical caller derive
the bound in all three printed final-component alternatives. -/
theorem execute_length_le_previous (m gamma beta : Nat) (out : List Nat)
    (hg : MuPublicDictionary.Support.inputCheck gamma = true)
    (hgap : TailGap m [gamma])
    (ho : out ∈ EvaluationFinalComponent.execute gamma beta)
    (hcover : unionInterpretation gamma < unionInterpretation beta → blockInputCheck gamma beta = true) :
    out.length ≤ initialHeight gamma + 1 := by
  have hs := (EvaluationFinalComponent.execute_clauses gamma beta out).mp ho
  have hstart := (Bool.and_eq_true.mp hs.1).1
  rcases hs.2 with ⟨hless, rfl⟩ | ⟨hless, fs, word, hf, hw, rfl⟩
  · simp only [List.length_singleton]; omega
  · have hgt := (Canonical.less_exact gamma beta).mp hless
    have hi := hcover hgt.2.2
    cases fs with
    | nil => exact False.elim (factors_nonempty gamma beta hstart hgt.2.2 hf)
    | cons first rest =>
      have hw : word ∈ blockExecute gamma first := by
        simpa only [EvaluationFinalComponent.firstCode, List.head?_cons, Option.getD_some] using hw
      cases ha : appendCheck gamma (first :: rest) with
      | false =>
        simpa only [finish, ha, Bool.cond_false] using
          EvaluationCoveredComponentLength.block_length_le_previous gamma first word hg hw
      | true =>
        cases rest with
        | nil => simp only [appendCheck, List.tail_cons, List.isEmpty_nil,
            Bool.not_true, Bool.false_and, Bool.false_eq_true] at ha
        | cons second rest =>
          have hform := factors_spec beta (first :: second :: rest) hf
          have hflag := (appendCheck_two_exact gamma first second rest
            (start_checked gamma hstart)
            (hform.2.1 first List.mem_cons_self)
            (hform.2.1 second (List.mem_cons_of_mem _ List.mem_cons_self))).mp ha
          have hfirst := first_factor_gap m gamma beta first (second :: rest) hg hgap hi
            hf hgt.2.2 hflag.1 hflag.2.1
          have hlength := EvaluationEpsilonComponentIntervals.block_length_le_target m gamma first word
            hw hfirst.1 hgap.1.le hfirst.2.1
          have hbase : word.length ≤ initialHeight gamma := hlength.trans hfirst.2.2
          simpa only [finish, ha, Bool.cond_true, List.length_append, List.length_singleton] using
            Nat.add_le_add_right hbase 1

end Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationFinalComponentProperLength
