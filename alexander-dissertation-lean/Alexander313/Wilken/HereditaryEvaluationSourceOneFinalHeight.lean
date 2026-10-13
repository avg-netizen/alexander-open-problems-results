import Alexander313.Wilken.HereditaryEvaluationSourceOneFinalHeightSupport

/-!
# Actual final component at source one has the original target-height bound

Every independently executing original-zero block has length bounded by
the actual original LOW target height plus one. When the final dispatcher
really appends the second factor, its actual first epsilon factor is in
the strict original gap. Its whole Reference saves the one entry needed
for that append. The bound uses the final target's original LOW height,
also when that target is not an epsilon. The sole upper guard is strict
first-grammar admission; no LOW ceiling representative is invented.
Recursive evaluation and the positive-source endpoint adapter are separate.
Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationSourceOneFinalHeight

open GlobalTrackingSequences (endpointCode TailGap)
open EvaluationRelativeCallers EvaluationFinalComponent EvaluationFinalComponent.Support
open EvaluationSourceOneFinalHeightSupport

theorem block_length_le_target (first beta : Nat) (word : List Nat)
    (ho : word ∈ blockExecute (endpointCode 0) first)
    (hb : Canonical.check beta = true)
    (hv : unionInterpretation first ≤ unionInterpretation beta)
    (hbound : unionInterpretation beta < finiteBase 1) : word.length ≤ sourceHeight beta + 1 := by
  have hs : word ∈ SourceOneRelativeAssignment.execute first := by
    simpa only [blockExecute, beq_self_eq_true, Bool.cond_true] using ho
  have hi := (SourceOneRelativeAssignment.execute_domain first).mp (Part.dom_iff_mem.mpr ⟨word, hs⟩)
  have hc := (SourceOneRelativeAssignment.inputCheck_exact first).mp hi
  have hn : SourceOneRelativeAssignment.boundaryCheck first = false := Bool.eq_false_of_not_eq_true (by
    intro ht
    have he := (SourceOneRelativeAssignment.boundaryCheck_exact first hi).mp ht
    exact (hv.trans_lt hbound).ne he)
  obtain ⟨hinput, hvalue, rawWord, hword, hout, hvalues⟩ :=
    SourceOneRelativeAssignment.execute_ordinary_source first word hs hn
  have hl := EvaluationOriginalSourceLength.source_one_assignment_length _ rawWord hword
  have hm := sourceHeight_mono first beta hc.1 hb hv hbound
  have hlength : word.length = rawWord.length := by
    rw [hout, GlobalAdditiveTracking.Return.sourceOneWord, List.length_map]
  rw [hlength]
  exact hl.trans (Nat.add_le_add_right hm 1)

theorem execute_length_bound (beta : Nat) (out : List Nat)
    (ho : out ∈ EvaluationFinalComponent.execute (endpointCode 0) beta)
    (hbound : unionInterpretation beta < finiteBase 1) : out.length ≤ sourceHeight beta + 1 := by
  have hs := (execute_clauses (endpointCode 0) beta out).mp ho
  have hinput := Bool.and_eq_true.mp hs.1
  have hbeta := (PublicTrackingSequences.principalCheck_exact beta).mp hinput.2
  rcases hs.2 with ⟨hless, rfl⟩ | ⟨hless, fs, word, hf, hw, rfl⟩
  · simp only [List.length_singleton]; omega
  · have hgt := (Canonical.less_exact _ _).mp hless
    cases fs with
    | nil => exact False.elim (factors_nonempty _ _ hinput.1 hgt.2.2 hf)
    | cons first rest =>
      have hform := factors_spec beta (first :: rest) hf
      have hfirst := first_factor_bounds (endpointCode 0) beta first rest hinput.1 hform hgt.2.2
      have hw : word ∈ blockExecute (endpointCode 0) first := by
        simpa only [EvaluationFinalComponent.firstCode, List.head?_cons, Option.getD_some] using hw
      cases ha : appendCheck (endpointCode 0) (first :: rest) with
      | false =>
        simpa only [finish, ha, Bool.cond_false] using
          block_length_le_target first beta word hw hbeta.1 hfirst.2 hbound
      | true =>
        cases rest with
        | nil => simp only [appendCheck, List.tail_cons, List.isEmpty_nil,
            Bool.not_true, Bool.false_and, Bool.false_eq_true] at ha
        | cons second rest =>
          have hflag := (appendCheck_two_exact (endpointCode 0) first second rest
            (start_checked _ hinput.1) (hform.2.1 first List.mem_cons_self)
            (hform.2.1 second (List.mem_cons_of_mem _ List.mem_cons_self))).mp ha
          have hgap : TailGap 0 [first] := ⟨
            (EvaluationProperComponentLengths.initial_floor 0).trans_lt hflag.2.1,
            (hfirst.2.trans_lt hbound).trans_eq (PublicUpsilonSegment.successor_value 0).symm⟩
          have hproper := GlobalTrackingSequences.SmallHSupport.proper_of_gap 0 first hflag.1 hgap
          have hlen := EvaluationEpsilonComponentIntervals.block_length_le_target 0 (endpointCode 0) first word
            hw hproper (EvaluationProperComponentLengths.initial_floor 0) hgap
          have hh := proper_height_le_target first beta hflag.1 hbeta.1 hfirst.2 hbound
          simpa only [finish, ha, Bool.cond_true, List.length_append, List.length_singleton] using
            Nat.add_le_add_right (hlen.trans hh) 1

end Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationSourceOneFinalHeight
