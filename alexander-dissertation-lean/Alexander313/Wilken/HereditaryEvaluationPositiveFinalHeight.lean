import Alexander313.Wilken.HereditaryEvaluationPositiveFinalHeightSupport
import Alexander313.Wilken.HereditaryEvaluationEpsilonComponentIntervals
import Alexander313.Wilken.HereditaryEvaluationProperComponentLengths

/-!
# Actual positive-endpoint final component uses the original target height

The actual covered dispatcher and RAW assignment derive the proper FIRST
of every nonsingleton ordinary component. Its literal public value lies
strictly above the endpoint and below the real target. The computed native
finite-source return bounds its height. If the final dispatcher appends its
actual second factor, the first epsilon component is a whole Reference,
saving exactly the extra entry. Arbitrary final principals are included;
the strict upper ceiling guard is explicit. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationPositiveFinalHeight

open NativeContext NativeContext.PublicEpsilonUnboundedIota
open GlobalTrackingSequences (endpointCode TailGap)
open EvaluationRelativeCallers EvaluationFinalComponent EvaluationFinalComponent.Support
open EvaluationPositiveFinalHeightSupport
open Hereditary.FinePredecessor (stripLast)

theorem block_length_le_target (s first beta : Nat) (out : List Nat)
    (ho : out ∈ blockExecute (endpointCode (s + 1)) first)
    (hb : Canonical.check beta = true)
    (hv : unionInterpretation first ≤ unionInterpretation beta)
    (hbound : unionInterpretation beta < finiteBase ((s + 1) + 1)) :
    out.length ≤ sourceHeight s beta + 1 := by
  let gamma := endpointCode (s + 1)
  have hg := GlobalMuDictionary.Support.endpoint_input s
  have hn := epsilon_not_initial gamma hg
  have hs : out ∈ MuCoveredRelativeAssignment.execute gamma first := by
    simpa only [blockExecute, hn, Bool.cond_false] using ho
  have ht := EvaluationBlocks.block_tracking gamma first out ho
  have hc := (MuCoveredRelativeAssignment.execute_clauses gamma first out).mp hs
  rcases hc.2 with ⟨hboundary, rfl⟩ | ⟨hboundary, raw, word, hraw, hw, rfl⟩
  · simp only [List.length_singleton]; omega
  · cases word with
    | nil => exact False.elim (SourceAdditiveTracking.Assignment.execute_nonempty gamma raw [] hw rfl)
    | cons front rest =>
      cases rest with
      | nil => simp only [MuCoveredRelativeAssignment.publicWord, List.length_map,
          List.length_singleton]; omega
      | cons next rest =>
        have htracker := SourceAdditiveTracking.Assignment.execute_tracking gamma raw _ hw
        have hconditions := (SourceTrackingRaw.trackingCheck_conditions gamma _).mp htracker
        have hmem : front ∈ stripLast (front :: next :: rest) := by
          rw [SkTracking.Support.stripLast_cons_nonempty front _ (List.cons_ne_nil _ _)]
          exact List.mem_cons_self
        have hfront := (SourceTrackingRaw.Support.inputCheck_exact gamma front).mp
          (hconditions.2.1.nodes front hmem)
        have hp := UniformPublicReturn.publicCode_spec gamma front
          ((UniformPublicReturn.inputCheck_exact gamma front).mpr hfront.1)
        have hfloor : finiteBase (s + 1) <
            unionInterpretation (UniformPublicReturn.publicCode gamma front) := by
          rw [hp.2]
          simpa only [gamma, base, PublicEpsilonSourceDictionary.endpointCode_value] using hfront.2.1
        have hupper : unionInterpretation (UniformPublicReturn.publicCode gamma front) ≤
            unionInterpretation beta := by
          rw [hp.2]
          exact (((SourceAdditiveTracking.Assignment.execute_spec gamma raw _ hw).2.1.2.1
            front List.mem_cons_self).trans_eq
              ((SkNextSearch.Support.search_spec gamma first raw hraw).2.2.2)).trans hv
        have hh := proper_height_le_target s _ beta hp.1
          (by rw [hp.2]; exact hfront.2.2) hfloor hb hupper hbound
        have hlen := EvaluationComponentReferenceLength.tracking_length_le_firstCode _ ht
        have hlen' : (MuCoveredRelativeAssignment.publicWord gamma (front :: next :: rest)).length ≤
            EvaluationInitialReferenceHeight.initialHeight
              (UniformPublicReturn.publicCode gamma front) + 1 := by
          simpa only [MuCoveredRelativeAssignment.publicWord, List.map_cons,
            SourceAdditiveTracking.Insertion.firstCode, List.head?_cons, Option.getD_some] using hlen
        exact hlen'.trans (Nat.add_le_add_right hh 1)

theorem execute_length_bound (s beta : Nat) (out : List Nat)
    (ho : out ∈ EvaluationFinalComponent.execute (endpointCode (s + 1)) beta)
    (hbound : unionInterpretation beta < finiteBase ((s + 1) + 1)) :
    out.length ≤ sourceHeight s beta + 1 := by
  have hs := (execute_clauses (endpointCode (s + 1)) beta out).mp ho
  have hinput := Bool.and_eq_true.mp hs.1
  have hbeta := (PublicTrackingSequences.principalCheck_exact beta).mp hinput.2
  rcases hs.2 with ⟨hless, rfl⟩ | ⟨hless, fs, word, hf, hw, rfl⟩
  · simp only [List.length_singleton]; omega
  · have hgt := (Canonical.less_exact _ _).mp hless
    cases fs with
    | nil => exact False.elim (factors_nonempty _ _ hinput.1 hgt.2.2 hf)
    | cons first rest =>
      have hform := factors_spec beta (first :: rest) hf
      have hfirst := first_factor_bounds (endpointCode (s + 1)) beta first rest hinput.1 hform hgt.2.2
      have hw : word ∈ blockExecute (endpointCode (s + 1)) first := by
        simpa only [EvaluationFinalComponent.firstCode, List.head?_cons, Option.getD_some] using hw
      cases ha : appendCheck (endpointCode (s + 1)) (first :: rest) with
      | false =>
        simpa only [finish, ha, Bool.cond_false] using
          block_length_le_target s first beta word hw hbeta.1 hfirst.2 hbound
      | true =>
        cases rest with
        | nil => simp only [appendCheck, List.tail_cons, List.isEmpty_nil,
            Bool.not_true, Bool.false_and, Bool.false_eq_true] at ha
        | cons second rest =>
          have hflag := (appendCheck_two_exact (endpointCode (s + 1)) first second rest
            (start_checked _ hinput.1) (hform.2.1 first List.mem_cons_self)
            (hform.2.1 second (List.mem_cons_of_mem _ List.mem_cons_self))).mp ha
          have hgap : TailGap (s + 1) [first] := ⟨
            (EvaluationProperComponentLengths.initial_floor (s + 1)).trans_lt hflag.2.1,
            (hfirst.2.trans_lt hbound).trans_eq (PublicUpsilonSegment.successor_value (s + 1)).symm⟩
          have hproper := GlobalTrackingSequences.SmallHSupport.proper_of_gap (s + 1) first hflag.1 hgap
          have hlen := EvaluationEpsilonComponentIntervals.block_length_le_target (s + 1)
            (endpointCode (s + 1)) first word hw hproper
            (EvaluationProperComponentLengths.initial_floor (s + 1)) hgap
          have hfloor : finiteBase (s + 1) < unionInterpretation first := by
            simpa only [PublicEpsilonSourceDictionary.endpointCode_value] using hflag.2.1
          have hh := proper_height_le_target s first beta (hform.2.1 first List.mem_cons_self)
            ((GlobalMuDictionary.Support.inputCheck_exact first).mp hflag.1).2
            hfloor hbeta.1 hfirst.2 hbound
          simpa only [finish, ha, Bool.cond_true, List.length_append, List.length_singleton] using
            Nat.add_le_add_right (hlen.trans hh) 1

end Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationPositiveFinalHeight
