import Alexander313.Wilken.HereditaryEvaluationSourceOneEpsilonComponentReference
import Alexander313.Wilken.HereditaryEvaluationEpsilonComponentReference
import Alexander313.Wilken.HereditaryEvaluationInitialHeightSameLevelMonotonicity
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingInsertionFidelitySupport

/-!
# The real epsilon component lies in its target's original finite gap

The actual literal previous-base assignment derives its complete proper
Reference and bounds its FIRST between that previous base and its target.
Original check-zero returns and native returns are treated independently.
Proper FIRST excludes equality with the source upsilon floor. Consequently
the real target gap and real previous-base floor put FIRST in that same gap.
Genuine same-source canonical-height monotonicity bounds its whole length
by the computed initial height of its actual target, with no extra one.
No source-level, FIRST interval, reference or height estimate is an input
to the actual block interval theorem. Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationEpsilonComponentIntervals

open EvaluationRelativeCallers GlobalTrackingSequences
open EvaluationInitialReferenceHeight
open NativeContext.SourceAdditiveTracking.Insertion (firstCode)

theorem block_reference (gamma beta : Nat) (word : List Nat)
    (ho : word ∈ blockExecute gamma beta)
    (hb : MuPublicDictionary.Support.inputCheck beta = true) :
    PublicTrackingSequences.Reference word := by
  cases he : (gamma == endpointCode 0) with
  | true =>
    exact EvaluationSourceOneEpsilonComponentReference.execute_reference beta word
      (by simpa only [blockExecute, he, Bool.cond_true] using ho) hb
  | false =>
    exact EvaluationEpsilonComponentReference.covered_execute_reference gamma beta word
      (by simpa only [blockExecute, he, Bool.cond_false] using ho) hb

theorem native_assignment_first_bounds (gamma raw : Nat) (word : List Nat)
    (ho : word ∈ NativeContext.SourceAdditiveTracking.Assignment.execute gamma raw) :
    unionInterpretation gamma ≤
        unionInterpretation (firstCode (MuCoveredRelativeAssignment.publicWord gamma word)) ∧
      unionInterpretation (firstCode (MuCoveredRelativeAssignment.publicWord gamma word)) ≤
        NativeContext.interpretation gamma raw := by
  have ht := NativeContext.SourceAdditiveTracking.Assignment.execute_tracking gamma raw word ho
  cases word with
  | nil => exact False.elim
      (NativeContext.SourceAdditiveTracking.Assignment.execute_nonempty gamma raw [] ho rfl)
  | cons first rest =>
    have hl := GlobalAdditiveTracking.Return.native_word_low gamma (first :: rest) ht
      first List.mem_cons_self
    have hp := NativeContext.UniformPublicReturn.publicCode_spec gamma first
      ((NativeContext.UniformPublicReturn.inputCheck_exact gamma first).mpr hl)
    have hfloor := NativeContext.SourceAdditiveTracking.InsertionFidelitySupport.tracking_first_ge_base
      gamma first rest ht
    have hupper := (NativeContext.SourceAdditiveTracking.Assignment.execute_spec gamma raw _ ho).2.1.2.1
      first List.mem_cons_self
    change unionInterpretation gamma ≤ NativeContext.interpretation gamma first at hfloor
    simpa only [MuCoveredRelativeAssignment.publicWord, List.map_cons, firstCode,
      List.head?_cons, Option.getD_some, hp.2] using And.intro hfloor hupper

theorem source_one_first_le (beta : Nat) (word : List Nat)
    (ho : word ∈ SourceOneRelativeAssignment.execute beta) :
    unionInterpretation (firstCode word) ≤ unionInterpretation beta := by
  have hc := (SourceOneRelativeAssignment.execute_clauses beta word).mp ho
  rcases hc.2 with ⟨hboundary, rfl⟩ | ⟨hboundary, hreturn⟩
  · simp only [firstCode, List.head?_cons, Option.getD_some]; exact le_rfl
  · obtain ⟨hchecked, hv, rawWord, hw, hout, hvalues⟩ :=
      SourceOneRelativeAssignment.execute_ordinary_source beta word ho hboundary
    cases rawWord with
    | nil => exact False.elim
        (SourceOneIota.SourceAdditiveTracking.Assignment.execute_nonempty _ [] hw rfl)
    | cons first rest =>
      have hl := GlobalAdditiveTracking.Return.source_one_word_low (first :: rest)
        (SourceOneIota.SourceAdditiveTracking.Assignment.execute_tracking _ _ hw)
        first List.mem_cons_self
      have hp := SourceOneIota.SourceTrackingRaw.Support.publicCode_spec first hl
      have hupper := SourceOneIota.SourceAdditiveTracking.Assignment.execute_all_bounds _ _ hw
        first List.mem_cons_self
      rw [hout, GlobalAdditiveTracking.Return.sourceOneWord, List.map_cons,
        firstCode, List.head?_cons, Option.getD_some, hp.2]
      exact hupper.trans_eq hv

/-- These actual FIRST bounds retain both independent original returns;
the proper target guard derives the whole Reference internally. -/
theorem block_first_bounds (gamma beta : Nat) (word : List Nat)
    (ho : word ∈ blockExecute gamma beta)
    (hb : MuPublicDictionary.Support.inputCheck beta = true) :
    unionInterpretation gamma ≤ unionInterpretation (firstCode word) ∧
      unionInterpretation (firstCode word) ≤ unionInterpretation beta := by
  cases he : (gamma == endpointCode 0) with
  | true =>
    have hs : word ∈ SourceOneRelativeAssignment.execute beta := by
      simpa only [blockExecute, he, Bool.cond_true] using ho
    have hr := block_reference gamma beta word ho hb
    have hn := EvaluationBlocks.block_tracking gamma beta word ho
    have hg : gamma = endpointCode 0 := beq_iff_eq.mp he
    have hf : MuPublicDictionary.Support.inputCheck (firstCode word) = true := by
      cases word with
      | nil => exact False.elim (hn.1 rfl)
      | cons first rest =>
        simpa only [firstCode, List.head?_cons, Option.getD_some] using hr.nodes first List.mem_cons_self
    have hp := EpsilonOffsets.epsilon_one_lt ((MuPublicDictionary.Support.inputCheck_image _).mp hf).2.1
    refine ⟨?_, source_one_first_le beta word hs⟩
    simpa only [hg, PublicEpsilonSourceDictionary.endpointCode_value, finiteBase_zero] using hp.le
  | false =>
    have hs : word ∈ MuCoveredRelativeAssignment.execute gamma beta := by
      simpa only [blockExecute, he, Bool.cond_false] using ho
    have hc := (MuCoveredRelativeAssignment.execute_clauses gamma beta word).mp hs
    have hi := (MuCoveredRelativeAssignment.Support.inputCheck_exact gamma beta).mp hc.1
    rcases hc.2 with ⟨hboundary, rfl⟩ | ⟨hboundary, raw, rawWord, hraw, hw, rfl⟩
    · simpa only [firstCode, List.head?_cons, Option.getD_some] using
        And.intro hi.2.2.2.2.1 (le_refl (unionInterpretation beta))
    · have hbounds := native_assignment_first_bounds gamma raw rawWord hw
      exact ⟨hbounds.1, hbounds.2.trans_eq
        (NativeContext.PublicEpsilonUnboundedIota.SkNextSearch.Support.search_spec gamma beta raw hraw).2.2.2⟩

theorem block_first_gap (m gamma beta : Nat) (word : List Nat)
    (ho : word ∈ blockExecute gamma beta)
    (hb : MuPublicDictionary.Support.inputCheck beta = true)
    (hfloor : sourceUpsilon (m : Ordinal.{0}) ≤ unionInterpretation gamma)
    (hgap : TailGap m [beta]) :
    TailGap m [firstCode word] ∧ MuPublicDictionary.Support.inputCheck (firstCode word) = true := by
  have hr := block_reference gamma beta word ho hb
  have ht := EvaluationBlocks.block_tracking gamma beta word ho
  have hf : MuPublicDictionary.Support.inputCheck (firstCode word) = true := by
    cases word with
    | nil => exact False.elim (ht.1 rfl)
    | cons first rest =>
      simpa only [firstCode, List.head?_cons, Option.getD_some] using hr.nodes first List.mem_cons_self
  have hbounds := block_first_bounds gamma beta word ho hb
  have hproper := (MuPublicDictionary.Support.inputCheck_image _).mp hf
  have hlt : sourceUpsilon (m : Ordinal.{0}) < unionInterpretation (firstCode word) := by
    apply lt_of_le_of_ne (hfloor.trans hbounds.1)
    intro heq
    exact hproper.2.2 ⟨(m : Ordinal.{0}), heq.symm⟩
  exact ⟨⟨hlt, hbounds.2.trans_lt hgap.2⟩, hf⟩

theorem block_length_le_target (m gamma beta : Nat) (word : List Nat)
    (ho : word ∈ blockExecute gamma beta)
    (hb : MuPublicDictionary.Support.inputCheck beta = true)
    (hfloor : sourceUpsilon (m : Ordinal.{0}) ≤ unionInterpretation gamma)
    (hgap : TailGap m [beta]) : word.length ≤ initialHeight beta := by
  have hr := block_reference gamma beta word ho hb
  have ht := EvaluationBlocks.block_tracking gamma beta word ho
  have hf := block_first_gap m gamma beta word ho hb hfloor hgap
  have hh := EvaluationInitialHeightSameLevelMonotonicity.initialHeight_mono_in_gap m _ beta
    hf.2 hb hf.1 hgap (block_first_bounds gamma beta word ho hb).2
  have hl : word.length ≤ initialHeight (firstCode word) := by
    cases word with
    | nil => exact False.elim (ht.1 rfl)
    | cons first rest =>
      simpa only [firstCode, List.head?_cons, Option.getD_some] using reference_length_le first rest hr
  exact hl.trans hh

end Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationEpsilonComponentIntervals
