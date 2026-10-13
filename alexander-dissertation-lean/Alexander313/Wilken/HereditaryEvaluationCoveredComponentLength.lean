import Alexander313.Wilken.HereditaryEvaluationEpsilonComponentIntervals

/-!
# Actual covered components obey the previous proper epsilon height

At a proper previous epsilon, every ordinary real assignment lies under
its independent public mu. A nonsingleton FIRST is a genuine proper RAW
epsilon strictly above that base. Its actual public return retains the
whole tracker and independent proper prefix, so public adjacency compares
the computed original initial heights. Singleton and printed boundary
words have length one. Thus no proper-target hypothesis is needed for
the common previous-height-plus-one length bound. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationCoveredComponentLength

open NativeContext
open NativeContext.PublicEpsilonUnboundedIota
open SourceTrackingSequences (lastCode)
open EvaluationInitialReferenceHeight EvaluationReferenceHeight
open EvaluationRelativeCallers
open NativeContext.SourceAdditiveTracking.Insertion (firstCode)
open Hereditary.FinePredecessor (stripLast)

theorem assignment_length_le_previous (gamma raw : Nat) (word : List Nat)
    (hg : MuPublicDictionary.Support.inputCheck gamma = true)
    (ho : word ∈ SourceAdditiveTracking.Assignment.execute gamma raw)
    (hcover : interpretation gamma raw ≤ publicMuValue gamma) :
    (MuCoveredRelativeAssignment.publicWord gamma word).length ≤ initialHeight gamma + 1 := by
  have hglobal := ((MuPublicDictionary.Support.inputCheck_exact gamma).mp hg).1
  have hc : interpretation gamma raw ≤ GlobalTrackingSequences.muValue gamma := by
    simpa only [GlobalTrackingSequences.muValue, GlobalMuDictionary.publicCode_proper gamma hg,
      publicMuValue] using hcover
  have ht := CoveredPublicMu.assignment_tracking gamma raw word hglobal ho hc
  cases word with
  | nil => exact False.elim (SourceAdditiveTracking.Assignment.execute_nonempty gamma raw [] ho rfl)
  | cons first rest =>
    cases rest with
    | nil => simp only [MuCoveredRelativeAssignment.publicWord, List.length_map, List.length_singleton]; omega
    | cons next rest =>
      have hraw := (SourceTrackingRaw.trackingCheck_conditions gamma _).mp
        (SourceAdditiveTracking.Assignment.execute_tracking gamma raw _ ho)
      have hmem : first ∈ stripLast (first :: next :: rest) := by
        rw [SkTracking.Support.stripLast_cons_nonempty first _ (List.cons_ne_nil _ _)]
        exact List.mem_cons_self
      have he := (SourceTrackingRaw.Support.inputCheck_exact gamma first).mp (hraw.2.1.nodes first hmem)
      have hp := UniformPublicReturn.publicCode_spec gamma first
        ((UniformPublicReturn.inputCheck_exact gamma first).mpr he.1)
      have hproper : MuPublicDictionary.Support.inputCheck (UniformPublicReturn.publicCode gamma first) = true := by
        apply ht.2.2.1.nodes
        rw [MuCoveredRelativeAssignment.publicWord, List.map_cons, List.map_cons,
          SkTracking.Support.stripLast_cons_nonempty _ _ (List.cons_ne_nil _ _)]
        exact List.mem_cons_self
      have hgt : unionInterpretation gamma < unionInterpretation (UniformPublicReturn.publicCode gamma first) := by
        rw [hp.2]
        exact he.2.1
      have hub : unionInterpretation (UniformPublicReturn.publicCode gamma first) ≤ publicMuValue gamma := by
        rw [hp.2]
        exact ((SourceAdditiveTracking.Assignment.execute_spec gamma raw _ ho).2.1.2.1
          first List.mem_cons_self).trans hcover
      have hheight := EvaluationInitialHeightCoveredMonotonicity.adjacency_monotone gamma
        (UniformPublicReturn.publicCode gamma first) hg hp.1
        ((MuPublicDictionary.Support.inputCheck_image _).mp hproper).2.1 hgt hub
      have hlen := EvaluationComponentReferenceLength.tracking_length_le_firstCode _ ht
      have hlen' : (MuCoveredRelativeAssignment.publicWord gamma (first :: next :: rest)).length ≤
          initialHeight (UniformPublicReturn.publicCode gamma first) + 1 := by
        simpa only [MuCoveredRelativeAssignment.publicWord, List.map_cons, firstCode,
          List.head?_cons, Option.getD_some] using hlen
      exact hlen'.trans (Nat.add_le_add_right hheight 1)

theorem execute_length_le_previous (gamma beta : Nat) (out : List Nat)
    (hg : MuPublicDictionary.Support.inputCheck gamma = true)
    (ho : out ∈ MuCoveredRelativeAssignment.execute gamma beta) :
    out.length ≤ initialHeight gamma + 1 := by
  have hs := (MuCoveredRelativeAssignment.execute_clauses gamma beta out).mp ho
  have hi := (MuCoveredRelativeAssignment.Support.inputCheck_exact gamma beta).mp hs.1
  rcases hs.2 with ⟨hboundary, rfl⟩ | ⟨hboundary, raw, word, hraw, hw, rfl⟩
  · simp only [List.length_singleton]; omega
  · have hcover : interpretation gamma raw ≤ publicMuValue gamma := by
      rw [(SkNextSearch.Support.search_spec gamma beta raw hraw).2.2.2]
      simpa only [GlobalTrackingSequences.muValue, GlobalMuDictionary.publicCode_proper gamma hg,
        publicMuValue] using hi.2.2.2.2.2
    exact assignment_length_le_previous gamma raw word hg hw hcover

theorem block_length_le_previous (gamma beta : Nat) (out : List Nat)
    (hg : MuPublicDictionary.Support.inputCheck gamma = true)
    (ho : out ∈ blockExecute gamma beta) : out.length ≤ initialHeight gamma + 1 := by
  have hglobal := ((MuPublicDictionary.Support.inputCheck_exact gamma).mp hg).1
  have he := epsilon_not_initial gamma hglobal
  apply execute_length_le_previous gamma beta out hg
  simpa only [blockExecute, he, Bool.cond_false] using ho

end Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationCoveredComponentLength
