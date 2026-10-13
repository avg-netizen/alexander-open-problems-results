import Alexander313.Wilken.HereditaryEvaluationEpsilonComponentReferenceSupport
import Alexander313.Wilken.HereditaryMuCoveredRelativePublicFidelity
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingProperPrefix

/-!
# Whole references of actual covered epsilon assignments

An independently executing native assignment at an epsilon input really
takes the multiplicative leaf branch. Its unchanged FINAL and genuine
proper-prefix interval derive strictness of the whole emitted word. The
actual covered public return supplies every independent public mu edge.
Its canonical FINAL is the literal public epsilon target. Thus the actual
covered relative epsilon component has a complete proper Reference, without
an externally supplied strictness, reference or final-entry certificate.
Common component height and the final second-factor append are separate.
Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationEpsilonComponentReference

open NativeContext
open NativeContext.PublicEpsilonUnboundedIota
open SourceTrackingSequences (lastCode lastCode_append_singleton)
open Hereditary.FinePredecessor (stripLast stripLast_split)
open GlobalAdditiveTracking.RelativeCertificate (lastCode_map)

theorem native_epsilon_word (q raw : Nat) (word : List Nat)
    (ho : word ∈ SourceAdditiveTracking.Assignment.execute q raw)
    (he : Ordinal.omega0 ^ interpretation q raw = interpretation q raw) :
    (word.map (interpretation q)).Pairwise (· < ·) ∧ lastCode word = raw := by
  have hi := (SourceAdditiveTracking.Assignment.inputCheck_exact q raw).mp
    (SourceAdditiveTracking.Assignment.execute_spec q raw word ho).1
  have hm : SourceMultiplicativePrincipal.inputCheck q raw = true :=
    (SourceMultiplicativePrincipal.inputCheck_exact q raw).mpr
      ⟨hi.1, hi.2.1, SourceMultiplicativePrincipal.epsilon_multiplicative _ he⟩
  have hw : word = SourceMultiplicativeTracking.rawWord q raw :=
    Part.mem_unique ho (SourceAdditiveTracking.Assignment.execute_multiplicative q raw hm)
  have hl : lastCode word = raw := by rw [hw]; exact SourceMultiplicativeTracking.rawWord_last q raw
  have ht := (SourceTrackingRaw.trackingCheck_conditions q word).mp
    (SourceAdditiveTracking.Assignment.execute_tracking q raw word ho)
  obtain ⟨last, hs, hmem⟩ := stripLast_split word ht.1
  have hlast : last = raw := by
    calc
      last = lastCode word := by rw [hs, lastCode_append_singleton]
      _ = raw := hl
  refine ⟨?_, hl⟩
  rw [hs, List.map_append, List.map_singleton]
  apply List.pairwise_append.mpr
  refine ⟨ht.2.1.strict, List.pairwise_singleton _ _, ?_⟩
  intro x hx y hy
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
  rw [List.mem_singleton.mp hy, hlast]
  exact (SourceAdditiveTracking.ProperPrefix.execute_prefix_interval q raw word ho d hd).2.2.2

theorem assignment_reference (gamma beta raw : Nat) (word : List Nat)
    (hg : GlobalMuDictionary.Support.inputCheck gamma = true)
    (hb : MuPublicDictionary.Support.inputCheck beta = true)
    (ho : word ∈ SourceAdditiveTracking.Assignment.execute gamma raw)
    (hv : interpretation gamma raw = unionInterpretation beta)
    (hcover : unionInterpretation beta ≤ GlobalTrackingSequences.muValue gamma) :
    PublicTrackingSequences.Reference (MuCoveredRelativeAssignment.publicWord gamma word) := by
  have hbeta := (MuPublicDictionary.Support.inputCheck_image beta).mp hb
  have he : Ordinal.omega0 ^ interpretation gamma raw = interpretation gamma raw := by
    rw [hv]; exact hbeta.2.1
  have hw := native_epsilon_word gamma raw word ho he
  have ht := CoveredPublicMu.assignment_tracking gamma raw word hg ho
    (hv.le.trans hcover)
  have hp := MuCoveredRelativeAssignment.publicWord_spec gamma raw word ho
  have hi := (SourceAdditiveTracking.Assignment.inputCheck_exact gamma raw).mp
    (SourceAdditiveTracking.Assignment.execute_spec gamma raw word ho).1
  have hr := UniformPublicReturn.publicCode_spec gamma raw
    ((UniformPublicReturn.inputCheck_exact gamma raw).mpr hi.1)
  have hc : UniformPublicReturn.publicCode gamma raw = beta :=
    Canonical.check_value_injective _ _ hr.1 hbeta.1 (hr.2.trans hv)
  have hlast : lastCode (MuCoveredRelativeAssignment.publicWord gamma word) = beta := by
    rw [MuCoveredRelativeAssignment.publicWord,
      lastCode_map _ word (SourceAdditiveTracking.Assignment.execute_nonempty gamma raw word ho), hw.2, hc]
  apply EvaluationEpsilonComponentReferenceSupport.tracking_whole_reference _ ht
  · rw [hp.2.2]; exact hw.1
  · rw [hlast]; exact hb

theorem covered_execute_reference (gamma beta : Nat) (out : List Nat)
    (ho : out ∈ MuCoveredRelativeAssignment.execute gamma beta)
    (hb : MuPublicDictionary.Support.inputCheck beta = true) :
    PublicTrackingSequences.Reference out := by
  have hs := (MuCoveredRelativeAssignment.execute_clauses gamma beta out).mp ho
  have hi := (MuCoveredRelativeAssignment.Support.inputCheck_exact gamma beta).mp hs.1
  rcases hs.2 with ⟨hboundary, rfl⟩ | ⟨hboundary, raw, word, hr, hw, rfl⟩
  · exact .one beta hb
  · exact assignment_reference gamma beta raw word hi.1 hb hw
      (SkNextSearch.Support.search_spec gamma beta raw hr).2.2.2 hi.2.2.2.2.2

end Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationEpsilonComponentReference
