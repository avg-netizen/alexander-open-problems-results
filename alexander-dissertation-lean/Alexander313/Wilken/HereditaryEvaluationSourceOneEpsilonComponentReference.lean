import Alexander313.Wilken.HereditaryEvaluationEpsilonComponentReferenceSupport
import Alexander313.Wilken.HereditarySourceOneRelativeAssignment
import Alexander313.Wilken.SourceOneNativeAdditiveTrackingProperPrefix
import Alexander313.Wilken.PublicEpsilonNativeMultiplicativePrincipal

/-!
# Whole epsilon references of the actual initial source-one assignment

The literal initial base one uses the original check-zero grammar. Its
actual epsilon assignment takes the genuine multiplicative leaf, whose
unchanged FINAL and real proper-prefix interval derive whole strictness.
The independently executing public return preserves the whole value word
and has literal canonical FINAL beta. Actual public Tracking then appends
that independently proper epsilon FINAL to the complete reference.
No Native base-one grammar, supplied strictness or reference is used.
Common height and the final second-factor append remain separate.
Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationSourceOneEpsilonComponentReference

open NativeContext.SourceTrackingSequences (lastCode lastCode_append_singleton)
open Hereditary.FinePredecessor (stripLast stripLast_split)
open GlobalAdditiveTracking.RelativeCertificate (lastCode_map)

theorem epsilon_word (raw : Nat) (word : List Nat)
    (ho : word ∈ SourceOneIota.SourceAdditiveTracking.Assignment.execute raw)
    (he : Ordinal.omega0 ^ interpretation 0 raw = interpretation 0 raw) :
    (word.map (interpretation 0)).Pairwise (· < ·) ∧ lastCode word = raw := by
  have hi := (SourceOneIota.SourceAdditiveTracking.Assignment.inputCheck_exact raw).mp
    (SourceOneIota.SourceAdditiveTracking.Assignment.execute_spec raw word ho).1
  have hm : SourceOneIota.SourceMultiplicativePrincipal.inputCheck raw = true :=
    (SourceOneIota.SourceMultiplicativePrincipal.inputCheck_exact raw).mpr
      ⟨hi.1, hi.2.1,
        NativeContext.SourceMultiplicativePrincipal.epsilon_multiplicative _ he⟩
  have hw : word = SourceOneIota.SourceMultiplicativeTracking.rawWord raw :=
    Part.mem_unique ho (SourceOneIota.SourceAdditiveTracking.Assignment.execute_multiplicative raw hm)
  have hl : lastCode word = raw := by
    rw [hw]; exact SourceOneIota.SourceMultiplicativeTracking.rawWord_last raw
  have ht := (SourceOneIota.SourceTrackingRaw.trackingCheck_exact word).mp
    (SourceOneIota.SourceAdditiveTracking.Assignment.execute_tracking raw word ho)
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
  exact (SourceOneIota.SourceAdditiveTracking.ProperPrefix.execute_prefix_interval raw word ho d hd).2.2.2

theorem execute_reference (beta : Nat) (out : List Nat)
    (ho : out ∈ SourceOneRelativeAssignment.execute beta)
    (hb : MuPublicDictionary.Support.inputCheck beta = true) :
    PublicTrackingSequences.Reference out := by
  have hc := (SourceOneRelativeAssignment.execute_clauses beta out).mp ho
  rcases hc.2 with ⟨hboundary, rfl⟩ | ⟨hboundary, hreturn⟩
  · exact .one beta hb
  · obtain ⟨hchecked, hv, word, hw, hout, hvalues⟩ :=
      SourceOneRelativeAssignment.execute_ordinary_source beta out ho hboundary
    have hbeta := (MuPublicDictionary.Support.inputCheck_image beta).mp hb
    have he : Ordinal.omega0 ^ interpretation 0 (GlobalAdditiveTracking.Source.sourceOneCode beta) =
        interpretation 0 (GlobalAdditiveTracking.Source.sourceOneCode beta) := by
      rw [hv]; exact hbeta.2.1
    have hs := epsilon_word _ word hw he
    have hi := (SourceOneIota.SourceAdditiveTracking.Assignment.inputCheck_exact _).mp
      (SourceOneIota.SourceAdditiveTracking.Assignment.execute_spec _ word hw).1
    have hp := SourceOneIota.SourceTrackingRaw.Support.publicCode_spec _ hi.1
    have hfinal : SourceOneIota.SourceTrackingRaw.Support.publicCode
        (GlobalAdditiveTracking.Source.sourceOneCode beta) = beta :=
      Canonical.check_value_injective _ _ hp.1 hbeta.1 (hp.2.trans hv)
    have hlast : lastCode out = beta := by
      rw [hout, GlobalAdditiveTracking.Return.sourceOneWord,
        lastCode_map _ word (SourceOneIota.SourceAdditiveTracking.Assignment.execute_nonempty _ word hw),
        hs.2, hfinal]
    apply EvaluationEpsilonComponentReferenceSupport.tracking_whole_reference out
      (SourceOneRelativeAssignment.execute_tracking beta out ho)
    · rw [hvalues]; exact hs.1
    · rw [hlast]; exact hb

end Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationSourceOneEpsilonComponentReference
