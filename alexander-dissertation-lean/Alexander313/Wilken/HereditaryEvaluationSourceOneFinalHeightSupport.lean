import Alexander313.Wilken.HereditaryEvaluationOriginalSourceLength
import Alexander313.Wilken.HereditaryEvaluationEpsilonComponentIntervals
import Alexander313.Wilken.HereditaryEvaluationProperComponentLengths

/-!
# Genuine original-zero height at every strict first-grammar target

The actual original return code gives a checked LOW value representative
strictly below the first grammar ceiling. Its canonical original height
is computed, and original LOW value order compares these heights. A real
epsilon RAW caller identifies the independently selected public initial
height with this same original height. No source code or height is supplied.
The grammar ceiling itself remains outside this LOW representation theorem.
Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationSourceOneFinalHeightSupport

open GlobalAdditiveTracking.Source (sourceOneCode sourceOneCode_primrec)
open EvaluationInitialReferenceHeight

def sourceHeight (beta : Nat) : Nat := SourceOne.CanonicalHeight.canonicalHeightCode (sourceOneCode beta)

theorem sourceHeight_primrec : Primrec sourceHeight :=
  SourceOne.CanonicalHeight.canonicalHeightCode_primrec.comp sourceOneCode_primrec

theorem source_code (beta : Nat) (hc : Canonical.check beta = true)
    (hb : unionInterpretation beta < finiteBase 1) :
    lowCheckCode 0 (sourceOneCode beta) = true ∧
      interpretation 0 (sourceOneCode beta) = unionInterpretation beta := by
  have hs := SourceZeta.Transport.returnCode_spec 0 beta hc hb
  exact ⟨((Theta.acceptedLowCode_iff 0 _).mp hs.1).1, hs.2⟩

theorem sourceHeight_mono (first beta : Nat)
    (hf : Canonical.check first = true) (hb : Canonical.check beta = true)
    (hv : unionInterpretation first ≤ unionInterpretation beta)
    (hbound : unionInterpretation beta < finiteBase 1) : sourceHeight first ≤ sourceHeight beta := by
  have hs := source_code first hf (hv.trans_lt hbound)
  have ht := source_code beta hb hbound
  have hl : SourceOne.PublicCodes.lowCheckCode (sourceOneCode first) = true := by
    simpa only [lowCheckCode_zero] using hs.1
  have hu : SourceOne.PublicCodes.lowCheckCode (sourceOneCode beta) = true := by
    simpa only [lowCheckCode_zero] using ht.1
  have he : SourceOne.PublicCodes.interpretation (sourceOneCode first) ≤
      SourceOne.PublicCodes.interpretation (sourceOneCode beta) := by
    simpa only [interpretation_zero] using hs.2.le.trans (hv.trans ht.2.ge)
  exact (SourceOne.HeightBoundary.canonicalHeightCode_le_iff_endpoint _ _ hl).mpr
    (he.trans_lt ((SourceOne.HeightBoundary.canonicalHeightCode_le_iff_endpoint _ _ hu).mp le_rfl))

theorem proper_height_le_target (first beta : Nat)
    (hf : GlobalMuDictionary.Support.inputCheck first = true)
    (hb : Canonical.check beta = true)
    (hv : unionInterpretation first ≤ unionInterpretation beta)
    (hbound : unionInterpretation beta < finiteBase 1) : initialHeight first ≤ sourceHeight beta := by
  have hi := (GlobalMuDictionary.Support.inputCheck_exact first).mp hf
  have hs := source_code first hi.1 (hv.trans_lt hbound)
  have hr : SourceOneIota.SourceTrackingRaw.Support.inputCheck (sourceOneCode first) = true :=
    (SourceOneIota.SourceTrackingRaw.Support.inputCheck_exact _).mpr ⟨hs.1,
      by rw [hs.2]; exact EpsilonOffsets.epsilon_one_lt hi.2,
      by rw [hs.2]; exact hi.2⟩
  have hp := SourceOneIota.SourceTrackingRaw.Support.publicCode_spec _ hs.1
  have he : SourceOneIota.SourceTrackingRaw.Support.publicCode (sourceOneCode first) = first :=
    Canonical.check_value_injective _ _ hp.1 hi.1 (hp.2.trans hs.2)
  have hh := EvaluationOriginalSourceLength.source_one_raw_height _ hr
  rw [he] at hh
  exact hh.le.trans (sourceHeight_mono first beta hi.1 hb hv hbound)

end Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationSourceOneFinalHeightSupport
