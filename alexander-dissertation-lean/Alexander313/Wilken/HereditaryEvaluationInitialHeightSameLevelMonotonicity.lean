import Alexander313.Wilken.HereditaryEvaluationInitialHeightPublicAgreement
import Alexander313.Wilken.HereditaryEvaluationInitialHeightCoveredMonotonicity

/-!
# Actual initial height is monotone within the genuine selected finite gap

The original dictionary gives accepted LOW HIGH representatives of both
proper public epsilons. When its computed source levels agree, genuine
LOW canonical-height monotonicity compares those original representatives.
Their actual Normal heights are exactly the independently computed initial
heights. A real strict finite gap supplies the source-level equality.
No global value-height monotonicity across changing sources is asserted.
Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationInitialHeightSameLevelMonotonicity

open NativeContext
open NativeContext.PublicEpsilonUnboundedIota
open EvaluationInitialReferenceHeight

theorem initialHeight_mono_same_level (gamma beta : Nat)
    (hg : MuPublicDictionary.Support.inputCheck gamma = true)
    (hb : MuPublicDictionary.Support.inputCheck beta = true)
    (hlevel : PublicEpsilonSourceDictionary.level beta = PublicEpsilonSourceDictionary.level gamma)
    (hv : unionInterpretation gamma ≤ unionInterpretation beta) :
    initialHeight gamma ≤ initialHeight beta := by
  by_cases hl : PublicEpsilonSourceDictionary.level gamma = 0
  · have hlb := hlevel.trans hl
    have ha := MuPublicDictionary.Support.source_one_root gamma hg hl
    have hc := MuPublicDictionary.Support.source_one_root beta hb hlb
    have halow : SourceOne.PublicCodes.lowCheckCode
        (PublicEpsilonSourceDictionary.sourceRootCode gamma) = true := by
      simpa only [lowCheckCode_zero] using SourceOneIota.root_low _ ha.1
    have hblow : SourceOne.PublicCodes.lowCheckCode
        (PublicEpsilonSourceDictionary.sourceRootCode beta) = true := by
      simpa only [lowCheckCode_zero] using SourceOneIota.root_low _ hc.1
    have hbound := (SourceOne.HeightBoundary.canonicalHeightCode_le_iff_endpoint _ _ hblow).mp le_rfl
    have hvalue : SourceOne.PublicCodes.interpretation
        (PublicEpsilonSourceDictionary.sourceRootCode gamma) ≤
      SourceOne.PublicCodes.interpretation (PublicEpsilonSourceDictionary.sourceRootCode beta) := by
      simpa only [interpretation_zero] using ha.2.le.trans (hv.trans hc.2.ge)
    have hm := (SourceOne.HeightBoundary.canonicalHeightCode_le_iff_endpoint _ _ halow).mpr
      (hvalue.trans_lt hbound)
    rw [SourceOne.CanonicalHeight.canonicalHeightCode_normal _
      (SourceOneIota.HeightSupport.root_source_accepted _ ha.1),
      SourceOne.CanonicalHeight.canonicalHeightCode_normal _
        (SourceOneIota.HeightSupport.root_source_accepted _ hc.1)] at hm
    simpa only [initialHeight, hl, hlb, beq_self_eq_true, Bool.cond_true] using hm
  · have hlb : PublicEpsilonSourceDictionary.level beta ≠ 0 := by
      rw [hlevel]; exact hl
    have ha := MuPublicDictionary.Support.native_root gamma hg hl
    have hc := MuPublicDictionary.Support.native_root beta hb hlb
    have hq : MuPublicDictionary.Support.nativeContext beta =
        MuPublicDictionary.Support.nativeContext gamma := by
      simp only [MuPublicDictionary.Support.nativeContext,
        PublicEpsilonSourceDictionary.sourceIndex, hlevel]
    have hroot : Mu.inputCheck (MuPublicDictionary.Support.nativeContext gamma)
        (MuPublicDictionary.Support.nativeRoot beta) = true := by
      simpa only [hq] using hc.1
    have hvalue : interpretation (MuPublicDictionary.Support.nativeContext gamma)
        (MuPublicDictionary.Support.nativeRoot gamma) ≤
      interpretation (MuPublicDictionary.Support.nativeContext gamma)
        (MuPublicDictionary.Support.nativeRoot beta) := by
      have hbvalue : interpretation (MuPublicDictionary.Support.nativeContext gamma)
          (MuPublicDictionary.Support.nativeRoot beta) = unionInterpretation beta := by
        simpa only [hq] using hc.2
      rw [ha.2, hbvalue]
      exact hv
    have hm := Mu.HeightSupport.canonicalHeightCode_mono_low _ _ _
      (root_low _ _ ha.1) (root_low _ _ hroot) hvalue
    rw [CanonicalHeight.canonicalHeightCode_normal _ _ (RootLowCollapse.root_accepted _ _ ha.1),
      CanonicalHeight.canonicalHeightCode_normal _ _ (RootLowCollapse.root_accepted _ _ hroot)] at hm
    simpa only [initialHeight, beq_eq_false_iff_ne.mpr hl,
      beq_eq_false_iff_ne.mpr hlb, Bool.cond_false] using hm

theorem initialHeight_mono_in_gap (m gamma beta : Nat)
    (hg : MuPublicDictionary.Support.inputCheck gamma = true)
    (hb : MuPublicDictionary.Support.inputCheck beta = true)
    (hggap : GlobalTrackingSequences.TailGap m [gamma])
    (hbgap : GlobalTrackingSequences.TailGap m [beta])
    (hv : unionInterpretation gamma ≤ unionInterpretation beta) :
    initialHeight gamma ≤ initialHeight beta := by
  have hgl := GlobalTrackingSequences.SmallHSupport.level_eq_of_gap m gamma
    ((MuPublicDictionary.Support.inputCheck_image gamma).mp hg).1 hggap
  have hbl := GlobalTrackingSequences.SmallHSupport.level_eq_of_gap m beta
    ((MuPublicDictionary.Support.inputCheck_image beta).mp hb).1 hbgap
  exact initialHeight_mono_same_level gamma beta hg hb (hbl.trans hgl.symm) hv

end Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationInitialHeightSameLevelMonotonicity
