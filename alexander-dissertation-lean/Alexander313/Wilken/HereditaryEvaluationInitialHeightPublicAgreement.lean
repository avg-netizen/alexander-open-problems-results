import Alexander313.Wilken.HereditaryEvaluationInitialReferenceHeight
import Alexander313.Wilken.HereditaryMuPublicDictionaryAgreement

/-!
# The actual original root computes the selected public initial height

Genuine original LOW epsilon admission forces the real least dictionary
scan to retain the same literal source. The selected original HIGH root
has the original value, so actual normal height invariance identifies its
printed first height with the original root's canonical height. This is
source-one check zero and the actual positive finite source, without an
assumed source index or a representative/height oracle. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationInitialHeightPublicAgreement

open NativeContext
open NativeContext.PublicEpsilonUnboundedIota
open EvaluationInitialReferenceHeight

theorem source_one (root : Nat) (hr : SourceOneIota.Mu.inputCheck root = true) :
    initialHeight (SourceOneIota.SourceTrackingRaw.Support.publicCode root) =
      SourceOne.CanonicalHeight.canonicalHeightCode root := by
  let gamma := SourceOneIota.SourceTrackingRaw.Support.publicCode root
  have hraw : SourceOneIota.SourceTrackingRaw.Support.inputCheck root = true :=
    (SourceOneIota.SourceTrackingRaw.Support.inputCheck_exact root).mpr
      ⟨SourceOneIota.root_low root hr,
        EpsilonOffsets.epsilon_one_lt (SourceOneIota.root_epsilon root hr),
        SourceOneIota.root_epsilon root hr⟩
  have hd := SourceOneIota.SkRaw.DictionaryAgreement.dictionary_spec root hraw
  have hg := MuPublicDictionary.Agreement.source_one_caller root hraw
  have hs := MuPublicDictionary.Support.source_one_root gamma hg hd.2.1
  have hp := SourceOneIota.SourceTrackingRaw.Support.publicCode_spec root
    (SourceOneIota.root_low root hr)
  have hv : SourceOne.PublicCodes.interpretation
      (PublicEpsilonSourceDictionary.sourceRootCode gamma) =
        SourceOne.PublicCodes.interpretation root := by
    simpa only [interpretation_zero] using hs.2.trans hp.2
  have he := SourceOne.CanonicalHeight.normalCode_height_invariant _ _
    (SourceOneIota.HeightSupport.root_source_accepted _ hs.1)
    (SourceOneIota.HeightSupport.root_source_accepted root hr) hv
  have hheight := SourceOne.CanonicalHeight.canonicalHeightCode_normal root
    (SourceOneIota.HeightSupport.root_source_accepted root hr)
  simpa only [initialHeight, gamma, hd.2.1, beq_self_eq_true, Bool.cond_true,
    hheight] using he

theorem positive (s root : Nat)
    (hr : Mu.inputCheck (NativePublicBridge.contextCode s) root = true) :
    initialHeight (UniformPublicReturn.publicCode (NativePublicBridge.contextCode s) root) =
      CanonicalHeight.canonicalHeightCode (NativePublicBridge.contextCode s) root := by
  let gamma := UniformPublicReturn.publicCode (NativePublicBridge.contextCode s) root
  have hraw : SourceTrackingRaw.Support.inputCheck (NativePublicBridge.contextCode s) root = true :=
    (SourceTrackingRaw.Support.inputCheck_exact _ root).mpr
      ⟨RootLowCollapse.root_low _ root hr, root_base_lt _ root hr, root_epsilon _ root hr⟩
  have hd := SkPublicDictionary.PositiveAgreement.dictionary_spec s root hraw
  have hg := MuPublicDictionary.Agreement.positive_caller s root hraw
  have hl : PublicEpsilonSourceDictionary.level gamma ≠ 0 := by rw [hd.2.1]; omega
  have hs := MuPublicDictionary.Support.native_root gamma hg hl
  have hindex := (PublicEpsilonSourceDictionary.positive_spec gamma s hd.1 hd.2.1 hd.2.2).1
  have hroot : Mu.inputCheck (NativePublicBridge.contextCode s)
      (MuPublicDictionary.Support.nativeRoot gamma) = true := by
    simpa only [MuPublicDictionary.Support.nativeContext, hindex] using hs.1
  have hvalue : interpretation (NativePublicBridge.contextCode s)
      (MuPublicDictionary.Support.nativeRoot gamma) = unionInterpretation gamma := by
    simpa only [MuPublicDictionary.Support.nativeContext, hindex] using hs.2
  have hp := UniformPublicReturn.publicCode_spec _ root
    ((UniformPublicReturn.inputCheck_exact _ root).mpr (RootLowCollapse.root_low _ root hr))
  have he := CanonicalHeight.normalCode_height_invariant _ _ _
    (RootLowCollapse.root_accepted _ _ hroot) (RootLowCollapse.root_accepted _ root hr)
    (hvalue.trans hp.2)
  have hheight := CanonicalHeight.canonicalHeightCode_normal _ root
    (RootLowCollapse.root_accepted _ root hr)
  have hz := beq_eq_false_iff_ne.mpr hl
  simpa only [initialHeight, gamma, hz, Bool.cond_false, hheight] using he

end Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationInitialHeightPublicAgreement
