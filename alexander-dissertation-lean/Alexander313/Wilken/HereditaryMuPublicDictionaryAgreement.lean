import Alexander313.Wilken.HereditaryMuPublicDictionary
import Alexander313.Wilken.HereditarySkPositiveDictionaryAgreement
import Alexander313.Wilken.SourceOneNativeSkPublicDictionaryAgreement

/-!
# Genuine original-source fidelity of the public mu query

Every original proper raw LOW epsilon at a positive finite source lies
strictly between that source's actual grammar endpoints. The genuine scan
therefore retains that SAME literal source. Original source-one LOW forces
level zero. Actual SAME-source mu spelling invariance identifies the
selected HIGH representative with the original raw epsilon. These proofs
identify an independently executing public mu query; no arbitrary
cross-source mu invariance or supplied source selection is used. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.MuPublicDictionary.Agreement

abbrev positivePublicCode := SkPublicDictionary.PositiveAgreement.publicCode
abbrev sourceOnePublicCode := SourceOneIota.SourceTrackingRaw.Support.publicCode

theorem positive_caller (s raw : Nat)
    (hr : NativeContext.SourceTrackingRaw.Support.inputCheck (NativePublicBridge.contextCode s) raw = true) :
    Support.inputCheck (positivePublicCode s raw) = true := by
  have hs := SkPublicDictionary.PositiveAgreement.dictionary_spec s raw hr
  exact (Support.inputCheck_exact _).mpr ⟨hs.1, hs.2.2⟩

theorem source_one_caller (raw : Nat)
    (hr : SourceOneIota.SourceTrackingRaw.Support.inputCheck raw = true) :
    Support.inputCheck (sourceOnePublicCode raw) = true := by
  have hs := SourceOneIota.SkRaw.DictionaryAgreement.dictionary_spec raw hr
  exact (Support.inputCheck_exact _).mpr ⟨hs.1, hs.2.2⟩

/-- Genuine original LOW endpoints retain the positive source literally,
then the actual spelling theorem identifies its selected mu value. -/
theorem positive_sourceValue (s raw : Nat)
    (hr : NativeContext.SourceTrackingRaw.Support.inputCheck (NativePublicBridge.contextCode s) raw = true) :
    Support.sourceValue (positivePublicCode s raw) =
      NativeContext.SourceTrackingRaw.Support.muValue (NativePublicBridge.contextCode s) raw := by
  have hd := SkPublicDictionary.PositiveAgreement.dictionary_spec s raw hr
  have hi := positive_caller s raw hr
  have hn : PublicEpsilonSourceDictionary.level (positivePublicCode s raw) ≠ 0 := by
    rw [hd.2.1]; omega
  have hs := Support.native_root _ hi hn
  have hp := PublicEpsilonSourceDictionary.positive_spec _ s hd.1 hd.2.1 hd.2.2
  have hroot : NativeContext.RootLowCollapse.rootCheck (NativePublicBridge.contextCode s)
      (Support.nativeRoot (positivePublicCode s raw)) = true := by
    simpa only [Support.nativeContext, hp.1] using hs.1
  have hvalue : NativeContext.interpretation (NativePublicBridge.contextCode s)
      (Support.nativeRoot (positivePublicCode s raw)) = unionInterpretation (positivePublicCode s raw) := by
    simpa only [Support.nativeContext, hp.1] using hs.2
  have hpublic := NativeContext.UniformPublicReturn.publicCode_spec _ raw
    ((NativeContext.UniformPublicReturn.inputCheck_exact _ raw).mpr
      (NativeContext.SourceTrackingRaw.Support.rootCode_spec _ raw hr).1)
  have hm := NativeContext.SourceTrackingRaw.Support.muValue_eq _ raw _ hr hroot
    (hpublic.2.symm.trans hvalue.symm)
  have hb : (PublicEpsilonSourceDictionary.level (positivePublicCode s raw) == 0) = false := by
    rw [hd.2.1]; simp
  simpa only [Support.sourceValue, hb, Bool.cond_false, Support.nativeContext, hp.1] using hm.symm

/-- Source-zero LOW forces the actual selected source-one branch, and
its genuine SAME-original-source mu theorem supplies numerical fidelity. -/
theorem source_one_sourceValue (raw : Nat)
    (hr : SourceOneIota.SourceTrackingRaw.Support.inputCheck raw = true) :
    Support.sourceValue (sourceOnePublicCode raw) = SourceOneIota.SourceTrackingRaw.Support.muValue raw := by
  have hd := SourceOneIota.SkRaw.DictionaryAgreement.dictionary_spec raw hr
  have hs := Support.source_one_root _ (source_one_caller raw hr) hd.2.1
  have hp := SourceOneIota.SourceTrackingRaw.Support.publicCode_spec raw
    (SourceOneIota.SourceTrackingRaw.Support.rootCode_spec raw hr).1
  have hm := SourceOneIota.SourceTrackingRaw.Support.muValue_eq raw _ hr hs.1
    (hp.2.symm.trans hs.2.symm)
  have hb : (PublicEpsilonSourceDictionary.level (sourceOnePublicCode raw) == 0) = true :=
    beq_iff_eq.mpr hd.2.1
  simpa only [Support.sourceValue, hb, Bool.cond_true] using hm.symm

theorem positive_public_mu (s raw : Nat)
    (hr : NativeContext.SourceTrackingRaw.Support.inputCheck (NativePublicBridge.contextCode s) raw = true) :
    unionInterpretation (MuPublicDictionary.publicCode (positivePublicCode s raw)) =
      NativeContext.SourceTrackingRaw.Support.muValue (NativePublicBridge.contextCode s) raw :=
  (MuPublicDictionary.publicCode_spec _ (positive_caller s raw hr)).2.trans
    (positive_sourceValue s raw hr)

theorem source_one_public_mu (raw : Nat)
    (hr : SourceOneIota.SourceTrackingRaw.Support.inputCheck raw = true) :
    unionInterpretation (MuPublicDictionary.publicCode (sourceOnePublicCode raw)) =
      SourceOneIota.SourceTrackingRaw.Support.muValue raw :=
  (MuPublicDictionary.publicCode_spec _ (source_one_caller raw hr)).2.trans
    (source_one_sourceValue raw hr)

end Alexander313.Wilken.RelativeTerm.Hereditary.MuPublicDictionary.Agreement
