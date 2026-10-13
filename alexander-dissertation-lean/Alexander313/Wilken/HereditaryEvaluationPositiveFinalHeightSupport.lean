import Alexander313.Wilken.HereditaryEvaluationOriginalSourceLength
import Alexander313.Wilken.HereditaryNativeLowArithmetic

/-!
# Computed original positive-source height below its actual grammar ceiling

The actual bounded original return and native translation produce LOW codes
at the finite positive source. Their canonical heights are computed rather
than supplied. LOW height monotonicity compares arbitrary represented targets;
the actual epsilon RAW parser identifies public FIRST height with that same
original height. No LOW representative is asserted at the upper ceiling.
Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationPositiveFinalHeightSupport

open NativeContext EvaluationInitialReferenceHeight

def sourceHeight (s beta : Nat) : Nat := CanonicalHeight.canonicalHeightCode
  (NativePublicBridge.contextCode s) (LowArithmetic.returnCode s beta)

theorem sourceHeight_primrec : Primrec₂ sourceHeight :=
  (CanonicalHeight.canonicalHeightCode_primrec.comp
    (NativePublicBridge.contextCode_primrec.comp Primrec.fst)
    (LowArithmetic.returnCode_primrec.comp Primrec.fst Primrec.snd)).to₂

theorem sourceHeight_mono (s first beta : Nat)
    (hf : Canonical.check first = true) (hb : Canonical.check beta = true)
    (hv : unionInterpretation first ≤ unionInterpretation beta)
    (hbound : unionInterpretation beta < finiteBase ((s + 1) + 1)) :
    sourceHeight s first ≤ sourceHeight s beta := by
  have hs := LowArithmetic.returnCode_spec s first hf (hv.trans_lt hbound)
  have ht := LowArithmetic.returnCode_spec s beta hb hbound
  exact Mu.HeightSupport.canonicalHeightCode_mono_low _ _ _ hs.1 ht.1
    (by rw [hs.2.2, ht.2.2]; exact hv)

theorem proper_height_le_target (s first beta : Nat)
    (hf : Canonical.check first = true)
    (he : Ordinal.omega0 ^ unionInterpretation first = unionInterpretation first)
    (hfloor : finiteBase (s + 1) < unionInterpretation first)
    (hb : Canonical.check beta = true)
    (hv : unionInterpretation first ≤ unionInterpretation beta)
    (hbound : unionInterpretation beta < finiteBase ((s + 1) + 1)) :
    initialHeight first ≤ sourceHeight s beta := by
  have hs := LowArithmetic.returnCode_spec s first hf (hv.trans_lt hbound)
  have hr : SourceTrackingRaw.Support.inputCheck (NativePublicBridge.contextCode s)
      (LowArithmetic.returnCode s first) = true := by
    apply (SourceTrackingRaw.Support.inputCheck_exact _ _).mpr
    refine ⟨hs.1, ?_, ?_⟩
    · rw [NativePublicBridge.contextCode_value, hs.2.2]; exact hfloor
    · rw [hs.2.2]; exact he
  have hp := UniformPublicReturn.publicCode_spec _ _
    ((UniformPublicReturn.inputCheck_exact _ _).mpr hs.1)
  have hcode : UniformPublicReturn.publicCode (NativePublicBridge.contextCode s)
      (LowArithmetic.returnCode s first) = first :=
    Canonical.check_value_injective _ _ hp.1 hf (hp.2.trans hs.2.2)
  have hh := EvaluationOriginalSourceLength.positive_raw_height s _ hr
  rw [hcode] at hh
  exact hh.le.trans (sourceHeight_mono s first beta hf hb hv hbound)

end Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationPositiveFinalHeightSupport
