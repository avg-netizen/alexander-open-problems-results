import Alexander313.Wilken.SourceOneNativeBoundedContextSourceReturn
import Alexander313.Wilken.SourceOneNativeBoundedContextLambda
import Alexander313.Wilken.HereditaryNativeRelativeZeta

/-!
# Genuine original source-one zeta pieces in the high return

The actual original checker and div/mod decomposition identify Definition
2.42 on each real high return branch. The shifted branch keeps its actual
low tail alpha+rho. No Native base-one parser or fixedness oracle occurs.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.BoundedContextLambda.TranslationSupport

open BoundedContextReturn

private theorem rawTree_code_eq (c : Nat) (hc : checkCode 0 c = true) :
    (ThetaCourse.rawTree c).code = c := by
  obtain ⟨t, he, ht⟩ := (checkCode_iff 0 c).mp hc
  rw [← he, ThetaCourse.rawTree_code]

theorem sourceValue_nodeCode (c : Nat) (hc : SourceDecomposition.inputCheck 0 c = true) :
    SourceZeta.sourceValue 0 (BoundedPublicReturn.nodeCode 0 c) =
      NativeContext.RelativeZeta.zetaValue (finiteBase 0)
        (interpretation 0 (SourceDecomposition.highCode 0 0 c))
        (interpretation 0 (SourceDecomposition.lowCode 0 0 c)) := by
  unfold SourceZeta.sourceValue NativeContext.RelativeZeta.zetaValue
    SourceFixedPoint.SourceStrict SourceFixedPoint.delta SourceFixedPoint.residual
  rw [SourceZeta.argumentCode, BoundedPublicReturn.nodeCode, Localization.argumentCode_theta,
    rawTree_code_eq c ((SourceDecomposition.inputCheck_exact 0 c).mp hc).1,
    ← (SourceDecomposition.parts_code_value 0 0 c hc).1,
    ← (SourceDecomposition.parts_code_value 0 0 c hc).2]

theorem directValue_of_parts (q root c : Nat) (hc : SourceDecomposition.inputCheck 0 c = true)
    (hΩ : omegaSequence (NativeContext.base q) 1 = omegaSequence (finiteBase 0) 1)
    (hv : NativeContext.interpretation q (NativeContext.DirectZeta.argumentCode root) = interpretation 0 c) :
    NativeContext.DirectZeta.sourceValue q root =
      NativeContext.RelativeZeta.zetaValue (NativeContext.base q)
        (interpretation 0 (SourceDecomposition.highCode 0 0 c))
        (interpretation 0 (SourceDecomposition.lowCode 0 0 c)) := by
  unfold NativeContext.DirectZeta.sourceValue NativeContext.RelativeZeta.zetaValue
    NativeContext.FixedPoint.SourceStrict NativeContext.FixedPoint.delta NativeContext.FixedPoint.residual
  rw [hv, hΩ, ← (SourceDecomposition.parts_code_value 0 0 c hc).1,
    ← (SourceDecomposition.parts_code_value 0 0 c hc).2]

theorem shiftedArgument_lowPart (a c : Nat) (ha : SourceOneIota.rootCheck a = true)
    (hc : SourceDecomposition.inputCheck 0 c = true) :
    interpretation 0 (SourceDecomposition.lowCode 0 0 (BoundedPublicReturn.shiftedArgument a c)) =
      interpretation 0 a + interpretation 0 (SourceDecomposition.lowCode 0 0 c) := by
  have hs := shiftedArgument_spec a c ha hc
  have ht : interpretation 0 a + interpretation 0 (SourceDecomposition.lowCode 0 0 c) <
      omegaSequence (finiteBase 0) 1 :=
    omegaSequence_add_closed (finiteBase 0) 0
      (by simpa only [finiteBase_zero] using root_lt_first a ha)
      (SourceDecomposition.lowPart_bound 0 0 c hc)
  obtain ⟨δ, hδ⟩ := SourceDecomposition.highPart_dvd 0 0 c hc
  rw [(SourceDecomposition.parts_code_value 0 0 _ hs.1).2, hs.2, hδ,
    Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt ht]

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.BoundedContextLambda.TranslationSupport
