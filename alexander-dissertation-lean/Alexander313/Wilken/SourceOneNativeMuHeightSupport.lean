import Alexander313.Wilken.SourceOneNativeMu
import Alexander313.Wilken.SourceOneNativeIotaEnclosure
import Alexander313.Wilken.SourceOneNativeLambdaRaw

/-!
# Actual source-one coefficient and lambda height comparisons

The original Omega-one equation places the computed coefficient below
Delta. Actual source-one iota order reflects that inequality in the genuine
alpha context. The executing lambda supplies a LOW upper bound, and the
real canonical-height endpoints make height monotone on these LOW values.
No source dictionary at a positive epsilon, comparison or height oracle.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.Mu.HeightSupport

theorem canonicalHeightCode_mono_low (q c d : Nat)
    (hc : NativeContext.lowCheckCode q c = true) (hd : NativeContext.lowCheckCode q d = true)
    (hle : NativeContext.interpretation q c ≤ NativeContext.interpretation q d) :
    NativeContext.CanonicalHeight.canonicalHeightCode q c ≤
      NativeContext.CanonicalHeight.canonicalHeightCode q d := by
  apply (NativeContext.HeightBoundary.canonicalHeightCode_le_iff_endpoint q _ c hc).mpr
  exact hle.trans_lt
    ((NativeContext.HeightBoundary.canonicalHeightCode_le_iff_endpoint q _ d hd).mp le_rfl)

private theorem literalCode_le_of_source_le (a c d : Nat)
    (hc : SourceOneIota.inputCheck a c = true) (hd : SourceOneIota.inputCheck a d = true)
    (hle : interpretation 0 c ≤ interpretation 0 d) :
    NativeContext.interpretation (alphaCode a) (literalCode a c) ≤
      NativeContext.interpretation (alphaCode a) (literalCode a d) := by
  apply le_of_not_gt
  intro hgt
  exact (not_lt_of_ge hle) ((literalCode_lt_iff a d c hd hc).mp hgt)

theorem coefficient_le_delta (a : Nat) (ha : inputCheck a = true) :
    interpretation 0 (OmegaQuotient.coefficientCode a) ≤ interpretation 0 (Lambda.deltaCode a) := by
  have hs := OmegaQuotient.coefficientCode_spec a ha
  have hΩ : 1 ≤ omegaSequence (finiteBase 0) 1 :=
    Order.one_le_iff_pos.mpr (omegaSequence_isSuccLimit (finiteBase 0) 0).bot_lt
  calc
    interpretation 0 (OmegaQuotient.coefficientCode a) ≤
        interpretation 0 (OmegaQuotient.coefficientCode a) +
          (OmegaQuotient.coefficientOffset a : Ordinal.{0}) := le_self_add
    _ = 1 * (interpretation 0 (OmegaQuotient.coefficientCode a) +
          (OmegaQuotient.coefficientOffset a : Ordinal.{0})) := (one_mul _).symm
    _ ≤ omegaSequence (finiteBase 0) 1 *
        (interpretation 0 (OmegaQuotient.coefficientCode a) +
          (OmegaQuotient.coefficientOffset a : Ordinal.{0})) := mul_le_mul' hΩ le_rfl
    _ = interpretation 0 (Lambda.deltaCode a) := hs.2.2.2

theorem mappedCoefficient_le_delta (a : Nat) (ha : inputCheck a = true) :
    NativeContext.interpretation (alphaCode a) (mappedCoefficient a) ≤
      NativeContext.interpretation (alphaCode a) (literalCode a (Lambda.deltaCode a)) :=
  literalCode_le_of_source_le a _ _ (OmegaQuotient.coefficient_iota_input a ha)
    (Lambda.delta_input a ha) (coefficient_le_delta a ha)

theorem mappedCoefficient_le_lambda (a out : Nat) (ho : out ∈ Lambda.execute a) :
    NativeContext.interpretation (alphaCode a) (mappedCoefficient a) ≤
      NativeContext.interpretation (alphaCode a) out := by
  have hs := Lambda.execute_spec a out ho
  rw [hs.2.2]
  exact (mappedCoefficient_le_delta a hs.1).trans le_self_add

theorem mappedCoefficient_canonical_height_le_lambda (a out : Nat) (ho : out ∈ Lambda.execute a) :
    NativeContext.CanonicalHeight.canonicalHeightCode (alphaCode a) (mappedCoefficient a) ≤
      NativeContext.CanonicalHeight.canonicalHeightCode (alphaCode a) out := by
  have ha := (Lambda.execute_spec a out ho).1
  exact canonicalHeightCode_mono_low _ _ _ (mappedCoefficient_spec a ha).1
    (Enclosure.lambda_low a out ho) (mappedCoefficient_le_lambda a out ho)

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.Mu.HeightSupport
