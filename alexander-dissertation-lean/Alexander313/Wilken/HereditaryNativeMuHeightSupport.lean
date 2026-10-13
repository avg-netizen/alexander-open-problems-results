import Alexander313.Wilken.HereditaryNativeMu
import Alexander313.Wilken.HereditaryNativeLambdaCanonicalHeight
import Alexander313.Wilken.HereditaryNativeIotaEnclosure

/-!
# Genuine comparison of the actual mu coefficient and lambda heights

The actual Omega-one coefficient equation places its limit coefficient below
the original high part. Full actual iota order transport then compares their
literal outputs. The executing lambda is its iota high part plus the actual
zeta value. Its original LOW admission follows from its genuine theta-zero
enclosure. The actual source height endpoints make canonical height monotone
on these original LOW inputs, including height zero. No value, order, LOW,
height or endpoint oracle is added. Source-only, uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Mu.HeightSupport

open NativePublicBridge (contextCode)

/-- Genuine canonical height is monotone in actual LOW ordinal values,
including the actual zero-index base endpoint. -/
theorem canonicalHeightCode_mono_low (q c d : Nat)
    (hc : lowCheckCode q c = true) (hd : lowCheckCode q d = true)
    (hle : interpretation q c ≤ interpretation q d) :
    CanonicalHeight.canonicalHeightCode q c ≤ CanonicalHeight.canonicalHeightCode q d := by
  apply (HeightBoundary.canonicalHeightCode_le_iff_endpoint q _ c hc).mpr
  exact hle.trans_lt ((HeightBoundary.canonicalHeightCode_le_iff_endpoint q _ d hd).mp le_rfl)

private theorem literalCode_le_of_source_le (s a c d : Nat)
    (hc : Iota.inputCheck s a c = true) (hd : Iota.inputCheck s a d = true)
    (hle : interpretation (contextCode s) c ≤ interpretation (contextCode s) d) :
    interpretation (Iota.alphaCode s a) (Iota.literalCode s a c) ≤
      interpretation (Iota.alphaCode s a) (Iota.literalCode s a d) := by
  obtain ⟨ha, t, hec, ht, hnt, hst⟩ := (Iota.inputCheck_exact s a c).mp hc
  obtain ⟨_, u, hed, hu, hnu, hsu⟩ := (Iota.inputCheck_exact s a d).mp hd
  have hrt := (Iota.restricted_iff_sourceStar s a ha t ht hnt).mpr hst
  have hru := (Iota.restricted_iff_sourceStar s a ha u hu hnu).mpr hsu
  have hs := (Iota.transform_le_iff s a ha t u ht hu hnt hnu hrt hru).mpr
    (by simpa only [hec, hed, interpretation_code] using hle)
  simpa only [Iota.literalCode, hc, hd, Bool.cond_true, hec, hed,
    Iota.stateCode_code, interpretation_code] using hs

/-- The genuine printed coefficient lambda is below its actual original
Delta, directly from Delta=Omega-one*(lambda+k). -/
theorem coefficient_le_delta (s a : Nat) (ha : inputCheck s a = true) :
    interpretation (contextCode s) (OmegaQuotient.coefficientCode s a) ≤
      interpretation (contextCode s) (Lambda.deltaCode a) := by
  have hs := OmegaQuotient.coefficientCode_spec s a ha
  have hΩ : 1 ≤ omegaSequence (base (contextCode s)) 1 :=
    Order.one_le_iff_pos.mpr (omegaSequence_isSuccLimit (base (contextCode s)) 0).bot_lt
  calc
    interpretation (contextCode s) (OmegaQuotient.coefficientCode s a) ≤
        interpretation (contextCode s) (OmegaQuotient.coefficientCode s a) +
          (OmegaQuotient.coefficientOffset s a : Ordinal.{0}) := le_self_add
    _ = 1 * (interpretation (contextCode s) (OmegaQuotient.coefficientCode s a) +
          (OmegaQuotient.coefficientOffset s a : Ordinal.{0})) := (one_mul _).symm
    _ ≤ omegaSequence (base (contextCode s)) 1 *
        (interpretation (contextCode s) (OmegaQuotient.coefficientCode s a) +
          (OmegaQuotient.coefficientOffset s a : Ordinal.{0})) := mul_le_mul' hΩ le_rfl
    _ = interpretation (contextCode s) (Lambda.deltaCode a) := hs.2.2.2

/-- The actual literal iota preserves the derived coefficient comparison;
all original source-star and Normal callers come from the original root. -/
theorem mappedCoefficient_le_delta (s a : Nat) (ha : inputCheck s a = true) :
    interpretation (Iota.alphaCode s a) (mappedCoefficient s a) ≤
      interpretation (Iota.alphaCode s a) (Iota.literalCode s a (Lambda.deltaCode a)) :=
  literalCode_le_of_source_le s a _ _ (OmegaQuotient.coefficient_iota_input s a ha)
    (Lambda.delta_input s a ha) (coefficient_le_delta s a ha)

/-- Every actual executing high lambda is an original LOW caller in its
actual alpha context, by its genuine admitted theta-zero enclosure. -/
theorem lambda_execute_low (s a out : Nat) (ho : out ∈ Lambda.execute s a) :
    lowCheckCode (Iota.alphaCode s a) out = true := by
  have hs := Lambda.execute_spec s a out ho
  have he := (Iota.Enclosure.delta_enclosure_spec s a hs.1).1
  have hr := (FixedPoint.checked_theta_range (Iota.alphaCode s a) 0
    (Iota.unshifted s a (Iota.Enclosure.deltaTerm a)) he).2
  apply OmegaPowers.low_of_bound _ _ ((Comparison.acceptedCode_exact _ _).mp hs.2.1).1
  exact (Iota.Enclosure.lambda_lt_enclosure s a out ho).trans hr

theorem mappedCoefficient_le_lambda (s a out : Nat) (ho : out ∈ Lambda.execute s a) :
    interpretation (Iota.alphaCode s a) (mappedCoefficient s a) ≤
      interpretation (Iota.alphaCode s a) out := by
  have hs := Lambda.execute_spec s a out ho
  rw [hs.2.2]
  exact (mappedCoefficient_le_delta s a hs.1).trans le_self_add

/-- The coefficient-height comparison is derived from actual values and
the original LOW endpoint characterization, with no height premise. -/
theorem mappedCoefficient_canonical_height_le_lambda (s a out : Nat)
    (ho : out ∈ Lambda.execute s a) :
    CanonicalHeight.canonicalHeightCode (Iota.alphaCode s a) (mappedCoefficient s a) ≤
      CanonicalHeight.canonicalHeightCode (Iota.alphaCode s a) out := by
  have ha := (Lambda.execute_spec s a out ho).1
  exact canonicalHeightCode_mono_low _ _ _ (mappedCoefficient_spec s a ha).1
    (lambda_execute_low s a out ho) (mappedCoefficient_le_lambda s a out ho)

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Mu.HeightSupport
