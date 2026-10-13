import Alexander313.Wilken.PublicEpsilonNativeUnboundedLambda
import Alexander313.Wilken.HereditaryNativeMuHeightSupport

/-!
# Genuine mu coefficient and lambda height comparison at every coded epsilon

The original ANY-q high-root guard derives the coefficient comparison from
the actual Omega-one quotient equation. The real unrestricted iota reflects
order on both derived callers. Actual beta-context lambda is LOW and equals
its mapped divided head plus the genuine zeta. The existing universal LOW
height-endpoint theorem therefore compares the actual coefficient and lambda
canonical heights, including height zero. No endpoint or height oracle.
These are source-only, uncompiled proof candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.Mu.HeightSupport

theorem coefficient_le_delta (q root : Nat) (ha : Mu.inputCheck q root = true) :
    interpretation q (OmegaQuotient.coefficientCode q root) ≤
      interpretation q (OmegaQuotient.deltaCode root) := by
  have hs := OmegaQuotient.coefficientCode_spec q root ha
  have hΩ : 1 ≤ omegaSequence (base q) 1 :=
    Order.one_le_iff_pos.mpr (omegaSequence_isSuccLimit (base q) 0).bot_lt
  calc
    interpretation q (OmegaQuotient.coefficientCode q root) ≤
        interpretation q (OmegaQuotient.coefficientCode q root) +
          (OmegaQuotient.coefficientOffset q root : Ordinal.{0}) := le_self_add
    _ = 1 * (interpretation q (OmegaQuotient.coefficientCode q root) +
          (OmegaQuotient.coefficientOffset q root : Ordinal.{0})) := (one_mul _).symm
    _ ≤ omegaSequence (base q) 1 *
        (interpretation q (OmegaQuotient.coefficientCode q root) +
          (OmegaQuotient.coefficientOffset q root : Ordinal.{0})) := mul_le_mul' hΩ le_rfl
    _ = interpretation q (OmegaQuotient.deltaCode root) := hs.2.2.2

theorem mappedCoefficient_le_delta (q root : Nat) (ha : Mu.inputCheck q root = true) :
    interpretation (betaCode q root) (mappedCoefficient q root) ≤
      interpretation (betaCode q root) (literalCode q root (OmegaQuotient.deltaCode root)) := by
  apply le_of_not_gt
  intro hlt
  have hs := (literalCode_lt_iff q root _ _ (Lambda.delta_input q root ha)
    (OmegaQuotient.coefficient_iota_input q root ha)).mp hlt
  exact hs.not_ge (coefficient_le_delta q root ha)

theorem mappedCoefficient_le_lambda (q root out : Nat) (ho : out ∈ Lambda.execute q root) :
    interpretation (betaCode q root) (mappedCoefficient q root) ≤
      interpretation (betaCode q root) out := by
  have hs := Lambda.execute_spec q root out ho
  rw [hs.2.2.2, Lambda.sourceValue]
  exact (mappedCoefficient_le_delta q root hs.1).trans le_self_add

theorem mappedCoefficient_canonical_height_le_lambda (q root out : Nat)
    (ho : out ∈ Lambda.execute q root) :
    CanonicalHeight.canonicalHeightCode (betaCode q root) (mappedCoefficient q root) ≤
      CanonicalHeight.canonicalHeightCode (betaCode q root) out := by
  have hs := Lambda.execute_spec q root out ho
  exact NativeContext.Mu.HeightSupport.canonicalHeightCode_mono_low _ _ _
    (mappedCoefficient_spec q root hs.1).1 hs.2.1 (mappedCoefficient_le_lambda q root out ho)

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.Mu.HeightSupport
