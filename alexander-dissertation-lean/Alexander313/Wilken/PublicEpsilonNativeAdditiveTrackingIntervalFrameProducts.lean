import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingIntervalFrames

/-!
# Real chronological residual products of the factor trace

Every recorded removal supplies its actual product equation. Reverse frame
order therefore reconstructs the current value from the terminal prefix.
Finite genuine multiplicative closure bounds this entire residual product,
not only the individual recorded factors, below the greater final factor.
The actual greater factor output derives that closure caller and the positive
prefix before division identifies the cumulative quotient. No accumulated
branch comparison or context composition is asserted. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.IntervalFrameProducts

open PublicEpsilonUnboundedIota IntervalFrames
open Alexander313.Wilken.MultiplicativeNormalForm MultiplicativePrincipalArithmetic

theorem segment_value_product {q target bound current : Nat} {frames : List Frame}
    (hs : Segment q target bound current frames) :
    interpretation q current = interpretation q target *
      factorProduct (frames.reverse.map (fun frame => interpretation q frame.2.2)) := by
  induction hs with
  | nil terminal hv => simpa only [List.reverse_nil, List.map_nil, factorProduct, mul_one] using hv
  | cons current child factor frames hf hsmall ht ih =>
    have hv := (Factor.execute_spec q current (child, factor) hf).2.2.2.2.2.2.2.2.2.2.1
    calc
      interpretation q current = interpretation q child * interpretation q factor := hv
      _ = (interpretation q target *
          factorProduct (frames.reverse.map (fun frame => interpretation q frame.2.2))) *
          interpretation q factor := congrArg (fun value => value * interpretation q factor) ih
      _ = interpretation q target *
          factorProduct (((current, (child, factor)) :: frames).reverse.map
            (fun frame => interpretation q frame.2.2)) := by
        simp only [List.reverse_cons, List.map_append, List.map_singleton,
          factorProduct_append, factorProduct, mul_one, mul_assoc]

theorem segment_product_lt {q target bound current : Nat} {frames : List Frame}
    (hs : Segment q target bound current frames)
    (hm : IsMultiplicativePrincipal (interpretation q bound))
    (hone : 1 < interpretation q bound) :
    factorProduct (frames.reverse.map (fun frame => interpretation q frame.2.2)) <
      interpretation q bound := by
  induction hs with
  | nil terminal hv => simpa only [List.reverse_nil, List.map_nil, factorProduct] using hone
  | cons current child factor frames hf hsmall ht ih =>
    simpa only [List.reverse_cons, List.map_append, List.map_singleton,
      factorProduct_append, factorProduct, mul_one] using hm.2.2 ih hsmall

/-- Actual greater factor membership derives the genuine M closure and
positive divisor. The observed segment's reverse factors are exactly the
current quotient and their WHOLE product is below the greater last factor. -/
theorem segment_actual_quotient (q greater prefix factor current : Nat) (frames : List Frame)
    (hf : (prefix, factor) ∈ Factor.execute q greater)
    (hs : Segment q prefix factor current frames) :
    interpretation q current / interpretation q prefix =
      factorProduct (frames.reverse.map (fun frame => interpretation q frame.2.2)) ∧
    factorProduct (frames.reverse.map (fun frame => interpretation q frame.2.2)) <
      interpretation q factor := by
  obtain ⟨_, hlp, _, _, _, _, hbase, _, hm, hone, _, _, _⟩ :=
    Factor.execute_spec q greater (prefix, factor) hf
  have hpos := (base_pos q (HeightBoundary.input_spec q prefix hlp).2.1).trans_le hbase
  refine ⟨?_, segment_product_lt hs hm hone⟩
  rw [segment_value_product hs]
  exact Ordinal.mul_div_cancel _ (ne_of_gt hpos)

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.IntervalFrameProducts
