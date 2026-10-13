import Alexander313.Wilken.HereditaryNativeBoundedContextSourceReturnSupport
import Alexander313.Wilken.LimitFiniteDecomposition

/-!
# Actual high part and coefficient of the returned intermediate root

The literal SAME-value return of a genuine intermediate root may insert
the outer alpha into its LOW argument tail. Both actual high branches
preserve the Omega-one high part. The returned original source root
therefore has the same Delta, and the genuine zero-or-limit plus finite
quotient is unique. All return and original-root callers are constructed;
no high-part, coefficient, admission or translation oracle is supplied.
Uncompiled source candidates. Iota commutation remains a separate proof.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.BoundedContextIota.SourceReturn

open NativePublicBridge (contextCode)

private theorem rawTree_code_eq (q c : Nat) (hc : checkCode q c = true) :
    (ThetaCourse.rawTree c).code = c := by
  obtain ⟨t, he, ht⟩ := (checkCode_exact q c).mp hc
  rw [← he, ThetaCourse.rawTree_code]

theorem shiftedArgument_spec (s a c : Nat) (ha : Iota.rootCheck s a = true)
    (hc : Decomposition.inputCheck (contextCode s) c = true) :
    Comparison.acceptedCode (contextCode s) (BoundedPublicReturn.shiftedArgument s a c) = true ∧
      interpretation (contextCode s) (BoundedPublicReturn.shiftedArgument s a c) =
        interpretation (contextCode s) (Decomposition.highCode 0 c) +
          (interpretation (contextCode s) a + interpretation (contextCode s) (Decomposition.lowCode 0 c)) := by
  have hp := Decomposition.parts_accepted (contextCode s) 0 c hc
  have hl := Arithmetic.addCode_spec (contextCode s) a (Decomposition.lowCode 0 c)
    (Iota.root_original s a ha) ((Comparison.acceptedCode_exact _ _).mp hp.2).1
  have hh := Arithmetic.addCode_spec (contextCode s) (Decomposition.highCode 0 c) _
    ((Comparison.acceptedCode_exact _ _).mp hp.1).1
    ((Comparison.acceptedCode_exact _ _).mp hl.1).1
  exact ⟨hh.1, hh.2.1.trans (congrArg _ hl.2.1)⟩

theorem shiftedArgument_highPart (s a c : Nat) (ha : Iota.rootCheck s a = true)
    (hc : Decomposition.inputCheck (contextCode s) c = true) :
    interpretation (contextCode s) (Decomposition.highCode 0 (BoundedPublicReturn.shiftedArgument s a c)) =
      interpretation (contextCode s) (Decomposition.highCode 0 c) := by
  let Ω := omegaSequence (base (contextCode s)) 1
  have hΩ : 0 < Ω := (omegaSequence_isSuccLimit (base (contextCode s)) 0).bot_lt
  have hs := shiftedArgument_spec s a c ha hc
  have ht : interpretation (contextCode s) a + interpretation (contextCode s) (Decomposition.lowCode 0 c) < Ω :=
    omegaSequence_add_closed (base (contextCode s)) 0
      (Iota.root_below_first_cardinal s a ha)
      (Decomposition.lowPart_bound (contextCode s) 0 c hc)
  obtain ⟨δ, hδ⟩ := Decomposition.highPart_dvd (contextCode s) 0 c hc
  rw [(Decomposition.parts_code_value (contextCode s) 0 _ hs.1).1, hs.2, hδ,
    Ordinal.mul_add_div _ hΩ.ne', Ordinal.div_eq_zero_of_lt ht, add_zero]

theorem zeroCode_highPart (s a c : Nat) (ha : Iota.rootCheck s a = true)
    (hc : Decomposition.inputCheck (contextCode s) c = true)
    (hz : FixedPoint.zeroCheck (Decomposition.highCode 0 c) = false) :
    interpretation (contextCode s) (Lambda.deltaCode (BoundedPublicReturn.zeroCode s a c)) =
      interpretation (contextCode s) (Decomposition.highCode 0 c) := by
  have he := rawTree_code_eq (contextCode s) c ((Decomposition.inputCheck_exact _ _).mp hc).1
  have hs := shiftedArgument_spec s a c ha hc
  have he' := rawTree_code_eq (contextCode s) _ ((Comparison.acceptedCode_exact _ _).mp hs.1).1
  simp only [BoundedPublicReturn.zeroCode, hz, Bool.cond_false]
  cases h : Normalization.lessRawCode (contextCode s) a
      (BoundedPublicReturn.nodeCode 0 (Decomposition.highCode 0 c)) with
  | true =>
    simp only [Lambda.deltaCode, Lambda.argumentCode, BoundedPublicReturn.nodeCode,
      Localization.argumentCode_theta, he]
  | false =>
    simpa only [Lambda.deltaCode, Lambda.argumentCode, BoundedPublicReturn.nodeCode,
      Localization.argumentCode_theta, he'] using shiftedArgument_highPart s a c ha hc

theorem returnedRoot_delta_value (s a root : Nat) (ha : rootCheck s a root = true) :
    interpretation (contextCode s) (Lambda.deltaCode (returnedRoot s a root)) =
      interpretation (sourceCode s a) (OmegaQuotient.deltaCode root) := by
  obtain ⟨houter, ⟨t, he, ht, hn, hh⟩, hb⟩ := (rootCheck_exact s a root).mp ha
  have hac := BaseTransformation.theta_argument_check (sourceCode s a) 0 t ht
  have hr : Restricted s a root t := by
    simpa only [he, Localization.argumentCode_theta, ThetaCourse.rawTree_code] using argument_restricted s a root ha
  let c := BoundedPublicReturn.sourceTermCode s a t
  have hc := sourceTermCode_spec s a root ha t hac hn hr
  have hΩ : 0 < omegaSequence (base (contextCode s)) 1 :=
    (omegaSequence_isSuccLimit (base (contextCode s)) 0).bot_lt
  have hhigh : omegaSequence (base (contextCode s)) 1 ≤ interpretation (contextCode s) c := by
    rw [hc.2, Iota.HeightSupport.root_omegaSequence_succ s a 0 houter]
    apply le_of_not_gt
    intro h
    exact (not_le_of_gt hh) ((denote_lt_iff_outerSort_le (sourceCode s a) t hac 1 (by omega)).mp h)
  have hp : 0 < interpretation (contextCode s) (Decomposition.highCode 0 c) := by
    rw [(Decomposition.parts_code_value (contextCode s) 0 c hc.1).1]
    exact mul_pos hΩ ((Ordinal.div_pos hΩ.ne').mpr hhigh)
  have hz : FixedPoint.zeroCheck (Decomposition.highCode 0 c) = false := by
    apply Bool.eq_false_of_not_eq_true
    intro h
    exact (ne_of_gt hp) ((FixedPoint.zeroCheck_exact (contextCode s) _
      (Decomposition.parts_accepted (contextCode s) 0 c hc.1).1).mp h)
  have hroot : returnedRoot s a root = BoundedPublicReturn.zeroCode s a c := by
    simpa only [returnedRoot, he, ThetaCourse.rawTree_code, BoundedPublicReturn.sourceTermCode_theta,
      BoundedPublicReturn.thetaCode, beq_self_eq_true, Bool.cond_true]
  rw [hroot, zeroCode_highPart s a c houter hc.1 hz,
    (Decomposition.parts_code_value (contextCode s) 0 c hc.1).1, hc.2,
    Iota.HeightSupport.root_omegaSequence_succ s a 0 houter]
  have hs := (Decomposition.parts_code_value (sourceCode s a) 0 (OmegaQuotient.argumentCode root)
    (OmegaQuotient.argument_accepted s a root ha)).1
  simpa only [OmegaQuotient.deltaCode, OmegaQuotient.argumentCode, he,
    Localization.argumentCode_theta, interpretation_code] using hs.symm

theorem returnedRoot_coefficient_value (s a root : Nat) (ha : rootCheck s a root = true) :
    interpretation (contextCode s) (NativeContext.OmegaQuotient.coefficientCode s (returnedRoot s a root)) =
        interpretation (sourceCode s a) (OmegaQuotient.coefficientCode s a root) ∧
      NativeContext.OmegaQuotient.coefficientOffset s (returnedRoot s a root) =
        OmegaQuotient.coefficientOffset s a root := by
  have hold := NativeContext.OmegaQuotient.coefficientCode_spec s _ (returnedRoot_iota_caller s a root ha)
  have hnew := OmegaQuotient.coefficientCode_spec s a root ha
  apply LimitFiniteDecomposition.high_part_coefficient_unique
    (omegaSequence (base (contextCode s)) 1) _ _ _ _
    (omegaSequence_isSuccLimit (base (contextCode s)) 0).bot_lt hold.2.2.1 hnew.2.2.1
  calc
    _ = interpretation (contextCode s) (Lambda.deltaCode (returnedRoot s a root)) := hold.2.2.2
    _ = interpretation (sourceCode s a) (OmegaQuotient.deltaCode root) := returnedRoot_delta_value s a root ha
    _ = omegaSequence (base (sourceCode s a)) 1 *
        (interpretation (sourceCode s a) (OmegaQuotient.coefficientCode s a root) +
          (OmegaQuotient.coefficientOffset s a root : Ordinal.{0})) := hnew.2.2.2.symm
    _ = _ := by rw [Iota.HeightSupport.root_omegaSequence_succ s a 0 (outer_root s a root ha)]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.BoundedContextIota.SourceReturn
