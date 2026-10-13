import Alexander313.Wilken.SourceOneNativeBoundedContextIotaReturn
import Alexander313.Wilken.PublicEpsilonNativeMu
import Alexander313.Wilken.LimitFiniteDecomposition

/-!
# Actual high part and coefficient after the source-one finite return

The genuine original source-one return may insert the outer alpha into the
LOW tail. Both real high return branches preserve Delta. The actual
zero-or-limit plus finite decomposition then determines the coefficient
and finite suffix uniquely. Original source-zero admission, Normality,
root shape and iota callers come from the constructed return adapter.
No Native base-one parser or high-part/coefficient oracle. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.BoundedContextReturn

private theorem original_rawTree_code (c : Nat) (hc : checkCode 0 c = true) :
    (ThetaCourse.rawTree c).code = c := by
  obtain ⟨t, he, ht⟩ := (checkCode_iff 0 c).mp hc
  rw [← he, ThetaCourse.rawTree_code]

theorem shiftedArgument_spec (a c : Nat) (ha : rootCheck a = true)
    (hc : SourceDecomposition.inputCheck 0 c = true) :
    Theta.acceptedCode 0 (BoundedPublicReturn.shiftedArgument a c) = true ∧
      interpretation 0 (BoundedPublicReturn.shiftedArgument a c) =
        interpretation 0 (SourceDecomposition.highCode 0 0 c) +
          (interpretation 0 a + interpretation 0 (SourceDecomposition.lowCode 0 0 c)) := by
  have hp := SourceDecomposition.parts_accepted 0 0 c hc
  have hl := Addition.normalizedSumCode_checked 0 a (SourceDecomposition.lowCode 0 0 c)
    (root_original a ha) ((Theta.acceptedCode_iff 0 _).mp hp.2).1
  have hh := Addition.normalizedSumCode_checked 0 (SourceDecomposition.highCode 0 0 c) _
    ((Theta.acceptedCode_iff 0 _).mp hp.1).1
    ((Theta.acceptedCode_iff 0 _).mp hl.1).1
  exact ⟨hh.1, hh.2.trans (congrArg _ hl.2)⟩

theorem shiftedArgument_highPart (a c : Nat) (ha : rootCheck a = true)
    (hc : SourceDecomposition.inputCheck 0 c = true) :
    interpretation 0 (SourceDecomposition.highCode 0 0 (BoundedPublicReturn.shiftedArgument a c)) =
      interpretation 0 (SourceDecomposition.highCode 0 0 c) := by
  let Ω := omegaSequence (finiteBase 0) 1
  have hΩ : 0 < Ω := (omegaSequence_isSuccLimit (finiteBase 0) 0).bot_lt
  have hs := shiftedArgument_spec a c ha hc
  have ht : interpretation 0 a + interpretation 0 (SourceDecomposition.lowCode 0 0 c) < Ω :=
    omegaSequence_add_closed (finiteBase 0) 0
      (by simpa only [finiteBase_zero] using root_lt_first a ha)
      (SourceDecomposition.lowPart_bound 0 0 c hc)
  obtain ⟨δ, hδ⟩ := SourceDecomposition.highPart_dvd 0 0 c hc
  rw [(SourceDecomposition.parts_code_value 0 0 _ hs.1).1, hs.2, hδ,
    Ordinal.mul_add_div _ hΩ.ne', Ordinal.div_eq_zero_of_lt ht, add_zero]

theorem zeroCode_highPart (a c : Nat) (ha : rootCheck a = true)
    (hc : SourceDecomposition.inputCheck 0 c = true)
    (hz : SourceFixedPoint.zeroCheck 0 (SourceDecomposition.highCode 0 0 c) = false) :
    interpretation 0 (Lambda.deltaCode (BoundedPublicReturn.zeroCode a c)) =
      interpretation 0 (SourceDecomposition.highCode 0 0 c) := by
  have he := original_rawTree_code c ((SourceDecomposition.inputCheck_exact 0 _).mp hc).1
  have hs := shiftedArgument_spec a c ha hc
  have he' := original_rawTree_code _ ((Theta.acceptedCode_iff 0 _).mp hs.1).1
  simp only [BoundedPublicReturn.zeroCode, hz, Bool.cond_false]
  cases h : Theta.Normalization.lessRawCode 0 a
      (BoundedPublicReturn.nodeCode 0 (SourceDecomposition.highCode 0 0 c)) with
  | true =>
    simp only [Lambda.deltaCode, Lambda.argumentCode, OmegaQuotient.deltaCode,
      OmegaQuotient.argumentCode, BoundedPublicReturn.nodeCode, Localization.argumentCode_theta, he]
  | false =>
    simpa only [Lambda.deltaCode, Lambda.argumentCode, OmegaQuotient.deltaCode,
      OmegaQuotient.argumentCode, BoundedPublicReturn.nodeCode, Localization.argumentCode_theta, he'] using
      shiftedArgument_highPart a c ha hc

/-- Both executing high-return branches preserve the original high part. -/
theorem returnedRoot_delta_value (a b : Nat) (ha : rootCheck a = true)
    (hb : NativeContext.PublicEpsilonIota.rootCheck (alphaCode a) b = true) :
    interpretation 0 (Lambda.deltaCode (returnedRoot a b)) =
      NativeContext.interpretation (alphaCode a) (NativeContext.PublicEpsilonIota.OmegaQuotient.deltaCode b) := by
  obtain ⟨_, ⟨t, he, ht, hn, hh⟩, _⟩ :=
    (NativeContext.PublicEpsilonIota.rootCheck_exact _ _).mp hb
  have hac := NativeContext.BaseTransformation.theta_argument_check (alphaCode a) 0 t ht
  have hr : NativeContext.PublicEpsilonIota.Restricted (alphaCode a) b t := by
    simpa only [he, Localization.argumentCode_theta, ThetaCourse.rawTree_code] using
      NativeContext.PublicEpsilonIota.argument_restricted (alphaCode a) b hb
  let c := BoundedPublicReturn.sourceTermCode a t
  have hc := sourceTermCode_spec a b ha hb t hac hn hr
  have hΩ : 0 < omegaSequence (finiteBase 0) 1 :=
    (omegaSequence_isSuccLimit (finiteBase 0) 0).bot_lt
  have hhigh : omegaSequence (finiteBase 0) 1 ≤ interpretation 0 c := by
    rw [hc.2, finiteBase_zero, HeightSupport.root_omegaSequence_succ a 0 ha]
    apply le_of_not_gt
    intro h
    exact (not_le_of_gt hh)
      ((NativeContext.denote_lt_iff_outerSort_le _ t hac 1 (by omega)).mp h)
  have hp : 0 < interpretation 0 (SourceDecomposition.highCode 0 0 c) := by
    rw [(SourceDecomposition.parts_code_value 0 0 c hc.1).1]
    exact mul_pos hΩ ((Ordinal.div_pos hΩ.ne').mpr hhigh)
  have hz : SourceFixedPoint.zeroCheck 0 (SourceDecomposition.highCode 0 0 c) = false := by
    apply Bool.eq_false_of_not_eq_true
    intro h
    exact (ne_of_gt hp) ((SourceFixedPoint.zeroCheck_exact 0 _
      (SourceDecomposition.parts_accepted 0 0 c hc.1).1).mp h)
  have hroot : returnedRoot a b = BoundedPublicReturn.zeroCode a c := by
    simpa only [returnedRoot, he, ThetaCourse.rawTree_code, BoundedPublicReturn.sourceTermCode_theta,
      BoundedPublicReturn.thetaCode, beq_self_eq_true, Bool.cond_true]
  rw [hroot, zeroCode_highPart a c ha hc.1 hz,
    (SourceDecomposition.parts_code_value 0 0 c hc.1).1, hc.2, finiteBase_zero,
    HeightSupport.root_omegaSequence_succ a 0 ha]
  have hs := (NativeContext.Decomposition.parts_code_value (alphaCode a) 0
    (NativeContext.PublicEpsilonIota.OmegaQuotient.argumentCode b)
    (NativeContext.PublicEpsilonIota.OmegaQuotient.Support.argument_accepted _ _ hb)).1
  simpa only [NativeContext.PublicEpsilonIota.OmegaQuotient.deltaCode,
    NativeContext.PublicEpsilonIota.OmegaQuotient.argumentCode, he,
    Localization.argumentCode_theta, NativeContext.interpretation_code] using hs.symm

theorem returnedRoot_coefficient_value (a b : Nat) (ha : rootCheck a = true)
    (hb : NativeContext.PublicEpsilonIota.rootCheck (alphaCode a) b = true) :
    interpretation 0 (OmegaQuotient.coefficientCode (returnedRoot a b)) =
        NativeContext.interpretation (alphaCode a)
          (NativeContext.PublicEpsilonIota.OmegaQuotient.coefficientCode (alphaCode a) b) ∧
      OmegaQuotient.coefficientOffset (returnedRoot a b) =
        NativeContext.PublicEpsilonIota.OmegaQuotient.coefficientOffset (alphaCode a) b := by
  have hold := OmegaQuotient.coefficientCode_spec _ (returnedRoot_iota_caller a b ha hb)
  have hnew := NativeContext.PublicEpsilonIota.OmegaQuotient.coefficientCode_spec _ _ hb
  apply LimitFiniteDecomposition.high_part_coefficient_unique
    (omegaSequence (finiteBase 0) 1) _ _ _ _
    (omegaSequence_isSuccLimit (finiteBase 0) 0).bot_lt hold.2.2.1 hnew.2.2.1
  calc
    _ = interpretation 0 (Lambda.deltaCode (returnedRoot a b)) := hold.2.2.2
    _ = NativeContext.interpretation (alphaCode a)
        (NativeContext.PublicEpsilonIota.OmegaQuotient.deltaCode b) := returnedRoot_delta_value a b ha hb
    _ = omegaSequence (NativeContext.base (alphaCode a)) 1 *
        (NativeContext.interpretation (alphaCode a)
          (NativeContext.PublicEpsilonIota.OmegaQuotient.coefficientCode (alphaCode a) b) +
            (NativeContext.PublicEpsilonIota.OmegaQuotient.coefficientOffset (alphaCode a) b : Ordinal.{0})) :=
      hnew.2.2.2.symm
    _ = _ := by rw [finiteBase_zero, HeightSupport.root_omegaSequence_succ a 0 ha]

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.BoundedContextReturn
