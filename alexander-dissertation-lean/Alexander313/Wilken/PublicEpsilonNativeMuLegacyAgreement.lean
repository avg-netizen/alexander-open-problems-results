import Alexander313.Wilken.PublicEpsilonNativeMu
import Alexander313.Wilken.PublicEpsilonNativeUnboundedMu

/-!
# Actual legacy and unrestricted mu agree on the genuine legacy domain

The original selected-root guard is retained as a real input. It derives
the unrestricted root caller; canonical value injection identifies both
beta and every stopped parameter. The actual finite transforms, quotient
word and executing mu output then agree literally. No selected endpoint
is obtained from the unrestricted guard. This comparison is needed when
an original source-one interval genuinely supplies the legacy caller.
No Native base-one parser or operator equality oracle. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.LegacyAgreement

theorem root_caller (q root : Nat) (ha : PublicEpsilonIota.rootCheck q root = true) :
    rootCheck q root = true :=
  (rootCheck_exact q root).mpr ((PublicEpsilonIota.rootCheck_exact q root).mp ha).2.1

theorem betaCode_eq (q root : Nat) (ha : PublicEpsilonIota.rootCheck q root = true) :
    betaCode q root = PublicEpsilonIota.betaCode q root := by
  have hn := betaCode_spec q root (root_caller q root ha)
  have ho := PublicEpsilonIota.betaCode_spec q root ha
  exact Canonical.check_value_injective _ _ hn.1 ho.1 (hn.2.trans ho.2.symm)

theorem parameterCode_eq (q root : Nat) (ha : PublicEpsilonIota.rootCheck q root = true)
    (t : RelativeTerm Nat) (ht : check q t = true)
    (hb : denote q t < interpretation q root) :
    parameterCode q t = PublicEpsilonIota.parameterCode q t := by
  have hr := (PublicEpsilonIota.rootCheck_exact q root).mp ha
  have hlow := PublicEpsilonIota.below_low q root ha t ht hb
  have ho := PublicEpsilonSourceDictionary.Return.publicCode_spec q t.code
    ((PublicEpsilonSourceDictionary.Return.inputCheck_exact q t.code).mpr
      ⟨hr.1, hlow, by simpa only [interpretation_code] using hb.trans hr.2.2⟩)
  have hn := UniformPublicReturn.publicCode_spec q t.code
    ((UniformPublicReturn.inputCheck_exact q t.code).mpr hlow)
  exact Canonical.check_value_injective _ _ hn.1 ho.1 (hn.2.trans ho.2.symm)

/-- Every checked original tree has exactly the same finite transformed
syntax on this actual common domain, including hidden arguments. -/
theorem transform_eq (q root : Nat) (ha : PublicEpsilonIota.rootCheck q root = true)
    (t : RelativeTerm Nat) (ht : check q t = true) :
    transform q root t = PublicEpsilonIota.transform q root t := by
  revert ht
  induction t with
  | parameter p =>
    intro ht
    have hp := checked_parameters q (.parameter p) ht p (by simp [RelativeTerm.parameters])
    have hb : denote q (.parameter p) < interpretation q root :=
      hp.2.trans_le (PublicEpsilonIota.root_base_le q root ha)
    simp only [transform, PublicEpsilonIota.transform, parameterCode_eq q root ha _ ht hb]
  | sum t u iht ihu =>
    intro ht
    have hc := BaseTransformation.sum_checks q t u ht
    cases hs : PublicEpsilonIota.small q root (.sum t u) with
    | true =>
      have hb := (PublicEpsilonIota.small_exact q root ha _ ht).mp hs
      have hsn : small q root (.sum t u) = true := hs
      simp only [transform, PublicEpsilonIota.transform, hs, hsn, Bool.cond_true,
        parameterCode_eq q root ha _ ht hb]
    | false =>
      have hsn : small q root (.sum t u) = false := hs
      simp only [transform, PublicEpsilonIota.transform, hs, hsn, Bool.cond_false,
        iht hc.1, ihu hc.2]
  | theta k t ih =>
    intro ht
    have hc := BaseTransformation.theta_argument_check q k t ht
    cases hs : PublicEpsilonIota.small q root (.theta k t) with
    | true =>
      have hb := (PublicEpsilonIota.small_exact q root ha _ ht).mp hs
      have hsn : small q root (.theta k t) = true := hs
      simp only [transform, PublicEpsilonIota.transform, hs, hsn, Bool.cond_true,
        parameterCode_eq q root ha _ ht hb]
    | false =>
      have hsn : small q root (.theta k t) = false := hs
      simp only [transform, PublicEpsilonIota.transform, hs, hsn, Bool.cond_false, ih hc]

theorem literalCode_eq (q root : Nat) (ha : PublicEpsilonIota.rootCheck q root = true)
    (t : RelativeTerm Nat) (ht : check q t = true) (hn : Comparison.Normal q t)
    (hr : PublicEpsilonIota.Restricted q root t) :
    literalCode q root t.code = PublicEpsilonIota.literalCode q root t.code := by
  rw [literalCode_code q root (root_caller q root ha) t ht hn hr,
    PublicEpsilonIota.literalCode_code q root ha t ht hn hr, transform_eq q root ha t ht]

theorem coefficientCode_eq (q root : Nat) (ha : PublicEpsilonIota.rootCheck q root = true) :
    OmegaQuotient.coefficientCode q root = PublicEpsilonIota.OmegaQuotient.coefficientCode q root := by
  rw [OmegaQuotient.coefficientCode_literal q root (root_caller q root ha),
    PublicEpsilonIota.OmegaQuotient.coefficientCode_literal q root ha]

theorem coefficientOffset_eq (q root : Nat) (ha : PublicEpsilonIota.rootCheck q root = true) :
    OmegaQuotient.coefficientOffset q root = PublicEpsilonIota.OmegaQuotient.coefficientOffset q root := by
  rw [OmegaQuotient.coefficientOffset_literal q root (root_caller q root ha),
    PublicEpsilonIota.OmegaQuotient.coefficientOffset_literal q root ha]

theorem mappedCoefficient_eq (q root : Nat) (ha : PublicEpsilonIota.rootCheck q root = true) :
    Mu.mappedCoefficient q root = PublicEpsilonIota.Mu.mappedCoefficient q root := by
  have hc := PublicEpsilonIota.OmegaQuotient.root_coefficient_spec q root ha
  rw [Mu.mappedCoefficient, PublicEpsilonIota.Mu.mappedCoefficient,
    OmegaQuotient.coefficientCode_literal q root (root_caller q root ha),
    PublicEpsilonIota.OmegaQuotient.coefficientCode_literal q root ha]
  exact literalCode_eq q root ha _ hc.1 hc.2.1 hc.2.2.1

theorem chi_eq (q root : Nat) (ha : PublicEpsilonIota.rootCheck q root = true) :
    Mu.chi q root = PublicEpsilonIota.Mu.chi q root := by
  rw [Mu.chi, PublicEpsilonIota.Mu.chi, betaCode_eq q root ha, mappedCoefficient_eq q root ha]

theorem exponentCode_eq (q root : Nat) (ha : PublicEpsilonIota.rootCheck q root = true) :
    Mu.exponentCode q root = PublicEpsilonIota.Mu.exponentCode q root := by
  rw [Mu.exponentCode, PublicEpsilonIota.Mu.exponentCode, Mu.tail, PublicEpsilonIota.Mu.tail,
    betaCode_eq q root ha, mappedCoefficient_eq q root ha, chi_eq q root ha,
    coefficientOffset_eq q root ha]

theorem muCode_eq (q root : Nat) (ha : PublicEpsilonIota.rootCheck q root = true) :
    Mu.muCode q root = PublicEpsilonIota.Mu.muCode q root := by
  rw [Mu.muCode_literal q root (root_caller q root ha),
    PublicEpsilonIota.Mu.muCode_literal q root ha, betaCode_eq q root ha,
    exponentCode_eq q root ha]

theorem sourceValue_eq (q root : Nat) (ha : PublicEpsilonIota.rootCheck q root = true) :
    Mu.sourceValue q root = PublicEpsilonIota.Mu.sourceValue q root := by
  rw [Mu.sourceValue, PublicEpsilonIota.Mu.sourceValue, betaCode_eq q root ha,
    mappedCoefficient_eq q root ha, coefficientOffset_eq q root ha]

theorem execute_eq (q root : Nat) (ha : PublicEpsilonIota.rootCheck q root = true) :
    Mu.execute q root = PublicEpsilonIota.Mu.execute q root := by
  simp only [Mu.execute, PublicEpsilonIota.Mu.execute, ha, root_caller q root ha,
    Bool.cond_true, muCode_eq q root ha]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.LegacyAgreement
