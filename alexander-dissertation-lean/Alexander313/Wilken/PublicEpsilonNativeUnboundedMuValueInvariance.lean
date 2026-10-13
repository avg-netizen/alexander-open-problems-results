import Alexander313.Wilken.PublicEpsilonNativeUnboundedMu
import Alexander313.Wilken.HereditaryNativeSourceChiInvariance
import Alexander313.Wilken.LimitFiniteDecomposition

/-!
# Actual mu is independent of original high-root spelling

At the SAME original admitted coded epsilon, real theta injection fixes
both original argument values. Actual high-part division and uniqueness
of the constructed zero-or-limit plus finite coefficient fix both quotient
components. Full original iota order and the genuine SAME-base chi theorem
then identify the computed exponents and mu values. No mu, coefficient,
indicator or normalization invariance is assumed. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.Mu.ValueInvariance

open ThetaCourse

/-- Equal original root values supply the SAME literal canonical target
base; both public return callers follow from the original root checks. -/
theorem betaCode_eq (q r s : Nat) (hr : rootCheck q r = true)
    (hs : rootCheck q s = true) (hv : interpretation q r = interpretation q s) :
    betaCode q r = betaCode q s :=
  UniformPublicReturn.publicCode_value_invariant q q r s
    ((UniformPublicReturn.inputCheck_exact q r).mpr (RootLowCollapse.root_low q r hr))
    ((UniformPublicReturn.inputCheck_exact q s).mpr (RootLowCollapse.root_low q s hs)) hv

theorem restricted_eq (q r s : Nat) (hv : interpretation q r = interpretation q s)
    (t : RelativeTerm Nat) : Restricted q r t ↔ Restricted q s t := by
  simp only [Restricted, hv]

theorem small_eq (q r s : Nat) (hr : rootCheck q r = true)
    (hs : rootCheck q s = true) (hv : interpretation q r = interpretation q s)
    (t : RelativeTerm Nat) (ht : check q t = true) : small q r t = small q s t := by
  cases h : small q r t with
  | true =>
    have hl := (small_exact q r hr t ht).mp h
    have he := (small_exact q s hs t ht).mpr (by rw [← hv]; exact hl)
    exact he.symm
  | false =>
    have he : small q s t = false := by
      apply Bool.eq_false_of_not_eq_true
      intro htrue
      have hl := (small_exact q s hs t ht).mp htrue
      have hh := (small_exact q r hr t ht).mpr (by rw [hv]; exact hl)
      rw [h] at hh
      cases hh
    exact he.symm

/-- The literal transform uses root values only at its genuine comparisons;
all stopped payloads already use the unchanged original q producer. -/
theorem transform_eq (q r s : Nat) (hr : rootCheck q r = true)
    (hs : rootCheck q s = true) (hv : interpretation q r = interpretation q s)
    (t : RelativeTerm Nat) (ht : check q t = true) : transform q r t = transform q s t := by
  revert ht
  induction t with
  | parameter p => intro ht; rfl
  | sum t u iht ihu =>
    intro ht
    have hc := BaseTransformation.sum_checks q t u ht
    simp only [transform, small_eq q r s hr hs hv (.sum t u) ht,
      iht hc.1, ihu hc.2]
  | theta k t ih =>
    intro ht
    simp only [transform, small_eq q r s hr hs hv (.theta k t) ht,
      ih (BaseTransformation.theta_argument_check q k t ht)]

theorem argument_value_eq (q r s : Nat) (hr : rootCheck q r = true)
    (hs : rootCheck q s = true) (hv : interpretation q r = interpretation q s) :
    interpretation q (OmegaQuotient.argumentCode r) =
      interpretation q (OmegaQuotient.argumentCode s) := by
  obtain ⟨a, he, ha, hn, hh⟩ := (rootCheck_exact q r).mp hr
  obtain ⟨b, hf, hb, hm, hi⟩ := (rootCheck_exact q s).mp hs
  have hx : denote q (.theta 0 a) = denote q (.theta 0 b) := by
    simpa only [he, hf, interpretation_code] using hv
  have hi := (SourceChi.Invariance.theta_value_injective q 0 0 a b ha hb hx).2
  simpa only [OmegaQuotient.argumentCode, he, hf, Localization.argumentCode_theta,
    interpretation_code] using hi

theorem delta_value_eq (q r s : Nat) (hr : rootCheck q r = true)
    (hs : rootCheck q s = true) (hv : interpretation q r = interpretation q s) :
    interpretation q (OmegaQuotient.deltaCode r) =
      interpretation q (OmegaQuotient.deltaCode s) := by
  rw [OmegaQuotient.deltaCode, OmegaQuotient.deltaCode,
    (Decomposition.parts_code_value q 0 _ (OmegaQuotient.Support.argument_accepted q r hr)).1,
    (Decomposition.parts_code_value q 0 _ (OmegaQuotient.Support.argument_accepted q s hs)).1,
    argument_value_eq q r s hr hs hv]

theorem coefficient_value_eq (q r s : Nat) (hr : rootCheck q r = true)
    (hs : rootCheck q s = true) (hv : interpretation q r = interpretation q s) :
    interpretation q (OmegaQuotient.coefficientCode q r) =
        interpretation q (OmegaQuotient.coefficientCode q s) ∧
      OmegaQuotient.coefficientOffset q r = OmegaQuotient.coefficientOffset q s := by
  have hc := OmegaQuotient.coefficientCode_spec q r hr
  have hd := OmegaQuotient.coefficientCode_spec q s hs
  apply LimitFiniteDecomposition.high_part_coefficient_unique (omegaSequence (base q) 1) _ _ _ _
    (omegaSequence_isSuccLimit (base q) 0).bot_lt hc.2.2.1 hd.2.2.1
  exact hc.2.2.2.trans ((delta_value_eq q r s hr hs hv).trans hd.2.2.2.symm)

/-- Both actual coefficient expressions have the same iota value, by true
original-domain order reflection and the literal equal-root transform. -/
theorem mappedCoefficient_value_eq (q r s : Nat) (hr : rootCheck q r = true)
    (hs : rootCheck q s = true) (hv : interpretation q r = interpretation q s) :
    interpretation (betaCode q r) (mappedCoefficient q r) =
      interpretation (betaCode q s) (mappedCoefficient q s) := by
  let t := BoundedContextIota.OmegaQuotient.limitTerm q (OmegaQuotient.argumentCode r)
  let u := BoundedContextIota.OmegaQuotient.limitTerm q (OmegaQuotient.argumentCode s)
  have hc := OmegaQuotient.root_coefficient_spec q r hr
  have hd := OmegaQuotient.root_coefficient_spec q s hs
  have hcut : Restricted q r u :=
    (restricted_eq q r s hv u).mpr hd.2.2.1
  have he : denote q t = denote q u := by
    simpa only [OmegaQuotient.coefficientCode_literal q r hr,
      OmegaQuotient.coefficientCode_literal q s hs, interpretation_code] using
        (coefficient_value_eq q r s hr hs hv).1
  have hm := (transform_eq_iff q r hr t u hc.1 hd.1 hc.2.1 hd.2.1 hc.2.2.1 hcut).mpr he
  have hb := betaCode_eq q r s hr hs hv
  calc
    interpretation (betaCode q r) (mappedCoefficient q r) =
        denote (betaCode q r) (transform q r t) := by
      rw [mappedCoefficient, OmegaQuotient.coefficientCode_literal q r hr,
        literalCode_code q r hr _ hc.1 hc.2.1 hc.2.2.1, interpretation_code]
    _ = denote (betaCode q r) (transform q r u) := hm
    _ = denote (betaCode q s) (transform q s u) := by
      rw [hb, transform_eq q r s hr hs hv u hd.1]
    _ = interpretation (betaCode q s) (mappedCoefficient q s) := by
      rw [mappedCoefficient, OmegaQuotient.coefficientCode_literal q s hs,
        literalCode_code q s hs _ hd.1 hd.2.1 hd.2.2.1, interpretation_code]

/-- The actual Boolean source chi is preserved at the SAME genuine beta
context, after its two original admission callers have been constructed. -/
theorem chi_eq (q r s : Nat) (hr : rootCheck q r = true)
    (hs : rootCheck q s = true) (hv : interpretation q r = interpretation q s) :
    chi q r = chi q s := by
  have hc := (mappedCoefficient_spec q r hr).2
  have hd := (mappedCoefficient_spec q s hs).2
  have he := mappedCoefficient_value_eq q r s hr hs hv
  have hb := betaCode_eq q r s hr hs hv
  rw [← hb] at hd he
  have hm := SourceChi.Invariance.chiCode_invariant (betaCode q r)
    (mappedCoefficient q r) (mappedCoefficient q s)
    ((SourceChi.inputCheck_exact _ _).mpr ((Comparison.acceptedCode_exact _ _).mp hc))
    ((SourceChi.inputCheck_exact _ _).mpr ((Comparison.acceptedCode_exact _ _).mp hd)) he
  simpa only [chi, ← hb] using hm

/-- Full original-source mu value invariance derives all coefficient and
indicator equalities from the original checked high-root value equality. -/
theorem sourceValue_eq (q r s : Nat) (hr : rootCheck q r = true)
    (hs : rootCheck q s = true) (hv : interpretation q r = interpretation q s) :
    sourceValue q r = sourceValue q s := by
  rw [sourceValue, sourceValue, ← chi_correct q r hr, ← chi_correct q s hs,
    mappedCoefficient_value_eq q r s hr hs hv, chi_eq q r s hr hs hv,
    (coefficient_value_eq q r s hr hs hv).2]

theorem execute_value_eq (q r s x y : Nat) (hx : x ∈ execute q r)
    (hy : y ∈ execute q s) (hv : interpretation q r = interpretation q s) :
    interpretation (betaCode q r) x = interpretation (betaCode q s) y := by
  have hc := execute_spec q r x hx
  have hd := execute_spec q s y hy
  exact hc.2.2.2.trans ((sourceValue_eq q r s hc.1 hd.1 hv).trans hd.2.2.2.symm)

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.Mu.ValueInvariance
