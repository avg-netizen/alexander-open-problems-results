import Alexander313.Wilken.SourceOneNativeMu
import Alexander313.Wilken.HereditaryNativeSourceChiInvariance
import Alexander313.Wilken.LimitFiniteDecomposition

/-!
# Actual original-source-one mu spelling invariance

All source callers use the ORIGINAL check zero and Theta.Normal zero.
Actual global theta injection fixes original arguments, real Omega-one
coefficient uniqueness fixes lambda and the finite offset, and full original
iota order fixes the mapped values. Chi is compared only at the genuine
SAME canonical alpha output context. No native base-one parser or assumed
mu, coefficient, indicator or normalization invariance. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.Mu.ValueInvariance

open ThetaCourse

theorem alphaCode_eq (r s : Nat) (hr : rootCheck r = true)
    (hs : rootCheck s = true) (hv : interpretation 0 r = interpretation 0 s) :
    alphaCode r = alphaCode s := by
  have hc := alphaCode_spec r hr
  have hd := alphaCode_spec s hs
  exact Canonical.check_value_injective _ _ hc.1 hd.1
    (hc.2.trans (hv.trans hd.2.symm))

theorem restricted_eq (r s : Nat) (hv : interpretation 0 r = interpretation 0 s)
    (t : RelativeTerm Nat) : Restricted r t ↔ Restricted s t := by
  simp only [Restricted, hv]

theorem small_eq (r s : Nat) (hr : rootCheck r = true)
    (hs : rootCheck s = true) (hv : interpretation 0 r = interpretation 0 s)
    (t : RelativeTerm Nat) (ht : check 0 t = true) : small r t = small s t := by
  cases h : small r t with
  | true =>
    have hl := (small_exact r hr t ht).mp h
    have he := (small_exact s hs t ht).mpr (by rw [← hv]; exact hl)
    exact he.symm
  | false =>
    have he : small s t = false := by
      apply Bool.eq_false_of_not_eq_true
      intro htrue
      have hl := (small_exact s hs t ht).mp htrue
      have hh := (small_exact r hr t ht).mpr (by rw [hv]; exact hl)
      rw [h] at hh
      cases hh
    exact he.symm

theorem transform_eq (r s : Nat) (hr : rootCheck r = true)
    (hs : rootCheck s = true) (hv : interpretation 0 r = interpretation 0 s)
    (t : RelativeTerm Nat) (ht : check 0 t = true) : transform r t = transform s t := by
  revert ht
  induction t with
  | parameter p => intro ht; rfl
  | sum t u iht ihu =>
    intro ht
    have hc := OrderSupport.sum_checks t u ht
    simp only [transform, small_eq r s hr hs hv (.sum t u) ht,
      iht hc.1, ihu hc.2]
  | theta k t ih =>
    intro ht
    simp only [transform, small_eq r s hr hs hv (.theta k t) ht,
      ih (OrderSupport.argument_checked k t ht)]

/-- Genuine original-source-zero notation and sort bounds license actual
collapse injection; no epsilon native dictionary is used at source one. -/
theorem argument_value_eq (r s : Nat) (hr : rootCheck r = true)
    (hs : rootCheck s = true) (hv : interpretation 0 r = interpretation 0 s) :
    interpretation 0 (OmegaQuotient.argumentCode r) =
      interpretation 0 (OmegaQuotient.argumentCode s) := by
  obtain ⟨a, he, ha, hn, hh⟩ := (rootCheck_exact r).mp hr
  obtain ⟨b, hf, hb, hm, hi⟩ := (rootCheck_exact s).mp hs
  have hac := SourceFixedPoint.checked_theta_argument 0 0 a ha
  have hbc := SourceFixedPoint.checked_theta_argument 0 0 b hb
  have hx : globalCollapse (finiteBase 0) 0 (denote 0 a) =
      globalCollapse (finiteBase 0) 0 (denote 0 b) := by
    simpa only [he, hf, interpretation_code, denote, RelativeTerm.eval] using hv
  have harg := (globalCollapse_eq_iff (finiteBase 0) (finiteBase_pos 0) 0
    (SourceFixedPoint.sourceOrdinal 0 0 a hac)
    (SourceFixedPoint.sourceOrdinal 0 0 b hbc)
    (SourceFixedPoint.checked_theta_sort 0 0 a ha)
    (SourceFixedPoint.checked_theta_sort 0 0 b hb)).mp hx
  simpa only [OmegaQuotient.argumentCode, he, hf, Localization.argumentCode_theta,
    interpretation_code] using harg

theorem delta_value_eq (r s : Nat) (hr : rootCheck r = true)
    (hs : rootCheck s = true) (hv : interpretation 0 r = interpretation 0 s) :
    interpretation 0 (OmegaQuotient.deltaCode r) =
      interpretation 0 (OmegaQuotient.deltaCode s) := by
  rw [OmegaQuotient.deltaCode, OmegaQuotient.deltaCode,
    (SourceDecomposition.parts_code_value 0 0 _ (OmegaQuotient.argument_accepted r hr)).1,
    (SourceDecomposition.parts_code_value 0 0 _ (OmegaQuotient.argument_accepted s hs)).1,
    argument_value_eq r s hr hs hv]

theorem coefficient_value_eq (r s : Nat) (hr : rootCheck r = true)
    (hs : rootCheck s = true) (hv : interpretation 0 r = interpretation 0 s) :
    interpretation 0 (OmegaQuotient.coefficientCode r) =
        interpretation 0 (OmegaQuotient.coefficientCode s) ∧
      OmegaQuotient.coefficientOffset r = OmegaQuotient.coefficientOffset s := by
  have hc := OmegaQuotient.coefficientCode_spec r hr
  have hd := OmegaQuotient.coefficientCode_spec s hs
  apply LimitFiniteDecomposition.high_part_coefficient_unique (omegaSequence (finiteBase 0) 1) _ _ _ _
    (omegaSequence_isSuccLimit (finiteBase 0) 0).bot_lt hc.2.2.1 hd.2.2.1
  exact hc.2.2.2.trans ((delta_value_eq r s hr hs hv).trans hd.2.2.2.symm)

theorem mappedCoefficient_value_eq (r s : Nat) (hr : rootCheck r = true)
    (hs : rootCheck s = true) (hv : interpretation 0 r = interpretation 0 s) :
    NativeContext.interpretation (alphaCode r) (mappedCoefficient r) =
      NativeContext.interpretation (alphaCode s) (mappedCoefficient s) := by
  let t := OmegaQuotient.limitTerm (OmegaQuotient.argumentCode r)
  let u := OmegaQuotient.limitTerm (OmegaQuotient.argumentCode s)
  have hc := OmegaQuotient.root_coefficient_spec r hr
  have hd := OmegaQuotient.root_coefficient_spec s hs
  have hcut : Restricted r u := (restricted_eq r s hv u).mpr hd.2.2.1
  have he : denote 0 t = denote 0 u := by
    simpa only [OmegaQuotient.coefficientCode_literal r hr,
      OmegaQuotient.coefficientCode_literal s hs, interpretation_code] using
        (coefficient_value_eq r s hr hs hv).1
  have hm := (transform_eq_iff r hr t u hc.1 hd.1 hc.2.1 hd.2.1 hc.2.2.1 hcut).mpr he
  have hb := alphaCode_eq r s hr hs hv
  calc
    NativeContext.interpretation (alphaCode r) (mappedCoefficient r) =
        NativeContext.denote (alphaCode r) (transform r t) := by
      rw [mappedCoefficient, OmegaQuotient.coefficientCode_literal r hr,
        literalCode_code r hr _ hc.1 hc.2.1 hc.2.2.1, NativeContext.interpretation_code]
    _ = NativeContext.denote (alphaCode r) (transform r u) := hm
    _ = NativeContext.denote (alphaCode s) (transform s u) := by
      rw [hb, transform_eq r s hr hs hv u hd.1]
    _ = NativeContext.interpretation (alphaCode s) (mappedCoefficient s) := by
      rw [mappedCoefficient, OmegaQuotient.coefficientCode_literal s hs,
        literalCode_code s hs _ hd.1 hd.2.1 hd.2.2.1, NativeContext.interpretation_code]

theorem chi_eq (r s : Nat) (hr : rootCheck r = true)
    (hs : rootCheck s = true) (hv : interpretation 0 r = interpretation 0 s) :
    chi r = chi s := by
  have hc := (mappedCoefficient_spec r hr).2
  have hd := (mappedCoefficient_spec s hs).2
  have he := mappedCoefficient_value_eq r s hr hs hv
  have hb := alphaCode_eq r s hr hs hv
  rw [← hb] at hd he
  have hm := NativeContext.SourceChi.Invariance.chiCode_invariant (alphaCode r)
    (mappedCoefficient r) (mappedCoefficient s)
    ((NativeContext.SourceChi.inputCheck_exact _ _).mpr ((NativeContext.Comparison.acceptedCode_exact _ _).mp hc))
    ((NativeContext.SourceChi.inputCheck_exact _ _).mpr ((NativeContext.Comparison.acceptedCode_exact _ _).mp hd)) he
  simpa only [chi, ← hb] using hm

theorem sourceValue_eq (r s : Nat) (hr : rootCheck r = true)
    (hs : rootCheck s = true) (hv : interpretation 0 r = interpretation 0 s) :
    sourceValue r = sourceValue s := by
  rw [sourceValue, sourceValue, ← chi_correct r hr, ← chi_correct s hs,
    mappedCoefficient_value_eq r s hr hs hv, chi_eq r s hr hs hv,
    (coefficient_value_eq r s hr hs hv).2]

theorem execute_value_eq (r s x y : Nat) (hx : x ∈ execute r)
    (hy : y ∈ execute s) (hv : interpretation 0 r = interpretation 0 s) :
    NativeContext.interpretation (alphaCode r) x = NativeContext.interpretation (alphaCode s) y := by
  have hc := execute_spec r x hx
  have hd := execute_spec s y hy
  exact hc.2.2.2.trans ((sourceValue_eq r s hc.1 hd.1 hv).trans hd.2.2.2.symm)

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.Mu.ValueInvariance
