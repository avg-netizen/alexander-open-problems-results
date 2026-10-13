import Alexander313.Wilken.HereditaryNativeBoundedContextSourceReturn
import Alexander313.Wilken.HereditaryNativeBoundedContextIotaReturn
import Alexander313.Wilken.HereditaryNativeSourceChiInvariance
import Alexander313.Wilken.HereditaryNativeMu

/-!
# Genuine mu translation on the bounded intermediate source

The actual finite return constructs an original-source high root with the
same canonical beta. Its genuine high part fixes the zero-or-limit and
finite quotient components. Actual iota commutation and original Normal
order reflection identify the mapped coefficients. The proved same-value
source indicator theorem identifies chi, and the real finite-tail and
omega-power producers therefore execute equal mu values.

This proves the source 3.8 equation for a genuine positive outer original
source and its admitted Normal high intermediate root below the ORIGINAL
outer alpha-plus. No returned-root, quotient, iota, chi or mu invariance
oracle is an input. The outer source-one adapter is separate. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.BoundedContextIota.Mu.Translation

open NativePublicBridge (contextCode)
open SourceReturn

theorem mappedCoefficient_value (s a root : Nat) (ha : inputCheck s a root = true) :
    interpretation (betaCode s a root)
        (NativeContext.Mu.mappedCoefficient s (returnedRoot s a root)) =
      interpretation (betaCode s a root) (mappedCoefficient s a root) := by
  have hroot := returnedRoot_iota_caller s a root ha
  have hn := OmegaQuotient.coefficientCode_spec s a root ha
  obtain ⟨_, t, he, ht, hnt, hstar⟩ :=
    (BoundedContextIota.inputCheck_exact s a root _).mp hn.2.1
  have hrt := (restricted_iff_sourceStar s a root ha t ht hnt).mpr hstar
  have hs := returnedTerm_spec s a root ha t ht hnt hrt
  have hcut := returnedTerm_restricted s a root ha t ht hnt hrt
  have ho := NativeContext.OmegaQuotient.coefficientCode_spec s (returnedRoot s a root) hroot
  have hct := Decomposition.input_tree (contextCode s) _ ho.1
  obtain ⟨_, u, heu, hu, hnu, hsu⟩ := (Iota.inputCheck_exact s _ _).mp ho.2.1
  have hcu : Iota.Restricted s (returnedRoot s a root)
      (ThetaCourse.rawTree (NativeContext.OmegaQuotient.coefficientCode s (returnedRoot s a root))) := by
    simpa only [heu, ThetaCourse.rawTree_code] using
      (Iota.restricted_iff_sourceStar s _ hroot u hu hnu).mpr hsu
  have hv : denote (contextCode s)
      (ThetaCourse.rawTree (NativeContext.OmegaQuotient.coefficientCode s (returnedRoot s a root))) =
        denote (contextCode s) (returnedTerm s a t) := by
    rw [Arithmetic.raw_value (contextCode s) _ ((Comparison.acceptedCode_exact _ _).mp ho.1).1,
      (returnedRoot_coefficient_value s a root ha).1, he, interpretation_code, hs.2.2]
  have hi := (Iota.transform_eq_iff s (returnedRoot s a root) hroot _ _
    hct.1 hs.1 hct.2 hs.2.1 hcu hcut).mpr hv
  rw [returnedRoot_alphaCode s a root ha] at hi
  have hc := transform_return_value s a root ha t ht hnt hrt
  have hcode : Iota.literalCode s (returnedRoot s a root)
      (NativeContext.OmegaQuotient.coefficientCode s (returnedRoot s a root)) =
        (Iota.transform s (returnedRoot s a root)
          (ThetaCourse.rawTree (NativeContext.OmegaQuotient.coefficientCode s (returnedRoot s a root)))).code := by
    simp only [Iota.literalCode, ho.2.1, Bool.cond_true, heu, Iota.stateCode_code, ThetaCourse.rawTree_code]
  simpa only [NativeContext.Mu.mappedCoefficient, hcode, mappedCoefficient, he,
    literalCode_code s a root ha t ht hnt hrt, interpretation_code] using hi.trans hc

theorem chi_eq (s a root : Nat) (ha : inputCheck s a root = true) :
    NativeContext.Mu.chi s (returnedRoot s a root) = chi s a root := by
  have ho := (NativeContext.Mu.mappedCoefficient_spec s _ (returnedRoot_iota_caller s a root ha)).2
  rw [returnedRoot_alphaCode s a root ha] at ho
  have hn := (mappedCoefficient_spec s a root ha).2
  have hs := SourceChi.Invariance.chiCode_invariant (betaCode s a root) _ _ ho hn
    (mappedCoefficient_value s a root ha)
  simpa only [NativeContext.Mu.chi, chi, returnedRoot_alphaCode s a root ha] using hs

theorem exponentCode_value (s a root : Nat) (ha : inputCheck s a root = true) :
    interpretation (betaCode s a root)
        (NativeContext.Mu.exponentCode s (returnedRoot s a root)) =
      interpretation (betaCode s a root) (exponentCode s a root) := by
  have ho := (NativeContext.Mu.exponentCode_spec s _ (returnedRoot_iota_caller s a root ha)).2.2
  rw [returnedRoot_alphaCode s a root ha] at ho
  rw [ho, (exponentCode_spec s a root ha).2.2, mappedCoefficient_value s a root ha,
    chi_eq s a root ha, (returnedRoot_coefficient_value s a root ha).2]

theorem muCode_value (s a root : Nat) (ha : inputCheck s a root = true) :
    interpretation (betaCode s a root)
        (NativeContext.Mu.muCode s (returnedRoot s a root)) =
      interpretation (betaCode s a root) (muCode s a root) := by
  have hroot := returnedRoot_iota_caller s a root ha
  have he := (NativeContext.Mu.exponentCode_spec s _ hroot).1
  have ho := (OmegaPowers.powerCode_spec (Iota.alphaCode s (returnedRoot s a root))
    (NativeContext.Mu.exponentCode s (returnedRoot s a root)) he).2.2
  rw [returnedRoot_alphaCode s a root ha] at ho
  have hn := (OmegaPowers.powerCode_spec (betaCode s a root) (exponentCode s a root)
    (exponentCode_spec s a root ha).1).2.2
  rw [NativeContext.Mu.muCode_literal s _ hroot, returnedRoot_alphaCode s a root ha,
    muCode_literal s a root ha, ho, hn, exponentCode_value s a root ha]

/-- Actual normal executions satisfy the source 3.8 translation equation;
the original-source mu caller is a conclusion of the intermediate guard. -/
theorem execute_translation (s a root out : Nat) (ho : out ∈ execute s a root) :
    ∃ originalOut : Nat, originalOut ∈ NativeContext.Mu.execute s (returnedRoot s a root) ∧
      Iota.alphaCode s (returnedRoot s a root) = betaCode s a root ∧
      interpretation (betaCode s a root) originalOut = interpretation (betaCode s a root) out := by
  obtain ⟨ha, rfl⟩ := (execute_graph s a root out).mp ho
  refine ⟨NativeContext.Mu.muCode s (returnedRoot s a root), ?_,
    returnedRoot_alphaCode s a root ha, muCode_value s a root ha⟩
  exact (NativeContext.Mu.execute_graph s _ _).mpr
    ⟨returnedRoot_iota_caller s a root ha, rfl⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.BoundedContextIota.Mu.Translation
