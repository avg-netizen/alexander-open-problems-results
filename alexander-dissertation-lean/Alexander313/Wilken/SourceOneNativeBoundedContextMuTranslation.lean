import Alexander313.Wilken.SourceOneNativeBoundedContextSourceReturn
import Alexander313.Wilken.SourceOneNativeMu
import Alexander313.Wilken.HereditaryNativeSourceChiInvariance

/-!
# Genuine mu translation through the original source-one return

The constructed original source-zero return preserves the actual high part,
zero-or-limit coefficient and finite suffix. Original Normal order reflection
and the proved full iota commutation identify the genuine mapped coefficients
at the same canonical beta. Actual chi invariance, finite-tail addition and
omega powers then identify executing Definition 3.6 outputs. The intermediate
caller is the genuine selected original endpoint; no Native base-one parser,
coefficient, indicator or mu invariance oracle. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.BoundedContextReturn.MuTranslation

open BoundedContextReturn

theorem mappedCoefficient_value (a b : Nat) (ha : SourceOneIota.rootCheck a = true)
    (hb : NativeContext.PublicEpsilonIota.rootCheck (alphaCode a) b = true) :
    NativeContext.interpretation (NativeContext.PublicEpsilonIota.betaCode (alphaCode a) b)
        (SourceOneIota.Mu.mappedCoefficient (returnedRoot a b)) =
      NativeContext.interpretation (NativeContext.PublicEpsilonIota.betaCode (alphaCode a) b)
        (NativeContext.PublicEpsilonIota.Mu.mappedCoefficient (alphaCode a) b) := by
  have hroot := returnedRoot_iota_caller a b ha hb
  have hn := NativeContext.PublicEpsilonIota.OmegaQuotient.coefficientCode_spec (alphaCode a) b hb
  obtain ⟨_, t, he, ht, hnt, hstar⟩ :=
    (NativeContext.PublicEpsilonIota.inputCheck_exact (alphaCode a) b _).mp hn.2.1
  have hrt := (NativeContext.PublicEpsilonIota.restricted_iff_sourceStar (alphaCode a) b hb t ht hnt).mpr hstar
  have hs := returnedTerm_spec a b ha hb t ht hnt hrt
  have hcut := returnedTerm_restricted a b ha hb t ht hnt hrt
  have ho := SourceOneIota.OmegaQuotient.coefficientCode_spec (returnedRoot a b) hroot
  have hct := SourceDecomposition.input_tree 0 _ ho.1
  obtain ⟨_, u, heu, hu, hnu, hsu⟩ := (SourceOneIota.inputCheck_exact _ _).mp ho.2.1
  have hcu : SourceOneIota.Restricted (returnedRoot a b)
      (ThetaCourse.rawTree (SourceOneIota.OmegaQuotient.coefficientCode (returnedRoot a b))) := by
    simpa only [heu, ThetaCourse.rawTree_code] using
      (SourceOneIota.restricted_iff_sourceStar _ hroot u hu hnu).mpr hsu
  have hv : denote 0
      (ThetaCourse.rawTree (SourceOneIota.OmegaQuotient.coefficientCode (returnedRoot a b))) =
        denote 0 (returnedTerm a t) := by
    rw [← SourceDecomposition.input_value 0 _ ho.1,
      (returnedRoot_coefficient_value a b ha hb).1, he, NativeContext.interpretation_code, hs.2.2]
  have hi := (SourceOneIota.transform_eq_iff (returnedRoot a b) hroot _ _
    hct.1 hs.1 hct.2 hs.2.1 hcu hcut).mpr hv
  rw [returnedRoot_alphaCode a b ha hb] at hi
  have hc := transform_return_value a b ha hb t ht hnt hrt
  have hcode : SourceOneIota.literalCode (returnedRoot a b)
      (SourceOneIota.OmegaQuotient.coefficientCode (returnedRoot a b)) =
        (SourceOneIota.transform (returnedRoot a b)
          (ThetaCourse.rawTree (SourceOneIota.OmegaQuotient.coefficientCode (returnedRoot a b)))).code := by
    simp only [SourceOneIota.literalCode, ho.2.1, Bool.cond_true, heu,
      SourceOneIota.stateCode_code, ThetaCourse.rawTree_code]
  simpa only [SourceOneIota.Mu.mappedCoefficient, hcode,
    NativeContext.PublicEpsilonIota.Mu.mappedCoefficient, he,
    NativeContext.PublicEpsilonIota.literalCode_code (alphaCode a) b hb t ht hnt hrt,
    NativeContext.interpretation_code] using hi.trans hc

theorem chi_eq (a b : Nat) (ha : SourceOneIota.rootCheck a = true)
    (hb : NativeContext.PublicEpsilonIota.rootCheck (alphaCode a) b = true) :
    SourceOneIota.Mu.chi (returnedRoot a b) =
      NativeContext.PublicEpsilonIota.Mu.chi (alphaCode a) b := by
  have ho := (SourceOneIota.Mu.mappedCoefficient_spec _ (returnedRoot_iota_caller a b ha hb)).2
  rw [returnedRoot_alphaCode a b ha hb] at ho
  have hn := (NativeContext.PublicEpsilonIota.Mu.mappedCoefficient_spec (alphaCode a) b hb).2
  have hs := NativeContext.SourceChi.Invariance.chiCode_invariant _ _ _ ho hn
    (mappedCoefficient_value a b ha hb)
  simpa only [SourceOneIota.Mu.chi, NativeContext.PublicEpsilonIota.Mu.chi,
    returnedRoot_alphaCode a b ha hb] using hs

theorem exponentCode_value (a b : Nat) (ha : SourceOneIota.rootCheck a = true)
    (hb : NativeContext.PublicEpsilonIota.rootCheck (alphaCode a) b = true) :
    NativeContext.interpretation (NativeContext.PublicEpsilonIota.betaCode (alphaCode a) b)
        (SourceOneIota.Mu.exponentCode (returnedRoot a b)) =
      NativeContext.interpretation (NativeContext.PublicEpsilonIota.betaCode (alphaCode a) b)
        (NativeContext.PublicEpsilonIota.Mu.exponentCode (alphaCode a) b) := by
  have ho := (SourceOneIota.Mu.exponentCode_spec _ (returnedRoot_iota_caller a b ha hb)).2.2
  rw [returnedRoot_alphaCode a b ha hb] at ho
  rw [ho, (NativeContext.PublicEpsilonIota.Mu.exponentCode_spec (alphaCode a) b hb).2.2,
    mappedCoefficient_value a b ha hb, chi_eq a b ha hb, (returnedRoot_coefficient_value a b ha hb).2]

theorem muCode_value (a b : Nat) (ha : SourceOneIota.rootCheck a = true)
    (hb : NativeContext.PublicEpsilonIota.rootCheck (alphaCode a) b = true) :
    NativeContext.interpretation (NativeContext.PublicEpsilonIota.betaCode (alphaCode a) b)
        (SourceOneIota.Mu.muCode (returnedRoot a b)) =
      NativeContext.interpretation (NativeContext.PublicEpsilonIota.betaCode (alphaCode a) b)
        (NativeContext.PublicEpsilonIota.Mu.muCode (alphaCode a) b) := by
  have hroot := returnedRoot_iota_caller a b ha hb
  have he := (SourceOneIota.Mu.exponentCode_spec _ hroot).1
  have ho := (NativeContext.OmegaPowers.powerCode_spec (SourceOneIota.alphaCode (returnedRoot a b))
    (SourceOneIota.Mu.exponentCode (returnedRoot a b)) he).2.2
  rw [returnedRoot_alphaCode a b ha hb] at ho
  have hn := (NativeContext.OmegaPowers.powerCode_spec
    (NativeContext.PublicEpsilonIota.betaCode (alphaCode a) b)
    (NativeContext.PublicEpsilonIota.Mu.exponentCode (alphaCode a) b)
    (NativeContext.PublicEpsilonIota.Mu.exponentCode_spec (alphaCode a) b hb).1).2.2
  rw [SourceOneIota.Mu.muCode_literal _ hroot, returnedRoot_alphaCode a b ha hb,
    NativeContext.PublicEpsilonIota.Mu.muCode_literal (alphaCode a) b hb, ho, hn,
    exponentCode_value a b ha hb]

/-- Both genuine normal executions have the same beta and output value. -/
theorem execute_translation (a b out : Nat) (ha : SourceOneIota.rootCheck a = true)
    (ho : out ∈ NativeContext.PublicEpsilonIota.Mu.execute (alphaCode a) b) :
    ∃ originalOut : Nat, originalOut ∈ SourceOneIota.Mu.execute (returnedRoot a b) ∧
      SourceOneIota.alphaCode (returnedRoot a b) = NativeContext.PublicEpsilonIota.betaCode (alphaCode a) b ∧
      NativeContext.interpretation (NativeContext.PublicEpsilonIota.betaCode (alphaCode a) b) originalOut =
        NativeContext.interpretation (NativeContext.PublicEpsilonIota.betaCode (alphaCode a) b) out := by
  obtain ⟨hb, rfl⟩ := (NativeContext.PublicEpsilonIota.Mu.execute_graph _ _ out).mp ho
  refine ⟨SourceOneIota.Mu.muCode (returnedRoot a b), ?_,
    returnedRoot_alphaCode a b ha hb, muCode_value a b ha hb⟩
  exact (SourceOneIota.Mu.execute_graph _ _).mpr ⟨returnedRoot_iota_caller a b ha hb, rfl⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.BoundedContextReturn.MuTranslation
