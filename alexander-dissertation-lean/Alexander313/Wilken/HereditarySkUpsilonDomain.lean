import Alexander313.Wilken.HereditarySourceUpsilonSupport
import Alexander313.Wilken.HereditarySkFiniteUpsilonDomain

/-!
# Exact upsilon-image domain of the public selected-source sk procedure

Every actual canonical public epsilon lies below the independently
constructed upsilon omega. The genuine ordinal source-grammar iteration
has only finite-index image values below that endpoint. Thus the real
finite dictionary basepoint test is exactly membership in the actual
semantic upsilon image, and its executing proper guard is exactly the
printed image exclusion on the constructed public domain. No arbitrary
cross-context mu, transfinite coding or assigned global TS/evaluation
claim is made. Uncompiled source candidate.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SkPublicDictionary.UpsilonDomain

theorem basePoint_true_iff_image (gamma : Nat)
    (hg : PublicEpsilonSourceDictionary.inputCheck gamma = true) :
    PublicEpsilonSourceDictionary.basePoint gamma = true ↔
      SourceUpsilonImage (unionInterpretation gamma) :=
  (FiniteDomain.basePoint_true_iff_finite gamma hg).trans
    (sourceUpsilon_image_below_omega _ (FiniteDomain.below_sourceUpsilonOmega gamma hg)).symm

theorem basePoint_false_iff_not_image (gamma : Nat)
    (hg : PublicEpsilonSourceDictionary.inputCheck gamma = true) :
    PublicEpsilonSourceDictionary.basePoint gamma = false ↔
      ¬ SourceUpsilonImage (unionInterpretation gamma) := by
  constructor
  · intro hb himage
    have ht := (basePoint_true_iff_image gamma hg).mpr himage
    rw [hb] at ht
    cases ht
  · intro hn
    cases hb : PublicEpsilonSourceDictionary.basePoint gamma with
    | false => rfl
    | true => exact False.elim (hn ((basePoint_true_iff_image gamma hg).mp hb))

/-- The actual selected-source public guard has exactly the original
canonical epsilon, genuine source-upsilon image exclusion and cutoff domain. -/
theorem inputCheck_exact (gamma cutoff : Nat) :
    Support.inputCheck gamma cutoff = true ↔
      Canonical.check gamma = true ∧
        Ordinal.omega0 ^ unionInterpretation gamma = unionInterpretation gamma ∧
          ¬ SourceUpsilonImage (unionInterpretation gamma) ∧ unionCheck cutoff = true := by
  constructor
  · intro hi
    have hs := (Support.inputCheck_exact gamma cutoff).mp hi
    have he := (PublicEpsilonSourceDictionary.inputCheck_exact gamma).mp hs.1
    exact ⟨he.1, he.2, (basePoint_false_iff_not_image gamma hs.1).mp hs.2.1, hs.2.2⟩
  · rintro ⟨hc, he, hn, hcut⟩
    have hg := (PublicEpsilonSourceDictionary.inputCheck_exact gamma).mpr ⟨hc, he⟩
    exact (Support.inputCheck_exact gamma cutoff).mpr
      ⟨hg, (basePoint_false_iff_not_image gamma hg).mpr hn, hcut⟩

theorem execute_domain (gamma cutoff : Nat) :
    (SkPublicDictionary.execute (gamma, cutoff)).Dom ↔
      Canonical.check gamma = true ∧
        Ordinal.omega0 ^ unionInterpretation gamma = unionInterpretation gamma ∧
          ¬ SourceUpsilonImage (unionInterpretation gamma) ∧ unionCheck cutoff = true :=
  (SkPublicDictionary.execute_domain gamma cutoff).trans (inputCheck_exact gamma cutoff)

end Alexander313.Wilken.RelativeTerm.Hereditary.SkPublicDictionary.UpsilonDomain
