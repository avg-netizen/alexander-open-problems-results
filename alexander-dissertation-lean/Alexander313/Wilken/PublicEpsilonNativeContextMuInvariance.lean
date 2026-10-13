import Alexander313.Wilken.PublicEpsilonNativeContextReturnCoefficientSupport
import Alexander313.Wilken.PublicEpsilonNativeUnboundedMuValueInvariance

/-!
# Genuine contextual mu equality on the original alpha-plus interval

The actual SAME-value return retains the genuine divided head and quotient
coefficient. Whole restricted iota commutation and actual Normal order
reflection identify the mapped coefficients; the real indicator operates
at literally the SAME canonical beta. The actual finite-tail and omega
power mu formulas therefore agree. SAME-source mu spelling invariance
then compares the ORIGINAL beta root with this derived returned root.

This establishes the executing Lemma3.8 equation for the genuine computed
SAME-value alpha-context translation on every original ANY-coded-epsilon
high-root alpha<beta<ORIGINAL alphaPlus input. No translated-root, product,
coefficient, indicator or mu fidelity oracle. Original source one is a
separate dictionary and is not substituted here. Uncompiled candidates.
-/

noncomputable section

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.ContextTranslation.MuInvariance

open ThetaCourse
open PublicEpsilonUnboundedIota
open ReturnCoefficientSupport

theorem returned_mappedCoefficient_value (q alpha beta : Nat)
    (ha : RootLowCollapse.rootCheck q alpha = true)
    (hb : RootLowCollapse.rootCheck (betaCode q alpha) beta = true)
    (hbeta : interpretation (betaCode q alpha) beta < Enclosure.sourceAlphaPlus q alpha) :
    interpretation (betaCode (betaCode q alpha) beta)
        (Mu.mappedCoefficient q (Return.returnedRoot q alpha beta)) =
      interpretation (betaCode (betaCode q alpha) beta) (Mu.mappedCoefficient (betaCode q alpha) beta) := by
  have hroot := (Return.returnedRoot_spec q alpha beta ha hb).1
  have hn := OmegaQuotient.coefficientCode_spec (betaCode q alpha) beta hb
  obtain ⟨_, t, he, ht, hnt, hstar⟩ :=
    (PublicEpsilonUnboundedIota.inputCheck_exact _ beta _).mp hn.2.1
  have hrt := (restricted_iff_sourceStar _ beta hb t ht hnt).mpr hstar
  have hs := ReturnSupport.returnedTerm_spec q alpha ha t ht
  have hcut := Return.returnedTerm_restricted q alpha beta ha hb t ht hnt hrt
  have ho := OmegaQuotient.coefficientCode_spec q (Return.returnedRoot q alpha beta) hroot
  have hct := Decomposition.input_tree q _ ho.1
  obtain ⟨_, u, heu, hu, hnu, hsu⟩ := (PublicEpsilonUnboundedIota.inputCheck_exact q _ _).mp ho.2.1
  have hcu : Restricted q (Return.returnedRoot q alpha beta)
      (rawTree (OmegaQuotient.coefficientCode q (Return.returnedRoot q alpha beta))) := by
    simpa only [heu, rawTree_code] using
      (restricted_iff_sourceStar q _ hroot u hu hnu).mpr hsu
  have hv : denote q (rawTree (OmegaQuotient.coefficientCode q (Return.returnedRoot q alpha beta))) =
      denote q (ReturnSupport.returnedTerm q alpha t) := by
    rw [Arithmetic.raw_value q _ ((Comparison.acceptedCode_exact q _).mp ho.1).1,
      (returnedRoot_coefficient_value q alpha beta ha hb hbeta).1,
      he, interpretation_code, hs.2.2]
  have hi := (transform_eq_iff q (Return.returnedRoot q alpha beta) hroot _ _
    hct.1 hs.1 hct.2 hs.2.1 hcu hcut).mpr hv
  rw [Return.returnedRoot_betaCode q alpha beta ha hb] at hi
  have hc := Return.transform_return_value q alpha beta ha hb t ht hnt hrt
  have hcode : literalCode q (Return.returnedRoot q alpha beta)
      (OmegaQuotient.coefficientCode q (Return.returnedRoot q alpha beta)) =
        (transform q (Return.returnedRoot q alpha beta)
          (rawTree (OmegaQuotient.coefficientCode q (Return.returnedRoot q alpha beta)))).code := by
    simp only [literalCode, ho.2.1, Bool.cond_true, heu, stateCode_code, rawTree_code]
  simpa only [Mu.mappedCoefficient, hcode, he,
    literalCode_code _ beta hb t ht hnt hrt, interpretation_code] using hi.trans hc

theorem returned_chi_eq (q alpha beta : Nat)
    (ha : RootLowCollapse.rootCheck q alpha = true)
    (hb : RootLowCollapse.rootCheck (betaCode q alpha) beta = true)
    (hbeta : interpretation (betaCode q alpha) beta < Enclosure.sourceAlphaPlus q alpha) :
    Mu.chi q (Return.returnedRoot q alpha beta) = Mu.chi (betaCode q alpha) beta := by
  have ho := (Mu.mappedCoefficient_spec q _ (Return.returnedRoot_spec q alpha beta ha hb).1).2
  rw [Return.returnedRoot_betaCode q alpha beta ha hb] at ho
  have hn := (Mu.mappedCoefficient_spec (betaCode q alpha) beta hb).2
  have hs := SourceChi.Invariance.chiCode_invariant (betaCode (betaCode q alpha) beta) _ _
    ((SourceChi.inputCheck_exact _ _).mpr ((Comparison.acceptedCode_exact _ _).mp ho))
    ((SourceChi.inputCheck_exact _ _).mpr ((Comparison.acceptedCode_exact _ _).mp hn))
    (returned_mappedCoefficient_value q alpha beta ha hb hbeta)
  simpa only [Mu.chi, Return.returnedRoot_betaCode q alpha beta ha hb] using hs

/-- The actual original-source returned root and actual alpha-context root
have equal mu values, with every coefficient and indicator caller derived. -/
theorem returned_sourceValue_eq (q alpha beta : Nat)
    (ha : RootLowCollapse.rootCheck q alpha = true)
    (hb : RootLowCollapse.rootCheck (betaCode q alpha) beta = true)
    (hbeta : interpretation (betaCode q alpha) beta < Enclosure.sourceAlphaPlus q alpha) :
    Mu.sourceValue q (Return.returnedRoot q alpha beta) = Mu.sourceValue (betaCode q alpha) beta := by
  have hr := (Return.returnedRoot_spec q alpha beta ha hb).1
  rw [Mu.sourceValue, Mu.sourceValue, ← Mu.chi_correct q _ hr,
    ← Mu.chi_correct (betaCode q alpha) beta hb,
    Return.returnedRoot_betaCode q alpha beta ha hb,
    returned_mappedCoefficient_value q alpha beta ha hb hbeta,
    returned_chi_eq q alpha beta ha hb hbeta,
    (returnedRoot_coefficient_value q alpha beta ha hb hbeta).2]

/-- The ORIGINAL mu and the mu of the genuine computed SAME-value
alpha-context translation satisfy the actual contextual Lemma3.8 equation. -/
theorem sourceValue_translation (q alpha beta : Nat)
    (hi : ContextTranslation.inputCheck q alpha beta = true) :
    Mu.sourceValue q beta = Mu.sourceValue (betaCode q alpha) (translatedRootCode q alpha beta) := by
  have hs := (ContextTranslation.inputCheck_exact q alpha beta).mp hi
  have ht := translatedRootCode_spec q alpha beta hi
  have hr := Return.returnedRoot_spec q alpha (translatedRootCode q alpha beta) hs.1 ht.1
  have hv : interpretation q beta = interpretation q
      (Return.returnedRoot q alpha (translatedRootCode q alpha beta)) := ht.2.symm.trans hr.2.symm
  exact (Mu.ValueInvariance.sourceValue_eq q beta _ hs.2.1 hr.1 hv).trans
    (returned_sourceValue_eq q alpha (translatedRootCode q alpha beta) hs.1 ht.1
      (ht.2.trans_lt hs.2.2.2))

/-- Every actual ORIGINAL mu execution has a real alpha-context mu
execution on the computed translation, at literally the SAME beta code. -/
theorem execute_translation (q alpha beta out : Nat)
    (hi : ContextTranslation.inputCheck q alpha beta = true) (ho : out ∈ Mu.execute q beta) :
    ∃ translatedOut : Nat,
      translatedOut ∈ Mu.execute (betaCode q alpha) (translatedRootCode q alpha beta) ∧
      interpretation (betaCode q beta) out = interpretation (betaCode q beta) translatedOut := by
  have ht := translatedRootCode_spec q alpha beta hi
  let targetOut := Mu.muCode (betaCode q alpha) (translatedRootCode q alpha beta)
  have he : targetOut ∈ Mu.execute (betaCode q alpha) (translatedRootCode q alpha beta) :=
    (Mu.execute_graph _ _ targetOut).mpr ⟨ht.1, rfl⟩
  have hs := Mu.execute_spec q beta out ho
  have hv := (Mu.muCode_spec (betaCode q alpha) (translatedRootCode q alpha beta) ht.1).2.2
  rw [translatedRootCode_betaCode q alpha beta hi] at hv
  exact ⟨targetOut, he, hs.2.2.2.trans ((sourceValue_translation q alpha beta hi).trans hv.symm)⟩

/-- Both actual executing outputs agree on every genuine original interval
query; no target mu equality or target output is an input oracle. -/
theorem execute_value_eq (q alpha beta out translatedOut : Nat)
    (hi : ContextTranslation.inputCheck q alpha beta = true) (ho : out ∈ Mu.execute q beta)
    (ht : translatedOut ∈ Mu.execute (betaCode q alpha) (translatedRootCode q alpha beta)) :
    interpretation (betaCode q beta) out = interpretation (betaCode q beta) translatedOut := by
  have hs := Mu.execute_spec q beta out ho
  have hu := Mu.execute_spec (betaCode q alpha) (translatedRootCode q alpha beta) translatedOut ht
  rw [translatedRootCode_betaCode q alpha beta hi] at hu
  exact hs.2.2.2.trans ((sourceValue_translation q alpha beta hi).trans hu.2.2.2.symm)

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.ContextTranslation.MuInvariance
