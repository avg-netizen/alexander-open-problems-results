import Alexander313.Wilken.HereditaryEvaluationReferenceHeight
import Alexander313.Wilken.SourceOneNativeIotaCanonicalHeightSupport

/-!
# The genuine original OWN successor never increases root height

Actual native addition has height at most its original argument and the
height-zero numeral. At original check zero, the genuinely checked raw
theta-zero sum with theta-zero zero has the same OWN successor value and
height at most the original root. The real canonical minimum therefore
gives the source-one estimate without identifying two normalizers.
Actual LOW endpoint monotonicity then bounds every original HIGH root
strictly inside this OWN interval. No SAME-value return height oracle or
native parser at base one occurs. Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationOwnCeilingHeight

open NativeContext
open NativeContext.PublicEpsilonUnboundedIota
open ThetaCourse

theorem positive_ceiling (q root : Nat) (hr : Mu.inputCheck q root = true) :
    CanonicalHeight.canonicalHeightCode q (ContextTranslation.sourceSuccessorCode q root) ≤
      CanonicalHeight.canonicalHeightCode q root := by
  have hc := ContextTranslation.sourceSuccessorCode_spec q root hr
  have ha := RootEndpointCollapse.argument_accepted q root hr
  have hu := OmegaPowerHeight.numeralCode_spec q 1 (RootLowCollapse.source_checked q root hr)
  have hs := Arithmetic.addCode_spec q (RootEndpointCollapse.argumentCode root)
    (OmegaPowerHeight.numeralCode 1)
    ((Comparison.acceptedCode_exact q _).mp ha).1
    ((Comparison.acceptedCode_exact q _).mp hu.2.1).1
  have hf := RootEndpointCollapse.firstCode_spec q root hr
  have hfcheck := ((Comparison.acceptedCode_exact q _).mp hf.1).1
  have hunit : heightCode (OmegaPowerHeight.numeralCode 1) = 0 := by
    simp only [OmegaPowerHeight.numeralCode, heightCode_code, RelativeTerm.height]
  obtain ⟨t, he, ht, hn, hh⟩ := (RootLowCollapse.rootCheck_exact q root).mp hr
  have harg : heightCode (RootEndpointCollapse.argumentCode root) = t.height := by
    simp only [RootEndpointCollapse.argumentCode, he, Localization.argumentCode_theta,
      heightCode_code]
  have hfirst : heightCode (RootEndpointCollapse.firstCode q root) ≤ t.height := by
    simpa only [RootEndpointCollapse.firstCode, hunit, harg, max_zero] using hs.2.2
  rw [CanonicalHeight.canonicalHeightCode_normal q _ hc.2.1,
    CanonicalHeight.canonicalHeightCode_normal q root (RootLowCollapse.root_accepted q root hr)]
  simp only [ContextTranslation.sourceSuccessorCode, OmegaPowers.thetaCode,
    heightCode_code, RelativeTerm.height, Nat.zero_add,
    Height.input_heightCode q _ hfcheck, he]
  exact max_le (le_max_left _ _) (hfirst.trans (le_max_right _ _))

theorem source_one_ceiling (root : Nat) (hr : SourceOneIota.Mu.inputCheck root = true) :
    SourceOne.CanonicalHeight.canonicalHeightCode
      (SourceOneIota.ContextTranslation.Support.sourceSuccessorCode root) ≤
        SourceOne.CanonicalHeight.canonicalHeightCode root := by
  have hc := SourceOneIota.ContextTranslation.Support.sourceSuccessorCode_spec root hr
  have hlow := PublicMts.ContextSupport.source_one_successor_low root hr
  have hcheck : SourceOne.PublicCodes.checkCode
      (SourceOneIota.ContextTranslation.Support.sourceSuccessorCode root) = true :=
    (SourceOne.HeightBoundary.input_spec _ (by simpa only [lowCheckCode_zero] using hlow)).1
  obtain ⟨t, he, ht, hn, hh⟩ := (SourceOneIota.rootCheck_exact root).mp hr
  have hparts : Hereditary.check 0 t = true ∧ t.outerSort ≤ 2 := by
    simpa only [Uniform.check_theta, Nat.zero_add, Bool.and_eq_true, decide_eq_true_eq] using ht
  have hsum : Hereditary.check 0 (.sum t SourceOneIota.OmegaQuotient.unitTerm) = true := by
    simp only [Uniform.check_sum, hparts.1, SourceOneIota.OmegaQuotient.unitTerm_spec.1,
      Bool.true_and]
  have hsort : (.sum t SourceOneIota.OmegaQuotient.unitTerm).outerSort ≤ 2 :=
    max_le hparts.2 (by decide)
  have hterm := SourceOneIota.OmegaQuotient.theta_checked 0 _ hsum hsort
  have hv : Hereditary.interpretation 0 (SourceOneIota.ContextTranslation.Support.sourceSuccessorCode root) =
      Hereditary.denote 0 (.theta 0 (.sum t SourceOneIota.OmegaQuotient.unitTerm)) := by
    rw [hc.2]
    have harg : Hereditary.interpretation 0 (SourceOneIota.Lambda.argumentCode root) = Hereditary.denote 0 t := by
      simp only [SourceOneIota.Lambda.argumentCode, he, Localization.argumentCode_theta,
        interpretation_code]
    change globalCollapse (finiteBase 0) 0
        (Hereditary.interpretation 0 (SourceOneIota.Lambda.argumentCode root) + 1) =
      globalCollapse (finiteBase 0) 0
        (Hereditary.denote 0 t + Hereditary.denote 0 SourceOneIota.OmegaQuotient.unitTerm)
    rw [harg, SourceOneIota.OmegaQuotient.unitTerm_spec.2.2]
  have hb := SourceOne.CanonicalHeight.canonicalHeightCode_le_representation _
    (.theta 0 (.sum t SourceOneIota.OmegaQuotient.unitTerm)) hcheck
    (by simpa only [check_zero] using hterm)
    (by simpa only [interpretation_zero, denote_zero] using hv)
  have huheight : SourceOneIota.OmegaQuotient.unitTerm.height = 1 := rfl
  rw [SourceOne.CanonicalHeight.canonicalHeightCode_normal root
    (SourceOneIota.HeightSupport.root_source_accepted root hr), he, heightCode_code]
  apply hb.trans
  change max 1 (max t.height SourceOneIota.OmegaQuotient.unitTerm.height) ≤ max 1 t.height
  exact max_le (le_max_left _ _)
    (max_le (le_max_right _ _) (by rw [huheight]; exact le_max_left _ _))

theorem positive_inside (q root next : Nat) (hr : Mu.inputCheck q root = true)
    (hn : Mu.inputCheck q next = true)
    (hcut : interpretation q next < Enclosure.sourceAlphaPlus q root) :
    CanonicalHeight.canonicalHeightCode q next ≤ CanonicalHeight.canonicalHeightCode q root := by
  have hc := ContextTranslation.sourceSuccessorCode_spec q root hr
  exact (Mu.HeightSupport.canonicalHeightCode_mono_low q next _
    (RootLowCollapse.root_low q next hn) hc.1 (hcut.trans_eq hc.2.2.symm).le).trans
      (positive_ceiling q root hr)

theorem source_one_inside (root next : Nat) (hr : SourceOneIota.Mu.inputCheck root = true)
    (hn : SourceOneIota.Mu.inputCheck next = true)
    (hcut : Hereditary.interpretation 0 next < SourceOneIota.Enclosure.sourceAlphaPlus root) :
    SourceOne.CanonicalHeight.canonicalHeightCode next ≤
      SourceOne.CanonicalHeight.canonicalHeightCode root := by
  have hc := SourceOneIota.ContextTranslation.Support.sourceSuccessorCode_spec root hr
  have hnlow : SourceOne.PublicCodes.lowCheckCode next = true := by
    simpa only [lowCheckCode_zero] using SourceOneIota.root_low next hn
  have hclow : SourceOne.PublicCodes.lowCheckCode
      (SourceOneIota.ContextTranslation.Support.sourceSuccessorCode root) = true := by
    simpa only [lowCheckCode_zero] using PublicMts.ContextSupport.source_one_successor_low root hr
  have hbound := (SourceOne.HeightBoundary.canonicalHeightCode_le_iff_endpoint _ _ hclow).mp le_rfl
  have hb := (SourceOne.HeightBoundary.canonicalHeightCode_le_iff_endpoint _ next hnlow).mpr
    (by simpa only [interpretation_zero] using (hcut.trans_eq hc.2.symm).trans hbound)
  exact hb.trans (source_one_ceiling root hr)

end Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationOwnCeilingHeight
