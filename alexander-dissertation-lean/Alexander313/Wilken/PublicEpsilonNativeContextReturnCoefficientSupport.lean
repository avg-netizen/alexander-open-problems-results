import Alexander313.Wilken.PublicEpsilonNativeContextReturn
import Alexander313.Wilken.HereditaryNativeSourceChiInvariance
import Alexander313.Wilken.LimitFiniteDecomposition

/-!
# Original divided-head fidelity of the semantic context return

The real alpha-context ceiling has no exposed theta-zero nodes. Actual
checked comparison therefore forces every intermediate high-root argument
below the ORIGINAL divided head. The concrete scalar dispatcher can only
use its unchanged or low-tail-insertion branch, and both retain that head.
Actual theta injectivity removes any spelling change by the final root
parser. The real zero-or-limit plus finite quotient is then unique. No
head, branch, coefficient or normalization fidelity oracle. Uncompiled.
-/

noncomputable section

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.ContextTranslation.ReturnCoefficientSupport

open ThetaCourse
open PublicEpsilonUnboundedIota

/-- Genuine original endpoint comparison forces argument descent. -/
theorem argument_lt_delta (q alpha : Nat) (ha : RootLowCollapse.rootCheck q alpha = true)
    (t : RelativeTerm Nat) (ht : check (betaCode q alpha) (.theta 0 t) = true)
    (hn : Comparison.Normal (betaCode q alpha) t)
    (hv : denote (betaCode q alpha) (.theta 0 t) < Enclosure.sourceAlphaPlus q alpha) :
    denote (betaCode q alpha) t < interpretation q (OmegaQuotient.deltaCode alpha) := by
  have hd := Enclosure.delta_original q alpha ha
  have hs := Enclosure.delta_enclosure_spec q alpha ha
  have hlt : denote (betaCode q alpha) (.theta 0 t) <
      denote (betaCode q alpha) (.theta 0 (Enclosure.unshifted q alpha (Enclosure.deltaTerm alpha))) := by
    change denote (betaCode q alpha) (.theta 0 t) <
      denote (betaCode q alpha) (Enclosure.deltaEnclosureTerm q alpha)
    rw [Enclosure.delta_enclosure_value q alpha ha]
    exact hv
  have hc := (Iota.OrderInduction.checked_theta_lt_iff_exposed _ 0 t
    (Enclosure.unshifted q alpha (Enclosure.deltaTerm alpha)) ht hs.1 hn hs.2.1).mp hlt
  have harg : denote (betaCode q alpha) t <
      denote (betaCode q alpha) (Enclosure.unshifted q alpha (Enclosure.deltaTerm alpha)) := by
    rcases hc with hc | ⟨x, hx, hle⟩
    · exact hc.1
    · rw [Enclosure.unshifted_exposed_zero q alpha ha _ hd.1 hd.2.2] at hx
      exact False.elim (List.not_mem_nil hx)
  rw [Enclosure.unshifted_value q alpha ha _ hd.1 hd.2.2] at harg
  exact harg.trans_eq (Arithmetic.raw_value q _
    ((Comparison.acceptedCode_exact q _).mp (LambdaSource.delta_accepted q alpha ha)).1)

/-- The actual full scalar has a theta-zero presentation whose argument
quotient is unchanged whenever its original argument is high and below
the genuine divided head. Its concrete tests exclude all other branches. -/
theorem scalar_presentation (q alpha c : Nat)
    (ha : RootLowCollapse.rootCheck q alpha = true)
    (hc : RootAboveHeadCollapse.argumentCheck q c = true)
    (hh : 1 < (rawTree c).outerSort)
    (hbound : interpretation q c < interpretation q (OmegaQuotient.deltaCode alpha)) :
    ∃ u : RelativeTerm Nat,
      RootCompleteScalarCollapse.collapseCode q alpha 0 c = (.theta 0 u).code ∧
      check q (.theta 0 u) = true ∧
      denote q u / omegaSequence (base q) 1 = interpretation q c / omegaSequence (base q) 1 := by
  have hac := (RootAboveHeadCollapse.argumentCheck_exact q c).mp hc
  have hi := (RootCompleteScalarCollapse.inputCheck_exact q alpha 0 c).mpr
    ⟨ha, hac.1, by simpa only [Nat.zero_add] using hac.2⟩
  have hhead : interpretation q (RootAboveHeadCollapse.headCode c) <
      interpretation q (RootEndpointCollapse.deltaCode alpha) :=
    (Decomposition.parts_le q 0 c hac.1).1.trans_lt hbound
  have hlarger : RootScalarCollapse.headLarger q alpha c = false := by
    apply Bool.eq_false_of_not_eq_true
    intro h
    exact (not_lt_of_ge hhead.le) ((RootScalarCollapse.headLarger_exact q alpha c ha hc).mp h)
  have hcovered : RootScalarCollapse.coveredCheck q alpha c = true := by
    simp only [RootScalarCollapse.coveredCheck, hlarger, Bool.not_false, Bool.true_or]
  have hknown : RootCompleteScalarCollapse.knownBranch q alpha 0 c = true := by
    simp only [RootCompleteScalarCollapse.knownBranch, decide_false, Bool.false_or, hcovered]
  have hs := RootCompleteScalarCollapse.scalar_caller q alpha 0 c hi hknown
  have hz : RootScalarCollapse.zeroInput q alpha c = true := by
    simpa only [RootScalarCollapse.inputCheck, decide_false, Bool.cond_false] using hs
  have hlow : ¬ (rawTree c).outerSort ≤ 1 := not_le_of_gt hh
  have hbelow : RootBelowHeadCollapse.headBelow q alpha c = true :=
    (RootBelowHeadCollapse.headBelow_exact q alpha c ha hc).mpr hhead
  have hout := RootCompleteScalarCollapse.collapseCode_spec q alpha 0 c hi
  cases habove : RootAboveHeadCollapse.headAbove q alpha c with
  | true =>
    have ha' := RootScalarCollapse.above_caller q alpha c hz habove
    have he : RootCompleteScalarCollapse.collapseCode q alpha 0 c =
        (.theta 0 (rawTree c) : RelativeTerm Nat).code := by
      simp only [RootCompleteScalarCollapse.collapseCode, hi, hknown, Bool.cond_true,
        RootScalarCollapse.collapseCode, hs, decide_false, Bool.cond_false,
        RootScalarCollapse.zeroCode, decide_eq_false hlow, habove,
        RootAboveHeadCollapse.collapseCode_eq q alpha c ha', RootPositiveCollapse.nodeCode]
    refine ⟨rawTree c, he, ?_, ?_⟩
    · have hcheck := ((Comparison.acceptedCode_exact q _).mp hout.1).1
      simpa only [he, checkCode_code] using hcheck
    · rw [Arithmetic.raw_value q c ((Comparison.acceptedCode_exact q c).mp hac.1).1]
  | false =>
    have hb' := RootScalarCollapse.below_caller q alpha c hz hh habove hbelow
    have hv := RootBelowHeadCollapse.shiftedArgumentCode_spec q alpha c hb'
    let d := RootBelowHeadCollapse.shiftedArgumentCode q alpha c
    have he : RootCompleteScalarCollapse.collapseCode q alpha 0 c =
        (.theta 0 (rawTree d) : RelativeTerm Nat).code := by
      simp only [RootCompleteScalarCollapse.collapseCode, hi, hknown, Bool.cond_true,
        RootScalarCollapse.collapseCode, hs, decide_false, Bool.cond_false,
        RootScalarCollapse.zeroCode, decide_eq_false hlow, habove, hbelow,
        RootBelowHeadCollapse.collapseCode, hb', OmegaPowers.thetaCode, d]
    refine ⟨rawTree d, he, ?_, ?_⟩
    · have hcheck := ((Comparison.acceptedCode_exact q _).mp hout.1).1
      simpa only [he, checkCode_code] using hcheck
    · have hΩ := (omegaSequence_isSuccLimit (base q) 0).bot_lt
      have htail := (RootBelowHeadCollapse.insertedTailCode_spec q alpha c hb').2.2
      rw [(RootBelowHeadCollapse.insertedTailCode_spec q alpha c hb').2.1] at htail
      rw [Arithmetic.raw_value q d ((Comparison.acceptedCode_exact q d).mp hv.1).1,
        hv.2.1, (Decomposition.parts_code_value q 0 c hac.1).1,
        Ordinal.mul_add_div _ hΩ.ne', Ordinal.div_eq_zero_of_lt htail, add_zero]

/-- The parsed source return retains the actual intermediate divided head,
including every spelling change by the genuine final-atom normalizer. -/
theorem returnedRoot_delta_value (q alpha beta : Nat)
    (ha : RootLowCollapse.rootCheck q alpha = true)
    (hb : RootLowCollapse.rootCheck (betaCode q alpha) beta = true)
    (hbeta : interpretation (betaCode q alpha) beta < Enclosure.sourceAlphaPlus q alpha) :
    interpretation q (OmegaQuotient.deltaCode (Return.returnedRoot q alpha beta)) =
      interpretation (betaCode q alpha) (OmegaQuotient.deltaCode beta) := by
  obtain ⟨t, he, ht, hn, hh⟩ := (RootLowCollapse.rootCheck_exact _ beta).mp hb
  have htc := BaseTransformation.theta_argument_check _ 0 t ht
  let c := ReturnSupport.returnedCode q alpha t
  have hc := ReturnSupport.returnedCode_spec q alpha ha t htc
  have hac := ((Comparison.acceptedCode_exact q c).mp hc.1).1
  have hsort : (rawTree c).outerSort ≤ 2 := ReturnSupport.returned_sort q alpha ha t htc c 2
    hc.1 hc.2 (by omega)
    ((denote_lt_iff_outerSort_le _ t htc 2 (by omega)).mp (FixedPoint.checked_theta_sort _ 0 t ht))
  have harg := (RootAboveHeadCollapse.argumentCheck_exact q c).mpr ⟨hc.1, hsort⟩
  have hhigh : 1 < (rawTree c).outerSort := by
    apply lt_of_not_ge
    intro hlo
    have hl := (denote_lt_iff_outerSort_le q _ (Arithmetic.raw_checked q c hac) 1 (by omega)).mpr hlo
    rw [Arithmetic.raw_value q c hac, hc.2,
      RootPositiveCollapse.root_omegaSequence_pos q alpha 1 ha (by omega), ← beta_base q alpha ha] at hl
    exact (not_le_of_gt hh) ((denote_lt_iff_outerSort_le _ t htc 1 (by omega)).mp hl)
  have hbound : interpretation q c < interpretation q (OmegaQuotient.deltaCode alpha) := by
    rw [hc.2]
    exact argument_lt_delta q alpha ha t ht hn (by simpa only [he, interpretation_code] using hbeta)
  obtain ⟨u, hu, huc, huv⟩ := scalar_presentation q alpha c ha harg hhigh hbound
  have hi := (RootCompleteScalarCollapse.inputCheck_exact q alpha 0 c).mpr ⟨ha, hc.1, hsort⟩
  have hs := RootCompleteScalarCollapse.collapseCode_spec q alpha 0 c hi
  have huvalue : denote q (.theta 0 u) = denote (betaCode q alpha) (.theta 0 t) := by
    rw [← interpretation_code, ← hu, hs.2, hc.2, ← beta_base q alpha ha]
    rfl
  have hr := Return.returnedRoot_spec q alpha beta ha hb
  obtain ⟨v, hv, hvc, hvn, hvh⟩ := (RootLowCollapse.rootCheck_exact q _).mp hr.1
  have hsame : denote q (.theta 0 v) = denote q (.theta 0 u) := by
    calc
      _ = interpretation q (Return.returnedRoot q alpha beta) := by rw [hv, interpretation_code]
      _ = denote (betaCode q alpha) (.theta 0 t) := by simpa only [he, interpretation_code] using hr.2
      _ = _ := huvalue.symm
  have hargs := (SourceChi.Invariance.theta_value_injective q 0 0 v u hvc huc hsame).2
  have hvr := OmegaQuotient.Support.argument_accepted q _ hr.1
  have htr := OmegaQuotient.Support.argument_accepted (betaCode q alpha) beta hb
  have hdv := (Decomposition.parts_code_value q 0 _ hvr).1
  have hdt := (Decomposition.parts_code_value (betaCode q alpha) 0 _ htr).1
  have hdv' : interpretation q (OmegaQuotient.deltaCode (Return.returnedRoot q alpha beta)) =
      omegaSequence (base q) 1 * (denote q v / omegaSequence (base q) 1) := by
    simpa only [OmegaQuotient.deltaCode, OmegaQuotient.argumentCode, hv,
      Localization.argumentCode_theta, interpretation_code] using hdv
  have hdt' : interpretation (betaCode q alpha) (OmegaQuotient.deltaCode beta) =
      omegaSequence (base (betaCode q alpha)) 1 *
        (denote (betaCode q alpha) t / omegaSequence (base (betaCode q alpha)) 1) := by
    simpa only [OmegaQuotient.deltaCode, OmegaQuotient.argumentCode, he,
      Localization.argumentCode_theta, interpretation_code] using hdt
  rw [hdv', hdt', hargs, huv, hc.2,
    RootPositiveCollapse.root_omegaSequence_pos q alpha 1 ha (by omega),
    ← beta_base q alpha ha]

/-- Actual zero-or-limit plus finite uniqueness identifies both executing
coefficients and offsets after the genuine divided-head calculation. -/
theorem returnedRoot_coefficient_value (q alpha beta : Nat)
    (ha : RootLowCollapse.rootCheck q alpha = true)
    (hb : RootLowCollapse.rootCheck (betaCode q alpha) beta = true)
    (hbeta : interpretation (betaCode q alpha) beta < Enclosure.sourceAlphaPlus q alpha) :
    interpretation q (OmegaQuotient.coefficientCode q (Return.returnedRoot q alpha beta)) =
        interpretation (betaCode q alpha) (OmegaQuotient.coefficientCode (betaCode q alpha) beta) ∧
      OmegaQuotient.coefficientOffset q (Return.returnedRoot q alpha beta) =
        OmegaQuotient.coefficientOffset (betaCode q alpha) beta := by
  have hr := Return.returnedRoot_spec q alpha beta ha hb
  have hc := OmegaQuotient.coefficientCode_spec q _ hr.1
  have hd := OmegaQuotient.coefficientCode_spec (betaCode q alpha) beta hb
  apply LimitFiniteDecomposition.high_part_coefficient_unique (omegaSequence (base q) 1) _ _ _ _
    (omegaSequence_isSuccLimit (base q) 0).bot_lt hc.2.2.1 hd.2.2.1
  exact hc.2.2.2.trans ((returnedRoot_delta_value q alpha beta ha hb hbeta).trans
    (by simpa only [RootPositiveCollapse.root_omegaSequence_pos q alpha 1 ha (by omega),
      ← beta_base q alpha ha] using hd.2.2.2.symm))

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.ContextTranslation.ReturnCoefficientSupport
