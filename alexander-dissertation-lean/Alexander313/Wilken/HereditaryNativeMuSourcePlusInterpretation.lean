import Alexander313.Wilken.HereditaryNativeMuSuccessorIntervals

/-!
# An auxiliary audit of the original-source mu successor interpretation

At every positive finite epsilon source context, the fixed native syntax
beta=theta0(theta1(Omega1)) and alpha=theta0(theta1(beta)) is admitted and
weak Normal. The actual Definition 3.6 producer returns beta: its genuine
coefficient is beta with finite offset zero, and its iota image is an actual
atomic alpha parameter, whose genuine chi is zero.

The actual original-source theta-argument successor of beta lies ABOVE the
original-source alpha successor. This tests the interpretation that the
second bound of Lemma 3.7 applies Convention 2.28 at the original source to
every returned mu value, including an alpha parameter. It is not a claim
against Wilken's intended contextual statement, whose parameter extension
is not specified by the available Convention 2.28 text. No new operation
is called the printed mu-plus. All candidates are uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Mu.SourcePlusInterpretation

open NativePublicBridge (contextCode contextCode_checked)

def betaArgument : RelativeTerm Nat := .theta 1 OmegaQuotient.baseTerm

def betaTerm : RelativeTerm Nat := .theta 0 betaArgument

def alphaArgument : RelativeTerm Nat := .theta 1 betaTerm

def alphaTerm : RelativeTerm Nat := .theta 0 alphaArgument

def rootCode : Nat := alphaTerm.code

private theorem omega_lt_threshold (q : Nat) :
    omegaSequence (base q) 1 < omegaSequence (base q) 1 * Ordinal.omega0 := by
  have hp := (omegaSequence_isSuccLimit (base q) 0).bot_lt
  simpa only [mul_one] using mul_lt_mul_of_pos_left Ordinal.one_lt_omega0 hp

/-- The actual nested theta-one argument is checked and weak Normal and
has the literal Omega-one squared value. The real below-threshold formula
is used; there is no assumed absorption or quotient formula. -/
theorem betaArgument_spec (q : Nat) (hq : baseCheck q = true) :
    check q betaArgument = true ∧ Comparison.Normal q betaArgument ∧
      denote q betaArgument = omegaSequence (base q) 1 * omegaSequence (base q) 1 := by
  have hs := OmegaQuotient.baseTerm_spec q hq
  refine ⟨OmegaQuotient.theta_checked q 1 _ hs.1 (by
    simp only [OmegaQuotient.baseTerm, RelativeTerm.outerSort]; omega), hs.2.1, ?_⟩
  change globalCollapse (base q) 1 (denote q OmegaQuotient.baseTerm) = _
  rw [hs.2.2, OmegaQuotient.theta_one_below_threshold (base q)
    (Or.inr (SourceChi.epsilon_base q hq)) _ (omega_lt_threshold q),
    omegaSequence_succ_omegaPower_eq_self (base q) 0]

/-- Beta is a genuine checked Normal LOW epsilon theta-zero term, hence
a proper limit. Its original Omega-one cardinal bound is derived. -/
theorem betaTerm_spec (q : Nat) (hq : baseCheck q = true) :
    check q betaTerm = true ∧ Comparison.Normal q betaTerm ∧
      Ordinal.omega0 ^ denote q betaTerm = denote q betaTerm ∧
      IsSuccLimit (denote q betaTerm) ∧ denote q betaTerm < omegaSequence (base q) 1 := by
  have hs := betaArgument_spec q hq
  have ht : check q betaTerm = true := OmegaQuotient.theta_checked q 0 _ hs.1 (by
    simp only [betaArgument, RelativeTerm.outerSort]; omega)
  have hp := (omegaSequence_isSuccLimit (base q) 0).bot_lt
  have hh : omegaSequence (base q) 1 ≤ denote q betaArgument := by
    rw [hs.2.2]
    calc
      omegaSequence (base q) 1 = omegaSequence (base q) 1 * 1 := (mul_one _).symm
      _ ≤ omegaSequence (base q) 1 * omegaSequence (base q) 1 :=
        mul_le_mul' le_rfl (Order.one_le_iff_pos.mpr hp)
  have he := SourceChi.Powers.theta_epsilon_of_high q betaArgument ht hh
  have hprincipal := (OmegaQuotient.theta_principal q 0 betaArgument ht).2
  exact ⟨ht, hs.2.1, he,
    Ordinal.isSuccLimit_of_isPrincipal_add (EpsilonOffsets.epsilon_one_lt he) hprincipal,
    (FixedPoint.checked_theta_range q 0 betaArgument ht).2⟩

/-- The original alpha argument is genuinely checked and weak Normal,
and its value is Omega-one times the actual beta epsilon. -/
theorem alphaArgument_spec (q : Nat) (hq : baseCheck q = true) :
    check q alphaArgument = true ∧ Comparison.Normal q alphaArgument ∧
      denote q alphaArgument = omegaSequence (base q) 1 * denote q betaTerm := by
  have hs := betaTerm_spec q hq
  refine ⟨OmegaQuotient.theta_checked q 1 _ hs.1 (by
    simp only [betaTerm, RelativeTerm.outerSort]; omega), hs.2.1, ?_⟩
  change globalCollapse (base q) 1 (denote q betaTerm) = _
  rw [OmegaQuotient.theta_one_below_threshold (base q)
    (Or.inr (SourceChi.epsilon_base q hq)) _ (hs.2.2.2.2.trans (omega_lt_threshold q)), hs.2.2.1]

/-- This fixed native code satisfies the complete original high-root mu
guard at every positive finite epsilon source context. -/
theorem root_spec (s : Nat) : Mu.inputCheck s rootCode = true := by
  have hs := alphaArgument_spec (contextCode s) (contextCode_checked s)
  apply (Mu.inputCheck_exact s rootCode).mpr
  exact ⟨alphaArgument, rfl, OmegaQuotient.theta_checked _ 0 _ hs.1 (by
    simp only [alphaArgument, RelativeTerm.outerSort]; omega), hs.2.1, by
      simp only [alphaArgument, RelativeTerm.outerSort]; omega⟩

/-- Full original hidden support bounds force beta strictly below alpha.
The actual original restriction is a conclusion of root admission. -/
theorem beta_lt_alpha (s : Nat) :
    denote (contextCode s) betaTerm < interpretation (contextCode s) rootCode := by
  have hs := Iota.argument_restricted s rootCode (root_spec s)
  have ht : ThetaCourse.rawTree (Localization.argumentCode rootCode) = alphaArgument := by
    simp only [rootCode, alphaTerm, Localization.argumentCode_theta, ThetaCourse.rawTree_code]
  rw [ht] at hs
  apply hs betaTerm
  change betaTerm ∈ RelativeTerm.PrincipalSupport.principalList 0 (.theta 1 betaTerm)
  rw [RelativeTerm.PrincipalSupport.principalList_theta_higher 0 1 betaTerm (by omega)]
  exact RelativeTerm.PrincipalSupport.principalList_root 0 betaArgument

/-- The real high-part operation returns the original argument value,
since that value is the proved exact Omega-one multiple. -/
theorem delta_value (s : Nat) :
    interpretation (contextCode s) (Lambda.deltaCode rootCode) =
      omegaSequence (base (contextCode s)) 1 * denote (contextCode s) betaTerm := by
  let q := contextCode s
  have hs := (Decomposition.parts_code_value q 0 (Lambda.argumentCode rootCode)
    (Lambda.argument_accepted s rootCode (root_spec s))).1
  have hv : interpretation q (Lambda.argumentCode rootCode) =
      omegaSequence (base q) 1 * denote q betaTerm := by
    simp only [Lambda.argumentCode, rootCode, alphaTerm, Localization.argumentCode_theta,
      interpretation_code]
    exact (alphaArgument_spec q (contextCode_checked s)).2.2
  change interpretation q (Decomposition.highCode 0 (Lambda.argumentCode rootCode)) = _
  rw [hs, hv]
  exact Ordinal.div_mul_cancel (omegaSequence_isSuccLimit (base q) 0).bot_lt.ne'
    (dvd_mul_right _ _)

/-- The genuine executing coefficient equation forces lambda=beta and
k=0. A positive finite k would make lambda+k a successor, contrary to the
derived proper-limit beta; no quotient or offset oracle is supplied. -/
theorem coefficient_value_offset (s : Nat) :
    interpretation (contextCode s) (OmegaQuotient.coefficientCode s rootCode) =
      denote (contextCode s) betaTerm ∧ OmegaQuotient.coefficientOffset s rootCode = 0 := by
  have hs := OmegaQuotient.coefficientCode_spec s rootCode (root_spec s)
  have he : interpretation (contextCode s) (OmegaQuotient.coefficientCode s rootCode) +
      (OmegaQuotient.coefficientOffset s rootCode : Ordinal.{0}) = denote (contextCode s) betaTerm :=
    mul_left_cancel₀ (omegaSequence_isSuccLimit (base (contextCode s)) 0).bot_lt.ne'
      (hs.2.2.2.trans (delta_value s))
  have hl := (betaTerm_spec (contextCode s) (contextCode_checked s)).2.2.2.1
  have hk : OmegaQuotient.coefficientOffset s rootCode = 0 := by
    cases h : OmegaQuotient.coefficientOffset s rootCode with
    | zero => rfl
    | succ k =>
      have hsuc : IsSuccLimit (Order.succ
          (interpretation (contextCode s) (OmegaQuotient.coefficientCode s rootCode) +
            (k : Ordinal.{0}))) := by
        rw [succ_eq_add_one, add_assoc, ← Nat.cast_succ, ← h, he]
        exact hl
      exact False.elim (not_isSuccLimit_succ _ hsuc)
  exact ⟨by simpa only [hk, Nat.cast_zero, add_zero] using he, hk⟩

/-- The actual iota producer returns an atomic target parameter for its
constructed original coefficient. Its value is beta and its real chi=0. -/
theorem mappedCoefficient_parameter (s : Nat) :
    ∃ p : Nat, Mu.mappedCoefficient s rootCode = (.parameter p : RelativeTerm Nat).code ∧
      interpretation (Iota.alphaCode s rootCode) (Mu.mappedCoefficient s rootCode) =
        denote (contextCode s) betaTerm ∧ Mu.chi s rootCode = false := by
  let t := OmegaQuotient.limitTerm s (Lambda.argumentCode rootCode)
  have ht := OmegaQuotient.root_coefficient_spec s rootCode (root_spec s)
  have he : denote (contextCode s) t = denote (contextCode s) betaTerm := by
    simpa only [OmegaQuotient.coefficientCode_literal s rootCode (root_spec s), interpretation_code] using
      (coefficient_value_offset s).1
  have hb := he.trans_lt (beta_lt_alpha s)
  have hi := OmegaQuotient.coefficient_iota_input s rootCode (root_spec s)
  have hl : Mu.mappedCoefficient s rootCode = (Iota.transform s rootCode t).code := by
    simp only [Mu.mappedCoefficient, Iota.literalCode, hi, Bool.cond_true,
      OmegaQuotient.coefficientCode_literal s rootCode (root_spec s), Iota.stateCode_code]
  have hp := Iota.transform_below s rootCode (root_spec s) t ht.1 hb
  refine ⟨Iota.parameterCode s t, hl.trans (congrArg RelativeTerm.code hp), ?_, ?_⟩
  · rw [hl, interpretation_code]
    exact (Iota.transform_parameter_value s rootCode (root_spec s) t ht.1 hb).2.trans he
  · rw [Mu.chi_correct s rootCode (root_spec s), hl, ThetaCourse.rawTree_code, hp,
      SourceChi.indicator_parameter]

/-- The literal guarded executing mu code returns beta, strictly below
the original alpha. The actual indicator and finite offset are derived. -/
theorem muCode_value (s : Nat) :
    interpretation (Iota.alphaCode s rootCode) (Mu.muCode s rootCode) =
      denote (contextCode s) betaTerm ∧
      interpretation (Iota.alphaCode s rootCode) (Mu.muCode s rootCode) <
        interpretation (contextCode s) rootCode := by
  obtain ⟨p, hp, hv, hc⟩ := mappedCoefficient_parameter s
  have he := (Mu.muCode_spec s rootCode (root_spec s)).2.2
  rw [Mu.sourceValue, ← Mu.chi_correct s rootCode (root_spec s), hc, Bool.cond_false,
    hv, (coefficient_value_offset s).2, Nat.cast_zero, add_zero, add_zero,
    (betaTerm_spec (contextCode s) (contextCode_checked s)).2.2.1] at he
  exact ⟨he, he.trans_lt (beta_lt_alpha s)⟩

/-- The genuine original-source beta successor is above the original
alpha successor. This is a comparison of two admitted original theta
successors, not a definition of an alpha-parameter plus operation. -/
theorem source_successor_reversal (s : Nat) :
    Iota.AlphaPlus.sourceValue s rootCode < denote (contextCode s)
      (Mu.SuccessorIntervals.sourceSuccessorTerm (contextCode s) betaArgument) := by
  let q := contextCode s
  have hq := contextCode_checked s
  have hb := betaArgument_spec q hq
  have hbt := betaTerm_spec q hq
  have ha := alphaArgument_spec q hq
  have hat : check q alphaTerm = true :=
    OmegaQuotient.theta_checked q 0 _ ha.1 (by
      simp only [alphaArgument, RelativeTerm.outerSort]; omega)
  have hsucc := Mu.SuccessorIntervals.sourceSuccessorTerm_spec q betaArgument hbt.1
  have hβsucc : denote q betaTerm < denote q
      (Mu.SuccessorIntervals.sourceSuccessorTerm q betaArgument) := by
    rw [hsucc.2.2.2]
    exact SourceCollapseSuccessors.global_collapse_lt_successor (base q) (base_pos q hq) 0
      (FixedPoint.sourceOrdinal q 0 betaArgument hb.1) (FixedPoint.checked_theta_sort q 0 betaArgument hbt.1)
  have hargs : denote q alphaArgument < denote q betaArgument := by
    rw [ha.2.2, hb.2.2]
    exact mul_lt_mul_of_pos_left hbt.2.2.2.2 (omegaSequence_isSuccLimit (base q) 0).bot_lt
  have hαβsucc : denote q alphaTerm < denote q
      (Mu.SuccessorIntervals.sourceSuccessorTerm q betaArgument) := by
    apply (Iota.OrderInduction.checked_theta_lt_iff_exposed q 0 alphaArgument
      (Arithmetic.addTerm q betaArgument.code (OmegaPowerHeight.numeralCode 1))
      hat hsucc.1 ha.2.1 hsucc.2.1).mpr
    refine Or.inl ⟨?_, ?_⟩
    · have ht := Arithmetic.addTerm_spec q betaArgument.code (OmegaPowerHeight.numeralCode 1)
        (by simpa only [checkCode_code] using hb.1)
        ((Comparison.acceptedCode_exact q _).mp (OmegaPowerHeight.numeralCode_spec q 1 hq).2.1).1
      have hv : denote q (Arithmetic.addTerm q betaArgument.code (OmegaPowerHeight.numeralCode 1)) =
          denote q betaArgument + 1 := by
        simpa only [interpretation_code, (OmegaPowerHeight.numeralCode_spec q 1 hq).2.2.1,
          Nat.cast_one] using ht.2.2
      rw [hv]
      exact hargs.trans (lt_add_one _)
    · intro t ht
      have he : t = betaTerm := by
        simpa [alphaArgument, betaTerm, exposedThetaList] using ht
      simpa only [he] using hβsucc
  have hlt := SourceCollapseSuccessorIntervals.global_successor_lt_endpoint_of_argument_lt
    (base q) (base_pos q hq) 0 (FixedPoint.sourceOrdinal q 0 betaArgument hb.1)
    (FixedPoint.sourceOrdinal q 0 alphaArgument ha.1)
    (FixedPoint.checked_theta_sort q 0 betaArgument hbt.1)
    (FixedPoint.checked_theta_sort q 0 alphaArgument hat) hargs (by
      simpa only [← hsucc.2.2.2] using hαβsucc)
  rw [hsucc.2.2.2]
  simpa only [Iota.AlphaPlus.sourceValue, Lambda.argumentCode, rootCode, alphaTerm,
    Localization.argumentCode_theta, interpretation_code] using hlt

/-- All original guards, execution, source mu representation and source
successor admission are derived for this concrete family. The displayed
strict reversal is confined to the ORIGINAL-source successor reading. -/
theorem interpretation_obstruction (s : Nat) :
    Mu.muCode s rootCode ∈ Mu.execute s rootCode ∧
      interpretation (Iota.alphaCode s rootCode) (Mu.muCode s rootCode) =
        denote (contextCode s) betaTerm ∧
      interpretation (Iota.alphaCode s rootCode) (Mu.muCode s rootCode) <
        interpretation (contextCode s) rootCode ∧
      Comparison.acceptedCode (contextCode s)
        (Mu.SuccessorIntervals.sourceSuccessorTerm (contextCode s) betaArgument).code = true ∧
      Iota.AlphaPlus.sourceValue s rootCode < denote (contextCode s)
        (Mu.SuccessorIntervals.sourceSuccessorTerm (contextCode s) betaArgument) := by
  have hs := Mu.SuccessorIntervals.sourceSuccessorTerm_spec (contextCode s) betaArgument
    (betaTerm_spec (contextCode s) (contextCode_checked s)).1
  refine ⟨(Mu.execute_graph s rootCode _).mpr ⟨root_spec s, rfl⟩,
    (muCode_value s).1, (muCode_value s).2, ?_, source_successor_reversal s⟩
  exact (Comparison.acceptedCode_exact _ _).mpr
    ⟨by simpa only [checkCode_code] using hs.1,
      by simpa only [ThetaCourse.rawTree_code] using hs.2.1⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Mu.SourcePlusInterpretation
