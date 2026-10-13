import Alexander313.Wilken.HereditaryNativeMuHeightSupport
import Alexander313.Wilken.HereditaryNativeLambdaSourceReturn

/-!
# Genuine original-source endpoint bounds for the actual native mu

The original source alpha-plus is a real high collapse at the original
argument plus one. Actual notation and cardinal bounds prove it epsilon.
The constructed coefficient is below Delta and actual iota order places
its image below the genuine source alpha-plus. Finite chi+k addition and
omega power stay below that epsilon. This proves the original endpoint
bound for actual normal and raw execution; actual low-interval coverage
also constructs same-value original-source return representatives.

The source base one, executing cross-context recoder and mu-plus endpoint
remain separate obligations. No endpoint, admission or return oracle.
Uncompiled drafts, retained outside the checkpoint.
-/

noncomputable section

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Mu.Bounds

open NativePublicBridge (contextCode contextCode_checked)

/-- The original successor endpoint is genuinely epsilon, by its ACTUAL
source high argument and genuine global notation, not an endpoint identity. -/
theorem source_alphaPlus_epsilon (s a : Nat) (ha : Mu.inputCheck s a = true) :
    Ordinal.omega0 ^ Iota.AlphaPlus.sourceValue s a = Iota.AlphaPlus.sourceValue s a := by
  obtain ⟨t, he, ht, hn, hh⟩ := (Iota.rootCheck_exact s a).mp ha
  let q := contextCode s
  have hq := contextCode_checked s
  have hp := base_pos q hq
  have hA : GlobalNotation (base q) 0 (interpretation q (Lambda.argumentCode a)) := by
    simpa only [Lambda.argumentCode, he, Localization.argumentCode_theta, interpretation_code] using
      checked_globalNotation q t (BaseTransformation.theta_argument_check q 0 t ht)
  have hOne : GlobalNotation (base q) 0 1 := GlobalNotation.parameter (by
    simpa only [omegaSequence_zero] using EpsilonOffsets.epsilon_one_lt (SourceChi.epsilon_base q hq))
  have hSucc : GlobalNotation (base q) 1 (interpretation q (Lambda.argumentCode a) + 1) :=
    globalNotation_embeds_next (base q) hp 0 (hA.add hOne)
  have hAs : interpretation q (Lambda.argumentCode a) < omegaSequence (base q) 2 := by
    simpa only [Lambda.argumentCode, he, Localization.argumentCode_theta, interpretation_code] using
      FixedPoint.checked_theta_sort q 0 t ht
  have hSort := (omegaSequence_isSuccLimit (base q) 1).add_one_lt hAs
  have hHigh : omegaSequence (base q) 1 ≤ interpretation q (Lambda.argumentCode a) + 1 :=
    (Lambda.argument_not_low s a ha).trans le_self_add
  exact SourceChi.Powers.global_high_epsilon (base q) (Or.inr (SourceChi.epsilon_base q hq))
    ⟨interpretation q (Lambda.argumentCode a) + 1, hSucc⟩ hSort hHigh

theorem mappedCoefficient_lt_source_alphaPlus (s a : Nat) (ha : Mu.inputCheck s a = true) :
    interpretation (Iota.alphaCode s a) (Mu.mappedCoefficient s a) < Iota.AlphaPlus.sourceValue s a :=
  (Mu.HeightSupport.mappedCoefficient_le_delta s a ha).trans_lt
    (Iota.AlphaPlus.literalDelta_lt_sourceValue s a ha)

/-- The actual finite-tail caller is below the ORIGINAL source endpoint,
including lambda=zero and all actual chi/finite-k branches. -/
theorem exponentCode_lt_source_alphaPlus (s a : Nat) (ha : Mu.inputCheck s a = true) :
    interpretation (Iota.alphaCode s a) (Mu.exponentCode s a) < Iota.AlphaPlus.sourceValue s a := by
  have he := source_alphaPlus_epsilon s a ha
  have hp : Ordinal.IsPrincipal (· + ·) (Iota.AlphaPlus.sourceValue s a) := by
    rw [← he]
    exact Ordinal.isPrincipal_add_omega0_opow _
  have hn : (Mu.tail s a : Ordinal.{0}) < Iota.AlphaPlus.sourceValue s a :=
    (Ordinal.natCast_lt_omega0 _).trans (epsilon_omega_lt he)
  have hs := OmegaPowerHeight.finiteTailCode_spec (Iota.alphaCode s a)
    (Mu.mappedCoefficient s a) (Mu.tail s a) (Mu.mappedCoefficient_spec s a ha).1
  rw [hs.2.2.1]
  exact hp (mappedCoefficient_lt_source_alphaPlus s a ha) hn

/-- The first endpoint inequality of source Lemma3.7 for the actual native
mu on its WHOLE original normal high-root guard, at positive finite epsilon. -/
theorem muCode_lt_source_alphaPlus (s a : Nat) (ha : Mu.inputCheck s a = true) :
    interpretation (Iota.alphaCode s a) (Mu.muCode s a) < Iota.AlphaPlus.sourceValue s a := by
  have hs := OmegaPowers.powerCode_spec (Iota.alphaCode s a) (Mu.exponentCode s a)
    (Mu.exponentCode_spec s a ha).1
  rw [Mu.muCode_literal s a ha, hs.2.2]
  exact (omegaPower_strictMono (exponentCode_lt_source_alphaPlus s a ha)).trans_eq
    (source_alphaPlus_epsilon s a ha)

theorem execute_lt_source_alphaPlus (s a out : Nat) (ho : out ∈ Mu.execute s a) :
    interpretation (Iota.alphaCode s a) out < Iota.AlphaPlus.sourceValue s a := by
  obtain ⟨ha, rfl⟩ := (Mu.execute_graph s a out).mp ho
  exact muCode_lt_source_alphaPlus s a ha

/-- Original RAW source argument value fidelity identifies its literal
alpha-plus. No normalized-domain or endpoint invariance premise is supplied. -/
theorem raw_execute_lt_original_source_alphaPlus (s a out : Nat) (ho : out ∈ Mu.Raw.execute s a) :
    interpretation (Mu.Raw.outputContext s a) out < Iota.AlphaPlus.sourceValue s a := by
  obtain ⟨ha, rfl⟩ := (Mu.Raw.execute_graph s a out).mp ho
  have hs := Bool.and_eq_true.mp ha
  have hb := muCode_lt_source_alphaPlus s (Mu.Raw.normalizedRoot s a) hs.2
  simpa only [Mu.Raw.muCode, ha, Bool.cond_true, Mu.Raw.outputContext,
    Lambda.Branches.Raw.normalized_source_alphaPlus s a hs.1] using hb

/-- Actual original source low-interval coverage constructs a checked
Normal LOW source code with the actual normal mu output's SAME ordinal value.
This is a mathematical return existence theorem, not an executing recoder. -/
theorem execute_source_code (s a out : Nat) (ho : out ∈ Mu.execute s a) :
    ∃ c : Nat, Comparison.acceptedCode (contextCode s) c = true ∧
      lowCheckCode (contextCode s) c = true ∧
        interpretation (contextCode s) c = interpretation (Iota.alphaCode s a) out := by
  have ha := (Mu.execute_spec s a out ho).1
  obtain ⟨t, ht, hn, hs, hv⟩ := Lambda.SourceReturn.normal_low_representative s _
    ((execute_lt_source_alphaPlus s a out ho).trans
      (Lambda.SourceReturn.alphaPlus_lt_source_boundary s a (Bool.and_eq_true.mp ha).1))
  refine ⟨t.code, (Comparison.acceptedCode_exact _ _).mpr ?_, ?_, ?_⟩
  · simpa only [checkCode_code, ThetaCourse.rawTree_code] using And.intro ht hn
  · simp only [lowCheckCode_code, lowCheck, ht, hs, decide_true, Bool.true_and]
  · simpa only [interpretation_code] using hv

theorem raw_execute_source_code (s a out : Nat) (ho : out ∈ Mu.Raw.execute s a) :
    ∃ c : Nat, Comparison.acceptedCode (contextCode s) c = true ∧
      lowCheckCode (contextCode s) c = true ∧
        interpretation (contextCode s) c = interpretation (Mu.Raw.outputContext s a) out := by
  have ha := Bool.and_eq_true.mp (Mu.Raw.execute_spec s a out ho).1
  obtain ⟨t, ht, hn, hs, hv⟩ := Lambda.SourceReturn.normal_low_representative s _
    ((raw_execute_lt_original_source_alphaPlus s a out ho).trans
      (Lambda.SourceReturn.raw_alphaPlus_lt_source_boundary s a ha.1))
  refine ⟨t.code, (Comparison.acceptedCode_exact _ _).mpr ?_, ?_, ?_⟩
  · simpa only [checkCode_code, ThetaCourse.rawTree_code] using And.intro ht hn
  · simp only [lowCheckCode_code, lowCheck, ht, hs, decide_true, Bool.true_and]
  · simpa only [interpretation_code] using hv

theorem execute_lt_public_endpoint (s a out : Nat) (ho : out ∈ Mu.execute s a) :
    interpretation (Iota.alphaCode s a) out < finiteBase ((s + 1) + 1) := by
  obtain ⟨c, hc, hl, hv⟩ := execute_source_code s a out ho
  simpa only [hv] using LowArithmetic.lowInput_bound s c hl

theorem raw_execute_lt_public_endpoint (s a out : Nat) (ho : out ∈ Mu.Raw.execute s a) :
    interpretation (Mu.Raw.outputContext s a) out < finiteBase ((s + 1) + 1) := by
  obtain ⟨c, hc, hl, hv⟩ := raw_execute_source_code s a out ho
  simpa only [hv] using LowArithmetic.lowInput_bound s c hl

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Mu.Bounds
