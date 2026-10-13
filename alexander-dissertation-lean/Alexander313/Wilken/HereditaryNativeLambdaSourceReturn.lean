import Alexander313.Wilken.HereditaryNativeLambdaRawAlphaPlus
import Alexander313.Wilken.HereditaryNativeLowArithmetic

/-!
# Genuine same-value original-source lambda representatives

The literal original source alpha-plus is itself a low original notation.
The actual lambda bound consequently places every output in the original
source low interval. Its proved coverage and actual normalizer construct a
checked weak-normal LOW original representative with exactly the output's
ordinal value, for both original normal and raw proper roots.

This proves source return existence. It does not assert a finite executing
cross-context translator, a syntactic inverse, or the stronger alpha-plus
identity. All proof candidates are uncompiled.
-/

noncomputable section

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Lambda.SourceReturn

open NativePublicBridge (contextCode contextCode_checked)

/-- The literal original source successor endpoint is in its genuine low
interval. Admission follows from the original theta argument and the true
global notation constructors, rather than from a target translation. -/
theorem alphaPlus_lt_source_boundary (s a : Nat)
    (ha : SourceZeta.inputCheck s a = true) :
    Iota.AlphaPlus.sourceValue s a < globalBoundary (base (contextCode s)) 0 := by
  obtain ⟨t, he, ht, hn⟩ := (SourceZeta.inputCheck_exact s a).mp ha
  let q := contextCode s
  have hq := contextCode_checked s
  have hp := base_pos q hq
  have hA : GlobalNotation (base q) 0 (interpretation q (Lambda.argumentCode a)) := by
    simpa only [Lambda.argumentCode, he, Localization.argumentCode_theta, interpretation_code] using
      checked_globalNotation q t (BaseTransformation.theta_argument_check q 0 t ht)
  have hAs : interpretation q (Lambda.argumentCode a) < omegaSequence (base q) 2 := by
    simpa only [Lambda.argumentCode, he, Localization.argumentCode_theta, interpretation_code] using
      FixedPoint.checked_theta_sort q 0 t ht
  have hOne : GlobalNotation (base q) 0 1 := GlobalNotation.parameter (by
    simpa only [omegaSequence_zero] using
      EpsilonOffsets.epsilon_one_lt ((baseCheck_exact q).mp hq).2)
  have hSucc := hA.add hOne
  have hSort : interpretation q (Lambda.argumentCode a) + 1 < omegaSequence (base q) 2 :=
    (omegaSequence_isSuccLimit (base q) 1).add_one_lt hAs
  have hArg := globalNotation_sorted_lt_boundary (base q) hp 0 0 le_rfl hSucc hSort
  have hEnd : GlobalNotation (base q) 0 (Iota.AlphaPlus.sourceValue s a) :=
    GlobalNotation.collapse le_rfl hSort hSucc
  exact (globalNotation_low_iff_lt_boundary (base q) hp 0 _).mp
    ⟨hEnd, (globalCollapse_bounds (base q) hp 0 _ hArg).2⟩

/-- Every ordinal in the proved original source low interval has an actual
checked weak-normal LOW original term with that exact ordinal value. -/
theorem normal_low_representative (s : Nat) (ξ : Ordinal.{0})
    (hξ : ξ < globalBoundary (base (contextCode s)) 0) :
    ∃ t : RelativeTerm Nat, check (contextCode s) t = true ∧
      Comparison.Normal (contextCode s) t ∧ t.outerSort ≤ 1 ∧ denote (contextCode s) t = ξ := by
  let q := contextCode s
  have hq := contextCode_checked s
  obtain ⟨t, ht, hv⟩ := (lt_boundary_iff_checked q hq ξ).mp hξ
  have hc := (Bool.and_eq_true.mp ht).1
  have hn := Normalization.normalize_checked q t hc
  have hvalue : denote q (Normalization.normalize q t) = ξ := hn.2.2.trans hv
  have hsmall : denote q (Normalization.normalize q t) < omegaSequence (base q) 1 := by
    rw [hvalue]
    exact hξ.trans (globalBoundary_lt_cardinal (base q) (base_pos q hq) 0)
  exact ⟨Normalization.normalize q t, hn.1, hn.2.1,
    (denote_lt_iff_outerSort_le q _ hn.1 1 (by omega)).mp hsmall, hvalue⟩

/-- Every actual normal two-branch lambda output has a SAME-VALUE
weak-normal LOW term at the ORIGINAL positive public source context. -/
theorem execute_source_term (s a out : Nat) (ho : out ∈ Branches.execute s a) :
    ∃ t : RelativeTerm Nat, check (contextCode s) t = true ∧
      Comparison.Normal (contextCode s) t ∧ t.outerSort ≤ 1 ∧
        denote (contextCode s) t = interpretation (Branches.outputContext s a) out := by
  have ha := (Branches.execute_spec s a out ho).1
  exact normal_low_representative s _
    ((Iota.AlphaPlus.branch_lambda_lt_sourceValue s a out ho).trans
      (alphaPlus_lt_source_boundary s a (Branches.original_input s a ha)))

/-- The derived original source term supplies a genuine admitted weak-normal
LOW source CODE. No code-conversion or source-admission oracle is assumed. -/
theorem execute_source_code (s a out : Nat) (ho : out ∈ Branches.execute s a) :
    ∃ c : Nat, Comparison.acceptedCode (contextCode s) c = true ∧
      lowCheckCode (contextCode s) c = true ∧
        interpretation (contextCode s) c = interpretation (Branches.outputContext s a) out := by
  obtain ⟨t, ht, hn, hs, hv⟩ := execute_source_term s a out ho
  refine ⟨t.code, (Comparison.acceptedCode_exact _ _).mpr ?_, ?_, ?_⟩
  · simpa only [checkCode_code, ThetaCourse.rawTree_code] using And.intro ht hn
  · simpa only [lowCheckCode_code, lowCheck, ht, hs, decide_true, Bool.true_and]
  · simpa only [interpretation_code] using hv

/-- The ORIGINAL raw source endpoint also belongs to the original low
interval; its actual normalizer preserves the original argument value. -/
theorem raw_alphaPlus_lt_source_boundary (s a : Nat)
    (ha : Branches.Raw.inputCheck s a = true) :
    Iota.AlphaPlus.sourceValue s a < globalBoundary (base (contextCode s)) 0 := by
  rw [← Branches.Raw.normalized_source_alphaPlus s a ha]
  exact alphaPlus_lt_source_boundary s (Branches.Raw.normalizedRoot s a)
    (Branches.original_input s _ (Bool.and_eq_true.mp ha).2)

/-- Every actual raw proper-root lambda output has a SAME-VALUE original
weak-normal LOW source term, with the actual selected output context. -/
theorem raw_execute_source_term (s a out : Nat) (ho : out ∈ Branches.Raw.execute s a) :
    ∃ t : RelativeTerm Nat, check (contextCode s) t = true ∧
      Comparison.Normal (contextCode s) t ∧ t.outerSort ≤ 1 ∧
        denote (contextCode s) t =
          interpretation (Branches.outputContext s (Branches.Raw.normalizedRoot s a)) out := by
  exact normal_low_representative s _
    ((Branches.Raw.execute_lt_original_source_alphaPlus s a out ho).trans
      (raw_alphaPlus_lt_source_boundary s a (Branches.Raw.execute_spec s a out ho).1))

theorem raw_execute_source_code (s a out : Nat) (ho : out ∈ Branches.Raw.execute s a) :
    ∃ c : Nat, Comparison.acceptedCode (contextCode s) c = true ∧
      lowCheckCode (contextCode s) c = true ∧ interpretation (contextCode s) c =
        interpretation (Branches.outputContext s (Branches.Raw.normalizedRoot s a)) out := by
  obtain ⟨t, ht, hn, hs, hv⟩ := raw_execute_source_term s a out ho
  refine ⟨t.code, (Comparison.acceptedCode_exact _ _).mpr ?_, ?_, ?_⟩
  · simpa only [checkCode_code, ThetaCourse.rawTree_code] using And.intro ht hn
  · simpa only [lowCheckCode_code, lowCheck, ht, hs, decide_true, Bool.true_and]
  · simpa only [interpretation_code] using hv

/-- The genuine source return derives the actual finite public endpoint
needed by bounded public recoders, for every executing normal branch. -/
theorem execute_lt_public_endpoint (s a out : Nat) (ho : out ∈ Branches.execute s a) :
    interpretation (Branches.outputContext s a) out < finiteBase ((s + 1) + 1) := by
  obtain ⟨c, hc, hl, hv⟩ := execute_source_code s a out ho
  have hb := LowArithmetic.lowInput_bound s c hl
  simpa only [hv] using hb

/-- The same actual finite caller bound holds for both executing raw
branches, in their genuine selected output context. -/
theorem raw_execute_lt_public_endpoint (s a out : Nat) (ho : out ∈ Branches.Raw.execute s a) :
    interpretation (Branches.outputContext s (Branches.Raw.normalizedRoot s a)) out <
      finiteBase ((s + 1) + 1) := by
  obtain ⟨c, hc, hl, hv⟩ := raw_execute_source_code s a out ho
  have hb := LowArithmetic.lowInput_bound s c hl
  simpa only [hv] using hb

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Lambda.SourceReturn
