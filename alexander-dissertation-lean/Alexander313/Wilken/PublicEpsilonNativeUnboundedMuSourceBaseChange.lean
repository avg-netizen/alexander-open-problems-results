import Alexander313.Wilken.PublicEpsilonNativeUnboundedMuSource
import Alexander313.Wilken.PublicEpsilonNativeUnboundedOmegaQuotientBaseChange
import Alexander313.Wilken.PublicEpsilonNativePowerBaseChange

/-!
# Genuine mu3.9 provenance, full cutoff and executing pi

The original high-root chosen Par supplies actual target admission and
coefficient/offset agreement. The original-source returned coefficient
retains FULL Par, while the actual shifted finite indicator computes equal
NEW-base bits. Actual original-source finite-tail and omega-power producers
therefore agree literally; their target checker supplies FULL output Par.
The actual pi caller and numerical executing equation are derived before
identifying the two genuine mu values. No target-iota parameter cutoff,
mu/indicator/translation oracle or selected endpoint is supplied. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.MuSource.BaseChange

open ThetaCourse
open BaseTransformation (ParBounded)

theorem target_root (q v root : Nat) (ha : inputCheck q root = true)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree root)) :
    inputCheck v root = true := OmegaQuotient.BaseChange.target_root q v root ha hv hp

theorem returnedCoefficient_change (q v root : Nat) (ha : inputCheck q root = true)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree root)) :
    returnedCoefficient q root = returnedCoefficient v root := by
  have hc := OmegaQuotient.coefficientCode_accepted q root ha
  have hpc := OmegaQuotient.BaseChange.coefficient_parBounded q v root ha hv hp
  have he := OmegaQuotient.BaseChange.coefficientCode_change q v root ha hv hp
  unfold returnedCoefficient
  rw [← he.1]
  exact NativeContext.ReturnedIota.sourceTermCode_change q v root _ ha hc hv hp hpc

theorem returnedCoefficient_parBounded (q v root : Nat) (ha : inputCheck q root = true)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree root)) :
    ParBounded q v (rawTree (returnedCoefficient q root)) :=
  NativeContext.ReturnedIota.sourceTermCode_parBounded q v root _ ha
    (OmegaQuotient.coefficientCode_accepted q root ha) hv hp
    (OmegaQuotient.BaseChange.coefficient_parBounded q v root ha hv hp)

/-- The target-beta chi bits agree through the actual ORIGINAL shifted
fold and the genuinely derived coefficient Par cutoff. -/
theorem relativeChi_change (q v root : Nat) (ha : inputCheck q root = true)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree root)) :
    relativeChi q root = relativeChi v root := by
  have hs := OmegaQuotient.root_coefficient_spec q root ha
  have hc := OmegaQuotient.BaseChange.coefficientCode_change q v root ha hv hp
  have hpcode := OmegaQuotient.BaseChange.coefficient_parBounded q v root ha hv hp
  have hpt : ParBounded q v
      (BoundedContextIota.OmegaQuotient.limitTerm q (OmegaQuotient.argumentCode root)) := by
    simpa only [OmegaQuotient.coefficientCode_literal q root ha, rawTree_code] using hpcode
  unfold relativeChi
  rw [← hc.1, OmegaQuotient.coefficientCode_literal q root ha]
  exact ShiftedIndicator.BaseChange.chiCode_change q v root ha _
    hs.1 hs.2.1 hs.2.2.1 hv hp hpt

theorem tail_change (q v root : Nat) (ha : inputCheck q root = true)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree root)) :
    tail q root = tail v root := by
  simp only [tail, relativeChi_change q v root ha hv hp,
    (OmegaQuotient.BaseChange.coefficientCode_change q v root ha hv hp).2]

theorem exponentCode_change (q v root : Nat) (ha : inputCheck q root = true)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree root)) :
    exponentCode q root = exponentCode v root := by
  have hr := target_root q v root ha hv hp
  have hq := ((Comparison.acceptedCode_exact q _).mp (returnedCoefficient_spec q root ha).1).1
  have ht : checkCode v (returnedCoefficient q root) = true := by
    rw [returnedCoefficient_change q v root ha hv hp]
    exact ((Comparison.acceptedCode_exact v _).mp (returnedCoefficient_spec v root hr).1).1
  unfold exponentCode
  rw [← returnedCoefficient_change q v root ha hv hp, ← tail_change q v root ha hv hp]
  exact OmegaPowers.BaseChange.finiteTailCode_context q v _ _
    (source_checked q root ha) hv hq ht

/-- The FULL exponent cutoff follows from an actual second-context
finite-tail checker, not from equality of ordinal values. -/
theorem exponentCode_payloads (q v root : Nat) (ha : inputCheck q root = true)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree root)) :
    Payloads v (rawTree (exponentCode q root)) := by
  have hr := target_root q v root ha hv hp
  have hc : checkCode v (exponentCode q root) = true := by
    rw [exponentCode_change q v root ha hv hp]
    exact (Bool.and_eq_true.mp (exponentCode_spec v root hr).1).1
  exact (checked_admissible v _ (Arithmetic.raw_checked v _ hc)).1

theorem exponentCode_parBounded (q v root : Nat) (ha : inputCheck q root = true)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree root)) :
    ParBounded q v (rawTree (exponentCode q root)) :=
  (BaseTransformation.parBounded_iff_payloads q v _
    (Arithmetic.raw_checked q _ (Bool.and_eq_true.mp (exponentCode_spec q root ha).1).1) hv).mpr
    (exponentCode_payloads q v root ha hv hp)

theorem sourceCode_change (q v root : Nat) (ha : inputCheck q root = true)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree root)) :
    sourceCode q root = sourceCode v root := by
  have hr := target_root q v root ha hv hp
  rw [sourceCode_literal q root ha, sourceCode_literal v root hr,
    ← exponentCode_change q v root ha hv hp]
  exact OmegaPowers.BaseChange.powerCode_change q v _ (exponentCode_spec q root ha).1 hv
    (exponentCode_parBounded q v root ha hv hp)

theorem sourceCode_parBounded (q v root : Nat) (ha : inputCheck q root = true)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree root)) :
    ParBounded q v (rawTree (sourceCode q root)) := by
  rw [sourceCode_literal q root ha]
  exact OmegaPowers.BaseChange.powerCode_parBounded q v _ (exponentCode_spec q root ha).1 hv
    (exponentCode_parBounded q v root ha hv hp)

theorem source_pi_caller (q v root : Nat) (ha : inputCheck q root = true)
    (hv : baseCheck v = true) (hl : base v < base q)
    (hp : ParBounded q v (rawTree root)) :
    BaseTransformation.inputCheck q v (sourceCode q root) = true :=
  (BaseTransformation.inputCheck_exact q v _).mpr
    ⟨(Bool.and_eq_true.mp (sourceCode_spec q root ha).1).1, hv, hl,
      sourceCode_parBounded q v root ha hv hp⟩

/-- Genuine source3.9: original-source mu has its chosen Par cutoff and
the actual pi execution is the actual smaller-context mu producer. -/
theorem source_lemma_3_9 (q v root : Nat) (ha : inputCheck q root = true)
    (hv : baseCheck v = true) (hl : base v < base q)
    (hp : ParBounded q v (rawTree root)) :
    ParBounded q v (rawTree (sourceCode q root)) ∧
      BaseTransformation.piCode q v (sourceCode q root) =
        sourceCode v (BaseTransformation.piCode q v root) := by
  refine ⟨sourceCode_parBounded q v root ha hv hp, ?_⟩
  rw [BaseTransformation.piCode_eq q v _ (source_pi_caller q v root ha hv hl hp),
    BaseTransformation.piCode_eq q v root
      (ShiftedIndicator.BaseChange.root_pi_caller q v root ha hv hl hp)]
  exact sourceCode_change q v root ha hv hp

theorem pi_source_value (q v root : Nat) (ha : inputCheck q root = true)
    (hv : baseCheck v = true) (hl : base v < base q)
    (hp : ParBounded q v (rawTree root)) :
    interpretation v (BaseTransformation.piCode q v (sourceCode q root)) =
      Mu.sourceValue v (BaseTransformation.piCode q v root) := by
  rw [(source_lemma_3_9 q v root ha hv hl hp).2,
    BaseTransformation.piCode_eq q v root
      (ShiftedIndicator.BaseChange.root_pi_caller q v root ha hv hl hp)]
  exact source_definition_3_6 v root (target_root q v root ha hv hp)

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.MuSource.BaseChange
