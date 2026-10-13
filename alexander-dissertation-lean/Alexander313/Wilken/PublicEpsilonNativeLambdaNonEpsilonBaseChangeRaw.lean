import Alexander313.Wilken.PublicEpsilonNativeLambdaNonEpsilonBaseChange
import Alexander313.Wilken.HereditaryNativeLambdaRawBranches

/-!
# Original raw non-epsilon lambda and smaller-base pi

The genuine native normalizer runs before the concrete non-epsilon lambda
checker. Its domain is exactly the ORIGINAL admitted proper non-epsilon
theta-zero tree. Original root and argument values are preserved, so the
actual output equals Definition2.45's zeta of the original raw argument.
Original chosen-presentation Par derives target admission, normalized
FULL Par and every executing pi caller. No supplied normalized guard,
target properness or output-cutoff oracle. HIGH lambda remains separate.
Source-only, uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Lambda.NonEpsilonBaseChange.Raw

open ThetaCourse
open BaseTransformation (ParBounded)

def rootCheck (q c : Nat) : Bool := checkCode q c && Localization.rootShape c

theorem rootCheck_primrec : Primrec₂ rootCheck :=
  (Primrec.and.comp checkCode_primrec
    (Localization.rootShape_primrec.comp Primrec.snd)).to₂

theorem rootCheck_exact (q c : Nat) : rootCheck q c = true ↔
    ∃ a : RelativeTerm Nat, c = (.theta 0 a).code ∧ check q (.theta 0 a) = true := by
  constructor
  · intro hc
    obtain ⟨ht, hs⟩ := Bool.and_eq_true.mp hc
    obtain ⟨t, he, ha⟩ := (checkCode_exact q c).mp ht
    obtain ⟨a, hta⟩ := (Localization.rootShape_code t).mp (by simpa only [← he] using hs)
    subst t
    exact ⟨a, he.symm, ha⟩
  · rintro ⟨a, rfl, ha⟩
    exact Bool.and_eq_true.mpr ⟨by simpa only [checkCode_code] using ha,
      (Localization.rootShape_code _).mpr ⟨a, rfl⟩⟩

def normalizedRoot (q c : Nat) : Nat := Normalization.normalizeCode q c

theorem normalizedRoot_primrec : Primrec₂ normalizedRoot :=
  Normalization.Effective.normalizeCode_primrec

theorem normalizedRoot_theta (q : Nat) (a : RelativeTerm Nat)
    (ha : check q (.theta 0 a) = true) :
    normalizedRoot q (.theta 0 a : RelativeTerm Nat).code =
      (.theta 0 (Normalization.normalize q a) : RelativeTerm Nat).code := by
  simp only [normalizedRoot, Normalization.normalizeCode, checkCode_code, ha,
    Bool.cond_true, rawTree_code, Normalization.normalize]

def inputCheck (q c : Nat) : Bool := rootCheck q c &&
  NonEpsilonBaseChange.inputCheck q (normalizedRoot q c)

theorem inputCheck_primrec : Primrec₂ inputCheck :=
  (Primrec.and.comp rootCheck_primrec
    (NonEpsilonBaseChange.inputCheck_primrec.comp Primrec.fst normalizedRoot_primrec)).to₂

/-- The original RAW proper non-epsilon domain, with no normalized-domain
or target-branch premise. -/
theorem inputCheck_exact (q c : Nat) : inputCheck q c = true ↔
    rootCheck q c = true ∧ base q < interpretation q c ∧
      Ordinal.omega0 ^ interpretation q c ≠ interpretation q c := by
  constructor
  · intro hc
    obtain ⟨hr, hn⟩ := Bool.and_eq_true.mp hc
    have hs := (NonEpsilonBaseChange.inputCheck_exact q _).mp hn
    have hv := (Normalization.normalizeCode_accepted q c (Bool.and_eq_true.mp hr).1).2
    exact ⟨hr, by simpa only [normalizedRoot, hv] using hs.2.1,
      by simpa only [normalizedRoot, hv] using hs.2.2⟩
  · rintro ⟨hr, hp, hε⟩
    obtain ⟨a, he, ha⟩ := (rootCheck_exact q c).mp hr
    have hn := Normalization.normalize_checked q (.theta 0 a) ha
    have hv := (Normalization.normalizeCode_accepted q c (Bool.and_eq_true.mp hr).1).2
    have hd : DirectZeta.inputCheck q (normalizedRoot q c) = true :=
      (DirectZeta.inputCheck_exact q _).mpr
        ⟨Normalization.normalize q a, by rw [he]; exact normalizedRoot_theta q a ha,
          by simpa only [Normalization.normalize] using hn.1,
          by simpa only [Normalization.normalize] using hn.2.1⟩
    exact Bool.and_eq_true.mpr ⟨hr, (NonEpsilonBaseChange.inputCheck_exact q _).mpr
      ⟨hd, by simpa only [normalizedRoot, hv] using hp,
        by simpa only [normalizedRoot, hv] using hε⟩⟩

/-- Both original root and argument values follow from the real normalizer. -/
theorem normalized_argument_value (q c : Nat) (hc : rootCheck q c = true) :
    interpretation q (DirectZeta.argumentCode (normalizedRoot q c)) =
      interpretation q (DirectZeta.argumentCode c) := by
  obtain ⟨a, rfl, ha⟩ := (rootCheck_exact q c).mp hc
  rw [normalizedRoot_theta q a ha]
  simp only [DirectZeta.argumentCode, Localization.argumentCode_theta, interpretation_code]
  exact (Normalization.normalize_checked q a (FixedPoint.checked_theta_argument q 0 a ha)).2.2

theorem sourceValue_normalized (q c : Nat) (hc : rootCheck q c = true) :
    DirectZeta.sourceValue q (normalizedRoot q c) = DirectZeta.sourceValue q c :=
  DirectZeta.sourceValue_argument_congr q _ c (normalized_argument_value q c hc)

def execute (q c : Nat) : Part Nat := cond (inputCheck q c)
  (NonEpsilonBaseChange.execute q (normalizedRoot q c)) Part.none

theorem execute_partrec : Partrec₂ execute := by
  have hp := NonEpsilonBaseChange.execute_partrec.comp Computable.fst normalizedRoot_primrec.to_comp
  exact (Partrec.cond inputCheck_primrec.to_comp hp Partrec.none).to₂

theorem execute_domain (q c : Nat) : (execute q c).Dom ↔ inputCheck q c = true := by
  cases hc : inputCheck q c with
  | false => simp only [execute, hc, Bool.cond_false, Part.not_none_dom, Bool.false_eq_true]
  | true => simp only [execute, hc, Bool.cond_true, NonEpsilonBaseChange.execute_domain,
      (Bool.and_eq_true.mp hc).2]

theorem execute_returns (q c : Nat) (hc : inputCheck q c = true) : ∃ out, out ∈ execute q c :=
  Part.dom_iff_mem.mp ((execute_domain q c).mpr hc)

theorem normalized_execution (q c out : Nat) (ho : out ∈ execute q c) :
    out ∈ NonEpsilonBaseChange.execute q (normalizedRoot q c) := by
  have hc := (execute_domain q c).mp (Part.dom_iff_mem.mpr ⟨out, ho⟩)
  simpa only [execute, hc, Bool.cond_true] using ho

theorem execute_spec (q c out : Nat) (ho : out ∈ execute q c) :
    inputCheck q c = true ∧ lowCheckCode q out = true ∧
      Comparison.acceptedCode q out = true ∧ interpretation q out = DirectZeta.sourceValue q c := by
  have hc := (execute_domain q c).mp (Part.dom_iff_mem.mpr ⟨out, ho⟩)
  have hs := NonEpsilonBaseChange.definition_2_45_spec q _ out (normalized_execution q c out ho)
  exact ⟨hc, hs.2.1, hs.2.2.1,
    hs.2.2.2.trans (sourceValue_normalized q c (Bool.and_eq_true.mp hc).1)⟩

/-- The original raw chosen Par set gives an actual target raw checker. -/
theorem target_root (q v c : Nat) (hc : rootCheck q c = true)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree c)) : rootCheck v c = true := by
  obtain ⟨a, he, ha⟩ := (rootCheck_exact q c).mp hc
  have ht : check v (.theta 0 a) = true := BaseTransformation.check_change q v _ ha hv
    ((BaseTransformation.parBounded_iff_payloads q v _ ha hv).mp
      (by simpa only [he, rawTree_code] using hp))
  exact (rootCheck_exact v c).mpr ⟨a, he, ht⟩

theorem inputCheck_context (q v c : Nat) (hcq : rootCheck q c = true)
    (hcv : rootCheck v c = true) : inputCheck q c = inputCheck v c := by
  have hq := (Bool.and_eq_true.mp hcq).1
  have hv := (Bool.and_eq_true.mp hcv).1
  have he := BaseTransformation.normalizeCode_context q v c hq hv
  have hnq := (Normalization.normalizeCode_checked q c hq).1
  have hnv : checkCode v (normalizedRoot q c) = true := by
    rw [normalizedRoot, he]; exact (Normalization.normalizeCode_checked v c hv).1
  simp only [inputCheck, hcq, hcv, Bool.true_and]
  exact (NonEpsilonBaseChange.inputCheck_context q v _ hnq hnv).trans
    (congrArg (NonEpsilonBaseChange.inputCheck v) he)

theorem target_input (q v c : Nat) (hc : inputCheck q c = true)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree c)) : inputCheck v c = true := by
  have hr := (Bool.and_eq_true.mp hc).1
  rw [← inputCheck_context q v c hr (target_root q v c hr hv hp)]
  exact hc

/-- Normalized FULL Par is constructed from the real target normalizer,
not inferred from value equality or supplied as a caller oracle. -/
theorem normalized_parBounded (q v c : Nat) (hc : inputCheck q c = true)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree c)) :
    ParBounded q v (rawTree (normalizedRoot q c)) := by
  have hr := (Bool.and_eq_true.mp hc).1
  have hq := (Bool.and_eq_true.mp hr).1
  have ht := (Bool.and_eq_true.mp (target_root q v c hr hv hp)).1
  have he := BaseTransformation.normalizeCode_context q v c hq ht
  have hnq := (Normalization.normalizeCode_checked q c hq).1
  have hnv : checkCode v (normalizedRoot q c) = true := by
    rw [normalizedRoot, he]; exact (Normalization.normalizeCode_checked v c ht).1
  exact (BaseTransformation.parBounded_iff_payloads q v _ (Arithmetic.raw_checked q _ hnq) hv).mpr
    (checked_admissible v _ (Arithmetic.raw_checked v _ hnv)).1

theorem execute_change (q v c : Nat) (hc : inputCheck q c = true)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree c)) : execute q c = execute v c := by
  have ht := target_input q v c hc hv hp
  have hq := (Bool.and_eq_true.mp (Bool.and_eq_true.mp hc).1).1
  have hvc := (Bool.and_eq_true.mp (Bool.and_eq_true.mp ht).1).1
  have he := BaseTransformation.normalizeCode_context q v c hq hvc
  simp only [execute, hc, ht, Bool.cond_true]
  exact (NonEpsilonBaseChange.execute_change q v _ (Bool.and_eq_true.mp hc).2 hv
    (normalized_parBounded q v c hc hv hp)).trans
      (congrArg (NonEpsilonBaseChange.execute v) he)

theorem output_parBounded (q v c out : Nat) (ho : out ∈ execute q c)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree c)) : ParBounded q v (rawTree out) := by
  have hc := (execute_domain q c).mp (Part.dom_iff_mem.mpr ⟨out, ho⟩)
  exact NonEpsilonBaseChange.output_parBounded q v _ out (normalized_execution q c out ho) hv
    (normalized_parBounded q v c hc hv hp)

theorem input_pi_caller (q v c : Nat) (hc : inputCheck q c = true)
    (hv : baseCheck v = true) (hl : base v < base q)
    (hp : ParBounded q v (rawTree c)) : BaseTransformation.inputCheck q v c = true :=
  (BaseTransformation.inputCheck_exact q v c).mpr
    ⟨(Bool.and_eq_true.mp (Bool.and_eq_true.mp hc).1).1, hv, hl, hp⟩

theorem output_pi_caller (q v c out : Nat) (ho : out ∈ execute q c)
    (hv : baseCheck v = true) (hl : base v < base q)
    (hp : ParBounded q v (rawTree c)) : BaseTransformation.inputCheck q v out = true :=
  (BaseTransformation.inputCheck_exact q v out).mpr
    ⟨(Bool.and_eq_true.mp (execute_spec q c out ho).2.1).1, hv, hl,
      output_parBounded q v c out ho hv hp⟩

theorem execute_pi (q v c : Nat) (hc : inputCheck q c = true)
    (hv : baseCheck v = true) (hl : base v < base q)
    (hp : ParBounded q v (rawTree c)) :
    (execute q c).map (BaseTransformation.piCode q v) =
      execute v (BaseTransformation.piCode q v c) := by
  have he := BaseTransformation.piCode_eq q v c (input_pi_caller q v c hc hv hl hp)
  rw [he]
  apply Part.ext
  intro out
  rw [Part.mem_map_iff]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [BaseTransformation.piCode_eq q v a (output_pi_caller q v c a ha hv hl hp)]
    rwa [← execute_change q v c hc hv hp]
  · intro ho
    have hq : out ∈ execute q c := by rwa [execute_change q v c hc hv hp]
    exact ⟨out, hq, BaseTransformation.piCode_eq q v out (output_pi_caller q v c out hq hv hl hp)⟩

/-- The existing ORIGINAL normalize-first BOTH-branch finite lambda has
an actual execution of this value in the same original output context. -/
theorem standard_lambda_execution (s c out : Nat)
    (ho : out ∈ execute (NativePublicBridge.contextCode s) c) :
    ∃ other, other ∈ Lambda.Branches.Raw.execute s c ∧
      Lambda.Branches.outputContext s (Lambda.Branches.Raw.normalizedRoot s c) =
        NativePublicBridge.contextCode s ∧
      interpretation (NativePublicBridge.contextCode s) other =
        interpretation (NativePublicBridge.contextCode s) out := by
  have hc := (execute_spec _ c out ho).1
  have hs := (inputCheck_exact _ c).mp hc
  obtain ⟨a, he, ha⟩ := (rootCheck_exact _ c).mp hs.1
  have hi : Lambda.Branches.Raw.inputCheck s c = true :=
    (Lambda.Branches.Raw.inputCheck_exact s c).mpr
      ⟨a, he, ha, by simpa only [he, interpretation_code] using hs.2.1⟩
  obtain ⟨other, hother⟩ := NonEpsilonBaseChange.standard_lambda_execution s _ out
    (normalized_execution _ c out ho)
  refine ⟨other, ?_, hother.2.1, hother.2.2⟩
  simpa only [Lambda.Branches.Raw.execute, hi, Bool.cond_true,
    Lambda.Branches.Raw.normalizedRoot, normalizedRoot] using hother.1

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Lambda.NonEpsilonBaseChange.Raw
