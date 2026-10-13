import Alexander313.Wilken.PublicEpsilonNativeLambdaNonEpsilonBaseChangeSupport

/-!
# The actual non-epsilon lambda branch commutes with smaller-base pi

The concrete checker has exactly the original proper Normal non-epsilon
theta-zero domain at ANY coded epsilon. Its real partial evaluator executes
the zeta branch of Definition2.45. Original Par derives target properness
and non-epsilon status; the genuine target output checker derives the FULL
output cutoff and actual pi caller. At every positive public finite source,
the original BOTH-branch lambda has an actual execution of the same value.
HIGH lambda/pi, raw normalization and full translation remain separate.
No supplied target branch, lambda identity or output-cutoff oracle.
Source-only, uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Lambda.NonEpsilonBaseChange

open ThetaCourse
open BaseTransformation (ParBounded)

def execute (q c : Nat) : Part Nat := cond (inputCheck q c) (DirectZeta.execute q c) Part.none

theorem execute_partrec : Partrec₂ execute :=
  (Partrec.cond inputCheck_primrec.to_comp DirectZeta.execute_partrec Partrec.none).to₂

theorem execute_domain (q c : Nat) : (execute q c).Dom ↔ inputCheck q c = true := by
  cases hc : inputCheck q c with
  | false => simp only [execute, hc, Bool.cond_false, Part.not_none_dom, Bool.false_eq_true]
  | true => simp only [execute, hc, Bool.cond_true, DirectZeta.execute_domain,
      ((inputCheck_exact q c).mp hc).1]

theorem execute_returns (q c : Nat) (hc : inputCheck q c = true) : ∃ out, out ∈ execute q c :=
  Part.dom_iff_mem.mp ((execute_domain q c).mpr hc)

theorem original_execution (q c out : Nat) (ho : out ∈ execute q c) :
    out ∈ DirectZeta.execute q c := by
  have hc := (execute_domain q c).mp (Part.dom_iff_mem.mpr ⟨out, ho⟩)
  simpa only [execute, hc, Bool.cond_true] using ho

/-- Actual Definition2.45 on its COMPLETE original non-epsilon domain:
the output remains in the original context and equals the genuine zeta. -/
theorem definition_2_45_spec (q c out : Nat) (ho : out ∈ execute q c) :
    inputCheck q c = true ∧ lowCheckCode q out = true ∧
      Comparison.acceptedCode q out = true ∧
      interpretation q out = DirectZeta.sourceValue q c := by
  have hc := (execute_domain q c).mp (Part.dom_iff_mem.mpr ⟨out, ho⟩)
  exact ⟨hc, (DirectZeta.execute_spec q c out (original_execution q c out ho)).2⟩

theorem execute_context (q v c : Nat) (hcq : inputCheck q c = true)
    (hcv : inputCheck v c = true) : execute q c = execute v c := by
  simp only [execute, hcq, hcv, Bool.cond_true,
    DirectZeta.BaseChange.execute_context q v c
      ((inputCheck_exact q c).mp hcq).1 ((inputCheck_exact v c).mp hcv).1]

theorem execute_change (q v c : Nat) (hc : inputCheck q c = true)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree c)) : execute q c = execute v c :=
  execute_context q v c hc (target_input q v c hc hv hp)

theorem output_payloads (q v c out : Nat) (ho : out ∈ execute q c)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree c)) : Payloads v (rawTree out) :=
  DirectZeta.BaseChange.output_payloads q v c out (original_execution q c out ho) hv hp

theorem output_parBounded (q v c out : Nat) (ho : out ∈ execute q c)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree c)) : ParBounded q v (rawTree out) :=
  DirectZeta.BaseChange.output_parBounded q v c out (original_execution q c out ho) hv hp

theorem output_pi_caller (q v c out : Nat) (ho : out ∈ execute q c)
    (hv : baseCheck v = true) (hl : base v < base q)
    (hp : ParBounded q v (rawTree c)) : BaseTransformation.inputCheck q v out = true :=
  DirectZeta.BaseChange.output_pi_caller q v c out (original_execution q c out ho) hv hl hp

/-- The non-epsilon clause of original Lemma2.48(e), as an equality of
the real partial executing pi/lambda computations, including zero outputs. -/
theorem execute_pi (q v c : Nat) (hc : inputCheck q c = true)
    (hv : baseCheck v = true) (hl : base v < base q)
    (hp : ParBounded q v (rawTree c)) :
    (execute q c).map (BaseTransformation.piCode q v) =
      execute v (BaseTransformation.piCode q v c) := by
  have hd := ((inputCheck_exact q c).mp hc).1
  have he := BaseTransformation.piCode_eq q v c (DirectZeta.BaseChange.input_pi_caller q v c hd hv hl hp)
  have ht := target_input q v c hc hv hp
  have hq : execute q c = DirectZeta.execute q c := by simp only [execute, hc, Bool.cond_true]
  have htarget : execute v (BaseTransformation.piCode q v c) =
      DirectZeta.execute v (BaseTransformation.piCode q v c) := by
    rw [he]
    simp only [execute, ht, Bool.cond_true]
  rw [hq, htarget]
  exact DirectZeta.BaseChange.execute_pi q v c hd hv hl hp

/-- The actual original positive-public BOTH-branch lambda, rather than
a renamed zeta routine, has a genuine execution with this exact value. -/
theorem standard_lambda_execution (s c out : Nat)
    (ho : out ∈ execute (NativePublicBridge.contextCode s) c) :
    ∃ other, other ∈ NativeContext.Lambda.Branches.execute s c ∧
      NativeContext.Lambda.Branches.outputContext s c = NativePublicBridge.contextCode s ∧
      interpretation (NativePublicBridge.contextCode s) other =
        interpretation (NativePublicBridge.contextCode s) out := by
  have hc := (definition_2_45_spec _ c out ho).1
  have hd := (inputCheck_exact _ c).mp hc
  obtain ⟨a, he, ht, hn⟩ := (DirectZeta.inputCheck_exact _ c).mp hd.1
  have hi : NativeContext.Lambda.Branches.inputCheck s c = true :=
    (NativeContext.Lambda.Branches.inputCheck_exact s c).mpr
      ⟨a, he, ht, hn, by simpa only [he, interpretation_code] using hd.2.1⟩
  obtain ⟨other, hother⟩ := NativeContext.Lambda.Branches.execute_returns s c hi
  have hs := NativeContext.Lambda.Branches.execute_non_epsilon s c other hother hd.2.2
  exact ⟨other, hother, hs.1, hs.2.2.1.trans
    (DirectZeta.execute_standard_value s c out (original_execution _ c out ho)).symm⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Lambda.NonEpsilonBaseChange
