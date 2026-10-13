import Alexander313.Wilken.PublicEpsilonNativeLogEndBaseChange
import Alexander313.Wilken.HereditaryNativeDirectZeta

/-!
# Actual STRICT and direct-zeta executing base change

The original admitted Normal theta-zero root and its chosen-presentation
Par cutoff derive the real target root checker. Its argument is genuinely
admitted Normal at both bases, so the existing finite fixed-point parser
proves equality of the actual STRICT tests. The actual cardinal residual
is literally the same word; real LOW last-log agreement completes both
partial execution branches. Checked target outputs supply FULL payload
and original Par bounds before the actual pi map is applied.
No STRICT, residual, logarithm, target-caller or output-cutoff oracle.
Native contexts are actual coded epsilons. Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.DirectZeta.BaseChange

open ThetaCourse
open BaseTransformation (ParBounded)

theorem inputCheck_context (q v c : Nat) (hcq : checkCode q c = true)
    (hcv : checkCode v c = true) : inputCheck q c = inputCheck v c := by
  simp only [inputCheck, SourceChi.BaseChange.acceptedCode_context q v c hcq hcv]

/-- Original chosen-presentation Par derives the complete target admitted
theta-zero caller; no second-context root guard is supplied. -/
theorem target_input (q v c : Nat) (hc : inputCheck q c = true)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree c)) : inputCheck v c = true := by
  obtain ⟨a, he, ht, hn⟩ := (inputCheck_exact q c).mp hc
  have hlq : lowCheckCode q c = true := by
    simp only [he, lowCheckCode_code, lowCheck, ht, RelativeTerm.outerSort,
      decide_true, Bool.true_and]
  have hlv := OmegaPowers.BaseChange.target_low q v c hlq hv hp
  rw [← inputCheck_context q v c (Bool.and_eq_true.mp hlq).1 (Bool.and_eq_true.mp hlv).1]
  exact hc

theorem strictCheck_context (q v c : Nat) (hcq : inputCheck q c = true)
    (hcv : inputCheck v c = true) : strictCheck q c = strictCheck v c :=
  SourceChi.BaseChange.strictCode_context q v 0 (argumentCode c)
    (argument_input q c hcq) (argument_input v c hcv)

/-- The exact original native direct-zeta computation, including the true
STRICT-false zero branch, agrees literally at both derived callers. -/
theorem execute_context (q v c : Nat) (hcq : inputCheck q c = true)
    (hcv : inputCheck v c = true) : execute q c = execute v c := by
  have hs := strictCheck_context q v c hcq hcv
  have hl := LogEnd.BaseChange.execute_context q v (residualCode c)
    (residualCode_spec q c hcq).1 (residualCode_spec v c hcv).1
  simp only [execute, hcq, hcv, Bool.cond_true, hs, hl]

theorem execute_change (q v c : Nat) (hc : inputCheck q c = true)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree c)) :
    execute q c = execute v c := execute_context q v c hc (target_input q v c hc hv hp)

/-- FULL hidden payload support is derived from the actual target
direct-zeta output checker, rather than from ordinal-value equality. -/
theorem output_payloads (q v c out : Nat) (ho : out ∈ execute q c)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree c)) :
    Payloads v (rawTree out) := by
  have hc := (execute_spec q c out ho).1
  have ht : out ∈ execute v c := by rw [← execute_change q v c hc hv hp]; exact ho
  have htarget := (Bool.and_eq_true.mp (execute_spec v c out ht).2.1).1
  exact (checked_admissible v _ (Arithmetic.raw_checked v out htarget)).1

theorem output_parBounded (q v c out : Nat) (ho : out ∈ execute q c)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree c)) :
    ParBounded q v (rawTree out) := by
  have hsource := (Bool.and_eq_true.mp (execute_spec q c out ho).2.1).1
  exact (BaseTransformation.parBounded_iff_payloads q v _
    (Arithmetic.raw_checked q out hsource) hv).mpr (output_payloads q v c out ho hv hp)

theorem input_pi_caller (q v c : Nat) (hc : inputCheck q c = true)
    (hv : baseCheck v = true) (hl : base v < base q)
    (hp : ParBounded q v (rawTree c)) : BaseTransformation.inputCheck q v c = true := by
  have hcheck := (Comparison.acceptedCode_exact q c).mp (Bool.and_eq_true.mp hc).1
  exact (BaseTransformation.inputCheck_exact q v c).mpr ⟨hcheck.1, hv, hl, hp⟩

theorem output_pi_caller (q v c out : Nat) (ho : out ∈ execute q c)
    (hv : baseCheck v = true) (hl : base v < base q)
    (hp : ParBounded q v (rawTree c)) : BaseTransformation.inputCheck q v out = true :=
  (BaseTransformation.inputCheck_exact q v out).mpr
    ⟨(Bool.and_eq_true.mp (execute_spec q c out ho).2.1).1, hv, hl,
      output_parBounded q v c out ho hv hp⟩

/-- Actual finite pi commutes with actual direct zeta on every original
chosen-presentation parameter cutoff, with all numerical zero outputs. -/
theorem execute_pi (q v c : Nat) (hc : inputCheck q c = true)
    (hv : baseCheck v = true) (hl : base v < base q)
    (hp : ParBounded q v (rawTree c)) :
    (execute q c).map (BaseTransformation.piCode q v) =
      execute v (BaseTransformation.piCode q v c) := by
  rw [BaseTransformation.piCode_eq q v c (input_pi_caller q v c hc hv hl hp)]
  have he := execute_change q v c hc hv hp
  apply Part.ext
  intro out
  constructor
  · intro hm
    obtain ⟨d, hd, hdo⟩ := (Part.mem_map_iff _).mp hm
    rw [BaseTransformation.piCode_eq q v d (output_pi_caller q v c d hd hv hl hp)] at hdo
    subst out
    rw [← he]
    exact hd
  · intro ht
    have ho : out ∈ execute q c := by rw [he]; exact ht
    exact (Part.mem_map_iff _).mpr ⟨out, ho,
      BaseTransformation.piCode_eq q v out (output_pi_caller q v c out ho hv hl hp)⟩

theorem pi_output_spec (q v c out : Nat) (ho : out ∈ execute q c)
    (hv : baseCheck v = true) (hl : base v < base q)
    (hp : ParBounded q v (rawTree c)) :
    lowCheckCode v (BaseTransformation.piCode q v out) = true ∧
      Comparison.acceptedCode v (BaseTransformation.piCode q v out) = true ∧
      interpretation v (BaseTransformation.piCode q v out) =
        sourceValue v (BaseTransformation.piCode q v c) := by
  have hc := (execute_spec q c out ho).1
  have ht : out ∈ execute v c := by rw [← execute_change q v c hc hv hp]; exact ho
  rw [BaseTransformation.piCode_eq q v c (input_pi_caller q v c hc hv hl hp),
    BaseTransformation.piCode_eq q v out (output_pi_caller q v c out ho hv hl hp)]
  exact (execute_spec v c out ht).2

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.DirectZeta.BaseChange
