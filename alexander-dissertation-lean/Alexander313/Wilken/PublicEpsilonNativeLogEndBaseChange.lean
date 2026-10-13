import Alexander313.Wilken.PublicEpsilonNativeLogEndBaseChangeSupport

/-!
# Genuine last-log output cutoffs and executing pi transport

The original RAW LOW source term and its chosen-presentation atomic-stop
Par cutoff derive the actual second-context checker. Literal agreement of
the genuine partial last-log computations then supplies a checked target
output. Its FULL hidden payload and original Par cutoffs follow from that
checker. Every actual pi caller, including zero outputs, is constructed.
No logarithm, output-cutoff or target-admission oracle. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.LogEnd.BaseChange

open ThetaCourse
open BaseTransformation (ParBounded)

theorem execute_change (q v c : Nat) (hc : lowCheckCode q c = true)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree c)) :
    execute q c = execute v c :=
  execute_context q v c hc (OmegaPowers.BaseChange.target_low q v c hc hv hp)

/-- The full syntactic target cutoff follows from the actual target
last-log output checker, including every hidden theta argument. -/
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

theorem input_pi_caller (q v c : Nat) (hc : lowCheckCode q c = true)
    (hv : baseCheck v = true) (hl : base v < base q)
    (hp : ParBounded q v (rawTree c)) : BaseTransformation.inputCheck q v c = true :=
  OmegaPowers.BaseChange.input_pi_caller q v c hc hv hl hp

theorem output_pi_caller (q v c out : Nat) (ho : out ∈ execute q c)
    (hv : baseCheck v = true) (hl : base v < base q)
    (hp : ParBounded q v (rawTree c)) : BaseTransformation.inputCheck q v out = true :=
  (BaseTransformation.inputCheck_exact q v out).mpr
    ⟨(Bool.and_eq_true.mp (execute_spec q c out ho).2.1).1, hv, hl,
      output_parBounded q v c out ho hv hp⟩

/-- The actual pi map commutes with the actual partial last-log routine
on the whole original smaller-payload RAW LOW domain. -/
theorem execute_pi (q v c : Nat) (hc : lowCheckCode q c = true)
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
      Hereditary.LogEnd.SourceLogSpec true
        (interpretation v (BaseTransformation.piCode q v c))
        (interpretation v (BaseTransformation.piCode q v out)) := by
  have hc := (execute_spec q c out ho).1
  have ht : out ∈ execute v c := by rw [← execute_change q v c hc hv hp]; exact ho
  rw [BaseTransformation.piCode_eq q v c (input_pi_caller q v c hc hv hl hp),
    BaseTransformation.piCode_eq q v out (output_pi_caller q v c out ho hv hl hp)]
  exact (execute_spec v c out ht).2

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.LogEnd.BaseChange
