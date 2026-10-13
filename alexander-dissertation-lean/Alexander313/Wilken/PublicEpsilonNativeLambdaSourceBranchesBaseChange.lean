import Alexander313.Wilken.PublicEpsilonNativeLambdaSourceBranches

/-!
# Full original-source lambda2.48(e) with genuine output provenance

Original chosen root Par derives the actual smaller-context proper root
and the same exhaustive branch. The genuine high returned-iota addition
or genuine non-epsilon direct-zeta execution agrees literally. Actual
target output admission supplies FULL hidden payload cutoff before output
Par and executing pi are concluded. No branch, target root, output Par,
source representation, selected endpoint or lambda transport oracle.
Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Lambda.SourceBranches.BaseChange

open ThetaCourse
open BaseTransformation (ParBounded)

theorem execute_change (q v root : Nat) (ha : inputCheck q root = true)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree root)) :
    execute q root = execute v root := by
  have ht := target_input q v root ha hv hp
  cases hh : high root with
  | true =>
    rw [execute_high q root ha hh, execute_high v root ht hh]
    exact PublicEpsilonUnboundedIota.LambdaSource.BaseChange.execute_change q v root
      (high_input q root ha hh) hv hp
  | false =>
    rw [execute_low q root ha hh, execute_low v root ht hh]
    exact NonEpsilonBaseChange.execute_change q v root (low_input q root ha hh) hv hp

theorem output_payloads (q v root out : Nat) (ho : out ∈ execute q root)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree root)) : Payloads v (rawTree out) := by
  have ha := (execute_spec q root out ho).1
  have ht : out ∈ execute v root := by rw [← execute_change q v root ha hv hp]; exact ho
  have hc := ((Comparison.acceptedCode_exact v out).mp (execute_spec v root out ht).2.2.1).1
  exact (checked_admissible v _ (Arithmetic.raw_checked v out hc)).1

theorem output_parBounded (q v root out : Nat) (ho : out ∈ execute q root)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree root)) :
    ParBounded q v (rawTree out) := by
  have hc := ((Comparison.acceptedCode_exact q out).mp (execute_spec q root out ho).2.2.1).1
  exact (BaseTransformation.parBounded_iff_payloads q v _ (Arithmetic.raw_checked q out hc) hv).mpr
    (output_payloads q v root out ho hv hp)

theorem root_pi_caller (q v root : Nat) (ha : inputCheck q root = true)
    (hv : baseCheck v = true) (hl : base v < base q)
    (hp : ParBounded q v (rawTree root)) : BaseTransformation.inputCheck q v root = true :=
  (BaseTransformation.inputCheck_exact q v root).mpr ⟨input_original q root ha, hv, hl, hp⟩

theorem output_pi_caller (q v root out : Nat) (ho : out ∈ execute q root)
    (hv : baseCheck v = true) (hl : base v < base q)
    (hp : ParBounded q v (rawTree root)) : BaseTransformation.inputCheck q v out = true :=
  (BaseTransformation.inputCheck_exact q v out).mpr
    ⟨((Comparison.acceptedCode_exact q out).mp (execute_spec q root out ho).2.2.1).1,
      hv, hl, output_parBounded q v root out ho hv hp⟩

/-- Full original Lemma2.48(e), on both executing proper Normal theta-zero
branches, derives FULL output Par and the genuine actual pi graph row. -/
theorem source_lemma_2_48_e (q v root out : Nat) (ho : out ∈ execute q root)
    (hv : baseCheck v = true) (hl : base v < base q)
    (hp : ParBounded q v (rawTree root)) :
    ParBounded q v (rawTree out) ∧
      BaseTransformation.piCode q v out ∈ execute v (BaseTransformation.piCode q v root) := by
  have ha := (execute_spec q root out ho).1
  refine ⟨output_parBounded q v root out ho hv hp, ?_⟩
  rw [BaseTransformation.piCode_eq q v out (output_pi_caller q v root out ho hv hl hp),
    BaseTransformation.piCode_eq q v root (root_pi_caller q v root ha hv hl hp),
    ← execute_change q v root ha hv hp]
  exact ho

theorem execute_pi (q v root : Nat) (ha : inputCheck q root = true)
    (hv : baseCheck v = true) (hl : base v < base q)
    (hp : ParBounded q v (rawTree root)) :
    (execute q root).map (BaseTransformation.piCode q v) =
      execute v (BaseTransformation.piCode q v root) := by
  rw [BaseTransformation.piCode_eq q v root (root_pi_caller q v root ha hv hl hp)]
  apply Part.ext
  intro out
  constructor
  · intro hm
    obtain ⟨d, hd, he⟩ := (Part.mem_map_iff _).mp hm
    rw [BaseTransformation.piCode_eq q v d (output_pi_caller q v root d hd hv hl hp)] at he
    subst out
    rw [← execute_change q v root ha hv hp]
    exact hd
  · intro ht
    have ho : out ∈ execute q root := by rw [execute_change q v root ha hv hp]; exact ht
    exact (Part.mem_map_iff _).mpr ⟨out, ho,
      BaseTransformation.piCode_eq q v out (output_pi_caller q v root out ho hv hl hp)⟩

theorem pi_output_spec (q v root out : Nat) (ho : out ∈ execute q root)
    (hv : baseCheck v = true) (hl : base v < base q)
    (hp : ParBounded q v (rawTree root)) :
    lowCheckCode v (BaseTransformation.piCode q v out) = true ∧
      Comparison.acceptedCode v (BaseTransformation.piCode q v out) = true ∧
      interpretation v (BaseTransformation.piCode q v out) =
        sourceValue v (BaseTransformation.piCode q v root) :=
  (execute_spec v _ _ (source_lemma_2_48_e q v root out ho hv hl hp).2).2

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Lambda.SourceBranches.BaseChange
