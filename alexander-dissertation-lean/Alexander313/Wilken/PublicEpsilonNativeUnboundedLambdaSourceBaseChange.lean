import Alexander313.Wilken.PublicEpsilonNativeUnboundedLambdaSource
import Alexander313.Wilken.PublicEpsilonNativeDirectZetaBaseChange
import Alexander313.Wilken.PublicEpsilonNativePowerBaseChangeSupport

/-!
# Genuine HIGH lambda2.48(e) original-source provenance and pi

Original chosen root Par derives the smaller-context root and its actual
divided high-part admission. Hence the high part itself has FULL Par, and
the actual returned-iota code retains that original provenance. Real direct
zeta executes the same numerical code, and actual normalized addition agrees
at the two derived callers. The second-context output checker gives FULL
lambda payloads before Par and the actual pi map are concluded.
No delta/output Par, stopped target payload bound, selected endpoint,
target root, source representation or lambda transport oracle is supplied.
These source-only candidates are uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.LambdaSource.BaseChange

open ThetaCourse
open BaseTransformation (ParBounded)

theorem target_root (q v root : Nat) (ha : inputCheck q root = true)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree root)) :
    inputCheck v root = true := RootLowCollapse.target_root q v root ha hv hp

/-- The actual target divided-head checker supplies FULL hidden payloads;
no chosen cutoff on Delta is added to the original root premise. -/
theorem delta_parBounded (q v root : Nat) (ha : inputCheck q root = true)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree root)) :
    ParBounded q v (rawTree (deltaCode root)) := by
  have hq := ((Comparison.acceptedCode_exact q _).mp (delta_accepted q root ha)).1
  have ht := ((Comparison.acceptedCode_exact v _).mp
    (delta_accepted v root (target_root q v root ha hv hp))).1
  exact (BaseTransformation.parBounded_iff_payloads q v _ (Arithmetic.raw_checked q _ hq) hv).mpr
    (checked_admissible v _ (Arithmetic.raw_checked v _ ht)).1

theorem returnedDelta_change (q v root : Nat) (ha : inputCheck q root = true)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree root)) :
    returnedDelta q root = returnedDelta v root :=
  NativeContext.ReturnedIota.sourceTermCode_change q v root _ ha (delta_accepted q root ha)
    hv hp (delta_parBounded q v root ha hv hp)

theorem returnedDelta_parBounded (q v root : Nat) (ha : inputCheck q root = true)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree root)) :
    ParBounded q v (rawTree (returnedDelta q root)) :=
  NativeContext.ReturnedIota.sourceTermCode_parBounded q v root _ ha (delta_accepted q root ha)
    hv hp (delta_parBounded q v root ha hv hp)

theorem sourceCode_change (q v root zeta : Nat) (ha : inputCheck q root = true)
    (hz : zeta ∈ DirectZeta.execute q root)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree root)) :
    sourceCode q root zeta = sourceCode v root zeta := by
  have hr := target_root q v root ha hv hp
  have hzv : zeta ∈ DirectZeta.execute v root := by
    rw [← DirectZeta.BaseChange.execute_change q v root (zeta_input q root ha) hv hp]
    exact hz
  have hdq := ((Comparison.acceptedCode_exact q _).mp (returnedDelta_spec q root ha).1).1
  have hdz := ((Comparison.acceptedCode_exact q _).mp (DirectZeta.execute_spec q root zeta hz).2.2.1).1
  have hdv : checkCode v (returnedDelta q root) = true := by
    rw [returnedDelta_change q v root ha hv hp]
    exact ((Comparison.acceptedCode_exact v _).mp (returnedDelta_spec v root hr).1).1
  have hzvcheck := ((Comparison.acceptedCode_exact v _).mp (DirectZeta.execute_spec v root zeta hzv).2.2.1).1
  unfold sourceCode
  rw [← returnedDelta_change q v root ha hv hp]
  exact OmegaPowers.BaseChange.addCode_context q v _ _ hdq hdz hdv hzvcheck

/-- The actual whole partial computations agree literally on the derived
smaller-source domain, retaining every numerical output including zero. -/
theorem execute_change (q v root : Nat) (ha : inputCheck q root = true)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree root)) :
    execute q root = execute v root := by
  have hr := target_root q v root ha hv hp
  have hz := DirectZeta.BaseChange.execute_change q v root (zeta_input q root ha) hv hp
  apply Part.ext
  intro out
  rw [execute_graph q root out, execute_graph v root out]
  constructor
  · rintro ⟨_, zeta, hzt, he⟩
    have hztv : zeta ∈ DirectZeta.execute v root := by rw [← hz]; exact hzt
    exact ⟨hr, zeta, hztv, (sourceCode_change q v root zeta ha hzt hv hp).symm.trans he⟩
  · rintro ⟨_, zeta, hzt, he⟩
    have hztq : zeta ∈ DirectZeta.execute q root := by rw [hz]; exact hzt
    exact ⟨ha, zeta, hztq, (sourceCode_change q v root zeta ha hztq hv hp).trans he⟩

/-- FULL original output Par follows from the real target output checker,
independently of any equality of ordinal values. -/
theorem output_parBounded (q v root out : Nat) (ho : out ∈ execute q root)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree root)) :
    ParBounded q v (rawTree out) := by
  have ha := (execute_spec q root out ho).1
  have ht : out ∈ execute v root := by rw [← execute_change q v root ha hv hp]; exact ho
  have hq := ((Comparison.acceptedCode_exact q out).mp (execute_spec q root out ho).2.2.1).1
  have htarget := ((Comparison.acceptedCode_exact v out).mp (execute_spec v root out ht).2.2.1).1
  exact (BaseTransformation.parBounded_iff_payloads q v _ (Arithmetic.raw_checked q out hq) hv).mpr
    (checked_admissible v _ (Arithmetic.raw_checked v out htarget)).1

theorem root_pi_caller (q v root : Nat) (ha : inputCheck q root = true)
    (hv : baseCheck v = true) (hl : base v < base q)
    (hp : ParBounded q v (rawTree root)) : BaseTransformation.inputCheck q v root = true :=
  (BaseTransformation.inputCheck_exact q v root).mpr ⟨root_original q root ha, hv, hl, hp⟩

theorem output_pi_caller (q v root out : Nat) (ho : out ∈ execute q root)
    (hv : baseCheck v = true) (hl : base v < base q)
    (hp : ParBounded q v (rawTree root)) : BaseTransformation.inputCheck q v out = true :=
  (BaseTransformation.inputCheck_exact q v out).mpr
    ⟨((Comparison.acceptedCode_exact q out).mp (execute_spec q root out ho).2.2.1).1,
      hv, hl, output_parBounded q v root out ho hv hp⟩

/-- HIGH source2.48(e): FULL original lambda Par and actual executing pi
are derived solely from the original high root and its chosen cutoff. -/
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

theorem pi_output_value (q v root out : Nat) (ho : out ∈ execute q root)
    (hv : baseCheck v = true) (hl : base v < base q)
    (hp : ParBounded q v (rawTree root)) :
    lowCheckCode v (BaseTransformation.piCode q v out) = true ∧
      Comparison.acceptedCode v (BaseTransformation.piCode q v out) = true ∧
      interpretation v (BaseTransformation.piCode q v out) =
        sourceValue v (BaseTransformation.piCode q v root) :=
  (execute_spec v _ _ (source_lemma_2_48_e q v root out ho hv hl hp).2).2

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.LambdaSource.BaseChange
