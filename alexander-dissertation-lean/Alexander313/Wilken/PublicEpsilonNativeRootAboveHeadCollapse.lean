import Alexander313.Wilken.PublicEpsilonNativeRootAboveHeadCollapseSupport

/-!
# Actual unbounded above-head relative collapse preserves Par and pi

Original root and argument Par derive all target admission and comparison
callers. Both genuine head-collapse tests agree literally, so the actual
above-head branch executes at the second context. Its real output checker
gives FULL hidden payload support and original Par before actual pi runs.

This covers arbitrary admitted HIGH heads with computed source head
collapse above beta, not only heads below the root's head. It imposes no
return endpoint or beta code. The complementary localized cutoff and full
returned-iota/chi/mu Lemma3.9 remain separate. Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RootAboveHeadCollapse

open ThetaCourse
open BaseTransformation (ParBounded)

theorem target_argument (q v c : Nat) (hc : argumentCheck q c = true)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree c)) : argumentCheck v c = true := by
  have hs := (argumentCheck_exact q c).mp hc
  exact (argumentCheck_exact v c).mpr ⟨RootPositiveCollapse.target_argument q v c hs.1 hv hp, hs.2⟩

theorem headAbove_context (q v b c : Nat) (hbq : RootLowCollapse.rootCheck q b = true)
    (hbv : RootLowCollapse.rootCheck v b = true) (hcq : argumentCheck q c = true)
    (hcv : argumentCheck v c = true) : headAbove q b c = headAbove v b c :=
  OmegaPowers.BaseChange.lessRawCode_context q v b (headNodeCode c)
    (RootLowCollapse.root_original q b hbq)
    ((Comparison.acceptedCode_exact q _).mp (headNodeCode_spec q c hcq).2.1).1
    (RootLowCollapse.root_original v b hbv)
    ((Comparison.acceptedCode_exact v _).mp (headNodeCode_spec v c hcv).2.1).1

/-- The original chosen Par cut derives every target branch caller,
including the genuine head-collapse comparison on arbitrary HIGH heads. -/
theorem target_input (q v b c : Nat) (hi : inputCheck q b c = true)
    (hv : baseCheck v = true) (hpb : ParBounded q v (rawTree b))
    (hpc : ParBounded q v (rawTree c)) : inputCheck v b c = true := by
  have hs := inputCheck_guards q b c hi
  have hbv := RootLowCollapse.target_root q v b hs.1 hv hpb
  have hcv := target_argument q v c hs.2.1 hv hpc
  exact Bool.and_eq_true.mpr ⟨hbv, Bool.and_eq_true.mpr ⟨hcv, by
    rw [← headAbove_context q v b c hs.1 hbv hs.2.1 hcv]
    exact hs.2.2⟩⟩

theorem collapseCode_context (q v b c : Nat) (hq : inputCheck q b c = true)
    (hv : inputCheck v b c = true) : collapseCode q b c = collapseCode v b c := by
  rw [collapseCode_eq q b c hq, collapseCode_eq v b c hv]

theorem collapseCode_change (q v b c : Nat) (hi : inputCheck q b c = true)
    (hv : baseCheck v = true) (hpb : ParBounded q v (rawTree b))
    (hpc : ParBounded q v (rawTree c)) : collapseCode q b c = collapseCode v b c :=
  collapseCode_context q v b c hi (target_input q v b c hi hv hpb hpc)

/-- Genuine target admission constructs FULL syntactic output payloads,
including every hidden theta argument in the original source node. -/
theorem collapseCode_payloads (q v b c : Nat) (hi : inputCheck q b c = true)
    (hv : baseCheck v = true) (hpb : ParBounded q v (rawTree b))
    (hpc : ParBounded q v (rawTree c)) : Payloads v (rawTree (collapseCode q b c)) := by
  have hs := collapseCode_spec v b c (target_input q v b c hi hv hpb hpc)
  have ht : checkCode v (collapseCode q b c) = true := by
    rw [collapseCode_change q v b c hi hv hpb hpc]
    exact (Bool.and_eq_true.mp hs.1).1
  exact (checked_admissible v _ (Arithmetic.raw_checked v _ ht)).1

theorem collapseCode_parBounded (q v b c : Nat) (hi : inputCheck q b c = true)
    (hv : baseCheck v = true) (hpb : ParBounded q v (rawTree b))
    (hpc : ParBounded q v (rawTree c)) : ParBounded q v (rawTree (collapseCode q b c)) :=
  (BaseTransformation.parBounded_iff_payloads q v _
    (Arithmetic.raw_checked q _ (Bool.and_eq_true.mp (collapseCode_spec q b c hi).1).1) hv).mpr
      (collapseCode_payloads q v b c hi hv hpb hpc)

theorem root_pi_caller (q v b c : Nat) (hi : inputCheck q b c = true)
    (hv : baseCheck v = true) (hl : base v < base q)
    (hpb : ParBounded q v (rawTree b)) : BaseTransformation.inputCheck q v b = true :=
  (BaseTransformation.inputCheck_exact q v b).mpr
    ⟨RootLowCollapse.root_original q b (inputCheck_guards q b c hi).1, hv, hl, hpb⟩

theorem argument_pi_caller (q v b c : Nat) (hi : inputCheck q b c = true)
    (hv : baseCheck v = true) (hl : base v < base q)
    (hpc : ParBounded q v (rawTree c)) : BaseTransformation.inputCheck q v c = true :=
  (BaseTransformation.inputCheck_exact q v c).mpr
    ⟨((Comparison.acceptedCode_exact q c).mp
      ((argumentCheck_exact q c).mp (inputCheck_guards q b c hi).2.1).1).1, hv, hl, hpc⟩

theorem output_pi_caller (q v b c : Nat) (hi : inputCheck q b c = true)
    (hv : baseCheck v = true) (hl : base v < base q)
    (hpb : ParBounded q v (rawTree b)) (hpc : ParBounded q v (rawTree c)) :
    BaseTransformation.inputCheck q v (collapseCode q b c) = true :=
  (BaseTransformation.inputCheck_exact q v _).mpr
    ⟨(Bool.and_eq_true.mp (collapseCode_spec q b c hi).1).1, hv, hl,
      collapseCode_parBounded q v b c hi hv hpb hpc⟩

theorem piCode_collapseCode (q v b c : Nat) (hi : inputCheck q b c = true)
    (hv : baseCheck v = true) (hl : base v < base q)
    (hpb : ParBounded q v (rawTree b)) (hpc : ParBounded q v (rawTree c)) :
    BaseTransformation.piCode q v (collapseCode q b c) =
      collapseCode v (BaseTransformation.piCode q v b) (BaseTransformation.piCode q v c) := by
  rw [BaseTransformation.piCode_eq q v _ (output_pi_caller q v b c hi hv hl hpb hpc),
    BaseTransformation.piCode_eq q v b (root_pi_caller q v b c hi hv hl hpb),
    BaseTransformation.piCode_eq q v c (argument_pi_caller q v b c hi hv hl hpc)]
  exact collapseCode_change q v b c hi hv hpb hpc

theorem piCode_collapse_value (q v b c : Nat) (hi : inputCheck q b c = true)
    (hv : baseCheck v = true) (hl : base v < base q)
    (hpb : ParBounded q v (rawTree b)) (hpc : ParBounded q v (rawTree c)) :
    interpretation v (BaseTransformation.piCode q v (collapseCode q b c)) =
      globalCollapse (interpretation v (BaseTransformation.piCode q v b)) 0
        (interpretation v (BaseTransformation.piCode q v c)) := by
  rw [BaseTransformation.piCode_eq q v _ (output_pi_caller q v b c hi hv hl hpb hpc),
    BaseTransformation.piCode_eq q v b (root_pi_caller q v b c hi hv hl hpb),
    BaseTransformation.piCode_eq q v c (argument_pi_caller q v b c hi hv hl hpc),
    collapseCode_change q v b c hi hv hpb hpc]
  exact (collapseCode_spec v b c (target_input q v b c hi hv hpb hpc)).2.2

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RootAboveHeadCollapse
