import Alexander313.Wilken.PublicEpsilonNativeRootBelowHeadCollapseSupport
import Alexander313.Wilken.PublicEpsilonNativeRootAboveHeadCollapse

/-!
# Actual below-head relative collapse retains full Par and executing pi

Original chosen root and argument Par derive both true target callers and
every computed branch test. Real normalized addition agrees literally at
those callers, so the complete constructed theta-zero output is admitted
at the target. Its genuine checker supplies FULL hidden payload support
and original Par before actual pi is invoked. No target guard, endpoint,
value-only payload bound or relative-collapse oracle. This covers positive
heads strictly below the original divided head whose collapse is at most
the original root; larger localized heads remain separate. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RootBelowHeadCollapse

open ThetaCourse
open BaseTransformation (ParBounded)

theorem headBelow_context (q v b c : Nat) (hbq : RootLowCollapse.rootCheck q b = true)
    (hbv : RootLowCollapse.rootCheck v b = true) (hcq : argumentCheck q c = true)
    (hcv : argumentCheck v c = true) : headBelow q b c = headBelow v b c :=
  OmegaPowers.BaseChange.lessRawCode_context q v (headCode c) (RootEndpointCollapse.deltaCode b)
    ((Comparison.acceptedCode_exact q _).mp (parts_accepted q c hcq).1).1
    ((Comparison.acceptedCode_exact q _).mp (delta_accepted q b hbq)).1
    ((Comparison.acceptedCode_exact v _).mp (parts_accepted v c hcv).1).1
    ((Comparison.acceptedCode_exact v _).mp (delta_accepted v b hbv)).1

theorem branchCheck_context (q v b c : Nat) (hbq : RootLowCollapse.rootCheck q b = true)
    (hbv : RootLowCollapse.rootCheck v b = true) (hcq : argumentCheck q c = true)
    (hcv : argumentCheck v c = true) : branchCheck q b c = branchCheck v b c := by
  simp only [branchCheck, headBelow_context q v b c hbq hbv hcq hcv,
    RootAboveHeadCollapse.headAbove_context q v b c hbq hbv hcq hcv]

/-- Original root and argument Par derive every actual target comparison,
including the strict divided-head cutoff and non-strict head-collapse cut. -/
theorem target_input (q v b c : Nat) (hi : inputCheck q b c = true)
    (hv : baseCheck v = true) (hpb : ParBounded q v (rawTree b))
    (hpc : ParBounded q v (rawTree c)) : inputCheck v b c = true := by
  have hs := inputCheck_guards q b c hi
  have hroot := RootLowCollapse.target_root q v b hs.1 hv hpb
  have harg := RootAboveHeadCollapse.target_argument q v c hs.2.1 hv hpc
  exact Bool.and_eq_true.mpr ⟨hroot, Bool.and_eq_true.mpr ⟨harg, by
    rw [← branchCheck_context q v b c hs.1 hroot hs.2.1 harg]
    exact hs.2.2⟩⟩

theorem insertedTailCode_context (q v b c : Nat) (hq : inputCheck q b c = true)
    (hv : inputCheck v b c = true) : insertedTailCode q b c = insertedTailCode v b c := by
  have hs := inputCheck_guards q b c hq
  have ht := inputCheck_guards v b c hv
  exact OmegaPowers.BaseChange.addCode_context q v b (tailCode c)
    (RootLowCollapse.root_original q b hs.1)
    ((Comparison.acceptedCode_exact q _).mp (parts_accepted q c hs.2.1).2).1
    (RootLowCollapse.root_original v b ht.1)
    ((Comparison.acceptedCode_exact v _).mp (parts_accepted v c ht.2.1).2).1

theorem shiftedArgumentCode_context (q v b c : Nat) (hq : inputCheck q b c = true)
    (hv : inputCheck v b c = true) : shiftedArgumentCode q b c = shiftedArgumentCode v b c := by
  have hs := inputCheck_guards q b c hq
  have ht := inputCheck_guards v b c hv
  have he := insertedTailCode_context q v b c hq hv
  have htv : checkCode v (insertedTailCode q b c) = true := by
    rw [he]
    exact ((Comparison.acceptedCode_exact v _).mp (insertedTailCode_spec v b c hv).1).1
  have ha := OmegaPowers.BaseChange.addCode_context q v (headCode c) (insertedTailCode q b c)
    ((Comparison.acceptedCode_exact q _).mp (parts_accepted q c hs.2.1).1).1
    ((Comparison.acceptedCode_exact q _).mp (insertedTailCode_spec q b c hq).1).1
    ((Comparison.acceptedCode_exact v _).mp (parts_accepted v c ht.2.1).1).1 htv
  exact ha.trans (congrArg (fun d => Arithmetic.addCode v (headCode c) d) he)

theorem collapseCode_context (q v b c : Nat) (hq : inputCheck q b c = true)
    (hv : inputCheck v b c = true) : collapseCode q b c = collapseCode v b c := by
  simp only [collapseCode, hq, hv, Bool.cond_true]
  exact congrArg OmegaPowers.thetaCode (shiftedArgumentCode_context q v b c hq hv)

theorem collapseCode_change (q v b c : Nat) (hi : inputCheck q b c = true)
    (hv : baseCheck v = true) (hpb : ParBounded q v (rawTree b))
    (hpc : ParBounded q v (rawTree c)) : collapseCode q b c = collapseCode v b c :=
  collapseCode_context q v b c hi (target_input q v b c hi hv hpb hpc)

/-- The genuine target output checker supplies every hidden payload bound. -/
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
      ((RootAboveHeadCollapse.argumentCheck_exact q c).mp (inputCheck_guards q b c hi).2.1).1).1,
      hv, hl, hpc⟩

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

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RootBelowHeadCollapse
