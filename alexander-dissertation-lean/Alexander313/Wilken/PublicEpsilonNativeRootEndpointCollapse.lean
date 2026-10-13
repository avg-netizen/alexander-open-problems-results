import Alexander313.Wilken.PublicEpsilonNativeRootEndpointCollapseSupport

/-!
# Original-head relative collapse retains full Par and executing pi

The original root and raw LOW tail Par cutoffs derive the actual second
root and tail checkers. Real normalized addition agrees literally there,
so the complete theta-zero output is genuinely admitted at both bases.
Its target checker supplies FULL hidden payload and original Par bounds,
before the actual pi map is invoked. Zero tails are included. No return
endpoint, relative-collapse, output-cutoff or target-caller oracle is used.
This scalar head branch does not assert the unbounded high return fold.
Source-only, uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RootEndpointCollapse

open ThetaCourse
open BaseTransformation (ParBounded)

theorem firstCode_context (q v b : Nat) (hq : rootCheck q b = true)
    (hv : rootCheck v b = true) : firstCode q b = firstCode v b := by
  have huq := OmegaPowerHeight.numeralCode_spec q 1 (RootLowCollapse.source_checked q b hq)
  have huv := OmegaPowerHeight.numeralCode_spec v 1 (RootLowCollapse.source_checked v b hv)
  exact OmegaPowers.BaseChange.addCode_context q v _ _
    ((Comparison.acceptedCode_exact q _).mp (argument_accepted q b hq)).1
    ((Comparison.acceptedCode_exact q _).mp huq.2.1).1
    ((Comparison.acceptedCode_exact v _).mp (argument_accepted v b hv)).1
    ((Comparison.acceptedCode_exact v _).mp huv.2.1).1

theorem successorArgumentCode_context (q v b c : Nat) (hq : inputCheck q b c = true)
    (hv : inputCheck v b c = true) :
    successorArgumentCode q b c = successorArgumentCode v b c := by
  have hs := (RootLowCollapse.inputCheck_exact q b c).mp hq
  have ht := (RootLowCollapse.inputCheck_exact v b c).mp hv
  have hf := firstCode_context q v b hs.1 ht.1
  have hfirstv : checkCode v (firstCode q b) = true := by
    rw [hf]
    exact ((Comparison.acceptedCode_exact v _).mp (firstCode_spec v b ht.1).1).1
  have he := OmegaPowers.BaseChange.addCode_context q v (firstCode q b) c
    ((Comparison.acceptedCode_exact q _).mp (firstCode_spec q b hs.1).1).1
    (Bool.and_eq_true.mp hs.2).1 hfirstv (Bool.and_eq_true.mp ht.2).1
  exact he.trans (congrArg (fun d => Arithmetic.addCode v d c) hf)

theorem collapseCode_context (q v b c : Nat) (hq : inputCheck q b c = true)
    (hv : inputCheck v b c = true) : collapseCode q b c = collapseCode v b c := by
  simp only [collapseCode, hq, hv, Bool.cond_true]
  exact congrArg OmegaPowers.thetaCode (successorArgumentCode_context q v b c hq hv)

theorem collapseCode_change (q v b c : Nat) (hi : inputCheck q b c = true)
    (hv : baseCheck v = true) (hpb : ParBounded q v (rawTree b))
    (hpc : ParBounded q v (rawTree c)) : collapseCode q b c = collapseCode v b c :=
  collapseCode_context q v b c hi (RootLowCollapse.target_input q v b c hi hv hpb hpc)

/-- The actual second output checker supplies EVERY hidden payload bound. -/
theorem collapseCode_payloads (q v b c : Nat) (hi : inputCheck q b c = true)
    (hv : baseCheck v = true) (hpb : ParBounded q v (rawTree b))
    (hpc : ParBounded q v (rawTree c)) : Payloads v (rawTree (collapseCode q b c)) := by
  have hs := collapseCode_spec v b c (RootLowCollapse.target_input q v b c hi hv hpb hpc)
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

theorem output_pi_caller (q v b c : Nat) (hi : inputCheck q b c = true)
    (hv : baseCheck v = true) (hl : base v < base q)
    (hpb : ParBounded q v (rawTree b)) (hpc : ParBounded q v (rawTree c)) :
    BaseTransformation.inputCheck q v (collapseCode q b c) = true :=
  (BaseTransformation.inputCheck_exact q v _).mpr
    ⟨(Bool.and_eq_true.mp (collapseCode_spec q b c hi).1).1, hv, hl,
      collapseCode_parBounded q v b c hi hv hpb hpc⟩

/-- The genuine finite pi map retains the constructed relative head call. -/
theorem piCode_collapseCode (q v b c : Nat) (hi : inputCheck q b c = true)
    (hv : baseCheck v = true) (hl : base v < base q)
    (hpb : ParBounded q v (rawTree b)) (hpc : ParBounded q v (rawTree c)) :
    BaseTransformation.piCode q v (collapseCode q b c) =
      collapseCode v (BaseTransformation.piCode q v b) (BaseTransformation.piCode q v c) := by
  rw [BaseTransformation.piCode_eq q v _ (output_pi_caller q v b c hi hv hl hpb hpc),
    BaseTransformation.piCode_eq q v b (RootLowCollapse.root_pi_caller q v b c hi hv hl hpb),
    BaseTransformation.piCode_eq q v c (RootLowCollapse.argument_pi_caller q v b c hi hv hl hpc)]
  exact collapseCode_change q v b c hi hv hpb hpc

theorem piCode_collapse_value (q v b c : Nat) (hi : inputCheck q b c = true)
    (hv : baseCheck v = true) (hl : base v < base q)
    (hpb : ParBounded q v (rawTree b)) (hpc : ParBounded q v (rawTree c)) :
    interpretation v (BaseTransformation.piCode q v (collapseCode q b c)) =
      globalCollapse (interpretation v (BaseTransformation.piCode q v b)) 0
        (interpretation v (deltaCode (BaseTransformation.piCode q v b)) +
          interpretation v (BaseTransformation.piCode q v c)) := by
  rw [BaseTransformation.piCode_eq q v _ (output_pi_caller q v b c hi hv hl hpb hpc),
    BaseTransformation.piCode_eq q v b (RootLowCollapse.root_pi_caller q v b c hi hv hl hpb),
    BaseTransformation.piCode_eq q v c (RootLowCollapse.argument_pi_caller q v b c hi hv hl hpc),
    collapseCode_change q v b c hi hv hpb hpc]
  exact (collapseCode_spec v b c (RootLowCollapse.target_input q v b c hi hv hpb hpc)).2.2

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RootEndpointCollapse
