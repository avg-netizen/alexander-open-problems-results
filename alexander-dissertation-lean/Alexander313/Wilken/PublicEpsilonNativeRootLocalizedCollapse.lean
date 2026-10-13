import Alexander313.Wilken.PublicEpsilonNativeRootLocalizedCollapseSupport
import Alexander313.Wilken.PublicEpsilonNativeRootScalarCollapse
import Alexander313.Wilken.PublicEpsilonNativeRootSupportThresholdBaseChange

/-!
# The actual localized finite producer retains FULL Par and pi

Original root and argument chosen-presentation Par derive the genuine
second-context localized branch. Head-only finite support selection and
its actual maximum agree literally, as do the selected finite shift and
the genuine normalized arithmetic. Target output admission derives FULL
hidden payload bounds before pi is invoked. No selected endpoint, target
caller, localization cutoff or output-cutoff oracle. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RootLocalizedCollapse

open ThetaCourse
open BaseTransformation (ParBounded)

theorem inputCheck_context (q v b c : Nat)
    (hbq : RootLowCollapse.rootCheck q b = true) (hbv : RootLowCollapse.rootCheck v b = true)
    (hcq : RootAboveHeadCollapse.argumentCheck q c = true)
    (hcv : RootAboveHeadCollapse.argumentCheck v c = true) :
    inputCheck q b c = inputCheck v b c := by
  simp only [inputCheck, hbq, hbv, hcq, hcv, Bool.true_and,
    RootScalarCollapse.headLarger_context q v b c hbq hbv hcq hcv,
    RootAboveHeadCollapse.headAbove_context q v b c hbq hbv hcq hcv]

theorem target_input (q v b c : Nat) (hi : inputCheck q b c = true)
    (hv : baseCheck v = true) (hpb : ParBounded q v (rawTree b))
    (hpc : ParBounded q v (rawTree c)) : inputCheck v b c = true := by
  have h := inputCheck_guards q b c hi
  have hb := RootLowCollapse.target_root q v b h.1 hv hpb
  have hc := RootAboveHeadCollapse.target_argument q v c h.2.1 hv hpc
  rw [← inputCheck_context q v b c h.1 hb h.2.1 hc]
  exact hi

theorem selectedCode_context (q v b c : Nat) (hq : inputCheck q b c = true)
    (hv : inputCheck v b c = true) : selectedCode q b c = selectedCode v b c := by
  have h := inputCheck_guards q b c hq
  have ht := inputCheck_guards v b c hv
  exact congrArg (fun o : Option Nat => o.getD 0)
    (RootSupportThreshold.BaseChange.selected_context q v b (headCode c) h.1 ht.1
      (head_argument q c h.2.1) (head_argument v c ht.2.1))

theorem selectedArgumentCode_context (q v b c : Nat) (hq : inputCheck q b c = true)
    (hv : inputCheck v b c = true) :
    selectedArgumentCode q b c = selectedArgumentCode v b c :=
  congrArg Localization.argumentCode (selectedCode_context q v b c hq hv)

theorem selectedTailCode_context (q v b c : Nat) (hq : inputCheck q b c = true)
    (hv : inputCheck v b c = true) : selectedTailCode q b c = selectedTailCode v b c :=
  congrArg (Decomposition.lowCode 0) (selectedArgumentCode_context q v b c hq hv)

theorem firstTailCode_context (q v b c : Nat) (hq : inputCheck q b c = true)
    (hv : inputCheck v b c = true) : firstTailCode q b c = firstTailCode v b c := by
  have he := selectedTailCode_context q v b c hq hv
  have hqa := selectedArgumentCode_accepted q b c hq
  have hva := selectedArgumentCode_accepted v b c hv
  have hqt := ((Comparison.acceptedCode_exact q _).mp
    (Decomposition.parts_accepted q 0 _ hqa).2).1
  have hvt : checkCode v (selectedTailCode q b c) = true := by
    rw [he]
    exact ((Comparison.acceptedCode_exact v _).mp (Decomposition.parts_accepted v 0 _ hva).2).1
  have huq := OmegaPowerHeight.numeralCode_spec q 1
    (RootLowCollapse.source_checked q b (inputCheck_guards q b c hq).1)
  have huv := OmegaPowerHeight.numeralCode_spec v 1
    (RootLowCollapse.source_checked v b (inputCheck_guards v b c hv).1)
  have hs := OmegaPowers.BaseChange.addCode_context q v (selectedTailCode q b c)
    (OmegaPowerHeight.numeralCode 1) hqt
    ((Comparison.acceptedCode_exact q _).mp huq.2.1).1 hvt
    ((Comparison.acceptedCode_exact v _).mp huv.2.1).1
  simpa only [firstTailCode, he] using hs

theorem headStrict_context (q v b c : Nat) (hq : inputCheck q b c = true)
    (hv : inputCheck v b c = true) : headStrict q b c = headStrict v b c := by
  have he := selectedCode_context q v b c hq hv
  have hqc := (RootBelowHeadCollapse.parts_accepted q c (inputCheck_guards q b c hq).2.1).1
  have hvc := (RootBelowHeadCollapse.parts_accepted v c (inputCheck_guards v b c hv).2.1).1
  have hqn := RootSupportThreshold.argumentHeadCode_spec q _ (selectedArgumentCode_accepted q b c hq)
  have hvn := RootSupportThreshold.argumentHeadCode_spec v _ (selectedArgumentCode_accepted v b c hv)
  have hvh : checkCode v (RootSupportThreshold.nodeHeadCode (selectedCode q b c)) = true := by
    rw [he]
    exact ((Comparison.acceptedCode_exact v _).mp hvn.1).1
  have hs := OmegaPowers.BaseChange.lessRawCode_context q v (headCode c)
    (RootSupportThreshold.nodeHeadCode (selectedCode q b c))
    ((Comparison.acceptedCode_exact q _).mp hqc).1
    ((Comparison.acceptedCode_exact q _).mp hqn.1).1
    ((Comparison.acceptedCode_exact v _).mp hvc).1 hvh
  simpa only [headStrict, he] using hs

theorem kappaCode_context (q v b c : Nat) (hq : inputCheck q b c = true)
    (hv : inputCheck v b c = true) : kappaCode q b c = kappaCode v b c := by
  simp only [kappaCode, headStrict_context q v b c hq hv,
    selectedCode_context q v b c hq hv, firstTailCode_context q v b c hq hv]

theorem insertedTailCode_context (q v b c : Nat) (hq : inputCheck q b c = true)
    (hv : inputCheck v b c = true) : insertedTailCode q b c = insertedTailCode v b c := by
  have he := kappaCode_context q v b c hq hv
  have hqk := ((Comparison.acceptedCode_exact q _).mp (kappaCode_spec q b c hq).1).1
  have hvk : checkCode v (kappaCode q b c) = true := by
    rw [he]
    exact ((Comparison.acceptedCode_exact v _).mp (kappaCode_spec v b c hv).1).1
  have hs := OmegaPowers.BaseChange.addCode_context q v (kappaCode q b c) (tailCode c)
    hqk ((Comparison.acceptedCode_exact q _).mp
      (RootBelowHeadCollapse.parts_accepted q c (inputCheck_guards q b c hq).2.1).2).1
    hvk ((Comparison.acceptedCode_exact v _).mp
      (RootBelowHeadCollapse.parts_accepted v c (inputCheck_guards v b c hv).2.1).2).1
  simpa only [insertedTailCode, he] using hs

theorem shiftedArgumentCode_context (q v b c : Nat) (hq : inputCheck q b c = true)
    (hv : inputCheck v b c = true) : shiftedArgumentCode q b c = shiftedArgumentCode v b c := by
  have he := insertedTailCode_context q v b c hq hv
  have hqi := ((Comparison.acceptedCode_exact q _).mp (insertedTailCode_spec q b c hq).1).1
  have hvi : checkCode v (insertedTailCode q b c) = true := by
    rw [he]
    exact ((Comparison.acceptedCode_exact v _).mp (insertedTailCode_spec v b c hv).1).1
  have hs := OmegaPowers.BaseChange.addCode_context q v (headCode c) (insertedTailCode q b c)
    ((Comparison.acceptedCode_exact q _).mp
      (RootBelowHeadCollapse.parts_accepted q c (inputCheck_guards q b c hq).2.1).1).1 hqi
    ((Comparison.acceptedCode_exact v _).mp
      (RootBelowHeadCollapse.parts_accepted v c (inputCheck_guards v b c hv).2.1).1).1 hvi
  simpa only [shiftedArgumentCode, he] using hs

theorem collapseCode_context (q v b c : Nat) (hq : inputCheck q b c = true)
    (hv : inputCheck v b c = true) : collapseCode q b c = collapseCode v b c := by
  simp only [collapseCode, hq, hv, Bool.cond_true,
    shiftedArgumentCode_context q v b c hq hv]

theorem collapseCode_change (q v b c : Nat) (hi : inputCheck q b c = true)
    (hv : baseCheck v = true) (hpb : ParBounded q v (rawTree b))
    (hpc : ParBounded q v (rawTree c)) : collapseCode q b c = collapseCode v b c :=
  collapseCode_context q v b c hi (target_input q v b c hi hv hpb hpc)

theorem collapseCode_payloads (q v b c : Nat) (hi : inputCheck q b c = true)
    (hv : baseCheck v = true) (hpb : ParBounded q v (rawTree b))
    (hpc : ParBounded q v (rawTree c)) : Payloads v (rawTree (collapseCode q b c)) := by
  have hs := collapseCode_checked v b c (target_input q v b c hi hv hpb hpc)
  have ht : checkCode v (collapseCode q b c) = true := by
    rw [collapseCode_change q v b c hi hv hpb hpc]
    exact ((Comparison.acceptedCode_exact v _).mp hs.2.1).1
  exact (checked_admissible v _ (Arithmetic.raw_checked v _ ht)).1

theorem collapseCode_parBounded (q v b c : Nat) (hi : inputCheck q b c = true)
    (hv : baseCheck v = true) (hpb : ParBounded q v (rawTree b))
    (hpc : ParBounded q v (rawTree c)) : ParBounded q v (rawTree (collapseCode q b c)) :=
  (BaseTransformation.parBounded_iff_payloads q v _
    (Arithmetic.raw_checked q _ ((Comparison.acceptedCode_exact q _).mp
      (collapseCode_checked q b c hi).2.1).1) hv).mpr
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
    ⟨((Comparison.acceptedCode_exact q _).mp
      ((RootAboveHeadCollapse.argumentCheck_exact q c).mp (inputCheck_guards q b c hi).2.1).1).1,
      hv, hl, hpc⟩

theorem output_pi_caller (q v b c : Nat) (hi : inputCheck q b c = true)
    (hv : baseCheck v = true) (hl : base v < base q)
    (hpb : ParBounded q v (rawTree b)) (hpc : ParBounded q v (rawTree c)) :
    BaseTransformation.inputCheck q v (collapseCode q b c) = true :=
  (BaseTransformation.inputCheck_exact q v _).mpr
    ⟨((Comparison.acceptedCode_exact q _).mp (collapseCode_checked q b c hi).2.1).1,
      hv, hl, collapseCode_parBounded q v b c hi hv hpb hpc⟩

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

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RootLocalizedCollapse
