import Alexander313.Wilken.PublicEpsilonNativeRootSupportThreshold
import Alexander313.Wilken.PublicEpsilonNativeRootAboveHeadCollapse

/-!
# Literal support threshold transport with complete parameter bounds

The original root and requested argument Par bounds derive the actual
second-context checker. The real exposed support filter and native VALUE
maximum agree literally. The selected support and its genuine successor
argument inherit FULL payload bounds from their derived target admission.
No selected dictionary endpoint or localization cutoff is an input.
Source-only, uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RootSupportThreshold.BaseChange

open ThetaCourse
open BaseTransformation (ParBounded)

theorem eligible_context (q v c d : Nat)
    (hcq : Comparison.acceptedCode q c = true)
    (hcv : Comparison.acceptedCode v c = true)
    (hdq : ∃ a : RelativeTerm Nat, d = (.theta 0 a).code ∧
      check q (.theta 0 a) = true ∧ Comparison.Normal q a)
    (hdv : ∃ a : RelativeTerm Nat, d = (.theta 0 a).code ∧
      check v (.theta 0 a) = true ∧ Comparison.Normal v a) :
    eligible q c d = eligible v c d := by
  have hq := argumentHeadCode_spec q c hcq
  have hv := argumentHeadCode_spec v c hcv
  have hnq := argumentHeadCode_spec q _ (node_accepted q d hdq).2
  have hnv := argumentHeadCode_spec v _ (node_accepted v d hdv).2
  have he := OmegaPowers.BaseChange.lessRawCode_context q v (nodeHeadCode d)
    (argumentHeadCode c)
    ((Comparison.acceptedCode_exact q _).mp hnq.1).1
    ((Comparison.acceptedCode_exact q _).mp hq.1).1
    ((Comparison.acceptedCode_exact v _).mp hnv.1).1
    ((Comparison.acceptedCode_exact v _).mp hv.1).1
  exact congrArg (fun b : Bool => !b) he

private theorem select_context (q v c : Nat) (ds : List Nat)
    (he : ∀ d ∈ ds, eligible q c d = eligible v c d) :
    select q c ds = select v c ds := by
  revert he
  induction ds with
  | nil => intro he; rfl
  | cons d ds ih =>
    intro he
    simp only [select, he d List.mem_cons_self,
      ih (fun e he' => he e (List.mem_cons_of_mem _ he'))]

theorem candidates_context (q v b c : Nat)
    (hbq : RootLowCollapse.rootCheck q b = true)
    (hbv : RootLowCollapse.rootCheck v b = true)
    (hcq : RootAboveHeadCollapse.argumentCheck q c = true)
    (hcv : RootAboveHeadCollapse.argumentCheck v c = true) :
    candidates q b c = candidates v b c := by
  apply select_context
  intro d hd
  exact eligible_context q v c d
    ((RootAboveHeadCollapse.argumentCheck_exact q c).mp hcq).1
    ((RootAboveHeadCollapse.argumentCheck_exact v c).mp hcv).1
    (fullCodes_node q b d hbq hd) (fullCodes_node v b d hbv hd)

/-- The actual maximum fold compares only genuinely admitted codes. -/
theorem best_context (q v : Nat) (ds : List Nat)
    (hq : ∀ d ∈ ds, checkCode q d = true)
    (hv : ∀ d ∈ ds, checkCode v d = true) : best q ds = best v ds := by
  revert hq hv
  induction ds with
  | nil => intro hq hv; rfl
  | cons d ds ih =>
    intro hq hv
    have hqt := fun e he => hq e (List.mem_cons_of_mem _ he)
    have hvt := fun e he => hv e (List.mem_cons_of_mem _ he)
    have ht := ih hqt hvt
    cases ho : best q ds with
    | none =>
      have hvo : best v ds = none := ht.symm.trans ho
      simp only [best, ho, hvo, choose]
    | some e =>
      have hvo : best v ds = some e := ht.symm.trans ho
      have hm := best_mem q ds e ho
      have he := OmegaPowers.BaseChange.lessRawCode_context q v e d
        (hqt e hm) (hq d List.mem_cons_self)
        (hvt e hm) (hv d List.mem_cons_self)
      simp only [best, ho, hvo, choose, he]

theorem selected_context (q v b c : Nat)
    (hbq : RootLowCollapse.rootCheck q b = true)
    (hbv : RootLowCollapse.rootCheck v b = true)
    (hcq : RootAboveHeadCollapse.argumentCheck q c = true)
    (hcv : RootAboveHeadCollapse.argumentCheck v c = true) :
    selected q b c = selected v b c := by
  have hd := candidates_context q v b c hbq hbv hcq hcv
  have hq : ∀ d ∈ candidates q b c, checkCode q d = true := by
    intro d hm
    have hf := ((select_mem q c d (fullCodes b)).mp hm).1
    exact ((Comparison.acceptedCode_exact q d).mp
      (node_accepted q d (fullCodes_node q b d hbq hf)).1).1
  have hv : ∀ d ∈ candidates q b c, checkCode v d = true := by
    intro d hm
    have hf := ((select_mem q c d (fullCodes b)).mp hm).1
    exact ((Comparison.acceptedCode_exact v d).mp
      (node_accepted v d (fullCodes_node v b d hbv hf)).1).1
  change best q (candidates q b c) = best v (candidates v b c)
  rw [← hd]
  exact best_context q v _ hq hv

theorem inputCheck_context (q v b c : Nat)
    (hbq : RootLowCollapse.rootCheck q b = true)
    (hbv : RootLowCollapse.rootCheck v b = true)
    (hcq : RootAboveHeadCollapse.argumentCheck q c = true)
    (hcv : RootAboveHeadCollapse.argumentCheck v c = true) :
    inputCheck q b c = inputCheck v b c := by
  have htq := RootEndpointCollapse.thetaCode_sorted_spec q c
    ((RootAboveHeadCollapse.argumentCheck_exact q c).mp hcq).1
    (RootAboveHeadCollapse.argument_sorted q c hcq)
  have htv := RootEndpointCollapse.thetaCode_sorted_spec v c
    ((RootAboveHeadCollapse.argumentCheck_exact v c).mp hcv).1
    (RootAboveHeadCollapse.argument_sorted v c hcv)
  have he := OmegaPowers.BaseChange.lessRawCode_context q v b (OmegaPowers.thetaCode c)
    (RootLowCollapse.root_original q b hbq)
    ((Comparison.acceptedCode_exact q _).mp htq.2.1).1
    (RootLowCollapse.root_original v b hbv)
    ((Comparison.acceptedCode_exact v _).mp htv.2.1).1
  simp only [inputCheck, hbq, hbv, hcq, hcv, Bool.true_and, he]

/-- Original Par supplies both actual target callers, including the
requested-collapse comparison. No target endpoint predicate is assumed. -/
theorem target_input (q v b c : Nat) (hi : inputCheck q b c = true)
    (hv : baseCheck v = true) (hpb : ParBounded q v (rawTree b))
    (hpc : ParBounded q v (rawTree c)) : inputCheck v b c = true := by
  have h := (inputCheck_exact q b c).mp hi
  have hb := RootLowCollapse.target_root q v b h.1 hv hpb
  have hc := RootAboveHeadCollapse.target_argument q v c h.2.1 hv hpc
  rw [← inputCheck_context q v b c h.1 hb h.2.1 hc]
  exact hi

theorem selected_change (q v b c : Nat) (hi : inputCheck q b c = true)
    (hv : baseCheck v = true) (hpb : ParBounded q v (rawTree b))
    (hpc : ParBounded q v (rawTree c)) : selected q b c = selected v b c := by
  have hq := (inputCheck_exact q b c).mp hi
  have ht := (inputCheck_exact v b c).mp (target_input q v b c hi hv hpb hpc)
  exact selected_context q v b c hq.1 ht.1 hq.2.1 ht.2.1

theorem successorCode_context (q v d : Nat)
    (hdq : ∃ a : RelativeTerm Nat, d = (.theta 0 a).code ∧
      check q (.theta 0 a) = true ∧ Comparison.Normal q a)
    (hdv : ∃ a : RelativeTerm Nat, d = (.theta 0 a).code ∧
      check v (.theta 0 a) = true ∧ Comparison.Normal v a) :
    successorCode q d = successorCode v d := by
  have hqq : baseCheck q = true := by
    obtain ⟨a, he, ha, hn⟩ := hdq
    exact (Bool.and_eq_true.mp ha).1
  have hvv : baseCheck v = true := by
    obtain ⟨a, he, ha, hn⟩ := hdv
    exact (Bool.and_eq_true.mp ha).1
  have hq := node_accepted q d hdq
  have ht := node_accepted v d hdv
  have huq := OmegaPowerHeight.numeralCode_spec q 1 hqq
  have huv := OmegaPowerHeight.numeralCode_spec v 1 hvv
  exact congrArg OmegaPowers.thetaCode (OmegaPowers.BaseChange.addCode_context q v
    (Localization.argumentCode d) (OmegaPowerHeight.numeralCode 1)
    ((Comparison.acceptedCode_exact q _).mp hq.2).1
    ((Comparison.acceptedCode_exact q _).mp huq.2.1).1
    ((Comparison.acceptedCode_exact v _).mp ht.2).1
    ((Comparison.acceptedCode_exact v _).mp huv.2.1).1)

theorem selected_parBounded (q v b c d : Nat) (hi : inputCheck q b c = true)
    (hs : selected q b c = some d) (hv : baseCheck v = true)
    (hpb : ParBounded q v (rawTree b)) (hpc : ParBounded q v (rawTree c)) :
    ParBounded q v (rawTree d) := by
  have ht := target_input q v b c hi hv hpb hpc
  have hst : selected v b c = some d :=
    (selected_change q v b c hi hv hpb hpc).symm.trans hs
  have hq := selected_interval q b c d hi hs
  have hn := selected_interval v b c d ht hst
  have hcq := ((Comparison.acceptedCode_exact q d).mp hq.2.2.1).1
  have hcv := ((Comparison.acceptedCode_exact v d).mp hn.2.2.1).1
  exact (BaseTransformation.parBounded_iff_payloads q v _
    (Arithmetic.raw_checked q d hcq) hv).mpr
      (checked_admissible v _ (Arithmetic.raw_checked v d hcv)).1

theorem successorCode_change (q v b c d : Nat) (hi : inputCheck q b c = true)
    (hs : selected q b c = some d) (hv : baseCheck v = true)
    (hpb : ParBounded q v (rawTree b)) (hpc : ParBounded q v (rawTree c)) :
    successorCode q d = successorCode v d := by
  have ht := target_input q v b c hi hv hpb hpc
  have hst : selected v b c = some d :=
    (selected_change q v b c hi hv hpb hpc).symm.trans hs
  exact successorCode_context q v d (selected_spec q b c d hi hs).2.1
    (selected_spec v b c d ht hst).2.1

theorem successorCode_parBounded (q v b c d : Nat) (hi : inputCheck q b c = true)
    (hs : selected q b c = some d) (hv : baseCheck v = true)
    (hpb : ParBounded q v (rawTree b)) (hpc : ParBounded q v (rawTree c)) :
    ParBounded q v (rawTree (successorCode q d)) := by
  have ht := target_input q v b c hi hv hpb hpc
  have hst : selected v b c = some d :=
    (selected_change q v b c hi hv hpb hpc).symm.trans hs
  have hq := successorCode_spec q d (selected_spec q b c d hi hs).2.1
  have hn := successorCode_spec v d (selected_spec v b c d ht hst).2.1
  have hcq := (HeightBoundary.input_spec q _ hq.1).1
  have hcv : checkCode v (successorCode q d) = true := by
    rw [successorCode_change q v b c d hi hs hv hpb hpc]
    exact (HeightBoundary.input_spec v _ hn.1).1
  exact (BaseTransformation.parBounded_iff_payloads q v _
    (Arithmetic.raw_checked q _ hcq) hv).mpr
      (checked_admissible v _ (Arithmetic.raw_checked v _ hcv)).1

theorem selected_pi_caller (q v b c d : Nat) (hi : inputCheck q b c = true)
    (hs : selected q b c = some d) (hv : baseCheck v = true) (hl : base v < base q)
    (hpb : ParBounded q v (rawTree b)) (hpc : ParBounded q v (rawTree c)) :
    BaseTransformation.inputCheck q v d = true :=
  (BaseTransformation.inputCheck_exact q v d).mpr
    ⟨((Comparison.acceptedCode_exact q d).mp (selected_interval q b c d hi hs).2.2.1).1,
      hv, hl, selected_parBounded q v b c d hi hs hv hpb hpc⟩

theorem successor_pi_caller (q v b c d : Nat) (hi : inputCheck q b c = true)
    (hs : selected q b c = some d) (hv : baseCheck v = true) (hl : base v < base q)
    (hpb : ParBounded q v (rawTree b)) (hpc : ParBounded q v (rawTree c)) :
    BaseTransformation.inputCheck q v (successorCode q d) = true :=
  (BaseTransformation.inputCheck_exact q v _).mpr
    ⟨(HeightBoundary.input_spec q _ (successorCode_spec q d
        (selected_spec q b c d hi hs).2.1).1).1,
      hv, hl, successorCode_parBounded q v b c d hi hs hv hpb hpc⟩

theorem piCode_successor (q v b c d : Nat) (hi : inputCheck q b c = true)
    (hs : selected q b c = some d) (hv : baseCheck v = true) (hl : base v < base q)
    (hpb : ParBounded q v (rawTree b)) (hpc : ParBounded q v (rawTree c)) :
    BaseTransformation.piCode q v (successorCode q d) =
      successorCode v (BaseTransformation.piCode q v d) := by
  rw [BaseTransformation.piCode_eq q v _ (successor_pi_caller q v b c d hi hs hv hl hpb hpc),
    BaseTransformation.piCode_eq q v d (selected_pi_caller q v b c d hi hs hv hl hpb hpc)]
  exact successorCode_change q v b c d hi hs hv hpb hpc

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RootSupportThreshold.BaseChange
