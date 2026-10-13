import Alexander313.Wilken.PublicEpsilonNativeRootScalarCollapseSupport
import Alexander313.Wilken.PublicEpsilonNativeRootBelowHeadCollapse
import Alexander313.Wilken.PublicEpsilonNativeRootEndpointCollapse

/-!
# Actual scalar dispatcher retains FULL Par and executing pi

Original chosen root and argument Par derive every target guard. The exact
computed exceptional branch is unchanged by the true raw comparisons.
Every selected finite scalar producer agrees literally at the derived
callers, so actual target admission supplies FULL output payloads and Par
before actual pi. This is an executing scalar dispatcher with an explicit
larger-head exception, not a complete returned-iota or mu base-change proof.
No target caller, output cutoff or selected endpoint oracle. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RootScalarCollapse

open ThetaCourse
open BaseTransformation (ParBounded)

theorem headLarger_context (q v b c : Nat) (hbq : RootLowCollapse.rootCheck q b = true)
    (hbv : RootLowCollapse.rootCheck v b = true) (hcq : RootAboveHeadCollapse.argumentCheck q c = true)
    (hcv : RootAboveHeadCollapse.argumentCheck v c = true) : headLarger q b c = headLarger v b c :=
  OmegaPowers.BaseChange.lessRawCode_context q v (RootEndpointCollapse.deltaCode b)
    (RootAboveHeadCollapse.headCode c)
    ((Comparison.acceptedCode_exact q _).mp (RootBelowHeadCollapse.delta_accepted q b hbq)).1
    ((Comparison.acceptedCode_exact q _).mp (RootBelowHeadCollapse.parts_accepted q c hcq).1).1
    ((Comparison.acceptedCode_exact v _).mp (RootBelowHeadCollapse.delta_accepted v b hbv)).1
    ((Comparison.acceptedCode_exact v _).mp (RootBelowHeadCollapse.parts_accepted v c hcv).1).1

theorem coveredCheck_context (q v b c : Nat) (hbq : RootLowCollapse.rootCheck q b = true)
    (hbv : RootLowCollapse.rootCheck v b = true) (hcq : RootAboveHeadCollapse.argumentCheck q c = true)
    (hcv : RootAboveHeadCollapse.argumentCheck v c = true) : coveredCheck q b c = coveredCheck v b c := by
  simp only [coveredCheck, headLarger_context q v b c hbq hbv hcq hcv,
    RootAboveHeadCollapse.headAbove_context q v b c hbq hbv hcq hcv]

theorem target_zeroInput (q v b c : Nat) (hi : zeroInput q b c = true)
    (hv : baseCheck v = true) (hpb : ParBounded q v (rawTree b))
    (hpc : ParBounded q v (rawTree c)) : zeroInput v b c = true := by
  have hs := zeroInput_guards q b c hi
  have hb := RootLowCollapse.target_root q v b hs.1 hv hpb
  have hc := RootAboveHeadCollapse.target_argument q v c hs.2.1 hv hpc
  exact Bool.and_eq_true.mpr ⟨hb, Bool.and_eq_true.mpr ⟨hc, by
    rw [← coveredCheck_context q v b c hs.1 hb hs.2.1 hc]
    exact hs.2.2⟩⟩

theorem zeroCode_context (q v b c : Nat) (hq : zeroInput q b c = true)
    (hv : zeroInput v b c = true) : zeroCode q b c = zeroCode v b c := by
  have hs := zeroInput_guards q b c hq
  have ht := zeroInput_guards v b c hv
  have ha := RootAboveHeadCollapse.headAbove_context q v b c hs.1 ht.1 hs.2.1 ht.2.1
  have hb := RootBelowHeadCollapse.headBelow_context q v b c hs.1 ht.1 hs.2.1 ht.2.1
  by_cases hl : (rawTree c).outerSort ≤ 1
  · simp only [zeroCode, decide_eq_true hl, Bool.cond_true]
    exact RootLowCollapse.collapseCode_context q v b c (low_caller q b c hq hl)
      (low_caller v b c hv hl)
  · have hh : 1 < (rawTree c).outerSort := lt_of_not_ge hl
    cases habove : RootAboveHeadCollapse.headAbove q b c with
    | true =>
      have hvabove : RootAboveHeadCollapse.headAbove v b c = true := ha.symm.trans habove
      simp only [zeroCode, decide_eq_false hl, habove, hvabove, Bool.cond_true, Bool.cond_false]
      exact RootAboveHeadCollapse.collapseCode_context q v b c
        (above_caller q b c hq habove) (above_caller v b c hv hvabove)
    | false =>
      have hvabove : RootAboveHeadCollapse.headAbove v b c = false := ha.symm.trans habove
      cases hbelow : RootBelowHeadCollapse.headBelow q b c with
      | true =>
        have hvbelow : RootBelowHeadCollapse.headBelow v b c = true := hb.symm.trans hbelow
        simp only [zeroCode, decide_eq_false hl, habove, hvabove, hbelow, hvbelow,
          Bool.cond_true, Bool.cond_false]
        exact RootBelowHeadCollapse.collapseCode_context q v b c
          (below_caller q b c hq hh habove hbelow) (below_caller v b c hv hh hvabove hvbelow)
      | false =>
        have hvbelow : RootBelowHeadCollapse.headBelow v b c = false := hb.symm.trans hbelow
        simp only [zeroCode, decide_eq_false hl, habove, hvabove, hbelow, hvbelow, Bool.cond_false]
        exact RootEndpointCollapse.collapseCode_context q v b (RootBelowHeadCollapse.tailCode c)
          (endpoint_caller q b c hq) (endpoint_caller v b c hv)

theorem target_input (q v b k c : Nat) (hi : inputCheck q b k c = true)
    (hv : baseCheck v = true) (hpb : ParBounded q v (rawTree b))
    (hpc : ParBounded q v (rawTree c)) : inputCheck v b k c = true := by
  by_cases hk : 0 < k
  · have hq : RootPositiveCollapse.inputCheck q b k c = true := by
      simpa only [inputCheck, decide_eq_true hk, Bool.cond_true] using hi
    simpa only [inputCheck, decide_eq_true hk, Bool.cond_true] using
      RootPositiveCollapse.target_input q v b k c hq hv hpb hpc
  · have hq : zeroInput q b c = true := by
      simpa only [inputCheck, decide_eq_false hk, Bool.cond_false] using hi
    simpa only [inputCheck, decide_eq_false hk, Bool.cond_false] using
      target_zeroInput q v b c hq hv hpb hpc

theorem collapseCode_context (q v b k c : Nat) (hq : inputCheck q b k c = true)
    (hv : inputCheck v b k c = true) : collapseCode q b k c = collapseCode v b k c := by
  by_cases hk : 0 < k
  · have hpq : RootPositiveCollapse.inputCheck q b k c = true := by
      simpa only [inputCheck, decide_eq_true hk, Bool.cond_true] using hq
    have hpv : RootPositiveCollapse.inputCheck v b k c = true := by
      simpa only [inputCheck, decide_eq_true hk, Bool.cond_true] using hv
    simpa only [collapseCode, hq, hv, decide_eq_true hk, Bool.cond_true] using
      RootPositiveCollapse.collapseCode_context q v b k c hpq hpv
  · have hzq : zeroInput q b c = true := by
      simpa only [inputCheck, decide_eq_false hk, Bool.cond_false] using hq
    have hzv : zeroInput v b c = true := by
      simpa only [inputCheck, decide_eq_false hk, Bool.cond_false] using hv
    simpa only [collapseCode, hq, hv, decide_eq_false hk, Bool.cond_true, Bool.cond_false] using
      zeroCode_context q v b c hzq hzv

theorem collapseCode_change (q v b k c : Nat) (hi : inputCheck q b k c = true)
    (hv : baseCheck v = true) (hpb : ParBounded q v (rawTree b))
    (hpc : ParBounded q v (rawTree c)) : collapseCode q b k c = collapseCode v b k c :=
  collapseCode_context q v b k c hi (target_input q v b k c hi hv hpb hpc)

/-- FULL output payloads follow from the true target checker, including
every hidden argument in the genuinely selected finite scalar output. -/
theorem collapseCode_payloads (q v b k c : Nat) (hi : inputCheck q b k c = true)
    (hv : baseCheck v = true) (hpb : ParBounded q v (rawTree b))
    (hpc : ParBounded q v (rawTree c)) : Payloads v (rawTree (collapseCode q b k c)) := by
  have hs := collapseCode_spec v b k c (target_input q v b k c hi hv hpb hpc)
  have ht : checkCode v (collapseCode q b k c) = true := by
    rw [collapseCode_change q v b k c hi hv hpb hpc]
    exact ((Comparison.acceptedCode_exact v _).mp hs.1).1
  exact (checked_admissible v _ (Arithmetic.raw_checked v _ ht)).1

theorem collapseCode_parBounded (q v b k c : Nat) (hi : inputCheck q b k c = true)
    (hv : baseCheck v = true) (hpb : ParBounded q v (rawTree b))
    (hpc : ParBounded q v (rawTree c)) : ParBounded q v (rawTree (collapseCode q b k c)) :=
  (BaseTransformation.parBounded_iff_payloads q v _
    (Arithmetic.raw_checked q _ ((Comparison.acceptedCode_exact q _).mp
      (collapseCode_spec q b k c hi).1).1) hv).mpr
      (collapseCode_payloads q v b k c hi hv hpb hpc)

theorem root_pi_caller (q v b k c : Nat) (hi : inputCheck q b k c = true)
    (hv : baseCheck v = true) (hl : base v < base q)
    (hpb : ParBounded q v (rawTree b)) : BaseTransformation.inputCheck q v b = true :=
  (BaseTransformation.inputCheck_exact q v b).mpr
    ⟨RootLowCollapse.root_original q b ((inputCheck_exact q b k c).mp hi).1, hv, hl, hpb⟩

theorem argument_pi_caller (q v b k c : Nat) (hi : inputCheck q b k c = true)
    (hv : baseCheck v = true) (hl : base v < base q)
    (hpc : ParBounded q v (rawTree c)) : BaseTransformation.inputCheck q v c = true :=
  (BaseTransformation.inputCheck_exact q v c).mpr
    ⟨((Comparison.acceptedCode_exact q c).mp ((inputCheck_exact q b k c).mp hi).2.1).1,
      hv, hl, hpc⟩

theorem output_pi_caller (q v b k c : Nat) (hi : inputCheck q b k c = true)
    (hv : baseCheck v = true) (hl : base v < base q)
    (hpb : ParBounded q v (rawTree b)) (hpc : ParBounded q v (rawTree c)) :
    BaseTransformation.inputCheck q v (collapseCode q b k c) = true :=
  (BaseTransformation.inputCheck_exact q v _).mpr
    ⟨((Comparison.acceptedCode_exact q _).mp (collapseCode_spec q b k c hi).1).1,
      hv, hl, collapseCode_parBounded q v b k c hi hv hpb hpc⟩

theorem piCode_collapseCode (q v b k c : Nat) (hi : inputCheck q b k c = true)
    (hv : baseCheck v = true) (hl : base v < base q)
    (hpb : ParBounded q v (rawTree b)) (hpc : ParBounded q v (rawTree c)) :
    BaseTransformation.piCode q v (collapseCode q b k c) =
      collapseCode v (BaseTransformation.piCode q v b) k (BaseTransformation.piCode q v c) := by
  rw [BaseTransformation.piCode_eq q v _ (output_pi_caller q v b k c hi hv hl hpb hpc),
    BaseTransformation.piCode_eq q v b (root_pi_caller q v b k c hi hv hl hpb),
    BaseTransformation.piCode_eq q v c (argument_pi_caller q v b k c hi hv hl hpc)]
  exact collapseCode_change q v b k c hi hv hpb hpc

theorem piCode_collapse_value (q v b k c : Nat) (hi : inputCheck q b k c = true)
    (hv : baseCheck v = true) (hl : base v < base q)
    (hpb : ParBounded q v (rawTree b)) (hpc : ParBounded q v (rawTree c)) :
    interpretation v (BaseTransformation.piCode q v (collapseCode q b k c)) =
      globalCollapse (interpretation v (BaseTransformation.piCode q v b)) k
        (interpretation v (BaseTransformation.piCode q v c)) := by
  rw [BaseTransformation.piCode_eq q v _ (output_pi_caller q v b k c hi hv hl hpb hpc),
    BaseTransformation.piCode_eq q v b (root_pi_caller q v b k c hi hv hl hpb),
    BaseTransformation.piCode_eq q v c (argument_pi_caller q v b k c hi hv hl hpc),
    collapseCode_change q v b k c hi hv hpb hpc]
  exact (collapseCode_spec v b k c (target_input q v b k c hi hv hpb hpc)).2

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RootScalarCollapse
