import Alexander313.Wilken.PublicEpsilonNativeRootPositiveCollapseSupport

/-!
# Positive relative collapse preserves the genuine original Par cutoff

Original root and argument Par guards derive the actual target callers.
The output keeps its positive theta syntax. Its genuine target checker
therefore yields the FULL hidden payload cutoff, and hence the original
atomic-stop Par predicate and actual pi caller/equation. This is a scalar
positive-collapse kernel. It supplies no full returned iota or chi/pi law.
No selected public-return endpoint or beta-code premise. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RootPositiveCollapse

open ThetaCourse
open BaseTransformation (ParBounded)

theorem target_argument (q v c : Nat) (hc : Comparison.acceptedCode q c = true)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree c)) :
    Comparison.acceptedCode v c = true := by
  have hs := (Comparison.acceptedCode_exact q c).mp hc
  obtain ⟨t, rfl, ht⟩ := (checkCode_exact q c).mp hs.1
  have hpt : Payloads v t := (BaseTransformation.parBounded_iff_payloads q v t ht hv).mp
    (by simpa only [rawTree_code] using hp)
  have hvt := BaseTransformation.check_change q v t ht hv hpt
  have hn : Comparison.Normal q t := by simpa only [rawTree_code] using hs.2
  exact (Comparison.acceptedCode_exact v t.code).mpr
    ⟨by simpa only [checkCode_code] using hvt,
      by simpa only [rawTree_code] using (BaseTransformation.normal_context q v t ht hvt).mp hn⟩

/-- Original syntax and chosen Par derive every second-context guard. -/
theorem target_input (q v b k c : Nat) (hi : inputCheck q b k c = true)
    (hv : baseCheck v = true) (hpb : ParBounded q v (rawTree b))
    (hpc : ParBounded q v (rawTree c)) : inputCheck v b k c = true := by
  have hs := (inputCheck_exact q b k c).mp hi
  exact (inputCheck_exact v b k c).mpr
    ⟨RootLowCollapse.target_root q v b hs.1 hv hpb,
      target_argument q v c hs.2.1 hv hpc, hs.2.2.1, hs.2.2.2⟩

theorem collapseCode_context (q v b k c : Nat) (hq : inputCheck q b k c = true)
    (hv : inputCheck v b k c = true) : collapseCode q b k c = collapseCode v b k c := by
  rw [collapseCode_eq q b k c hq, collapseCode_eq v b k c hv]

theorem collapseCode_change (q v b k c : Nat) (hi : inputCheck q b k c = true)
    (hv : baseCheck v = true) (hpb : ParBounded q v (rawTree b))
    (hpc : ParBounded q v (rawTree c)) : collapseCode q b k c = collapseCode v b k c :=
  collapseCode_context q v b k c hi (target_input q v b k c hi hv hpb hpc)

/-- This is the FULL syntactic output cutoff from the actual target
checker. It does not infer parameter bounds from output value alone. -/
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

/-- Actual pi executions retain the real root, argument and output codes. -/
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

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RootPositiveCollapse
