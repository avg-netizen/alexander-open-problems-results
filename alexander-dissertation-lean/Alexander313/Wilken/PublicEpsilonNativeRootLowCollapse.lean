import Alexander313.Wilken.PublicEpsilonNativeRootLowCollapseSupport

/-!
# Actual LOW relative collapse preserves original Par and commutes with pi

All second-context root, argument and arithmetic callers follow from the
original root and argument atomic-stop Par guards. Literal branch agreement
gives a genuinely checked target output, hence its FULL hidden payload
cutoff. This is a complete LOW-argument relative-collapse kernel; high
arguments, the full returned iota payload theorem and Lemma 3.9 remain
separate. No selected-return endpoint or beta-code premise. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RootLowCollapse

open ThetaCourse
open BaseTransformation (ParBounded)

theorem rootCheck_context (q v b : Nat) (hbq : checkCode q b = true)
    (hbv : checkCode v b = true) : rootCheck q b = rootCheck v b := by
  simp only [rootCheck, SourceChi.BaseChange.acceptedCode_context q v b hbq hbv]

/-- The original root Par supplies the true target Normal high-root caller. -/
theorem target_root (q v b : Nat) (ha : rootCheck q b = true)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree b)) :
    rootCheck v b = true := by
  have ht := OmegaPowers.BaseChange.target_low q v b (root_low q b ha) hv hp
  rw [← rootCheck_context q v b (root_original q b ha) (Bool.and_eq_true.mp ht).1]
  exact ha

theorem target_input (q v b c : Nat) (hi : inputCheck q b c = true)
    (hv : baseCheck v = true) (hpb : ParBounded q v (rawTree b))
    (hpc : ParBounded q v (rawTree c)) : inputCheck v b c = true := by
  have hs := (inputCheck_exact q b c).mp hi
  exact (inputCheck_exact v b c).mpr ⟨target_root q v b hs.1 hv hpb,
    OmegaPowers.BaseChange.target_low q v c hs.2 hv hpc⟩

theorem aboveOffset_context (q v b c : Nat) (hbq : rootCheck q b = true)
    (hbv : rootCheck v b = true) (hcq : lowCheckCode q c = true)
    (hcv : lowCheckCode v c = true) : aboveOffset q b c = aboveOffset v b c := by
  have hq := (Bool.and_eq_true.mp hcq).1
  have hv := (Bool.and_eq_true.mp hcv).1
  have hh := OmegaPowers.BaseChange.headCode_context q v c hq hv
  have hheadv : checkCode v (OmegaPowers.Offsets.headCode q c) = true := by
    rw [hh]
    exact OmegaPowers.BaseChange.headCode_checked v c hv
  have he := OmegaPowers.BaseChange.lessRawCode_context q v b (OmegaPowers.Offsets.headCode q c)
    (root_original q b hbq) (OmegaPowers.BaseChange.headCode_checked q c hq)
    (root_original v b hbv) hheadv
  simp only [aboveOffset, OmegaPowers.BaseChange.offsetsCheck_context q v c hcq hcv]
  exact congrArg₂ (· && ·) rfl
    (he.trans (congrArg (Normalization.lessRawCode v b) hh))

theorem exponentCode_context (q v b c : Nat) (hbq : rootCheck q b = true)
    (hbv : rootCheck v b = true) (hcq : lowCheckCode q c = true)
    (hcv : lowCheckCode v c = true) : exponentCode q b c = exponentCode v b c := by
  have hs := aboveOffset_context q v b c hbq hbv hcq hcv
  have ht := OmegaPowers.BaseChange.finiteTailCode_context q v c 1
    (source_checked q b hbq) (source_checked v b hbv)
    (Bool.and_eq_true.mp hcq).1 (Bool.and_eq_true.mp hcv).1
  have ha := OmegaPowers.BaseChange.addCode_context q v b c
    (root_original q b hbq) (Bool.and_eq_true.mp hcq).1
    (root_original v b hbv) (Bool.and_eq_true.mp hcv).1
  simp only [exponentCode, hs, ht, ha]

theorem collapseCode_context (q v b c : Nat) (hq : inputCheck q b c = true)
    (hv : inputCheck v b c = true) : collapseCode q b c = collapseCode v b c := by
  have hs := (inputCheck_exact q b c).mp hq
  have ht := (inputCheck_exact v b c).mp hv
  have he := exponentCode_context q v b c hs.1 ht.1 hs.2 ht.2
  have hlowv : lowCheckCode v (exponentCode q b c) = true := by
    rw [he]
    exact (exponentCode_spec v b c ht.1 ht.2).1
  have hp := OmegaPowers.BaseChange.powerCode_context q v (exponentCode q b c)
    (exponentCode_spec q b c hs.1 hs.2).1 hlowv
  simp only [collapseCode, hq, hv, Bool.cond_true]
  exact hp.trans (congrArg (OmegaPowers.powerCode v) he)

theorem collapseCode_change (q v b c : Nat) (hi : inputCheck q b c = true)
    (hv : baseCheck v = true) (hpb : ParBounded q v (rawTree b))
    (hpc : ParBounded q v (rawTree c)) : collapseCode q b c = collapseCode v b c :=
  collapseCode_context q v b c hi (target_input q v b c hi hv hpb hpc)

/-- The FULL syntactic output cutoff follows from the actual target checker. -/
theorem collapseCode_payloads (q v b c : Nat) (hi : inputCheck q b c = true)
    (hv : baseCheck v = true) (hpb : ParBounded q v (rawTree b))
    (hpc : ParBounded q v (rawTree c)) : Payloads v (rawTree (collapseCode q b c)) := by
  have hs := collapseCode_spec v b c (target_input q v b c hi hv hpb hpc)
  have hc : checkCode v (collapseCode q b c) = true := by
    rw [collapseCode_change q v b c hi hv hpb hpc]
    exact (Bool.and_eq_true.mp hs.1).1
  exact (checked_admissible v _ (Arithmetic.raw_checked v _ hc)).1

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
    ⟨root_original q b ((inputCheck_exact q b c).mp hi).1, hv, hl, hpb⟩

theorem argument_pi_caller (q v b c : Nat) (hi : inputCheck q b c = true)
    (hv : baseCheck v = true) (hl : base v < base q)
    (hpc : ParBounded q v (rawTree c)) : BaseTransformation.inputCheck q v c = true :=
  (BaseTransformation.inputCheck_exact q v c).mpr
    ⟨(Bool.and_eq_true.mp ((inputCheck_exact q b c).mp hi).2).1, hv, hl, hpc⟩

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
  rw [piCode_collapseCode q v b c hi hv hl hpb hpc,
    BaseTransformation.piCode_eq q v b (root_pi_caller q v b c hi hv hl hpb),
    BaseTransformation.piCode_eq q v c (argument_pi_caller q v b c hi hv hl hpc)]
  exact (collapseCode_spec v b c (target_input q v b c hi hv hpb hpc)).2.2

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RootLowCollapse
