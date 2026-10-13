import Alexander313.Wilken.PublicEpsilonNativeRootCompleteScalarCollapseSupport
import Alexander313.Wilken.PublicEpsilonNativeRootLocalizedCollapse

/-!
# Complete scalar construction with FULL syntactic Par and actual pi

Original chosen root and argument Par derive the entire target scalar
domain. Genuine raw comparisons and selected support agree literally,
including the localized branch. The actual target checker yields FULL
hidden output payload bounds before actual pi is invoked. This proves
scalar construction and transport, not whole returned-term or mu
base-change compatibility. No target caller or cutoff oracle. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RootCompleteScalarCollapse

open ThetaCourse
open BaseTransformation (ParBounded)

theorem positive_caller (q b k c : Nat) (hi : inputCheck q b k c = true)
    (hk : 0 < k) : RootPositiveCollapse.inputCheck q b k c = true :=
  (RootPositiveCollapse.inputCheck_exact q b k c).mpr
    ⟨((inputCheck_exact q b k c).mp hi).1,
      ((inputCheck_exact q b k c).mp hi).2.1, hk, ((inputCheck_exact q b k c).mp hi).2.2⟩

theorem target_input (q v b k c : Nat) (hi : inputCheck q b k c = true)
    (hv : baseCheck v = true) (hpb : ParBounded q v (rawTree b))
    (hpc : ParBounded q v (rawTree c)) : inputCheck v b k c = true := by
  by_cases hk : 0 < k
  · have ht := (RootPositiveCollapse.inputCheck_exact v b k c).mp
      (RootPositiveCollapse.target_input q v b k c (positive_caller q b k c hi hk) hv hpb hpc)
    exact (inputCheck_exact v b k c).mpr ⟨ht.1, ht.2.1, ht.2.2.2⟩
  · have he : k = 0 := by omega
    subst k
    have hc := (RootAboveHeadCollapse.argumentCheck_exact v c).mp
      (RootAboveHeadCollapse.target_argument q v c (zero_argument q b c hi) hv hpc)
    exact (inputCheck_exact v b 0 c).mpr
      ⟨RootLowCollapse.target_root q v b ((inputCheck_exact q b 0 c).mp hi).1 hv hpb,
        hc.1, by simpa only [Nat.zero_add] using hc.2⟩

theorem knownBranch_context (q v b k c : Nat) (hq : inputCheck q b k c = true)
    (hv : inputCheck v b k c = true) : knownBranch q b k c = knownBranch v b k c := by
  by_cases hk : 0 < k
  · simp only [knownBranch, decide_eq_true hk, Bool.true_or]
  · have he : k = 0 := by omega
    subst k
    simp only [knownBranch, decide_eq_false hk, Bool.false_or]
    exact RootScalarCollapse.coveredCheck_context q v b c
      ((inputCheck_exact q b 0 c).mp hq).1 ((inputCheck_exact v b 0 c).mp hv).1
      (zero_argument q b c hq) (zero_argument v b c hv)

theorem collapseCode_context (q v b k c : Nat) (hq : inputCheck q b k c = true)
    (hv : inputCheck v b k c = true) : collapseCode q b k c = collapseCode v b k c := by
  have he := knownBranch_context q v b k c hq hv
  cases hb : knownBranch q b k c with
  | true =>
    have hbt : knownBranch v b k c = true := he.symm.trans hb
    simpa only [collapseCode, hq, hv, hb, hbt, Bool.cond_true] using
      RootScalarCollapse.collapseCode_context q v b k c
        (scalar_caller q b k c hq hb) (scalar_caller v b k c hv hbt)
  | false =>
    have hbt : knownBranch v b k c = false := he.symm.trans hb
    simpa only [collapseCode, hq, hv, hb, hbt, Bool.cond_true, Bool.cond_false] using
      RootLocalizedCollapse.collapseCode_context q v b c
        (localized_caller q b k c hq hb) (localized_caller v b k c hv hbt)

theorem collapseCode_change (q v b k c : Nat) (hi : inputCheck q b k c = true)
    (hv : baseCheck v = true) (hpb : ParBounded q v (rawTree b))
    (hpc : ParBounded q v (rawTree c)) : collapseCode q b k c = collapseCode v b k c :=
  collapseCode_context q v b k c hi (target_input q v b k c hi hv hpb hpc)

/-- Actual second-context admission derives the FULL hidden output
parameter cutoff on every original scalar branch. -/
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

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RootCompleteScalarCollapse
