import Alexander313.Wilken.PublicEpsilonNativeReturnedIota

/-!
# FULL original-source Par and pi for the provenance producer

Every stop retains ORIGINAL source payload syntax. True dual source
admission and root admission derive recursive arithmetic and scalar
callers, so the actual producer agrees literally. The true target output
checker supplies FULL hidden payload bounds before pi. This argument
requires no target selected endpoint and does not assume iota-image Par.
The actual generic iota mapped-value equation has its original separate
guard. No full Mu3.9 claim yet. Source-only and uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.ReturnedIota

open ThetaCourse
open BaseTransformation (ParBounded)

theorem returnedTreeCode_context (q v b : Nat)
    (hbq : RootLowCollapse.rootCheck q b = true) (hbv : RootLowCollapse.rootCheck v b = true)
    (t : RelativeTerm Nat) (htq : check q t = true) (htv : check v t = true)
    (hnq : Comparison.Normal q t) (hnv : Comparison.Normal v t) :
    returnedTreeCode q b t = returnedTreeCode v b t := by
  revert htq htv hnq hnv
  induction t with
  | parameter p => intros; rfl
  | sum t u iht ihu =>
    intro htq htv hnq hnv
    have hq := BaseTransformation.sum_checks q t u htq
    have hv := BaseTransformation.sum_checks v t u htv
    have het := iht hq.1 hv.1 hnq.1 hnv.1
    have heu := ihu hq.2 hv.2 hnq.2.1 hnv.2.1
    have hqt := ((Comparison.acceptedCode_exact q _).mp
      (returnedTreeCode_admitted q b hbq t hq.1 hnq.1).1).1
    have hqu := ((Comparison.acceptedCode_exact q _).mp
      (returnedTreeCode_admitted q b hbq u hq.2 hnq.2.1).1).1
    have hvt : checkCode v (returnedTreeCode q b t) = true := by
      rw [het]
      exact ((Comparison.acceptedCode_exact v _).mp
        (returnedTreeCode_admitted v b hbv t hv.1 hnv.1).1).1
    have hvu : checkCode v (returnedTreeCode q b u) = true := by
      rw [heu]
      exact ((Comparison.acceptedCode_exact v _).mp
        (returnedTreeCode_admitted v b hbv u hv.2 hnv.2.1).1).1
    simpa only [returnedTreeCode, het, heu] using
      OmegaPowers.BaseChange.addCode_context q v _ _ hqt hqu hvt hvu
  | theta k t ih =>
    intro htq htv hnq hnv
    cases k with
    | zero => rfl
    | succ k =>
      have hq := FixedPoint.checked_theta_argument q (k + 1) t htq
      have hv := FixedPoint.checked_theta_argument v (k + 1) t htv
      have he := ih hq hv hnq hnv
      have hs := returnedTreeCode_admitted q b hbq t hq hnq
      have ht := returnedTreeCode_admitted v b hbv t hv hnv
      have hiq := scalar_caller q b k hbq t htq _ hs.1 hs.2
      have hiv : RootCompleteScalarCollapse.inputCheck v b k (returnedTreeCode q b t) = true := by
        rw [he]
        exact scalar_caller v b k hbv t htv _ ht.1 ht.2
      simpa only [returnedTreeCode, he] using
        RootCompleteScalarCollapse.collapseCode_context q v b k _ hiq hiv

theorem sourceTermCode_context (q v b c : Nat)
    (hbq : RootLowCollapse.rootCheck q b = true) (hbv : RootLowCollapse.rootCheck v b = true)
    (hcq : Comparison.acceptedCode q c = true) (hcv : Comparison.acceptedCode v c = true) :
    sourceTermCode q b c = sourceTermCode v b c := by
  have hq := (Comparison.acceptedCode_exact q c).mp hcq
  have hv := (Comparison.acceptedCode_exact v c).mp hcv
  obtain ⟨t, he, ht⟩ := (checkCode_exact q c).mp hq.1
  have htv : check v t = true := by
    simpa only [← he, rawTree_code] using Arithmetic.raw_checked v c hv.1
  have hnt : Comparison.Normal q t := by simpa only [← he, rawTree_code] using hq.2
  have hnv : Comparison.Normal v t := by simpa only [← he, rawTree_code] using hv.2
  simpa only [← he, sourceTermCode_code] using returnedTreeCode_context q v b hbq hbv t ht htv hnt hnv

theorem target_source (q v c : Nat) (hc : Comparison.acceptedCode q c = true)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree c)) :
    Comparison.acceptedCode v c = true := by
  have hs := (Comparison.acceptedCode_exact q c).mp hc
  have hq := Arithmetic.raw_checked q c hs.1
  have hp' := (BaseTransformation.parBounded_iff_payloads q v (rawTree c) hq hv).mp hp
  have ht := BaseTransformation.check_change q v (rawTree c)
    hq hv hp'
  have hn := (BaseTransformation.normal_context q v (rawTree c)
    (Arithmetic.raw_checked q c hs.1) ht).mp hs.2
  obtain ⟨t, he, hchecked⟩ := (checkCode_exact q c).mp hs.1
  have htv : checkCode v c = true := by
    rw [← he, checkCode_code]
    simpa only [← he, rawTree_code] using ht
  exact (Comparison.acceptedCode_exact v c).mpr ⟨htv, hn⟩

/-- Original chosen root and source Par derive actual target source and
root callers and literal returned-source code agreement. -/
theorem sourceTermCode_change (q v b c : Nat) (hb : RootLowCollapse.rootCheck q b = true)
    (hc : Comparison.acceptedCode q c = true) (hv : baseCheck v = true)
    (hpb : ParBounded q v (rawTree b)) (hpc : ParBounded q v (rawTree c)) :
    sourceTermCode q b c = sourceTermCode v b c :=
  sourceTermCode_context q v b c hb (RootLowCollapse.target_root q v b hb hv hpb)
    hc (target_source q v c hc hv hpc)

/-- FULL returned-source payloads follow from the actual second-context
output checker; stopped target canonical parameters are never assumed
to satisfy the original smaller-source cutoff. -/
theorem sourceTermCode_payloads (q v b c : Nat) (hb : RootLowCollapse.rootCheck q b = true)
    (hc : Comparison.acceptedCode q c = true) (hv : baseCheck v = true)
    (hpb : ParBounded q v (rawTree b)) (hpc : ParBounded q v (rawTree c)) :
    Payloads v (rawTree (sourceTermCode q b c)) := by
  have hs := sourceTermCode_admitted v b c (RootLowCollapse.target_root q v b hb hv hpb)
    (target_source q v c hc hv hpc)
  have ht : checkCode v (sourceTermCode q b c) = true := by
    rw [sourceTermCode_change q v b c hb hc hv hpb hpc]
    exact ((Comparison.acceptedCode_exact v _).mp hs.1).1
  exact (checked_admissible v _ (Arithmetic.raw_checked v _ ht)).1

theorem sourceTermCode_parBounded (q v b c : Nat) (hb : RootLowCollapse.rootCheck q b = true)
    (hc : Comparison.acceptedCode q c = true) (hv : baseCheck v = true)
    (hpb : ParBounded q v (rawTree b)) (hpc : ParBounded q v (rawTree c)) :
    ParBounded q v (rawTree (sourceTermCode q b c)) :=
  (BaseTransformation.parBounded_iff_payloads q v _
    (Arithmetic.raw_checked q _ ((Comparison.acceptedCode_exact q _).mp
      (sourceTermCode_admitted q b c hb hc).1).1) hv).mpr
        (sourceTermCode_payloads q v b c hb hc hv hpb hpc)

theorem sourceTermCode_pi_caller (q v b c : Nat) (hb : RootLowCollapse.rootCheck q b = true)
    (hc : Comparison.acceptedCode q c = true) (hv : baseCheck v = true)
    (hl : base v < base q) (hpb : ParBounded q v (rawTree b))
    (hpc : ParBounded q v (rawTree c)) : BaseTransformation.inputCheck q v (sourceTermCode q b c) = true :=
  (BaseTransformation.inputCheck_exact q v _).mpr
    ⟨((Comparison.acceptedCode_exact q _).mp (sourceTermCode_admitted q b c hb hc).1).1,
      hv, hl, sourceTermCode_parBounded q v b c hb hc hv hpb hpc⟩

theorem piCode_sourceTermCode (q v b c : Nat) (hb : RootLowCollapse.rootCheck q b = true)
    (hc : Comparison.acceptedCode q c = true) (hv : baseCheck v = true)
    (hl : base v < base q) (hpb : ParBounded q v (rawTree b))
    (hpc : ParBounded q v (rawTree c)) :
    BaseTransformation.piCode q v (sourceTermCode q b c) =
      sourceTermCode v (BaseTransformation.piCode q v b) (BaseTransformation.piCode q v c) := by
  have hbr : BaseTransformation.inputCheck q v b = true :=
    (BaseTransformation.inputCheck_exact q v b).mpr ⟨RootLowCollapse.root_original q b hb, hv, hl, hpb⟩
  have hcr : BaseTransformation.inputCheck q v c = true :=
    (BaseTransformation.inputCheck_exact q v c).mpr
      ⟨((Comparison.acceptedCode_exact q c).mp hc).1, hv, hl, hpc⟩
  rw [BaseTransformation.piCode_eq q v _ (sourceTermCode_pi_caller q v b c hb hc hv hl hpb hpc),
    BaseTransformation.piCode_eq q v b hbr, BaseTransformation.piCode_eq q v c hcr]
  exact sourceTermCode_change q v b c hb hc hv hpb hpc

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.ReturnedIota
