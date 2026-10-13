import Alexander313.Wilken.PublicEpsilonNativeUnboundedIotaShiftedIndicator
import Alexander313.Wilken.PublicEpsilonNativeRootLowCollapse

/-!
# Genuine chosen-Par callers for the relative indicator

The original root and source atomic-stop Par bounds derive second-context
admission. Every original theta-zero support comparison transfers through
the actual native comparator, so the original full restriction derives the
target full restriction. The finite source fold then identifies the two
actual NEW-base indicators. No Par bound on stopped iota parameters, target
admission/restriction, relative-indicator equality or endpoint is assumed.
This is a source3.9 dependency, not the completed mu/pi equation. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.ShiftedIndicator.BaseChange

open ThetaCourse
open BaseTransformation (ParBounded)

/-- Actual original-context strict comparison transfers below the same
written high root at two genuinely admitted source contexts. -/
theorem below_root_context (q v b : Nat)
    (hq : rootCheck q b = true) (hv : rootCheck v b = true)
    (t : RelativeTerm Nat) (htq : check q t = true) (htv : check v t = true)
    (hnq : Comparison.Normal q t)
    (hlt : denote q t < interpretation q b) : denote v t < interpretation v b := by
  have hbq := Decomposition.input_tree q b (RootLowCollapse.root_accepted q b hq)
  have hbv := Decomposition.input_tree v b (RootLowCollapse.root_accepted v b hv)
  have hnv := (BaseTransformation.normal_context q v t htq htv).mp hnq
  have hc : Comparison.less q t (rawTree b) = true :=
    (Comparison.less_correct q t (rawTree b) htq hbq.1 hnq hbq.2).mpr
      (by rwa [← Decomposition.input_value q b (RootLowCollapse.root_accepted q b hq)])
  have hcv : Comparison.less v t (rawTree b) = true := by
    rw [← BaseTransformation.less_context q v t (rawTree b)]
    exact hc
  have h := (Comparison.less_correct v t (rawTree b) htv hbv.1 hnv hbv.2).mp hcv
  rwa [← Decomposition.input_value v b (RootLowCollapse.root_accepted v b hv)] at h

/-- Every ORIGINAL support node retains its strict root cutoff through
real checked comparison, without a target support premise. -/
theorem restricted_context (q v b : Nat)
    (hq : rootCheck q b = true) (hv : rootCheck v b = true)
    (t : RelativeTerm Nat) (htq : check q t = true) (htv : check v t = true)
    (hnq : Comparison.Normal q t) (hr : Restricted q b t) : Restricted v b t := by
  revert htq htv hnq hr
  induction t with
  | parameter p =>
    intro htq htv hnq hr u hu
    simp only [Iota.fullList, RelativeTerm.PrincipalSupport.principalList, List.not_mem_nil] at hu
  | sum a c iha ihc =>
    intro htq htv hnq hr
    have hcq := BaseTransformation.sum_checks q a c htq
    have hcv := BaseTransformation.sum_checks v a c htv
    have hrs := (restricted_sum q b a c).mp hr
    exact (restricted_sum v b a c).mpr
      ⟨iha hcq.1 hcv.1 hnq.1 hrs.1, ihc hcq.2 hcv.2 hnq.2.1 hrs.2⟩
  | theta k a ih =>
    intro htq htv hnq hr
    have haq := FixedPoint.checked_theta_argument q k a htq
    have hav := FixedPoint.checked_theta_argument v k a htv
    cases k with
    | zero =>
      have hrs := (restricted_theta_zero q b a).mp hr
      exact (restricted_theta_zero v b a).mpr
        ⟨below_root_context q v b hq hv (.theta 0 a) htq htv hnq hrs.1,
          ih haq hav hnq hrs.2⟩
    | succ k =>
      exact (restricted_theta_succ v b k a).mpr
        (ih haq hav hnq ((restricted_theta_succ q b k a).mp hr))

theorem target_tree (q v : Nat) (t : RelativeTerm Nat) (ht : check q t = true)
    (hv : baseCheck v = true) (hp : ParBounded q v t) : check v t = true :=
  BaseTransformation.check_change q v t ht hv
    ((BaseTransformation.parBounded_iff_payloads q v t ht hv).mp hp)

/-- ORIGINAL root/source Par derives every target source caller, including
the target restricted domain; no target admission or invariant is supplied. -/
theorem target_callers (q v b : Nat) (ha : rootCheck q b = true)
    (t : RelativeTerm Nat) (ht : check q t = true) (hn : Comparison.Normal q t)
    (hr : Restricted q b t) (hv : baseCheck v = true)
    (hpb : ParBounded q v (rawTree b)) (hpt : ParBounded q v t) :
    rootCheck v b = true ∧ check v t = true ∧
      Comparison.Normal v t ∧ Restricted v b t := by
  have hb := RootLowCollapse.target_root q v b ha hv hpb
  have htv := target_tree q v t ht hv hpt
  exact ⟨hb, htv, (BaseTransformation.normal_context q v t ht htv).mp hn,
    restricted_context q v b ha hb t ht htv hn hr⟩

/-- The two genuinely different target-base indicators agree under ONLY
the original root/source guards and chosen source Par cutoff. -/
theorem mapped_chi_change (q v b : Nat) (ha : rootCheck q b = true)
    (t : RelativeTerm Nat) (ht : check q t = true) (hn : Comparison.Normal q t)
    (hr : Restricted q b t) (hv : baseCheck v = true)
    (hpb : ParBounded q v (rawTree b)) (hpt : ParBounded q v t) :
    SourceChi.chiCode (betaCode q b) (transform q b t).code =
      SourceChi.chiCode (betaCode v b) (transform v b t).code := by
  have hs := target_callers q v b ha t ht hn hr hv hpb hpt
  rw [SourceChi.chiCode_correct _ _ (transform_checked q b ha t ht hr)
      (transform_normal q b ha t ht hn hr),
    SourceChi.chiCode_correct _ _ (transform_checked v b hs.1 t hs.2.1 hs.2.2.2)
      (transform_normal v b hs.1 t hs.2.1 hs.2.2.1 hs.2.2.2)]
  exact mapped_indicator_context q v b ha hs.1 t ht hs.2.1 hn hr hs.2.2.2

theorem chiCode_change (q v b : Nat) (ha : rootCheck q b = true)
    (t : RelativeTerm Nat) (ht : check q t = true) (hn : Comparison.Normal q t)
    (hr : Restricted q b t) (hv : baseCheck v = true)
    (hpb : ParBounded q v (rawTree b)) (hpt : ParBounded q v t) :
    ShiftedIndicator.chiCode q b t.code = ShiftedIndicator.chiCode v b t.code := by
  have hs := target_callers q v b ha t ht hn hr hv hpb hpt
  rw [ShiftedIndicator.chiCode_correct q b ha t ht hn hr,
    ShiftedIndicator.chiCode_correct v b hs.1 t hs.2.1 hs.2.2.1 hs.2.2.2]
  exact mapped_chi_change q v b ha t ht hn hr hv hpb hpt

/-- The actual source pi caller is derived from original admission and
chosen Par; the relative-bit commutation uses its genuine literal output. -/
theorem source_pi_caller (q v b : Nat) (ha : rootCheck q b = true)
    (t : RelativeTerm Nat) (ht : check q t = true) (hv : baseCheck v = true)
    (hl : base v < base q) (hp : ParBounded q v t) :
    BaseTransformation.inputCheck q v t.code = true :=
  (BaseTransformation.inputCheck_exact q v t.code).mpr
    ⟨by simpa only [checkCode_code] using ht, hv, hl,
      by simpa only [rawTree_code] using hp⟩

theorem root_pi_caller (q v b : Nat) (ha : rootCheck q b = true)
    (hv : baseCheck v = true) (hl : base v < base q) (hp : ParBounded q v (rawTree b)) :
    BaseTransformation.inputCheck q v b = true :=
  (BaseTransformation.inputCheck_exact q v b).mpr ⟨root_original q b ha, hv, hl, hp⟩

theorem chiCode_pi (q v b : Nat) (ha : rootCheck q b = true)
    (t : RelativeTerm Nat) (ht : check q t = true) (hn : Comparison.Normal q t)
    (hr : Restricted q b t) (hv : baseCheck v = true) (hl : base v < base q)
    (hpb : ParBounded q v (rawTree b)) (hpt : ParBounded q v t) :
    ShiftedIndicator.chiCode v (BaseTransformation.piCode q v b)
      (BaseTransformation.piCode q v t.code) = ShiftedIndicator.chiCode q b t.code := by
  rw [BaseTransformation.piCode_eq q v b (root_pi_caller q v b ha hv hl hpb),
    BaseTransformation.piCode_eq q v t.code (source_pi_caller q v b ha t ht hv hl hpt)]
  exact (chiCode_change q v b ha t ht hn hr hv hpb hpt).symm

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.ShiftedIndicator.BaseChange
