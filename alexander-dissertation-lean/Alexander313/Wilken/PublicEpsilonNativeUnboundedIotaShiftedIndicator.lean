import Alexander313.Wilken.PublicEpsilonNativeUnboundedIotaShiftedIndicatorSupport

/-!
# Actual shifted indicator and genuine original-presentation transport

A joint syntax induction identifies the finite source fold with the actual
indicator and every actual high-label list of the transformed tree. The
fixed/high-choice and zero-argument tests are derived from original theta
admission. The same original fold agrees at two genuinely admitted source
bases, so its base-change proof uses original syntax provenance instead of
an unjustified cutoff on newly produced target parameters. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.ShiftedIndicator

open ThetaCourse

private theorem baseCase_transform (q b k : Nat) (ha : rootCheck q b = true)
    (a : RelativeTerm Nat) (ht : check q a = true) (hn : Comparison.Normal q a)
    (hr : Restricted q b a) :
    SourceChi.baseCase (betaCode q b) k (transform q b a).code = baseCase q (k + 1) a.code := by
  have hi := ReturnedIota.original_accepted q a ht hn
  have hti := ReturnedIota.original_accepted (betaCode q b) (transform q b a)
    (transform_checked q b ha a ht hr) (transform_normal q b ha a ht hn hr)
  have hz : FixedPoint.zeroCheck (transform q b a).code = FixedPoint.zeroCheck a.code := by
    apply Bool.eq_iff_iff.mpr
    rw [FixedPoint.zeroCheck_exact (betaCode q b) _ hti, FixedPoint.zeroCheck_exact q _ hi]
    simpa only [interpretation_code] using FixedPointTransport.transform_zero_iff q b ha a ht hn hr
  have hk : (k + 1 == 1) = (k == 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    omega
  simp only [SourceChi.baseCase, baseCase, hk, hz]

/-- The ORIGINAL high-root/check/Normal/Restricted guards derive the actual
target indicator and every high-label bit list by simultaneous descent. -/
theorem indicator_highBits_transform (q b : Nat) (ha : rootCheck q b = true)
    (t : RelativeTerm Nat) (ht : check q t = true) (hn : Comparison.Normal q t)
    (hr : Restricted q b t) :
    SourceChi.indicator (betaCode q b) (transform q b t) = indicator q t ∧
      ∀ m, SourceChi.Arithmetic.highBits (betaCode q b) m (transform q b t) = highBits q (m + 1) t := by
  revert ht hn hr
  induction t with
  | parameter p =>
    intro ht hn hr
    constructor
    · rfl
    · intro m
      rw [transform, SourceChi.Arithmetic.highBits_parameter, highBits_parameter]
  | sum a c iha ihc =>
    intro ht hn hr
    have hs := SourceChi.sum_children q a c ht hn
    have hrs := (restricted_sum q b a c).mp hr
    have hia := iha hs.1 hs.2.1 hrs.1
    have hic := ihc hs.2.2.1 hs.2.2.2.1 hrs.2
    cases he : small q b (.sum a c) with
    | true =>
      have hlow := (OrderSupport.small_iff_outerSort q b ha _ ht hr).mp he
      constructor
      · simp only [transform, he, Bool.cond_true, SourceChi.indicator_parameter,
          indicator_low q (.sum a c) hlow]
      · intro m
        rw [transform, he, Bool.cond_true, SourceChi.Arithmetic.highBits_parameter]
        exact (highBits_low q (m + 1) (.sum a c) (by omega)).symm
    | false =>
      constructor
      · simpa only [transform, he, Bool.cond_false, SourceChi.indicator_sum, indicator_sum] using hic.1
      · intro m
        simp only [transform, he, Bool.cond_false, SourceChi.Arithmetic.highBits_sum,
          highBits_sum, hia.2 m, hic.2 m]
  | theta k a ih =>
    intro ht hn hr
    cases k with
    | zero =>
      rw [OrderSupport.transform_low q b ha (.theta 0 a) ht hr le_rfl]
      constructor
      · rfl
      · intro m
        simp only [SourceChi.Arithmetic.highBits_parameter, highBits_theta,
          Decomposition.above, RelativeTerm.outerSort, Nat.add_lt_add_iff_right,
          Nat.not_lt_zero, decide_false, Bool.cond_false]
    | succ k =>
      have hac := FixedPoint.checked_theta_argument q (k + 1) a ht
      have har := (restricted_theta_succ q b k a).mp hr
      have hi := ih hac hn har
      have hb := baseCase_transform q b k ha a hac hn har
      have hh := LogEndZeroTransport.chooseHigh_theta_argument_transform q b k ha a ht hn har
      have hk0 : (k + 1 == 0) = false := by simp
      have hchi : SourceChi.indicator (betaCode q b) (.theta k (transform q b a)) =
          indicator q (.theta (k + 1) a) := by
        rw [target_indicator_theta_bits, indicator_theta_bits, hk0, Bool.cond_false,
          hb, hh, hi.2 k, hi.1]
      rw [OrderSupport.transform_theta_succ q b k ha a ht hr]
      refine ⟨hchi, ?_⟩
      intro m
      simp only [SourceChi.Arithmetic.highBits_theta, highBits_theta, hchi,
        Decomposition.above, RelativeTerm.outerSort, Nat.add_lt_add_iff_right]

theorem indicator_transform (q b : Nat) (ha : rootCheck q b = true)
    (t : RelativeTerm Nat) (ht : check q t = true) (hn : Comparison.Normal q t)
    (hr : Restricted q b t) :
    SourceChi.indicator (betaCode q b) (transform q b t) = indicator q t :=
  (indicator_highBits_transform q b ha t ht hn hr).1

theorem highBits_transform (q b m : Nat) (ha : rootCheck q b = true)
    (t : RelativeTerm Nat) (ht : check q t = true) (hn : Comparison.Normal q t)
    (hr : Restricted q b t) :
    SourceChi.Arithmetic.highBits (betaCode q b) m (transform q b t) = highBits q (m + 1) t :=
  (indicator_highBits_transform q b ha t ht hn hr).2 m

/-- The source fold's complete ORIGINAL labelled state agrees at two
genuinely admitted contexts; all original fixed/last-component callers derive. -/
theorem state_context (q v : Nat) (t : RelativeTerm Nat)
    (hq : check q t = true) (hv : check v t = true) (hn : Comparison.Normal q t) :
    state q t = state v t := by
  revert hq hv hn
  induction t with
  | parameter p => intro hq hv hn; rfl
  | sum a c iha ihc =>
    intro hq hv hn
    have hs := SourceChi.sum_children q a c hq hn
    have ht := BaseTransformation.sum_checks v a c hv
    change SourceChi.sumState (state q a) (state q c) = SourceChi.sumState (state v a) (state v c)
    rw [iha hs.1 ht.1 hs.2.1, ihc hs.2.2.1 ht.2 hs.2.2.2.1]
  | theta k a ih =>
    intro hq hv hn
    have haq := SourceChi.theta_argument_parts q k a hq hn
    have hnv : Comparison.Normal v (.theta k a) :=
      (BaseTransformation.normal_context q v _ hq hv).mp hn
    have hav := SourceChi.theta_argument_parts v k a hv hnv
    have he := ih (FixedPoint.checked_theta_argument q k a hq)
      (FixedPoint.checked_theta_argument v k a hv) hn
    have hc := SourceChi.BaseChange.chooseHigh_context q v k a.code haq.1 hav.1
    change thetaState q k (state q a) = thetaState v k (state v a)
    rw [he]
    unfold thetaState
    simp only [state_tree, baseCase, hc]

theorem indicator_context (q v : Nat) (t : RelativeTerm Nat)
    (hq : check q t = true) (hv : check v t = true) (hn : Comparison.Normal q t) :
    indicator q t = indicator v t :=
  congrArg (fun s : State => s.2.1) (state_context q v t hq hv hn)

/-- This identifies indicators at TWO genuinely different target roots
through the same original finite source fold, without identifying either
one with the original source-base indicator. -/
theorem mapped_indicator_context (q v b : Nat)
    (hq : rootCheck q b = true) (hv : rootCheck v b = true)
    (t : RelativeTerm Nat) (ht : check q t = true) (htv : check v t = true)
    (hn : Comparison.Normal q t) (hr : Restricted q b t) (hrv : Restricted v b t) :
    SourceChi.indicator (betaCode q b) (transform q b t) =
      SourceChi.indicator (betaCode v b) (transform v b t) := by
  have hnv := (BaseTransformation.normal_context q v t ht htv).mp hn
  exact (indicator_transform q b hq t ht hn hr).trans
    ((indicator_context q v t ht htv hn).trans
      (indicator_transform v b hv t htv hnv hrv).symm)

def chiCode (q b c : Nat) : Bool := inputCheck q b c && (stateCode q c).2.1

theorem chiCode_primrec : Primrec (fun p : Nat × (Nat × Nat) => chiCode p.1 p.2.1 p.2.2) :=
  Primrec.and.comp
    (inputCheck_primrec.comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)) ((Primrec.fst.comp Primrec.snd).comp
    (stateCode_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd)))

/-- The actual guarded finite ORIGINAL-source fold computes the actual
target-beta chi on its constructed iota tree, including the base-value bit. -/
theorem chiCode_correct (q b : Nat) (ha : rootCheck q b = true)
    (t : RelativeTerm Nat) (ht : check q t = true) (hn : Comparison.Normal q t)
    (hr : Restricted q b t) :
    chiCode q b t.code = SourceChi.chiCode (betaCode q b) (transform q b t).code := by
  have hi := (inputCheck_exact q b t.code).mpr
    ⟨ha, t, rfl, ht, hn, (restricted_iff_sourceStar q b ha t ht hn).mp hr⟩
  simp only [chiCode, hi, Bool.true_and, stateCode_code]
  exact ((SourceChi.chiCode_correct _ _ (transform_checked q b ha t ht hr)
    (transform_normal q b ha t ht hn hr)).trans (indicator_transform q b ha t ht hn hr)).symm

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.ShiftedIndicator
