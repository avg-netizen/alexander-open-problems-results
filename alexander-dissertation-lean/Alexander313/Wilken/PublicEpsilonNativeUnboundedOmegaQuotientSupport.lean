import Alexander313.Wilken.HereditaryNativeBoundedContextOmegaQuotient
import Alexander313.Wilken.PublicEpsilonNativeUnboundedIotaOrderSupport

/-!
# Genuine complete quotient atoms at every original coded epsilon source

The original source is ANY literal admitted coded epsilon q. Its genuine
high root beta and original full support restriction supply the real LOW
omega-power, corrected middle theta-one and high absorption callers.
The scalar finite operations are reused from the already proved ANY-q
quotient implementation. The original RootLow guard is used directly, without a canonical spelling
or selected endpoint. No fixed-source root or restriction theorem is applied
at a new source. Source-only and uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.OmegaQuotient.Support

open PublicEpsilonUnboundedIota (Restricted fullList)
open Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.OmegaQuotient
  (baseTerm thresholdTerm theta_checked baseTerm_spec thresholdTerm_spec theta_principal
   theta_one_high_absorbs wordHeight wordHeight_mem unitTest unitTest_exact selectUnits
   selectUnits_primrec selectUnits_mem selectUnits_filter theta_one_below_threshold
   theta_one_shifted_quotient theta_one_above_threshold principal_above_second_absorbs)
open BoundedContextIota.OmegaQuotient (atomTerm argumentCode)

theorem argument_accepted (q root : Nat) (ha : rootCheck q root = true) :
    Decomposition.inputCheck q (argumentCode root) = true := by
  obtain ⟨t, he, ht, hn, hh⟩ := (rootCheck_exact q root).mp ha
  apply (Decomposition.inputCheck_exact _ _).mpr
  exact ⟨by simpa only [argumentCode, he, Localization.argumentCode_theta, checkCode_code] using
    BaseTransformation.theta_argument_check _ 0 t ht,
    by simpa only [argumentCode, he, Localization.argumentCode_theta, ThetaCourse.rawTree_code] using hn⟩

theorem zero_restricted (q root : Nat) : Restricted q root Normalization.zeroTree := by
  intro u hu
  simp only [Normalization.zeroTree, fullList,
    RelativeTerm.PrincipalSupport.principalList, List.not_mem_nil] at hu

theorem atoms_restricted (q root : Nat) (t : RelativeTerm Nat)
    (hr : Restricted q root t) (u : RelativeTerm Nat) (hu : u ∈ Comparison.atoms t) :
    Restricted q root u := by
  revert hr hu
  induction t with
  | parameter p =>
    intro hr hu
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hu
    intro v hv
    simp only [fullList, RelativeTerm.PrincipalSupport.principalList,
      List.not_mem_nil] at hv
  | sum t v iht ihv =>
    intro hr hu
    have hs := (PublicEpsilonUnboundedIota.restricted_sum q root t v).mp hr
    rcases List.mem_append.mp hu with hu | hu
    · exact iht hs.1 hu
    · exact ihv hs.2 hu
  | theta k t ih =>
    intro hr hu
    exact (List.mem_singleton.mp hu).symm ▸ hr

theorem buildRev_restricted (q root : Nat) (as : List (RelativeTerm Nat))
    (hr : ∀ t ∈ as, Restricted q root t) : Restricted q root (Normalization.buildRev as) := by
  revert hr
  induction as with
  | nil => intro _; exact zero_restricted q root
  | cons t as ih =>
    intro hr
    exact (PublicEpsilonUnboundedIota.restricted_sum q root _ _).mpr
      ⟨ih (fun u hu => hr u (List.mem_cons_of_mem _ hu)), hr t List.mem_cons_self⟩

theorem buildAtoms_restricted (q root : Nat) (as : List (RelativeTerm Nat))
    (hr : ∀ t ∈ as, Restricted q root t) : Restricted q root (Normalization.buildAtoms as) :=
  buildRev_restricted q root as.reverse (fun t ht => hr t (List.mem_reverse.mp ht))

theorem normalize_restricted (q root : Nat) (t : RelativeTerm Nat)
    (ht : check q t = true) (hr : Restricted q root t) :
    Restricted q root (Normalization.normalize q t) := by
  revert ht hr
  induction t with
  | parameter p => intro ht hr; exact hr
  | sum t u iht ihu =>
    intro ht hr
    have hc := BaseTransformation.sum_checks q t u ht
    have hs := (PublicEpsilonUnboundedIota.restricted_sum q root t u).mp hr
    apply buildAtoms_restricted
    intro v hv
    have hm := Normalization.normalizeAtoms_mem q v _ hv
    rcases List.mem_append.mp hm with hm | hm
    · exact atoms_restricted q root _ (iht hc.1 hs.1) v hm
    · exact atoms_restricted q root _ (ihu hc.2 hs.2) v hm
  | theta k t ih =>
    intro ht hr
    have hc := BaseTransformation.theta_argument_check q k t ht
    cases k with
    | zero =>
      have hs := (PublicEpsilonUnboundedIota.restricted_theta_zero q root t).mp hr
      apply (PublicEpsilonUnboundedIota.restricted_theta_zero q root _).mpr
      refine ⟨?_, ih hc hs.2⟩
      have hv := (Normalization.normalize_checked q t hc).2.2
      change globalCollapse (base q) 0
        (denote q (Normalization.normalize q t)) < _
      rw [hv]
      exact hs.1
    | succ k =>
      exact (PublicEpsilonUnboundedIota.restricted_theta_succ q root k _).mpr
        (ih hc ((PublicEpsilonUnboundedIota.restricted_theta_succ q root k t).mp hr))

theorem subtract_restricted (q root c d : Nat)
    (hd : checkCode q d = true)
    (hr : Restricted q root (ThetaCourse.rawTree d)) :
    Restricted q root (Arithmetic.subtractTerm q c d) := by
  cases hl : Arithmetic.leCode q c d with
  | false => simpa only [Arithmetic.subtractTerm, hl, Bool.cond_false] using zero_restricted q root
  | true =>
    simp only [Arithmetic.subtractTerm, hl, Bool.cond_true]
    apply buildAtoms_restricted
    intro t ht
    have hm := Arithmetic.differenceWord_mem q c d t ht
    have hn := normalize_restricted q root (ThetaCourse.rawTree d)
      (Arithmetic.raw_checked _ d hd) hr
    have hc : Arithmetic.normalizedWord q d =
        Comparison.atoms (Normalization.normalize q (ThetaCourse.rawTree d)) := by
      simp only [Arithmetic.normalizedWord, Normalization.normalizeCode, hd,
        Bool.cond_true, Decomposition.word, ThetaCourse.rawTree_code]
    rw [hc] at hm
    exact atoms_restricted q root _ hn t hm

theorem atom_spec (q root k : Nat) (ha : PublicEpsilonUnboundedIota.rootCheck q root = true)
    (t : RelativeTerm Nat) (ht : check q (.theta (k + 1) t) = true)
    (hn : Comparison.Normal q t)
    (hr : Restricted q root (.theta (k + 1) t)) :
    check q (atomTerm q (.theta (k + 1) t)) = true ∧
      Comparison.Normal q (atomTerm q (.theta (k + 1) t)) ∧
      Restricted q root (atomTerm q (.theta (k + 1) t)) ∧
      0 < denote q (atomTerm q (.theta (k + 1) t)) ∧
      Ordinal.IsPrincipal (· + ·) (denote q (atomTerm q (.theta (k + 1) t))) ∧
      omegaSequence (base q) 1 *
          denote q (atomTerm q (.theta (k + 1) t)) =
        denote q (.theta (k + 1) t) := by
  have hq := source_checked q root ha
  have hc := FixedPoint.checked_theta_argument q (k + 1) t ht
  have hrt := (PublicEpsilonUnboundedIota.restricted_theta_succ q root k t).mp hr
  have hτ : base q = 1 ∨ Ordinal.omega0 ^ base q = base q :=
    Or.inr ((baseCheck_exact q).mp hq).2
  have hp := theta_principal q (k + 1) t ht
  cases k with
  | succ k =>
    have hk : (k + 1 + 1 == 1) = false := by
      apply Bool.eq_false_of_not_eq_true
      intro he
      have h := beq_iff_eq.mp he
      omega
    simp only [atomTerm, hk, Bool.cond_false]
    refine ⟨ht, hn, hr, hp.1, hp.2, ?_⟩
    exact principal_above_second_absorbs (base q) _ hp.2
      (((omegaSequence_strictMono (base q)).monotone (by omega : 2 ≤ k + 1 + 1)).trans
        (FixedPoint.checked_theta_range q (k + 1 + 1) t ht).1)
  | zero =>
    simp only [Nat.zero_add, atomTerm, beq_self_eq_true, Bool.cond_true]
    by_cases hl : t.outerSort ≤ 1
    · have hi : lowCheckCode q t.code = true := by
        simp only [lowCheckCode_code, lowCheck, hc, hl,
          decide_true, Bool.true_and]
      have hs := OmegaPowers.powerCode_spec q t.code hi
      have hx := Decomposition.input_tree q _ hs.2.1
      have hv : denote q (ThetaCourse.rawTree (OmegaPowers.powerCode q t.code)) =
          Ordinal.omega0 ^ denote q t := by
        rw [← Decomposition.input_value q _ hs.2.1, hs.2.2, interpretation_code]
      have hlow : (ThetaCourse.rawTree (OmegaPowers.powerCode q t.code)).outerSort ≤ 1 := by
        obtain ⟨u, he, hu⟩ := (lowCheckCode_exact q _).mp hs.1
        simpa only [← he, ThetaCourse.rawTree_code] using of_decide_eq_true (Bool.and_eq_true.mp hu).2
      have hb : denote q (ThetaCourse.rawTree (OmegaPowers.powerCode q t.code)) <
          interpretation q root := by
        rw [hv, ← PublicEpsilonUnboundedIota.beta_base q root ha]
        have hβ : denote q t < base (PublicEpsilonUnboundedIota.betaCode q root) := by
          rw [PublicEpsilonUnboundedIota.beta_base q root ha]
          exact PublicEpsilonUnboundedIota.OrderSupport.restricted_low_below q root ha t hc hrt hl
        exact (omegaPower_strictMono hβ).trans_eq
          ((baseCheck_exact _).mp (PublicEpsilonUnboundedIota.betaCode_baseCheck q root ha)).2
      have hxrest : Restricted q root (ThetaCourse.rawTree (OmegaPowers.powerCode q t.code)) := by
        intro u hu
        exact (Iota.Inverse.fullList_value_le_low q _ u hx.1 hx.2 hlow hu).trans_lt hb
      simp only [hl, decide_true, Bool.cond_true]
      refine ⟨hx.1, hx.2, hxrest, ?_, ?_, ?_⟩
      · rw [hv]; exact Ordinal.opow_pos _ Ordinal.omega0_pos
      · rw [hv]; exact Ordinal.isPrincipal_add_omega0_opow _
      · rw [hv]
        change omegaSequence (base q) 1 * Ordinal.omega0 ^ denote q t =
          globalCollapse (base q) 1 (denote q t)
        exact (theta_one_below_threshold (base q) hτ _
          (((denote_lt_iff_outerSort_le q t hc 1 (by omega)).mpr hl).trans (by
            calc
              omegaSequence (base q) 1 = omegaSequence (base q) 1 * 1 := (mul_one _).symm
              _ < omegaSequence (base q) 1 * Ordinal.omega0 :=
                mul_lt_mul_of_pos_left Ordinal.one_lt_omega0
                  (omegaSequence_isSuccLimit (base q) 0).bot_lt))).symm
    · have hbase : omegaSequence (base q) 1 ≤ denote q t := le_of_not_gt (by
        intro h
        exact hl ((denote_lt_iff_outerSort_le q t hc 1 (by omega)).mp h))
      have hthreshold := thresholdTerm_spec q hq
      cases hm : Comparison.less q t thresholdTerm with
      | true =>
        have hβ : denote q t < omegaSequence (base q) 1 * Ordinal.omega0 := by
          simpa only [hthreshold.2.2] using
            (Comparison.less_correct q t thresholdTerm hc hthreshold.1 hn hthreshold.2.1).mp hm
        have hbaseTerm := baseTerm_spec q hq
        have hbc : checkCode q baseTerm.code = true := by
          simpa only [checkCode_code] using hbaseTerm.1
        have htc : checkCode q t.code = true := by simpa only [checkCode_code] using hc
        have hs := Arithmetic.subtractTerm_spec q baseTerm.code t.code hbc htc
        have hscheck := Comparison.admitted_checked q _ hq _ hs.1
        have hv : denote q (Arithmetic.subtractTerm q baseTerm.code t.code) =
            denote q t - omegaSequence (base q) 1 := by
          simpa only [interpretation_code, hbaseTerm.2.2] using hs.2.2
        have hsort : (Arithmetic.subtractTerm q baseTerm.code t.code).outerSort ≤ 3 := by
          apply (denote_lt_iff_outerSort_le q _ hscheck 3 (by omega)).mp
          rw [hv]
          exact (Ordinal.sub_le_self _ _).trans_lt (FixedPoint.checked_theta_sort q 1 t ht)
        have hout := theta_checked q 1 _ hscheck hsort
        have houtp := theta_principal q 1 _ hout
        simp only [hl, decide_false, Bool.cond_false, hm, Bool.cond_true]
        refine ⟨hout, hs.2.1, (PublicEpsilonUnboundedIota.restricted_theta_succ q root 0 _).mpr
          (subtract_restricted q root baseTerm.code t.code htc (by
            simpa only [ThetaCourse.rawTree_code] using hrt)), houtp.1, houtp.2, ?_⟩
        change omegaSequence (base q) 1 * globalCollapse (base q) 1
          (denote q (Arithmetic.subtractTerm q baseTerm.code t.code)) =
          globalCollapse (base q) 1 (denote q t)
        rw [hv]
        exact theta_one_shifted_quotient (base q) hτ _ hbase hβ
      | false =>
        have hβ : omegaSequence (base q) 1 * Ordinal.omega0 ≤ denote q t := by
          rw [← hthreshold.2.2]
          apply le_of_not_gt
          intro h
          have he := (Comparison.less_correct q t thresholdTerm hc hthreshold.1 hn hthreshold.2.1).mpr h
          simp only [hm, Bool.false_eq_true] at he
        simp only [hl, decide_false, Bool.cond_false, hm, Bool.cond_false]
        refine ⟨ht, hn, hr, hp.1, hp.2, ?_⟩
        by_cases hβlow : denote q t < omegaSequence (base q) 2
        · exact theta_one_above_threshold (base q) hτ _ hβ hβlow
        · exact theta_one_high_absorbs q t ht (le_of_not_gt hβlow)

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.OmegaQuotient.Support
