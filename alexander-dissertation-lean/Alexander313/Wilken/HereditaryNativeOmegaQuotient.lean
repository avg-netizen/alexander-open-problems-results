import Alexander313.Wilken.HereditaryNativeOmegaQuotientSupport
import Alexander313.Wilken.HereditaryNativeLambda

/-!
# Actual native Omega-one quotients of the original high ANF

Low theta-one inputs are treated by the genuine corrected exponent law.
An input below Omega-one uses the existing actual low omega-power producer;
the middle interval removes Omega-one from the original argument; the upper
interval and higher atoms are retained only after proving left absorption.
The original full support restriction is derived for every constructed term.
Source-only candidates outside the current package checkpoint.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.OmegaQuotient

open NativePublicBridge (contextCode contextCode_checked)
open Iota (Restricted fullList)

theorem zero_restricted (s a : Nat) : Restricted s a Normalization.zeroTree := by
  intro u hu
  simp only [Normalization.zeroTree, fullList,
    RelativeTerm.PrincipalSupport.principalList, List.not_mem_nil] at hu

theorem atoms_restricted (s a : Nat) (t : RelativeTerm Nat)
    (hr : Restricted s a t) (u : RelativeTerm Nat) (hu : u ∈ Comparison.atoms t) :
    Restricted s a u := by
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
    have hs := (Iota.restricted_sum s a t v).mp hr
    rcases List.mem_append.mp hu with hu | hu
    · exact iht hs.1 hu
    · exact ihv hs.2 hu
  | theta k t ih =>
    intro hr hu
    exact (List.mem_singleton.mp hu).symm ▸ hr

theorem buildRev_restricted (s a : Nat) (as : List (RelativeTerm Nat))
    (hr : ∀ t ∈ as, Restricted s a t) : Restricted s a (Normalization.buildRev as) := by
  revert hr
  induction as with
  | nil => intro _; exact zero_restricted s a
  | cons t as ih =>
    intro hr
    exact (Iota.restricted_sum s a _ _).mpr
      ⟨ih (fun u hu => hr u (List.mem_cons_of_mem _ hu)), hr t List.mem_cons_self⟩

theorem buildAtoms_restricted (s a : Nat) (as : List (RelativeTerm Nat))
    (hr : ∀ t ∈ as, Restricted s a t) : Restricted s a (Normalization.buildAtoms as) :=
  buildRev_restricted s a as.reverse (fun t ht => hr t (List.mem_reverse.mp ht))

/-- Normalization retains each theta-zero VALUE and only selects original
atoms at sums; full original restriction is consequently a conclusion. -/
theorem normalize_restricted (s a : Nat) (t : RelativeTerm Nat)
    (ht : check (contextCode s) t = true) (hr : Restricted s a t) :
    Restricted s a (Normalization.normalize (contextCode s) t) := by
  revert ht hr
  induction t with
  | parameter p => intro ht hr; exact hr
  | sum t u iht ihu =>
    intro ht hr
    have hc := BaseTransformation.sum_checks (contextCode s) t u ht
    have hs := (Iota.restricted_sum s a t u).mp hr
    apply buildAtoms_restricted
    intro v hv
    have hm := Normalization.normalizeAtoms_mem (contextCode s) v _ hv
    rcases List.mem_append.mp hm with hm | hm
    · exact atoms_restricted s a _ (iht hc.1 hs.1) v hm
    · exact atoms_restricted s a _ (ihu hc.2 hs.2) v hm
  | theta k t ih =>
    intro ht hr
    have hc := BaseTransformation.theta_argument_check (contextCode s) k t ht
    cases k with
    | zero =>
      have hs := (Iota.restricted_theta_zero s a t).mp hr
      apply (Iota.restricted_theta_zero s a _).mpr
      refine ⟨?_, ih hc hs.2⟩
      have hv := (Normalization.normalize_checked (contextCode s) t hc).2.2
      change globalCollapse (base (contextCode s)) 0
        (denote (contextCode s) (Normalization.normalize (contextCode s) t)) < _
      rw [hv]
      exact hs.1
    | succ k =>
      exact (Iota.restricted_theta_succ s a k _).mpr
        (ih hc ((Iota.restricted_theta_succ s a k t).mp hr))

theorem subtract_restricted (s a c d : Nat)
    (hd : checkCode (contextCode s) d = true)
    (hr : Restricted s a (ThetaCourse.rawTree d)) :
    Restricted s a (Arithmetic.subtractTerm (contextCode s) c d) := by
  cases hl : Arithmetic.leCode (contextCode s) c d with
  | false => simpa only [Arithmetic.subtractTerm, hl, Bool.cond_false] using zero_restricted s a
  | true =>
    simp only [Arithmetic.subtractTerm, hl, Bool.cond_true]
    apply buildAtoms_restricted
    intro t ht
    have hm := Arithmetic.differenceWord_mem (contextCode s) c d t ht
    have hn := normalize_restricted s a (ThetaCourse.rawTree d)
      (Arithmetic.raw_checked _ d hd) hr
    have hc : Arithmetic.normalizedWord (contextCode s) d =
        Comparison.atoms (Normalization.normalize (contextCode s) (ThetaCourse.rawTree d)) := by
      simp only [Arithmetic.normalizedWord, Normalization.normalizeCode, hd,
        Bool.cond_true, Decomposition.word, ThetaCourse.rawTree_code]
    rw [hc] at hm
    exact atoms_restricted s a _ hn t hm

def baseTerm : RelativeTerm Nat := .theta 1 Normalization.zeroTree

def thresholdTerm : RelativeTerm Nat := .theta 1 (ThetaCourse.rawTree LogEndZero.unitCode)

theorem theta_checked (q k : Nat) (t : RelativeTerm Nat)
    (ht : check q t = true) (hs : t.outerSort ≤ k + 2) : check q (.theta k t) = true := by
  have hq := (Bool.and_eq_true.mp ht).1
  let n := SourceOne.PublicCodes.fragment (.theta k t)
  have hn : t.height ≤ n := (le_max_right (k + 1) t.height).trans
    (SourceOne.PublicCodes.height_le_fragment (.theta k t))
  have ha := Comparison.checked_admissible q n t ht hn
  have hk : k < n := by
    have h := (le_max_left (k + 1) t.height).trans
      (SourceOne.PublicCodes.height_le_fragment (.theta k t))
    omega
  exact Comparison.admitted_checked q n hq _
    ⟨ha.1, .theta (Nat.zero_le k) hk
      ((source_eval_lt_iff_outerSort_le (base q) parameters n t ha.2 (k + 2)
        (by omega)).mpr hs) ha.2⟩

theorem baseTerm_spec (q : Nat) (hq : baseCheck q = true) :
    check q baseTerm = true ∧ Comparison.Normal q baseTerm ∧
      denote q baseTerm = omegaSequence (base q) 1 := by
  refine ⟨theta_checked q 1 _ (Normalization.zeroTree_checked q hq) (by decide),
    Normalization.zeroTree_normal q, ?_⟩
  change globalCollapse (base q) 1 (denote q Normalization.zeroTree) = _
  rw [Normalization.zeroTree_denote]
  exact globalCollapse_zero (base q) (base_pos q hq) (BaseTransformation.base_additive q hq) 1

theorem thresholdTerm_spec (q : Nat) (hq : baseCheck q = true) :
    check q thresholdTerm = true ∧ Comparison.Normal q thresholdTerm ∧
      denote q thresholdTerm = omegaSequence (base q) 1 * Ordinal.omega0 := by
  have hu := Decomposition.input_tree q _ (LogEndZero.unitCode_accepted q hq)
  refine ⟨theta_checked q 1 _ hu.1 (by
    simp only [LogEndZero.unitCode, ThetaCourse.rawTree_code, RelativeTerm.outerSort]; omega),
    hu.2, ?_⟩
  change globalCollapse (base q) 1 (denote q (ThetaCourse.rawTree LogEndZero.unitCode)) = _
  rw [← Decomposition.input_value q _ (LogEndZero.unitCode_accepted q hq),
    LogEndZero.unitCode_value]
  exact theta_one_unit (base q) (Or.inr ((baseCheck_exact q).mp hq).2)

def atomTerm (s : Nat) : RelativeTerm Nat → RelativeTerm Nat
  | .theta k t => cond (k == 1)
      (cond (decide (t.outerSort ≤ 1))
        (ThetaCourse.rawTree (LowArithmetic.omegaCode s t.code))
        (cond (Comparison.less (contextCode s) t thresholdTerm)
          (.theta 1 (Arithmetic.subtractTerm (contextCode s) baseTerm.code t.code)) (.theta 1 t)))
      (.theta k t)
  | t => t


theorem theta_principal (q k : Nat) (t : RelativeTerm Nat)
    (ht : check q (.theta k t) = true) :
    0 < denote q (.theta k t) ∧ Ordinal.IsPrincipal (· + ·) (denote q (.theta k t)) := by
  have hq := (Bool.and_eq_true.mp ht).1
  have ha := NativeContext.checked_admissible q (.theta k t) ht
  have hp := Comparison.theta_pos_principal q _ k hq t ha
  rw [← denote_eq_finite q _ hq (.theta k t) ha.2] at hp
  exact hp

/-- A high theta-one input has a genuine epsilon value strictly above
Omega-one, by the actual finite high-collapse theorem on its real domain. -/
theorem theta_one_high_absorbs (q : Nat) (t : RelativeTerm Nat)
    (ht : check q (.theta 1 t) = true)
    (hhigh : omegaSequence (base q) 2 ≤ denote q t) :
    omegaSequence (base q) 1 * denote q (.theta 1 t) = denote q (.theta 1 t) := by
  have hq := (Bool.and_eq_true.mp ht).1
  have ha := NativeContext.checked_admissible q (.theta 1 t) ht
  have haa := Comparison.admitted_argument ha
  let n := SourceOne.PublicCodes.fragment (.theta 1 t)
  have hn : 1 < n := by
    cases ha.2 with
    | theta h0k hkn hsort ha => exact hkn
  have hh : omegaSequence (base q) 2 ≤ finiteDenote q n t := by
    rw [← denote_eq_finite q n hq t haa.2]
    exact hhigh
  have hp : sourceFiniteCollapse (base q) n 1 (finiteDenote q n t) <
      omegaSequence (base q) 2 := by
    rw [← denote_eq_finite q n hq (.theta 1 t) ha.2]
    exact (FixedPoint.checked_theta_range q 1 t ht).2
  have he := sourceFiniteCollapse_high_omegaPower_eq_self (base q) (base_pos q hq)
    n 1 hn (finiteDenote q n t) hh hp
  have hb := sourceFiniteCollapse_high_base_lt (base q) (base_pos q hq)
    n 1 hn (finiteDenote q n t) hh
  rw [denote_eq_finite q n hq (.theta 1 t) ha.2]
  exact epsilon_above_absorbs _ _ (omegaSequence_succ_omegaPower_eq_self (base q) 0) he hb

/-- ALL originally checked restricted high principal atoms receive an
actual checked Normal restricted quotient, with the true multiplication
identity. No quotient representation or output-admission premise is supplied. -/
theorem atom_spec (s a k : Nat) (ha : Iota.rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (contextCode s) (.theta (k + 1) t) = true)
    (hn : Comparison.Normal (contextCode s) t)
    (hr : Restricted s a (.theta (k + 1) t)) :
    check (contextCode s) (atomTerm s (.theta (k + 1) t)) = true ∧
      Comparison.Normal (contextCode s) (atomTerm s (.theta (k + 1) t)) ∧
      Restricted s a (atomTerm s (.theta (k + 1) t)) ∧
      0 < denote (contextCode s) (atomTerm s (.theta (k + 1) t)) ∧
      Ordinal.IsPrincipal (· + ·) (denote (contextCode s) (atomTerm s (.theta (k + 1) t))) ∧
      omegaSequence (base (contextCode s)) 1 *
          denote (contextCode s) (atomTerm s (.theta (k + 1) t)) =
        denote (contextCode s) (.theta (k + 1) t) := by
  let q := contextCode s
  have hq := contextCode_checked s
  have hc := FixedPoint.checked_theta_argument q (k + 1) t ht
  have hrt := (Iota.restricted_theta_succ s a k t).mp hr
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
    · have hi : LowArithmetic.lowInput s t.code = true := by
        simp only [LowArithmetic.lowInput, lowCheckCode_code, lowCheck, hc, hl,
          decide_true, Bool.true_and]
      have hs := LowArithmetic.omegaCode_spec s t.code hi
      have hx := Decomposition.input_tree q _ hs.2.1
      have hv : denote q (ThetaCourse.rawTree (LowArithmetic.omegaCode s t.code)) =
          Ordinal.omega0 ^ denote q t := by
        rw [← Decomposition.input_value q _ hs.2.1, hs.2.2, interpretation_code]
      have hlow : (ThetaCourse.rawTree (LowArithmetic.omegaCode s t.code)).outerSort ≤ 1 := by
        obtain ⟨u, he, hu⟩ := (lowCheckCode_exact q _).mp hs.1
        simpa only [← he, ThetaCourse.rawTree_code] using of_decide_eq_true (Bool.and_eq_true.mp hu).2
      have hb : denote q (ThetaCourse.rawTree (LowArithmetic.omegaCode s t.code)) <
          interpretation q a := by
        rw [hv, ← Iota.alpha_base s a ha]
        have hβ : denote q t < base (Iota.alphaCode s a) := by
          rw [Iota.alpha_base s a ha]
          exact Iota.restricted_low_below s a ha t hc hrt hl
        exact (omegaPower_strictMono hβ).trans_eq
          ((baseCheck_exact _).mp (Iota.alphaCode_baseCheck s a ha)).2
      have hxrest : Restricted s a (ThetaCourse.rawTree (LowArithmetic.omegaCode s t.code)) := by
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
        refine ⟨hout, hs.2.1, (Iota.restricted_theta_succ s a 0 _).mpr
          (subtract_restricted s a baseTerm.code t.code htc (by
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


private def atomNumeric (s : Nat) (t : RelativeTerm Nat) : RelativeTerm Nat :=
  let c := (t.code - 1).unpair.2
  let b := ThetaCourse.rawTree c.unpair.2
  cond (((t.code - 1).unpair.1 == 2) && (c.unpair.1 == 1))
    (cond (decide (b.outerSort ≤ 1))
      (ThetaCourse.rawTree (LowArithmetic.omegaCode s b.code))
      (cond (Comparison.less (contextCode s) b thresholdTerm)
        (.theta 1 (Arithmetic.subtractTerm (contextCode s) baseTerm.code b.code)) (.theta 1 b))) t

private theorem atomNumeric_eq (s : Nat) (t : RelativeTerm Nat) : atomNumeric s t = atomTerm s t := by
  cases t <;> simp [atomNumeric, atomTerm, RelativeTerm.code, Nat.unpair_pair,
    ThetaCourse.rawTree_code]

theorem atomTerm_primrec : Primrec₂ atomTerm := by
  have ht := Primrec.snd
  have hs := Primrec.fst
  have hc := Primrec.unpair.comp (Primrec.nat_sub.comp (code_primrec.comp ht) (Primrec.const 1))
  have hb := ThetaCourse.rawTree_primrec.comp
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp hc)))
  have hcontext := NativePublicBridge.contextCode_primrec.comp hs
  have htest := Primrec.and.comp
    (Primrec.beq.comp (Primrec.fst.comp hc) (Primrec.const 2))
    (Primrec.beq.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp hc))) (Primrec.const 1))
  have hsmall := (Primrec.nat_le.comp (outerSort_primrec.comp hb) (Primrec.const 1)).decide
  have hpower := ThetaCourse.rawTree_primrec.comp
    (LowArithmetic.omegaCode_primrec.comp hs (code_primrec.comp hb))
  have hless := Comparison.Effective.less_primrec.comp
    (hcontext.pair (hb.pair (Primrec.const thresholdTerm)))
  have hsub := Arithmetic.subtractTerm_primrec.comp
    (hcontext.pair ((Primrec.const baseTerm.code).pair (code_primrec.comp hb)))
  have hmiddle := theta_primrec.comp (Primrec.const 1) hsub
  have hunchanged := theta_primrec.comp (Primrec.const 1) hb
  have h := htest.cond (hsmall.cond hpower (hless.cond hmiddle hunchanged)) ht
  change Primrec (fun p : Nat × RelativeTerm Nat => atomNumeric p.1 p.2) at h
  simpa only [atomNumeric_eq] using h.to₂

def quotientWord (s c : Nat) : List (RelativeTerm Nat) :=
  (Decomposition.highWord 0 c).map (atomTerm s)

theorem quotientWord_primrec : Primrec₂ quotientWord := by
  have hlist := Decomposition.highWord_primrec.comp (Primrec.const 0) Primrec.snd
  have hmap : Primrec₂ (fun p : Nat × Nat => fun t : RelativeTerm Nat => atomTerm p.1 t) :=
    (atomTerm_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
  exact (Primrec.list_map hlist hmap).to₂

theorem high_atom_spec (s a c : Nat) (ha : Iota.rootCheck s a = true)
    (hc : Decomposition.inputCheck (contextCode s) c = true)
    (hr : Restricted s a (ThetaCourse.rawTree c)) (t : RelativeTerm Nat)
    (ht : t ∈ Decomposition.highWord 0 c) :
    check (contextCode s) (atomTerm s t) = true ∧
      Comparison.Normal (contextCode s) (atomTerm s t) ∧ Restricted s a (atomTerm s t) ∧
      0 < denote (contextCode s) (atomTerm s t) ∧
      Ordinal.IsPrincipal (· + ·) (denote (contextCode s) (atomTerm s t)) ∧
      omegaSequence (base (contextCode s)) 1 * denote (contextCode s) (atomTerm s t) =
        denote (contextCode s) t := by
  have hm := (Decomposition.highWord_mem 0 c t).mp ht
  have hs := (Decomposition.word_spec (contextCode s) c hc).1 t hm.1
  have htRest := atoms_restricted s a (ThetaCourse.rawTree c) hr t hm.1
  rcases Comparison.atoms_shape (ThetaCourse.rawTree c) t hm.1 with ⟨p, rfl⟩ | ⟨k, u, rfl⟩
  · have hb := hm.2
    simp only [Decomposition.above, RelativeTerm.outerSort, Nat.zero_add,
      decide_false, Bool.false_eq_true] at hb
  · cases k with
    | zero =>
      have hb := hm.2
      simp only [Decomposition.above, RelativeTerm.outerSort, Nat.zero_add,
        Nat.lt_irrefl, decide_false, Bool.false_eq_true] at hb
    | succ k => exact atom_spec s a k ha u hs.1 hs.2.1 htRest

private theorem quotient_map_normal (q : Nat) (Ω : Ordinal.{0}) (hΩ : 0 < Ω)
    (f : RelativeTerm Nat → RelativeTerm Nat) (as : List (RelativeTerm Nat))
    (hn : IsAdditiveNormalForm (as.map (denote q)))
    (hs : ∀ t ∈ as, 0 < denote q (f t) ∧ Ordinal.IsPrincipal (· + ·) (denote q (f t)) ∧
      Ω * denote q (f t) = denote q t) :
    IsAdditiveNormalForm ((as.map f).map (denote q)) := by
  revert hn hs
  induction as with
  | nil => intro hn hs; simpa only [List.map_nil] using hn
  | cons t as ih =>
    intro hn hs
    have hp := List.pairwise_cons.mp hn.2
    have htail : IsAdditiveNormalForm (as.map (denote q)) :=
      ⟨fun p hp' => hn.1 p (List.mem_cons_of_mem _ hp'), hp.2⟩
    have ht := hs t List.mem_cons_self
    have htnew := ih htail (fun u hu => hs u (List.mem_cons_of_mem _ hu))
    refine ⟨?_, List.pairwise_cons.mpr ⟨?_, htnew.2⟩⟩
    · intro p hp'
      rcases List.mem_cons.mp hp' with rfl | hp'
      · exact ⟨ht.1, ht.2.1⟩
      · exact htnew.1 p hp'
    · intro p hp'
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hp'
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
      have hvnew := hs v (List.mem_cons_of_mem _ hv)
      apply le_of_not_gt
      intro hbad
      have hb := mul_lt_mul_of_pos_left hbad hΩ
      rw [ht.2.2, hvnew.2.2] at hb
      exact (hp.1 (denote q v) (List.mem_map.mpr ⟨v, hv, rfl⟩)).not_lt hb

theorem quotientWord_normal (s a c : Nat) (ha : Iota.rootCheck s a = true)
    (hc : Decomposition.inputCheck (contextCode s) c = true)
    (hr : Restricted s a (ThetaCourse.rawTree c)) :
    IsAdditiveNormalForm ((quotientWord s c).map (denote (contextCode s))) := by
  apply quotient_map_normal (contextCode s) (omegaSequence (base (contextCode s)) 1)
    (omegaSequence_isSuccLimit (base (contextCode s)) 0).bot_lt (atomTerm s)
    (Decomposition.highWord 0 c) (Decomposition.words_normal (contextCode s) 0 c hc).1
  intro t ht
  have hs := high_atom_spec s a c ha hc hr t ht
  exact ⟨hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2⟩

def wordHeight : List (RelativeTerm Nat) → Nat
  | [] => 0
  | t :: as => max t.height (wordHeight as)

theorem wordHeight_mem (as : List (RelativeTerm Nat)) (t : RelativeTerm Nat)
    (ht : t ∈ as) : t.height ≤ wordHeight as := by
  revert ht
  induction as with
  | nil => intro ht; simp only [List.not_mem_nil] at ht
  | cons u as ih =>
    intro ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact le_max_left _ _
    · exact (ih ht).trans (le_max_right _ _)

theorem quotientWord_good (s a c : Nat) (ha : Iota.rootCheck s a = true)
    (hc : Decomposition.inputCheck (contextCode s) c = true)
    (hr : Restricted s a (ThetaCourse.rawTree c)) :
    Normalization.GoodAtoms (contextCode s) (wordHeight (quotientWord s c)) (quotientWord s c) := by
  intro t ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  have hs := high_atom_spec s a c ha hc hr u hu
  exact ⟨Comparison.checked_admissible _ _ _ hs.1 (wordHeight_mem _ _ ht),
    hs.2.1, hs.2.2.2.1, hs.2.2.2.2.1⟩

def quotientTerm (s c : Nat) : RelativeTerm Nat := Normalization.buildAtoms (quotientWord s c)

theorem quotientTerm_primrec : Primrec₂ quotientTerm :=
  Normalization.Effective.buildAtoms_primrec.comp₂ quotientWord_primrec

private theorem mul_principalSum_map (q : Nat) (Ω : Ordinal.{0})
    (f : RelativeTerm Nat → RelativeTerm Nat) (as : List (RelativeTerm Nat))
    (hs : ∀ t ∈ as, Ω * denote q (f t) = denote q t) :
    Ω * principalSum ((as.map f).map (denote q)) = principalSum (as.map (denote q)) := by
  revert hs
  induction as with
  | nil => intro _; simp only [List.map_nil, principalSum, mul_zero]
  | cons t as ih =>
    intro hs
    simp only [List.map_cons, principalSum, mul_add]
    rw [hs t List.mem_cons_self, ih (fun u hu => hs u (List.mem_cons_of_mem _ hu))]

/-- Every ORIGINAL Normal restricted source input yields its actual complete
high-part quotient. The original high part is the real ANF projection. -/
theorem quotientTerm_spec (s a c : Nat) (ha : Iota.rootCheck s a = true)
    (hc : Decomposition.inputCheck (contextCode s) c = true)
    (hr : Restricted s a (ThetaCourse.rawTree c)) :
    check (contextCode s) (quotientTerm s c) = true ∧
      Comparison.Normal (contextCode s) (quotientTerm s c) ∧ Restricted s a (quotientTerm s c) ∧
      omegaSequence (base (contextCode s)) 1 * denote (contextCode s) (quotientTerm s c) =
        interpretation (contextCode s) (Decomposition.highCode 0 c) := by
  have hg := quotientWord_good s a c ha hc hr
  have had := Normalization.buildAtoms_admissible (contextCode s) _ (contextCode_checked s) _ hg
  refine ⟨Comparison.admitted_checked _ _ (contextCode_checked s) _ had,
    Normalization.buildAtoms_normal _ _ _ hg (quotientWord_normal s a c ha hc hr), ?_, ?_⟩
  · apply buildAtoms_restricted
    intro t ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
    exact (high_atom_spec s a c ha hc hr u hu).2.2.1
  · rw [quotientTerm, Normalization.buildAtoms_denote]
    have hv := mul_principalSum_map (contextCode s) (omegaSequence (base (contextCode s)) 1)
      (atomTerm s) (Decomposition.highWord 0 c) (fun t ht =>
        (high_atom_spec s a c ha hc hr t ht).2.2.2.2.2)
    exact hv.trans (by
      simpa only [Decomposition.highCode, interpretation_code] using
        (Decomposition.parts_word_values (contextCode s) 0 c).1.symm)


def unitTest (q : Nat) (t : RelativeTerm Nat) : Bool :=
  Comparison.equal q t (ThetaCourse.rawTree LogEndZero.unitCode)

theorem unitTest_primrec : Primrec₂ unitTest :=
  (Comparison.Effective.equal_primrec.comp
    (Primrec.fst.pair (Primrec.snd.pair (Primrec.const (ThetaCourse.rawTree LogEndZero.unitCode))))).to₂

theorem unitTest_exact (q : Nat) (hq : baseCheck q = true) (t : RelativeTerm Nat)
    (ht : check q t = true) (hn : Comparison.Normal q t) :
    unitTest q t = true ↔ denote q t = 1 := by
  have hu := Decomposition.input_tree q _ (LogEndZero.unitCode_accepted q hq)
  have hv : denote q (ThetaCourse.rawTree LogEndZero.unitCode) = 1 := by
    rw [← Decomposition.input_value q _ (LogEndZero.unitCode_accepted q hq), LogEndZero.unitCode_value]
  simpa only [unitTest, hv] using Comparison.equal_correct q t _ ht hu.1 hn hu.2

/-- The finite right fold selects exactly unit or nonunit quotient atoms. -/
def selectUnits (units : Bool) (q : Nat) : List (RelativeTerm Nat) → List (RelativeTerm Nat)
  | [] => []
  | t :: as => cond (cond units (unitTest q t) (!unitTest q t))
      (t :: selectUnits units q as) (selectUnits units q as)

theorem selectUnits_primrec : Primrec
    (fun p : (Bool × Nat) × List (RelativeTerm Nat) => selectUnits p.1.1 p.1.2 p.2) := by
  have htest := unitTest_primrec.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
    (Primrec.fst.comp Primrec.snd)
  have hkeep := (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).cond htest (Primrec.not.comp htest)
  have hstep : Primrec₂ (fun p : (Bool × Nat) × List (RelativeTerm Nat) =>
      fun v : RelativeTerm Nat × List (RelativeTerm Nat) =>
        cond (cond p.1.1 (unitTest p.1.2 v.1) (!unitTest p.1.2 v.1)) (v.1 :: v.2) v.2) :=
    (hkeep.cond (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  have h := Primrec.list_foldr Primrec.snd (Primrec.const []) hstep
  have he : (fun p : (Bool × Nat) × List (RelativeTerm Nat) => p.2.foldr
      (fun t as => cond (cond p.1.1 (unitTest p.1.2 t) (!unitTest p.1.2 t)) (t :: as) as) []) =
      (fun p => selectUnits p.1.1 p.1.2 p.2) := by
    funext p
    rcases p with ⟨⟨units, q⟩, as⟩
    induction as with
    | nil => rfl
    | cons t as ih => simp only [List.foldr_cons, selectUnits, ih]
  rw [he] at h
  exact h

theorem selectUnits_filter (units : Bool) (q : Nat) (as : List (RelativeTerm Nat)) :
    selectUnits units q as = as.filter (fun t => cond units (unitTest q t) (!unitTest q t)) := by
  induction as with
  | nil => rfl
  | cons t as ih =>
    cases h : cond units (unitTest q t) (!unitTest q t) <;> simp [selectUnits, h, ih]

theorem selectUnits_mem (units : Bool) (q : Nat) (as : List (RelativeTerm Nat)) (t : RelativeTerm Nat) :
    t ∈ selectUnits units q as ↔ t ∈ as ∧ cond units (unitTest q t) (!unitTest q t) = true := by
  rw [selectUnits_filter, List.mem_filter]

private theorem selectUnits_all (q : Nat) (as : List (RelativeTerm Nat))
    (h : ∀ t ∈ as, unitTest q t = true) : selectUnits true q as = as ∧ selectUnits false q as = [] := by
  revert h
  induction as with
  | nil => intro h; exact ⟨rfl, rfl⟩
  | cons t as ih =>
    intro h
    have ht := h t List.mem_cons_self
    have hs := ih (fun u hu => h u (List.mem_cons_of_mem _ hu))
    constructor
    · simp only [selectUnits, ht, Bool.cond_true, Bool.cond_false, Bool.not_true, hs.1]
    · simp only [selectUnits, ht, Bool.cond_true, Bool.cond_false, Bool.not_true, hs.2]

private theorem unit_partition (q : Nat) (hq : baseCheck q = true) (as : List (RelativeTerm Nat))
    (hn : IsAdditiveNormalForm (as.map (denote q)))
    (hs : ∀ t ∈ as, check q t = true ∧ Comparison.Normal q t) :
    as = selectUnits false q as ++ selectUnits true q as := by
  revert hn hs
  induction as with
  | nil => intro hn hs; rfl
  | cons t as ih =>
    intro hn hs
    have hp := List.pairwise_cons.mp hn.2
    have htail : IsAdditiveNormalForm (as.map (denote q)) :=
      ⟨fun p hm => hn.1 p (List.mem_cons_of_mem _ hm), hp.2⟩
    have ht := hs t List.mem_cons_self
    cases he : unitTest q t with
    | false =>
      have hi := ih htail (fun u hu => hs u (List.mem_cons_of_mem _ hu))
      simp only [selectUnits, he, Bool.cond_false, Bool.not_false, Bool.cond_true,
        List.cons_append, ← hi]
    | true =>
      have hv := (unitTest_exact q hq t ht.1 ht.2).mp he
      have hall : ∀ u ∈ as, unitTest q u = true := by
        intro u hu
        have hus := hs u (List.mem_cons_of_mem _ hu)
        apply (unitTest_exact q hq u hus.1 hus.2).mpr
        have hupos := (hn.1 _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨u, hu, rfl⟩))).1
        have hule : denote q u ≤ 1 := by
          rw [← hv]
          exact hp.1 _ (List.mem_map.mpr ⟨u, hu, rfl⟩)
        exact le_antisymm hule (Order.one_le_iff_pos.mpr hupos)
      have hall' := selectUnits_all q as hall
      simp only [selectUnits, he, Bool.cond_true, Bool.not_true, Bool.cond_false,
        hall'.1, hall'.2, List.nil_append]

private theorem selected_normal (q : Nat) (units : Bool) (as : List (RelativeTerm Nat))
    (hn : IsAdditiveNormalForm (as.map (denote q))) :
    IsAdditiveNormalForm ((selectUnits units q as).map (denote q)) := by
  rw [selectUnits_filter]
  have hbase : (as.filter (fun t => cond units (unitTest q t) (!unitTest q t))).Sublist as :=
    List.filter_sublist
  have hsub := hbase.map (denote q)
  exact ⟨fun p hp => hn.1 p (hsub.subset hp), hn.2.sublist hsub⟩

private theorem unit_sum (q : Nat) (hq : baseCheck q = true) (as : List (RelativeTerm Nat))
    (hs : ∀ t ∈ as, check q t = true ∧ Comparison.Normal q t) :
    principalSum ((selectUnits true q as).map (denote q)) =
      ((selectUnits true q as).length : Ordinal.{0}) := by
  have hv : ∀ t ∈ selectUnits true q as, denote q t = 1 := by
    intro t ht
    have hm := (selectUnits_mem true q as t).mp ht
    exact (unitTest_exact q hq t (hs t hm.1).1 (hs t hm.1).2).mp hm.2
  generalize he : selectUnits true q as = bs at hv ⊢
  clear he
  revert hv
  induction bs with
  | nil => intro hv; simp only [List.map_nil, principalSum, List.length_nil, Nat.cast_zero]
  | cons t bs ih =>
    intro hv
    simp only [List.map_cons, principalSum, List.length_cons]
    rw [hv t List.mem_cons_self, ih (fun u hu => hv u (List.mem_cons_of_mem _ hu)),
      ← Nat.cast_one, ← Nat.cast_add]
    exact congrArg (fun n : Nat => (n : Ordinal.{0})) (Nat.add_comm 1 bs.length)

private theorem principalSum_limit_zero (as : List Ordinal.{0})
    (hs : ∀ p ∈ as, 1 < p ∧ Ordinal.IsPrincipal (· + ·) p) :
    principalSum as = 0 ∨ IsSuccLimit (principalSum as) := by
  revert hs
  induction as with
  | nil => intro hs; exact Or.inl rfl
  | cons p as ih =>
    intro hs
    have hp := hs p List.mem_cons_self
    have ht := ih (fun q hq => hs q (List.mem_cons_of_mem _ hq))
    apply Or.inr
    rcases ht with hz | hl
    · simpa only [principalSum, hz, add_zero] using Ordinal.isSuccLimit_of_isPrincipal_add hp.1 hp.2
    · exact Ordinal.isSuccLimit_add _ hl

def limitWord (s c : Nat) : List (RelativeTerm Nat) := selectUnits false (contextCode s) (quotientWord s c)
def finiteOffset (s c : Nat) : Nat := (selectUnits true (contextCode s) (quotientWord s c)).length
def limitTerm (s c : Nat) : RelativeTerm Nat := Normalization.buildAtoms (limitWord s c)

theorem limitWord_primrec : Primrec₂ limitWord :=
  (selectUnits_primrec.comp (((Primrec.const false).pair
    (NativePublicBridge.contextCode_primrec.comp Primrec.fst)).pair quotientWord_primrec)).to₂

theorem finiteOffset_primrec : Primrec₂ finiteOffset :=
  (Primrec.list_length.comp (selectUnits_primrec.comp
    (((Primrec.const true).pair (NativePublicBridge.contextCode_primrec.comp Primrec.fst)).pair
      quotientWord_primrec))).to₂

theorem limitTerm_primrec : Primrec₂ limitTerm :=
  Normalization.Effective.buildAtoms_primrec.comp₂ limitWord_primrec

/-- The literal original high part has the complete printed decomposition
Omega-one*(lambda+k), with lambda zero or a PROPER limit and finite k.
Both original lambda admission and the original source restriction are
derived by the actual finite ANF construction. -/
theorem limitTerm_spec (s a c : Nat) (ha : Iota.rootCheck s a = true)
    (hc : Decomposition.inputCheck (contextCode s) c = true)
    (hr : Restricted s a (ThetaCourse.rawTree c)) :
    check (contextCode s) (limitTerm s c) = true ∧
      Comparison.Normal (contextCode s) (limitTerm s c) ∧ Restricted s a (limitTerm s c) ∧
      (denote (contextCode s) (limitTerm s c) = 0 ∨ IsSuccLimit (denote (contextCode s) (limitTerm s c))) ∧
      omegaSequence (base (contextCode s)) 1 *
          (denote (contextCode s) (limitTerm s c) + (finiteOffset s c : Ordinal.{0})) =
        interpretation (contextCode s) (Decomposition.highCode 0 c) := by
  let q := contextCode s
  have hq := contextCode_checked s
  have hn := quotientWord_normal s a c ha hc hr
  have hs : ∀ t ∈ quotientWord s c, check q t = true ∧ Comparison.Normal q t := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
    have h := high_atom_spec s a c ha hc hr u hu
    exact ⟨h.1, h.2.1⟩
  have hg := quotientWord_good s a c ha hc hr
  have hmem : ∀ t ∈ limitWord s c, t ∈ quotientWord s c := fun t ht =>
    ((selectUnits_mem false q _ t).mp ht).1
  have hgood : Normalization.GoodAtoms q (wordHeight (quotientWord s c)) (limitWord s c) :=
    fun t ht => hg t (hmem t ht)
  have had := Normalization.buildAtoms_admissible q _ hq _ hgood
  refine ⟨Comparison.admitted_checked q _ hq _ had,
    Normalization.buildAtoms_normal q _ _ hgood (selected_normal q false _ hn), ?_, ?_, ?_⟩
  · apply buildAtoms_restricted
    intro t ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp (hmem t ht)
    exact (high_atom_spec s a c ha hc hr u hu).2.2.1
  · rw [limitTerm, Normalization.buildAtoms_denote]
    apply principalSum_limit_zero
    intro p hp
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hp
    have hm := (selectUnits_mem false q _ t).mp ht
    have hp' := hn.1 _ (List.mem_map.mpr ⟨t, hm.1, rfl⟩)
    refine ⟨lt_of_le_of_ne (Order.one_le_iff_pos.mpr hp'.1) ?_, hp'.2⟩
    intro he
    have hut := (unitTest_exact q hq t (hs t hm.1).1 (hs t hm.1).2).mpr he.symm
    have hnot := hm.2
    simp only [Bool.cond_false, hut, Bool.not_true, Bool.false_eq_true] at hnot
  · have hv : denote q (quotientTerm s c) = denote q (limitTerm s c) +
        (finiteOffset s c : Ordinal.{0}) := by
      rw [quotientTerm, Normalization.buildAtoms_denote,
        unit_partition q hq (quotientWord s c) hn hs, List.map_append, principalSum_append,
        unit_sum q hq _ hs]
      rw [limitTerm, Normalization.buildAtoms_denote]
      rfl
    rw [← hv]
    exact (quotientTerm_spec s a c ha hc hr).2.2.2


/-- The original high theta-zero root supplies EVERY coefficient caller. -/
theorem root_coefficient_spec (s a : Nat) (ha : Iota.rootCheck s a = true) :
    check (contextCode s) (limitTerm s (Lambda.argumentCode a)) = true ∧
      Comparison.Normal (contextCode s) (limitTerm s (Lambda.argumentCode a)) ∧
      Restricted s a (limitTerm s (Lambda.argumentCode a)) ∧
      (denote (contextCode s) (limitTerm s (Lambda.argumentCode a)) = 0 ∨
        IsSuccLimit (denote (contextCode s) (limitTerm s (Lambda.argumentCode a)))) ∧
      omegaSequence (base (contextCode s)) 1 *
          (denote (contextCode s) (limitTerm s (Lambda.argumentCode a)) +
            (finiteOffset s (Lambda.argumentCode a) : Ordinal.{0})) =
        interpretation (contextCode s) (Lambda.deltaCode a) :=
  limitTerm_spec s a _ ha (Lambda.argument_accepted s a ha) (Iota.argument_restricted s a ha)

def coefficientCode (s a : Nat) : Nat :=
  cond (Iota.rootCheck s a) (limitTerm s (Lambda.argumentCode a)).code 0

def coefficientOffset (s a : Nat) : Nat :=
  cond (Iota.rootCheck s a) (finiteOffset s (Lambda.argumentCode a)) 0

theorem coefficientCode_primrec : Primrec₂ coefficientCode :=
  (Iota.rootCheck_primrec.cond (code_primrec.comp
    (limitTerm_primrec.comp Primrec.fst (Localization.argumentCode_primrec.comp Primrec.snd)))
    (Primrec.const 0)).to₂

theorem coefficientOffset_primrec : Primrec₂ coefficientOffset :=
  (Iota.rootCheck_primrec.cond (finiteOffset_primrec.comp Primrec.fst
    (Localization.argumentCode_primrec.comp Primrec.snd)) (Primrec.const 0)).to₂

theorem coefficientCode_literal (s a : Nat) (ha : Iota.rootCheck s a = true) :
    coefficientCode s a = (limitTerm s (Lambda.argumentCode a)).code := by
  simp only [coefficientCode, ha, Bool.cond_true]

theorem coefficientOffset_literal (s a : Nat) (ha : Iota.rootCheck s a = true) :
    coefficientOffset s a = finiteOffset s (Lambda.argumentCode a) := by
  simp only [coefficientOffset, ha, Bool.cond_true]

theorem coefficientCode_accepted (s a : Nat) (ha : Iota.rootCheck s a = true) :
    Comparison.acceptedCode (contextCode s) (coefficientCode s a) = true := by
  have hs := root_coefficient_spec s a ha
  rw [coefficientCode_literal s a ha]
  exact (Comparison.acceptedCode_exact _ _).mpr
    ⟨by simpa only [checkCode_code] using hs.1,
      by simpa only [ThetaCourse.rawTree_code] using hs.2.1⟩

theorem coefficient_iota_input (s a : Nat) (ha : Iota.rootCheck s a = true) :
    Iota.inputCheck s a (coefficientCode s a) = true := by
  have hs := root_coefficient_spec s a ha
  apply (Iota.inputCheck_exact s a _).mpr
  refine ⟨ha, limitTerm s (Lambda.argumentCode a), coefficientCode_literal s a ha,
    hs.1, hs.2.1, ?_⟩
  exact (Iota.restricted_iff_sourceStar s a ha _ hs.1 hs.2.1).mp hs.2.2.1

/-- Full executing coefficient construction on the ORIGINAL root guard:
actual admission/Normal, proper-limit-or-zero lambda, and the exact source
Delta=Omega-one*(lambda+k) are proved for the literal numerical outputs. -/
theorem coefficientCode_spec (s a : Nat) (ha : Iota.rootCheck s a = true) :
    Comparison.acceptedCode (contextCode s) (coefficientCode s a) = true ∧
      Iota.inputCheck s a (coefficientCode s a) = true ∧
      (interpretation (contextCode s) (coefficientCode s a) = 0 ∨
        IsSuccLimit (interpretation (contextCode s) (coefficientCode s a))) ∧
      omegaSequence (base (contextCode s)) 1 *
          (interpretation (contextCode s) (coefficientCode s a) + (coefficientOffset s a : Ordinal.{0})) =
        interpretation (contextCode s) (Lambda.deltaCode a) := by
  have hs := root_coefficient_spec s a ha
  refine ⟨coefficientCode_accepted s a ha, coefficient_iota_input s a ha, ?_, ?_⟩
  · simpa only [coefficientCode_literal s a ha, interpretation_code] using hs.2.2.2.1
  · simpa only [coefficientCode_literal s a ha, coefficientOffset_literal s a ha,
      interpretation_code] using hs.2.2.2.2

theorem coefficientCode_rejected (s a : Nat) (ha : Iota.rootCheck s a = false) :
    coefficientCode s a = 0 ∧ coefficientOffset s a = 0 := by
  constructor
  · simp only [coefficientCode, ha, Bool.cond_false]
  · simp only [coefficientOffset, ha, Bool.cond_false]


/-- The coefficient belongs to the genuine source sort below Omega-two;
this follows from the actual multiplication equation and original root sort. -/
theorem coefficient_below_second (s a : Nat) (ha : Iota.rootCheck s a = true) :
    interpretation (contextCode s) (coefficientCode s a) <
      omegaSequence (base (contextCode s)) 2 := by
  have hs := coefficientCode_spec s a ha
  have hΩ : 1 ≤ omegaSequence (base (contextCode s)) 1 :=
    Order.one_le_iff_pos.mpr (omegaSequence_isSuccLimit (base (contextCode s)) 0).bot_lt
  have hle : interpretation (contextCode s) (coefficientCode s a) ≤
      interpretation (contextCode s) (Lambda.deltaCode a) := by
    calc
      interpretation (contextCode s) (coefficientCode s a) ≤
          interpretation (contextCode s) (coefficientCode s a) + (coefficientOffset s a : Ordinal.{0}) :=
        le_self_add
      _ = 1 * (interpretation (contextCode s) (coefficientCode s a) +
          (coefficientOffset s a : Ordinal.{0})) := (one_mul _).symm
      _ ≤ omegaSequence (base (contextCode s)) 1 *
          (interpretation (contextCode s) (coefficientCode s a) + (coefficientOffset s a : Ordinal.{0})) :=
        mul_le_mul' hΩ le_rfl
      _ = interpretation (contextCode s) (Lambda.deltaCode a) := hs.2.2.2
  have hd : interpretation (contextCode s) (Lambda.deltaCode a) ≤
      interpretation (contextCode s) (Lambda.argumentCode a) := by
    rw [Lambda.deltaCode,
      (Decomposition.parts_code_value (contextCode s) 0 (Lambda.argumentCode a)
        (Lambda.argument_accepted s a ha)).1]
    exact Ordinal.mul_div_le _ _
  obtain ⟨t, he, ht, hn, hhigh⟩ := (Iota.rootCheck_exact s a).mp ha
  have hsort : interpretation (contextCode s) (Lambda.argumentCode a) <
      omegaSequence (base (contextCode s)) 2 := by
    simpa only [Lambda.argumentCode, he, Localization.argumentCode_theta, interpretation_code] using
      FixedPoint.checked_theta_sort (contextCode s) 0 t ht
  exact (hle.trans hd).trans_lt hsort

/-- The literal actual iota coefficient is LOW and Normal at the actual
new alpha base. It is therefore a DERIVED caller for chi, finite addition,
and an actual arbitrary-coded-base LOW omega-power producer. -/
theorem coefficient_iota_low (s a : Nat) (ha : Iota.rootCheck s a = true) :
    lowCheckCode (Iota.alphaCode s a) (Iota.literalCode s a (coefficientCode s a)) = true ∧
      Comparison.acceptedCode (Iota.alphaCode s a) (Iota.literalCode s a (coefficientCode s a)) = true := by
  let t := limitTerm s (Lambda.argumentCode a)
  have hs := root_coefficient_spec s a ha
  have hi := coefficient_iota_input s a ha
  have hsort : t.outerSort ≤ 2 :=
    (denote_lt_iff_outerSort_le (contextCode s) t hs.1 2 (by omega)).mp (by
      simpa only [coefficientCode_literal s a ha, interpretation_code] using coefficient_below_second s a ha)
  have htransform := Iota.transform_checked s a ha t hs.1 hs.2.2.1
  have hnormal := Iota.transform_normal s a ha t hs.1 hs.2.1 hs.2.2.1
  have houter : (Iota.transform s a t).outerSort ≤ 1 := by
    have h := Iota.transform_outerSort s a ha t hs.1 hs.2.2.1
    omega
  have he : Iota.literalCode s a (coefficientCode s a) = (Iota.transform s a t).code := by
    simp only [Iota.literalCode, hi, Bool.cond_true, coefficientCode_literal s a ha, Iota.stateCode_code]
  rw [he]
  refine ⟨?_, (Comparison.acceptedCode_exact _ _).mpr
    ⟨by simpa only [checkCode_code] using htransform,
      by simpa only [ThetaCourse.rawTree_code] using hnormal⟩⟩
  simp only [lowCheckCode_code, lowCheck, htransform, houter, decide_true, Bool.true_and]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.OmegaQuotient
