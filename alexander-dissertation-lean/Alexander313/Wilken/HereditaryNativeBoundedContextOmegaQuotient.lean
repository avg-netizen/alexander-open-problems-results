import Alexander313.Wilken.HereditaryNativeBoundedContextOmegaQuotientSupport
import Alexander313.Wilken.HereditaryNativeBoundedContextIotaOrderInduction

/-!
# Actual complete Omega-one quotient in the bounded intermediate source

The genuine source is the computed outer alpha. Every original high ANF
atom receives its real admitted Normal quotient, using ANY-coded-epsilon
native omega power for LOW theta-one arguments and the complete corrected
middle/upper threshold laws. Actual original restriction and the finite
unit suffix derive lambda-zero-or-limit and Delta=Omega-one*(lambda+k).
The actual intermediate iota coefficient caller is then constructed.
No quotient, source/target admission or Normal oracle is assumed. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.BoundedContextIota.OmegaQuotient

open Support
open BoundedContextIota (Restricted fullList)
open Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.OmegaQuotient
  (baseTerm thresholdTerm theta_checked baseTerm_spec thresholdTerm_spec theta_principal
   theta_one_high_absorbs wordHeight wordHeight_mem unitTest unitTest_exact selectUnits
   selectUnits_primrec selectUnits_mem selectUnits_filter theta_one_below_threshold
   theta_one_shifted_quotient theta_one_above_threshold principal_above_second_absorbs)

def argumentCode (root : Nat) : Nat := Localization.argumentCode root

def deltaCode (root : Nat) : Nat := Decomposition.highCode 0 (argumentCode root)

theorem argumentCode_primrec : Primrec argumentCode := Localization.argumentCode_primrec

theorem deltaCode_primrec : Primrec deltaCode :=
  Decomposition.highCode_primrec.comp (Primrec.const 0) argumentCode_primrec

theorem argument_accepted (s a root : Nat) (ha : rootCheck s a root = true) :
    Decomposition.inputCheck (sourceCode s a) (argumentCode root) = true := by
  obtain ⟨_, ⟨t, he, ht, hn, hh⟩, _⟩ := (rootCheck_exact s a root).mp ha
  apply (Decomposition.inputCheck_exact _ _).mpr
  exact ⟨by simpa only [argumentCode, he, Localization.argumentCode_theta, checkCode_code] using
    BaseTransformation.theta_argument_check _ 0 t ht,
    by simpa only [argumentCode, he, Localization.argumentCode_theta, ThetaCourse.rawTree_code] using hn⟩

theorem zero_restricted (s a root : Nat) : Restricted s a root Normalization.zeroTree := by
  intro u hu
  simp only [Normalization.zeroTree, fullList,
    RelativeTerm.PrincipalSupport.principalList, List.not_mem_nil] at hu

theorem atoms_restricted (s a root : Nat) (t : RelativeTerm Nat)
    (hr : Restricted s a root t) (u : RelativeTerm Nat) (hu : u ∈ Comparison.atoms t) :
    Restricted s a root u := by
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
    have hs := (BoundedContextIota.restricted_sum s a root t v).mp hr
    rcases List.mem_append.mp hu with hu | hu
    · exact iht hs.1 hu
    · exact ihv hs.2 hu
  | theta k t ih =>
    intro hr hu
    exact (List.mem_singleton.mp hu).symm ▸ hr

theorem buildRev_restricted (s a root : Nat) (as : List (RelativeTerm Nat))
    (hr : ∀ t ∈ as, Restricted s a root t) : Restricted s a root (Normalization.buildRev as) := by
  revert hr
  induction as with
  | nil => intro _; exact zero_restricted s a root
  | cons t as ih =>
    intro hr
    exact (BoundedContextIota.restricted_sum s a root _ _).mpr
      ⟨ih (fun u hu => hr u (List.mem_cons_of_mem _ hu)), hr t List.mem_cons_self⟩

theorem buildAtoms_restricted (s a root : Nat) (as : List (RelativeTerm Nat))
    (hr : ∀ t ∈ as, Restricted s a root t) : Restricted s a root (Normalization.buildAtoms as) :=
  buildRev_restricted s a root as.reverse (fun t ht => hr t (List.mem_reverse.mp ht))

theorem normalize_restricted (s a root : Nat) (t : RelativeTerm Nat)
    (ht : check (sourceCode s a) t = true) (hr : Restricted s a root t) :
    Restricted s a root (Normalization.normalize (sourceCode s a) t) := by
  revert ht hr
  induction t with
  | parameter p => intro ht hr; exact hr
  | sum t u iht ihu =>
    intro ht hr
    have hc := BaseTransformation.sum_checks (sourceCode s a) t u ht
    have hs := (BoundedContextIota.restricted_sum s a root t u).mp hr
    apply buildAtoms_restricted
    intro v hv
    have hm := Normalization.normalizeAtoms_mem (sourceCode s a) v _ hv
    rcases List.mem_append.mp hm with hm | hm
    · exact atoms_restricted s a root _ (iht hc.1 hs.1) v hm
    · exact atoms_restricted s a root _ (ihu hc.2 hs.2) v hm
  | theta k t ih =>
    intro ht hr
    have hc := BaseTransformation.theta_argument_check (sourceCode s a) k t ht
    cases k with
    | zero =>
      have hs := (BoundedContextIota.restricted_theta_zero s a root t).mp hr
      apply (BoundedContextIota.restricted_theta_zero s a root _).mpr
      refine ⟨?_, ih hc hs.2⟩
      have hv := (Normalization.normalize_checked (sourceCode s a) t hc).2.2
      change globalCollapse (base (sourceCode s a)) 0
        (denote (sourceCode s a) (Normalization.normalize (sourceCode s a) t)) < _
      rw [hv]
      exact hs.1
    | succ k =>
      exact (BoundedContextIota.restricted_theta_succ s a root k _).mpr
        (ih hc ((BoundedContextIota.restricted_theta_succ s a root k t).mp hr))

theorem subtract_restricted (s a root c d : Nat)
    (hd : checkCode (sourceCode s a) d = true)
    (hr : Restricted s a root (ThetaCourse.rawTree d)) :
    Restricted s a root (Arithmetic.subtractTerm (sourceCode s a) c d) := by
  cases hl : Arithmetic.leCode (sourceCode s a) c d with
  | false => simpa only [Arithmetic.subtractTerm, hl, Bool.cond_false] using zero_restricted s a root
  | true =>
    simp only [Arithmetic.subtractTerm, hl, Bool.cond_true]
    apply buildAtoms_restricted
    intro t ht
    have hm := Arithmetic.differenceWord_mem (sourceCode s a) c d t ht
    have hn := normalize_restricted s a root (ThetaCourse.rawTree d)
      (Arithmetic.raw_checked _ d hd) hr
    have hc : Arithmetic.normalizedWord (sourceCode s a) d =
        Comparison.atoms (Normalization.normalize (sourceCode s a) (ThetaCourse.rawTree d)) := by
      simp only [Arithmetic.normalizedWord, Normalization.normalizeCode, hd,
        Bool.cond_true, Decomposition.word, ThetaCourse.rawTree_code]
    rw [hc] at hm
    exact atoms_restricted s a root _ hn t hm

def atomTerm (q : Nat) : RelativeTerm Nat → RelativeTerm Nat
  | .theta k t => cond (k == 1)
      (cond (decide (t.outerSort ≤ 1))
        (ThetaCourse.rawTree (OmegaPowers.powerCode q t.code))
        (cond (Comparison.less q t thresholdTerm)
          (.theta 1 (Arithmetic.subtractTerm q baseTerm.code t.code)) (.theta 1 t)))
      (.theta k t)
  | t => t

theorem atom_spec (s a root k : Nat) (ha : BoundedContextIota.rootCheck s a root = true)
    (t : RelativeTerm Nat) (ht : check (sourceCode s a) (.theta (k + 1) t) = true)
    (hn : Comparison.Normal (sourceCode s a) t)
    (hr : Restricted s a root (.theta (k + 1) t)) :
    check (sourceCode s a) (atomTerm (sourceCode s a) (.theta (k + 1) t)) = true ∧
      Comparison.Normal (sourceCode s a) (atomTerm (sourceCode s a) (.theta (k + 1) t)) ∧
      Restricted s a root (atomTerm (sourceCode s a) (.theta (k + 1) t)) ∧
      0 < denote (sourceCode s a) (atomTerm (sourceCode s a) (.theta (k + 1) t)) ∧
      Ordinal.IsPrincipal (· + ·) (denote (sourceCode s a) (atomTerm (sourceCode s a) (.theta (k + 1) t))) ∧
      omegaSequence (base (sourceCode s a)) 1 *
          denote (sourceCode s a) (atomTerm (sourceCode s a) (.theta (k + 1) t)) =
        denote (sourceCode s a) (.theta (k + 1) t) := by
  let q := sourceCode s a
  have hq := sourceCode_checked s a root ha
  have hc := FixedPoint.checked_theta_argument q (k + 1) t ht
  have hrt := (BoundedContextIota.restricted_theta_succ s a root k t).mp hr
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
        rw [hv, ← BoundedContextIota.beta_base s a root ha]
        have hβ : denote q t < base (BoundedContextIota.betaCode s a root) := by
          rw [BoundedContextIota.beta_base s a root ha]
          exact BoundedContextIota.OrderSupport.restricted_low_below s a root ha t hc hrt hl
        exact (omegaPower_strictMono hβ).trans_eq
          ((baseCheck_exact _).mp (BoundedContextIota.betaCode_baseCheck s a root ha)).2
      have hxrest : Restricted s a root (ThetaCourse.rawTree (OmegaPowers.powerCode q t.code)) := by
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
        refine ⟨hout, hs.2.1, (BoundedContextIota.restricted_theta_succ s a root 0 _).mpr
          (subtract_restricted s a root baseTerm.code t.code htc (by
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

private def atomNumeric (q : Nat) (t : RelativeTerm Nat) : RelativeTerm Nat :=
  let c := (t.code - 1).unpair.2
  let b := ThetaCourse.rawTree c.unpair.2
  cond (((t.code - 1).unpair.1 == 2) && (c.unpair.1 == 1))
    (cond (decide (b.outerSort ≤ 1))
      (ThetaCourse.rawTree (OmegaPowers.powerCode q b.code))
      (cond (Comparison.less (q) b thresholdTerm)
        (.theta 1 (Arithmetic.subtractTerm (q) baseTerm.code b.code)) (.theta 1 b))) t

private theorem atomNumeric_eq (q : Nat) (t : RelativeTerm Nat) : atomNumeric q t = atomTerm q t := by
  cases t <;> simp [atomNumeric, atomTerm, RelativeTerm.code, Nat.unpair_pair,
    ThetaCourse.rawTree_code]

theorem atomTerm_primrec : Primrec₂ atomTerm := by
  have ht := Primrec.snd
  have hq := Primrec.fst
  have hc := Primrec.unpair.comp (Primrec.nat_sub.comp (code_primrec.comp ht) (Primrec.const 1))
  have hb := ThetaCourse.rawTree_primrec.comp
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp hc)))
  have hcontext := hq
  have htest := Primrec.and.comp
    (Primrec.beq.comp (Primrec.fst.comp hc) (Primrec.const 2))
    (Primrec.beq.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp hc))) (Primrec.const 1))
  have hsmall := (Primrec.nat_le.comp (outerSort_primrec.comp hb) (Primrec.const 1)).decide
  have hpower := ThetaCourse.rawTree_primrec.comp
    (OmegaPowers.powerCode_primrec.comp hq (code_primrec.comp hb))
  have hless := Comparison.Effective.less_primrec.comp
    (hcontext.pair (hb.pair (Primrec.const thresholdTerm)))
  have hsub := Arithmetic.subtractTerm_primrec.comp
    (hcontext.pair ((Primrec.const baseTerm.code).pair (code_primrec.comp hb)))
  have hmiddle := theta_primrec.comp (Primrec.const 1) hsub
  have hunchanged := theta_primrec.comp (Primrec.const 1) hb
  have h := htest.cond (hsmall.cond hpower (hless.cond hmiddle hunchanged)) ht
  change Primrec (fun p : Nat × RelativeTerm Nat => atomNumeric p.1 p.2) at h
  simpa only [atomNumeric_eq] using h.to₂

def quotientWord (q c : Nat) : List (RelativeTerm Nat) :=
  (Decomposition.highWord 0 c).map (atomTerm q)

theorem quotientWord_primrec : Primrec₂ quotientWord := by
  have hlist := Decomposition.highWord_primrec.comp (Primrec.const 0) Primrec.snd
  have hmap : Primrec₂ (fun p : Nat × Nat => fun t : RelativeTerm Nat => atomTerm p.1 t) :=
    (atomTerm_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
  exact (Primrec.list_map hlist hmap).to₂

theorem high_atom_spec (s a root c : Nat) (ha : BoundedContextIota.rootCheck s a root = true)
    (hc : Decomposition.inputCheck (sourceCode s a) c = true)
    (hr : Restricted s a root (ThetaCourse.rawTree c)) (t : RelativeTerm Nat)
    (ht : t ∈ Decomposition.highWord 0 c) :
    check (sourceCode s a) (atomTerm (sourceCode s a) t) = true ∧
      Comparison.Normal (sourceCode s a) (atomTerm (sourceCode s a) t) ∧ Restricted s a root (atomTerm (sourceCode s a) t) ∧
      0 < denote (sourceCode s a) (atomTerm (sourceCode s a) t) ∧
      Ordinal.IsPrincipal (· + ·) (denote (sourceCode s a) (atomTerm (sourceCode s a) t)) ∧
      omegaSequence (base (sourceCode s a)) 1 * denote (sourceCode s a) (atomTerm (sourceCode s a) t) =
        denote (sourceCode s a) t := by
  have hm := (Decomposition.highWord_mem 0 c t).mp ht
  have hs := (Decomposition.word_spec (sourceCode s a) c hc).1 t hm.1
  have htRest := atoms_restricted s a root (ThetaCourse.rawTree c) hr t hm.1
  rcases Comparison.atoms_shape (ThetaCourse.rawTree c) t hm.1 with ⟨p, rfl⟩ | ⟨k, u, rfl⟩
  · have hb := hm.2
    simp only [Decomposition.above, RelativeTerm.outerSort, Nat.zero_add,
      decide_false, Bool.false_eq_true] at hb
  · cases k with
    | zero =>
      have hb := hm.2
      simp only [Decomposition.above, RelativeTerm.outerSort, Nat.zero_add,
        Nat.lt_irrefl, decide_false, Bool.false_eq_true] at hb
    | succ k => exact atom_spec s a root k ha u hs.1 hs.2.1 htRest

theorem quotientWord_normal (s a root c : Nat) (ha : BoundedContextIota.rootCheck s a root = true)
    (hc : Decomposition.inputCheck (sourceCode s a) c = true)
    (hr : Restricted s a root (ThetaCourse.rawTree c)) :
    IsAdditiveNormalForm ((quotientWord (sourceCode s a) c).map (denote (sourceCode s a))) := by
  apply quotient_map_normal (sourceCode s a) (omegaSequence (base (sourceCode s a)) 1)
    (omegaSequence_isSuccLimit (base (sourceCode s a)) 0).bot_lt (atomTerm (sourceCode s a))
    (Decomposition.highWord 0 c) (Decomposition.words_normal (sourceCode s a) 0 c hc).1
  intro t ht
  have hs := high_atom_spec s a root c ha hc hr t ht
  exact ⟨hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2⟩

theorem quotientWord_good (s a root c : Nat) (ha : BoundedContextIota.rootCheck s a root = true)
    (hc : Decomposition.inputCheck (sourceCode s a) c = true)
    (hr : Restricted s a root (ThetaCourse.rawTree c)) :
    Normalization.GoodAtoms (sourceCode s a) (wordHeight (quotientWord (sourceCode s a) c)) (quotientWord (sourceCode s a) c) := by
  intro t ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  have hs := high_atom_spec s a root c ha hc hr u hu
  exact ⟨Comparison.checked_admissible _ _ _ hs.1 (wordHeight_mem _ _ ht),
    hs.2.1, hs.2.2.2.1, hs.2.2.2.2.1⟩

def quotientTerm (q c : Nat) : RelativeTerm Nat := Normalization.buildAtoms (quotientWord q c)

theorem quotientTerm_primrec : Primrec₂ quotientTerm :=
  Normalization.Effective.buildAtoms_primrec.comp₂ quotientWord_primrec

theorem quotientTerm_spec (s a root c : Nat) (ha : BoundedContextIota.rootCheck s a root = true)
    (hc : Decomposition.inputCheck (sourceCode s a) c = true)
    (hr : Restricted s a root (ThetaCourse.rawTree c)) :
    check (sourceCode s a) (quotientTerm (sourceCode s a) c) = true ∧
      Comparison.Normal (sourceCode s a) (quotientTerm (sourceCode s a) c) ∧ Restricted s a root (quotientTerm (sourceCode s a) c) ∧
      omegaSequence (base (sourceCode s a)) 1 * denote (sourceCode s a) (quotientTerm (sourceCode s a) c) =
        interpretation (sourceCode s a) (Decomposition.highCode 0 c) := by
  have hg := quotientWord_good s a root c ha hc hr
  have had := Normalization.buildAtoms_admissible (sourceCode s a) _ (sourceCode_checked s a root ha) _ hg
  refine ⟨Comparison.admitted_checked _ _ (sourceCode_checked s a root ha) _ had,
    Normalization.buildAtoms_normal _ _ _ hg (quotientWord_normal s a root c ha hc hr), ?_, ?_⟩
  · apply buildAtoms_restricted
    intro t ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
    exact (high_atom_spec s a root c ha hc hr u hu).2.2.1
  · rw [quotientTerm, Normalization.buildAtoms_denote]
    have hv := mul_principalSum_map (sourceCode s a) (omegaSequence (base (sourceCode s a)) 1)
      (atomTerm (sourceCode s a)) (Decomposition.highWord 0 c) (fun t ht =>
        (high_atom_spec s a root c ha hc hr t ht).2.2.2.2.2)
    exact hv.trans (by
      simpa only [Decomposition.highCode, interpretation_code] using
        (Decomposition.parts_word_values (sourceCode s a) 0 c).1.symm)

def limitWord (q c : Nat) : List (RelativeTerm Nat) := selectUnits false q (quotientWord q c)

def finiteOffset (q c : Nat) : Nat := (selectUnits true q (quotientWord q c)).length

def limitTerm (q c : Nat) : RelativeTerm Nat := Normalization.buildAtoms (limitWord q c)

theorem limitWord_primrec : Primrec₂ limitWord :=
  (selectUnits_primrec.comp (((Primrec.const false).pair Primrec.fst).pair quotientWord_primrec)).to₂

theorem finiteOffset_primrec : Primrec₂ finiteOffset :=
  (Primrec.list_length.comp (selectUnits_primrec.comp
    (((Primrec.const true).pair Primrec.fst).pair quotientWord_primrec))).to₂

theorem limitTerm_primrec : Primrec₂ limitTerm :=
  Normalization.Effective.buildAtoms_primrec.comp₂ limitWord_primrec

theorem limitTerm_spec (s a root c : Nat) (ha : BoundedContextIota.rootCheck s a root = true)
    (hc : Decomposition.inputCheck (sourceCode s a) c = true)
    (hr : Restricted s a root (ThetaCourse.rawTree c)) :
    check (sourceCode s a) (limitTerm (sourceCode s a) c) = true ∧
      Comparison.Normal (sourceCode s a) (limitTerm (sourceCode s a) c) ∧ Restricted s a root (limitTerm (sourceCode s a) c) ∧
      (denote (sourceCode s a) (limitTerm (sourceCode s a) c) = 0 ∨ IsSuccLimit (denote (sourceCode s a) (limitTerm (sourceCode s a) c))) ∧
      omegaSequence (base (sourceCode s a)) 1 *
          (denote (sourceCode s a) (limitTerm (sourceCode s a) c) + (finiteOffset (sourceCode s a) c : Ordinal.{0})) =
        interpretation (sourceCode s a) (Decomposition.highCode 0 c) := by
  let q := sourceCode s a
  have hq := sourceCode_checked s a root ha
  have hn := quotientWord_normal s a root c ha hc hr
  have hs : ∀ t ∈ quotientWord (sourceCode s a) c, check q t = true ∧ Comparison.Normal q t := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
    have h := high_atom_spec s a root c ha hc hr u hu
    exact ⟨h.1, h.2.1⟩
  have hg := quotientWord_good s a root c ha hc hr
  have hmem : ∀ t ∈ limitWord (sourceCode s a) c, t ∈ quotientWord (sourceCode s a) c := fun t ht =>
    ((selectUnits_mem false q _ t).mp ht).1
  have hgood : Normalization.GoodAtoms q (wordHeight (quotientWord (sourceCode s a) c)) (limitWord (sourceCode s a) c) :=
    fun t ht => hg t (hmem t ht)
  have had := Normalization.buildAtoms_admissible q _ hq _ hgood
  refine ⟨Comparison.admitted_checked q _ hq _ had,
    Normalization.buildAtoms_normal q _ _ hgood (selected_normal q false _ hn), ?_, ?_, ?_⟩
  · apply buildAtoms_restricted
    intro t ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp (hmem t ht)
    exact (high_atom_spec s a root c ha hc hr u hu).2.2.1
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
  · have hv : denote q (quotientTerm (sourceCode s a) c) = denote q (limitTerm (sourceCode s a) c) +
        (finiteOffset (sourceCode s a) c : Ordinal.{0}) := by
      rw [quotientTerm, Normalization.buildAtoms_denote,
        unit_partition q hq (quotientWord (sourceCode s a) c) hn hs, List.map_append, principalSum_append,
        unit_sum q hq _ hs]
      rw [limitTerm, Normalization.buildAtoms_denote]
      rfl
    rw [← hv]
    exact (quotientTerm_spec s a root c ha hc hr).2.2.2

theorem root_coefficient_spec (s a root : Nat) (ha : BoundedContextIota.rootCheck s a root = true) :
    check (sourceCode s a) (limitTerm (sourceCode s a) (argumentCode root)) = true ∧
      Comparison.Normal (sourceCode s a) (limitTerm (sourceCode s a) (argumentCode root)) ∧
      Restricted s a root (limitTerm (sourceCode s a) (argumentCode root)) ∧
      (denote (sourceCode s a) (limitTerm (sourceCode s a) (argumentCode root)) = 0 ∨
        IsSuccLimit (denote (sourceCode s a) (limitTerm (sourceCode s a) (argumentCode root)))) ∧
      omegaSequence (base (sourceCode s a)) 1 *
          (denote (sourceCode s a) (limitTerm (sourceCode s a) (argumentCode root)) +
            (finiteOffset (sourceCode s a) (argumentCode root) : Ordinal.{0})) =
        interpretation (sourceCode s a) (deltaCode root) :=
  limitTerm_spec s a root _ ha (argument_accepted s a root ha) (BoundedContextIota.argument_restricted s a root ha)

def coefficientCode (s a root : Nat) : Nat :=
  cond (rootCheck s a root) (limitTerm (sourceCode s a) (argumentCode root)).code 0

def coefficientOffset (s a root : Nat) : Nat :=
  cond (rootCheck s a root) (finiteOffset (sourceCode s a) (argumentCode root)) 0

theorem coefficientCode_primrec : Primrec (fun p : Context => coefficientCode p.1.1 p.1.2 p.2) :=
  rootCheck_primrec.cond (code_primrec.comp (limitTerm_primrec.comp
    (sourceCode_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst))
    (argumentCode_primrec.comp Primrec.snd))) (Primrec.const 0)

theorem coefficientOffset_primrec : Primrec (fun p : Context => coefficientOffset p.1.1 p.1.2 p.2) :=
  rootCheck_primrec.cond (finiteOffset_primrec.comp
    (sourceCode_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst))
    (argumentCode_primrec.comp Primrec.snd)) (Primrec.const 0)

theorem coefficientCode_literal (s a root : Nat) (ha : BoundedContextIota.rootCheck s a root = true) :
    coefficientCode s a root = (limitTerm (sourceCode s a) (argumentCode root)).code := by
  simp only [coefficientCode, ha, Bool.cond_true]

theorem coefficientOffset_literal (s a root : Nat) (ha : BoundedContextIota.rootCheck s a root = true) :
    coefficientOffset s a root = finiteOffset (sourceCode s a) (argumentCode root) := by
  simp only [coefficientOffset, ha, Bool.cond_true]

theorem coefficientCode_accepted (s a root : Nat) (ha : BoundedContextIota.rootCheck s a root = true) :
    Comparison.acceptedCode (sourceCode s a) (coefficientCode s a root) = true := by
  have hs := root_coefficient_spec s a root ha
  rw [coefficientCode_literal s a root ha]
  exact (Comparison.acceptedCode_exact _ _).mpr
    ⟨by simpa only [checkCode_code] using hs.1,
      by simpa only [ThetaCourse.rawTree_code] using hs.2.1⟩

theorem coefficient_iota_input (s a root : Nat) (ha : BoundedContextIota.rootCheck s a root = true) :
    BoundedContextIota.inputCheck s a root (coefficientCode s a root) = true := by
  have hs := root_coefficient_spec s a root ha
  apply (BoundedContextIota.inputCheck_exact s a root _).mpr
  refine ⟨ha, limitTerm (sourceCode s a) (argumentCode root), coefficientCode_literal s a root ha,
    hs.1, hs.2.1, ?_⟩
  exact (BoundedContextIota.restricted_iff_sourceStar s a root ha _ hs.1 hs.2.1).mp hs.2.2.1

theorem coefficientCode_spec (s a root : Nat) (ha : BoundedContextIota.rootCheck s a root = true) :
    Comparison.acceptedCode (sourceCode s a) (coefficientCode s a root) = true ∧
      BoundedContextIota.inputCheck s a root (coefficientCode s a root) = true ∧
      (interpretation (sourceCode s a) (coefficientCode s a root) = 0 ∨
        IsSuccLimit (interpretation (sourceCode s a) (coefficientCode s a root))) ∧
      omegaSequence (base (sourceCode s a)) 1 *
          (interpretation (sourceCode s a) (coefficientCode s a root) + (coefficientOffset s a root : Ordinal.{0})) =
        interpretation (sourceCode s a) (deltaCode root) := by
  have hs := root_coefficient_spec s a root ha
  refine ⟨coefficientCode_accepted s a root ha, coefficient_iota_input s a root ha, ?_, ?_⟩
  · simpa only [coefficientCode_literal s a root ha, interpretation_code] using hs.2.2.2.1
  · simpa only [coefficientCode_literal s a root ha, coefficientOffset_literal s a root ha,
      interpretation_code] using hs.2.2.2.2

theorem coefficientCode_rejected (s a root : Nat) (ha : BoundedContextIota.rootCheck s a root = false) :
    coefficientCode s a root = 0 ∧ coefficientOffset s a root = 0 := by
  constructor
  · simp only [coefficientCode, ha, Bool.cond_false]
  · simp only [coefficientOffset, ha, Bool.cond_false]

theorem coefficient_below_second (s a root : Nat) (ha : BoundedContextIota.rootCheck s a root = true) :
    interpretation (sourceCode s a) (coefficientCode s a root) <
      omegaSequence (base (sourceCode s a)) 2 := by
  have hs := coefficientCode_spec s a root ha
  have hΩ : 1 ≤ omegaSequence (base (sourceCode s a)) 1 :=
    Order.one_le_iff_pos.mpr (omegaSequence_isSuccLimit (base (sourceCode s a)) 0).bot_lt
  have hle : interpretation (sourceCode s a) (coefficientCode s a root) ≤
      interpretation (sourceCode s a) (deltaCode root) := by
    calc
      interpretation (sourceCode s a) (coefficientCode s a root) ≤
          interpretation (sourceCode s a) (coefficientCode s a root) + (coefficientOffset s a root : Ordinal.{0}) :=
        le_self_add
      _ = 1 * (interpretation (sourceCode s a) (coefficientCode s a root) +
          (coefficientOffset s a root : Ordinal.{0})) := (one_mul _).symm
      _ ≤ omegaSequence (base (sourceCode s a)) 1 *
          (interpretation (sourceCode s a) (coefficientCode s a root) + (coefficientOffset s a root : Ordinal.{0})) :=
        mul_le_mul' hΩ le_rfl
      _ = interpretation (sourceCode s a) (deltaCode root) := hs.2.2.2
  have hd : interpretation (sourceCode s a) (deltaCode root) ≤
      interpretation (sourceCode s a) (argumentCode root) := by
    rw [deltaCode,
      (Decomposition.parts_code_value (sourceCode s a) 0 (argumentCode root)
        (argument_accepted s a root ha)).1]
    exact Ordinal.mul_div_le _ _
  obtain ⟨_, ⟨t, he, ht, hn, hhigh⟩, _⟩ := (BoundedContextIota.rootCheck_exact s a root).mp ha
  have hsort : interpretation (sourceCode s a) (argumentCode root) <
      omegaSequence (base (sourceCode s a)) 2 := by
    simpa only [argumentCode, he, Localization.argumentCode_theta, interpretation_code] using
      FixedPoint.checked_theta_sort (sourceCode s a) 0 t ht
  exact (hle.trans hd).trans_lt hsort

theorem coefficient_iota_low (s a root : Nat) (ha : BoundedContextIota.rootCheck s a root = true) :
    lowCheckCode (BoundedContextIota.betaCode s a root) (BoundedContextIota.literalCode s a root (coefficientCode s a root)) = true ∧
      Comparison.acceptedCode (BoundedContextIota.betaCode s a root) (BoundedContextIota.literalCode s a root (coefficientCode s a root)) = true := by
  let t := limitTerm (sourceCode s a) (argumentCode root)
  have hs := root_coefficient_spec s a root ha
  have hi := coefficient_iota_input s a root ha
  have hsort : t.outerSort ≤ 2 :=
    (denote_lt_iff_outerSort_le (sourceCode s a) t hs.1 2 (by omega)).mp (by
      simpa only [coefficientCode_literal s a root ha, interpretation_code] using coefficient_below_second s a root ha)
  have htransform := BoundedContextIota.transform_checked s a root ha t hs.1 hs.2.2.1
  have hnormal := BoundedContextIota.transform_normal s a root ha t hs.1 hs.2.1 hs.2.2.1
  have houter : (BoundedContextIota.transform s a root t).outerSort ≤ 1 := by
    have h := BoundedContextIota.transform_outerSort s a root ha t hs.1 hs.2.2.1
    omega
  have he : BoundedContextIota.literalCode s a root (coefficientCode s a root) = (BoundedContextIota.transform s a root t).code := by
    simp only [BoundedContextIota.literalCode, hi, Bool.cond_true, coefficientCode_literal s a root ha, BoundedContextIota.stateCode_code]
  rw [he]
  refine ⟨?_, (Comparison.acceptedCode_exact _ _).mpr
    ⟨by simpa only [checkCode_code] using htransform,
      by simpa only [ThetaCourse.rawTree_code] using hnormal⟩⟩
  simp only [lowCheckCode_code, lowCheck, htransform, houter, decide_true, Bool.true_and]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.BoundedContextIota.OmegaQuotient
