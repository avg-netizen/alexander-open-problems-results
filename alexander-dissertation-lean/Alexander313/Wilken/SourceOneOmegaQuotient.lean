import Alexander313.Wilken.SourceOneOmegaQuotientSupport
import Alexander313.Wilken.HereditarySourceDecomposition

/-!
# The complete original base-one high-ANF quotient

Every original high principal atom receives an originally checked Normal
restricted quotient. Genuine theta-one low, middle and upper thresholds are
kept distinct; the corrected epsilon exponent law includes tau=1. The real
original theta-atom ANF supplies the whole Omega-one*(lambda+k) decomposition,
including zero lambda. The original root alone derives the iota/LOW caller.
No quotient, admission, restriction or representation oracle. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.OmegaQuotient

open OrderSupport
open NativeContext.OmegaQuotient (theta_one_below_threshold theta_one_shifted_quotient
  theta_one_above_threshold principal_above_second_absorbs)

def atomTerm : RelativeTerm Nat → RelativeTerm Nat
  | .theta k t => cond (k == 1)
      (cond (decide (t.outerSort ≤ 1)) (ThetaCourse.rawTree (lowPowerCode t.code))
        (cond (Theta.less 0 t thresholdTerm)
          (.theta 1 (Difference.tree 0 baseTerm.code t.code)) (.theta 1 t)))
      (.theta k t)
  | t => t

theorem atom_spec (a k : Nat) (ha : rootCheck a = true) (t : RelativeTerm Nat)
    (ht : check 0 (.theta (k + 1) t) = true) (hn : Theta.Normal 0 t)
    (hr : Restricted a (.theta (k + 1) t)) :
    check 0 (atomTerm (.theta (k + 1) t)) = true ∧
      Theta.Normal 0 (atomTerm (.theta (k + 1) t)) ∧
      Restricted a (atomTerm (.theta (k + 1) t)) ∧
      0 < denote 0 (atomTerm (.theta (k + 1) t)) ∧
      Ordinal.IsPrincipal (· + ·) (denote 0 (atomTerm (.theta (k + 1) t))) ∧
      omegaSequence (finiteBase 0) 1 * denote 0 (atomTerm (.theta (k + 1) t)) =
        denote 0 (.theta (k + 1) t) := by
  have hc := argument_checked (k + 1) t ht
  have hrt := (restricted_theta_succ a k t).mp hr
  have hτ : finiteBase 0 = 1 ∨ Ordinal.omega0 ^ finiteBase 0 = finiteBase 0 :=
    Or.inl finiteBase_zero
  have hp := theta_principal (k + 1) t ht
  cases k with
  | succ k =>
    have hk : (k + 1 + 1 == 1) = false := by
      apply Bool.eq_false_of_not_eq_true
      intro he
      have h := beq_iff_eq.mp he
      omega
    simp only [atomTerm, hk, Bool.cond_false]
    refine ⟨ht, hn, hr, hp.1, hp.2, ?_⟩
    exact principal_above_second_absorbs (finiteBase 0) _ hp.2
      (((omegaSequence_strictMono (finiteBase 0)).monotone (by omega : 2 ≤ k + 1 + 1)).trans
        (SourceFixedPoint.checked_theta_range 0 (k + 1 + 1) t ht).1)
  | zero =>
    simp only [Nat.zero_add, atomTerm, beq_self_eq_true, Bool.cond_true]
    by_cases hl : t.outerSort ≤ 1
    · have hi : lowCheckCode 0 t.code = true := by
        simp only [lowCheckCode_code, lowCheck, hc, hl, decide_true, Bool.true_and]
      have hs := lowPowerCode_spec t.code hi
      have hx := (Theta.acceptedLowCode_iff 0 _).mp hs.1
      obtain ⟨u, he, hu⟩ := (lowCheckCode_iff 0 _).mp hx.1
      have huc := (Bool.and_eq_true.mp hu).1
      have hlow : (ThetaCourse.rawTree (lowPowerCode t.code)).outerSort ≤ 1 := by
        simpa only [← he, ThetaCourse.rawTree_code] using
          of_decide_eq_true (Bool.and_eq_true.mp hu).2
      have hout : check 0 (ThetaCourse.rawTree (lowPowerCode t.code)) = true := by
        simpa only [← he, ThetaCourse.rawTree_code] using huc
      have hv : denote 0 (ThetaCourse.rawTree (lowPowerCode t.code)) = Ordinal.omega0 ^ denote 0 t := by
        simpa only [← he, interpretation_code, ThetaCourse.rawTree_code] using hs.2
      have hb : denote 0 (ThetaCourse.rawTree (lowPowerCode t.code)) < interpretation 0 a := by
        rw [hv]
        exact (omegaPower_strictMono (restricted_low_below a ha t hc hrt hl)).trans_eq
          (root_epsilon a ha)
      have hxrest : Restricted a (ThetaCourse.rawTree (lowPowerCode t.code)) := by
        intro u hu
        exact (fullList_value_le_low _ u hout hx.2 hlow hu).trans_lt hb
      simp only [hl, decide_true, Bool.cond_true]
      refine ⟨hout, hx.2, hxrest, ?_, ?_, ?_⟩
      · rw [hv]; exact Ordinal.opow_pos _ Ordinal.omega0_pos
      · rw [hv]; exact Ordinal.isPrincipal_add_omega0_opow _
      · rw [hv]
        change omegaSequence (finiteBase 0) 1 * Ordinal.omega0 ^ denote 0 t =
          globalCollapse (finiteBase 0) 1 (denote 0 t)
        exact (theta_one_below_threshold (finiteBase 0) hτ _
          (((denote_lt_iff_outerSort_le 0 t hc 1 (by omega)).mpr hl).trans (by
            calc
              omegaSequence (finiteBase 0) 1 = omegaSequence (finiteBase 0) 1 * 1 := (mul_one _).symm
              _ < omegaSequence (finiteBase 0) 1 * Ordinal.omega0 :=
                mul_lt_mul_of_pos_left Ordinal.one_lt_omega0
                  (omegaSequence_isSuccLimit (finiteBase 0) 0).bot_lt))).symm
    · have hbase : omegaSequence (finiteBase 0) 1 ≤ denote 0 t := le_of_not_gt (by
        intro h
        exact hl ((denote_lt_iff_outerSort_le 0 t hc 1 (by omega)).mp h))
      cases hm : Theta.less 0 t thresholdTerm with
      | true =>
        have hβ : denote 0 t < omegaSequence (finiteBase 0) 1 * Ordinal.omega0 := by
          simpa only [thresholdTerm_spec.2.2] using
            (Theta.less_correct 0 t thresholdTerm hc thresholdTerm_spec.1 hn thresholdTerm_spec.2.1).mp hm
        have hbc : checkCode 0 baseTerm.code = true := by
          simpa only [checkCode_code] using baseTerm_spec.1
        have htc : checkCode 0 t.code = true := by simpa only [checkCode_code] using hc
        have hs := Difference.tree_spec 0 baseTerm.code t.code hbc htc (by
          simpa only [interpretation_code, baseTerm_spec.2.2] using hbase)
        have hv : denote 0 (Difference.tree 0 baseTerm.code t.code) =
            denote 0 t - omegaSequence (finiteBase 0) 1 := by
          simpa only [interpretation_code, baseTerm_spec.2.2] using hs.2.2.2
        have hsort : (Difference.tree 0 baseTerm.code t.code).outerSort ≤ 3 := by
          apply (denote_lt_iff_outerSort_le 0 _ hs.1 3 (by omega)).mp
          rw [hv]
          exact (Ordinal.sub_le_self _ _).trans_lt (SourceFixedPoint.checked_theta_sort 0 1 t ht)
        have hout := theta_checked 1 _ hs.1 hsort
        have houtp := theta_principal 1 _ hout
        simp only [hl, decide_false, Bool.cond_false, hm, Bool.cond_true]
        refine ⟨hout, hs.2.1, (restricted_theta_succ a 0 _).mpr
          (subtract_restricted a baseTerm.code t.code htc (by
            simpa only [ThetaCourse.rawTree_code] using hrt)), houtp.1, houtp.2, ?_⟩
        change omegaSequence (finiteBase 0) 1 * globalCollapse (finiteBase 0) 1
          (denote 0 (Difference.tree 0 baseTerm.code t.code)) = globalCollapse (finiteBase 0) 1 (denote 0 t)
        rw [hv]
        exact theta_one_shifted_quotient (finiteBase 0) hτ _ hbase hβ
      | false =>
        have hβ : omegaSequence (finiteBase 0) 1 * Ordinal.omega0 ≤ denote 0 t := by
          rw [← thresholdTerm_spec.2.2]
          apply le_of_not_gt
          intro h
          have he := (Theta.less_correct 0 t thresholdTerm hc thresholdTerm_spec.1 hn
            thresholdTerm_spec.2.1).mpr h
          simp only [hm, Bool.false_eq_true] at he
        simp only [hl, decide_false, Bool.cond_false, hm, Bool.cond_false]
        refine ⟨ht, hn, hr, hp.1, hp.2, ?_⟩
        by_cases hβlow : denote 0 t < omegaSequence (finiteBase 0) 2
        · exact theta_one_above_threshold (finiteBase 0) hτ _ hβ hβlow
        · exact theta_one_high_absorbs t ht (le_of_not_gt hβlow)

private def atomNumeric (t : RelativeTerm Nat) : RelativeTerm Nat :=
  let c := (t.code - 1).unpair.2
  let b := ThetaCourse.rawTree c.unpair.2
  cond (((t.code - 1).unpair.1 == 2) && (c.unpair.1 == 1))
    (cond (decide (b.outerSort ≤ 1)) (ThetaCourse.rawTree (lowPowerCode b.code))
      (cond (Theta.less 0 b thresholdTerm)
        (.theta 1 (Difference.tree 0 baseTerm.code b.code)) (.theta 1 b))) t

private theorem atomNumeric_eq (t : RelativeTerm Nat) : atomNumeric t = atomTerm t := by
  cases t <;> simp [atomNumeric, atomTerm, RelativeTerm.code, Nat.unpair_pair, ThetaCourse.rawTree_code]

theorem atomTerm_primrec : Primrec atomTerm := by
  have hc := Primrec.unpair.comp (Primrec.nat_sub.comp code_primrec (Primrec.const 1))
  have hb := ThetaCourse.rawTree_primrec.comp
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp hc)))
  have htest := Primrec.and.comp
    (Primrec.beq.comp (Primrec.fst.comp hc) (Primrec.const 2))
    (Primrec.beq.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp hc))) (Primrec.const 1))
  have hsmall := (Primrec.nat_le.comp (outerSort_primrec.comp hb) (Primrec.const 1)).decide
  have hpower := ThetaCourse.rawTree_primrec.comp (lowPowerCode_primrec.comp (code_primrec.comp hb))
  have hless := Theta.Effective.less_primrec.comp
    ((Primrec.const 0).pair (hb.pair (Primrec.const thresholdTerm)))
  have hsub := Difference.tree_primrec.comp
    ((Primrec.const 0).pair ((Primrec.const baseTerm.code).pair (code_primrec.comp hb)))
  have hmiddle := theta_primrec.comp (Primrec.const 1) hsub
  have hunchanged := theta_primrec.comp (Primrec.const 1) hb
  have h := htest.cond (hsmall.cond hpower (hless.cond hmiddle hunchanged)) Primrec.id
  change Primrec atomNumeric at h
  simpa only [atomNumeric_eq] using h

def quotientWord (c : Nat) : List (RelativeTerm Nat) :=
  (SourceDecomposition.highWord 0 0 c).map atomTerm

theorem quotientWord_primrec : Primrec quotientWord := by
  have hlist := SourceDecomposition.highWord_primrec.comp
    ((Primrec.const 0).pair ((Primrec.const 0).pair Primrec.id))
  exact Primrec.list_map hlist ((atomTerm_primrec.comp Primrec.snd).to₂)

theorem high_atom_spec (a c : Nat) (ha : rootCheck a = true)
    (hc : SourceDecomposition.inputCheck 0 c = true)
    (hr : Restricted a (ThetaCourse.rawTree c)) (t : RelativeTerm Nat)
    (ht : t ∈ SourceDecomposition.highWord 0 0 c) :
    check 0 (atomTerm t) = true ∧ Theta.Normal 0 (atomTerm t) ∧ Restricted a (atomTerm t) ∧
      0 < denote 0 (atomTerm t) ∧ Ordinal.IsPrincipal (· + ·) (denote 0 (atomTerm t)) ∧
      omegaSequence (finiteBase 0) 1 * denote 0 (atomTerm t) = denote 0 t := by
  have hm := (SourceDecomposition.highWord_mem 0 0 c t).mp ht
  have hs := (SourceDecomposition.word_spec 0 c hc).1 t hm.1
  have htRest := restricted_atoms a (ThetaCourse.rawTree c) t hr hm.1
  rcases SourceDecomposition.word_shape 0 c t hm.1 with ⟨p, rfl⟩ | ⟨k, u, rfl⟩
  · have hb := hm.2
    simp only [SourceDecomposition.above, RelativeTerm.outerSort, Nat.zero_add,
      decide_false, Bool.false_eq_true] at hb
  · cases k with
    | zero =>
      have hb := hm.2
      simp only [SourceDecomposition.above, RelativeTerm.outerSort, Nat.zero_add,
        Nat.lt_irrefl, decide_false, Bool.false_eq_true] at hb
    | succ k => exact atom_spec a k ha u hs.1 hs.2.1 htRest

private theorem quotient_map_normal (Ω : Ordinal.{0}) (hΩ : 0 < Ω)
    (f : RelativeTerm Nat → RelativeTerm Nat) (as : List (RelativeTerm Nat))
    (hn : IsAdditiveNormalForm (as.map (denote 0)))
    (hs : ∀ t ∈ as, 0 < denote 0 (f t) ∧ Ordinal.IsPrincipal (· + ·) (denote 0 (f t)) ∧
      Ω * denote 0 (f t) = denote 0 t) :
    IsAdditiveNormalForm ((as.map f).map (denote 0)) := by
  revert hn hs
  induction as with
  | nil => intro hn hs; simpa only [List.map_nil] using hn
  | cons t as ih =>
    intro hn hs
    have hp := List.pairwise_cons.mp hn.2
    have htail : IsAdditiveNormalForm (as.map (denote 0)) :=
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
      exact (hp.1 (denote 0 v) (List.mem_map.mpr ⟨v, hv, rfl⟩)).not_lt hb

theorem quotientWord_normal (a c : Nat) (ha : rootCheck a = true)
    (hc : SourceDecomposition.inputCheck 0 c = true) (hr : Restricted a (ThetaCourse.rawTree c)) :
    IsAdditiveNormalForm ((quotientWord c).map (denote 0)) := by
  apply quotient_map_normal (omegaSequence (finiteBase 0) 1)
    (omegaSequence_isSuccLimit (finiteBase 0) 0).bot_lt atomTerm
    (SourceDecomposition.highWord 0 0 c) (SourceDecomposition.words_normal 0 0 c hc).1
  intro t ht
  have hs := high_atom_spec a c ha hc hr t ht
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

theorem quotientWord_good (a c : Nat) (ha : rootCheck a = true)
    (hc : SourceDecomposition.inputCheck 0 c = true) (hr : Restricted a (ThetaCourse.rawTree c)) :
    Theta.Normalization.GoodAtoms 0 (wordHeight (quotientWord c)) (quotientWord c) := by
  intro t ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  have hs := high_atom_spec a c ha hc hr u hu
  exact ⟨Theta.checked_admissible 0 _ _ hs.1
    (wordHeight_mem _ _ ht), hs.2.1, hs.2.2.2.1, hs.2.2.2.2.1⟩

def quotientTerm (c : Nat) : RelativeTerm Nat := Theta.Normalization.buildAtoms 0 (quotientWord c)

theorem quotientTerm_primrec : Primrec quotientTerm :=
  Theta.Normalization.Effective.buildAtoms_primrec.comp (Primrec.const 0) quotientWord_primrec

private theorem mul_principalSum_map (Ω : Ordinal.{0}) (f : RelativeTerm Nat → RelativeTerm Nat)
    (as : List (RelativeTerm Nat)) (hs : ∀ t ∈ as, Ω * denote 0 (f t) = denote 0 t) :
    Ω * principalSum ((as.map f).map (denote 0)) = principalSum (as.map (denote 0)) := by
  revert hs
  induction as with
  | nil => intro _; simp only [List.map_nil, principalSum, mul_zero]
  | cons t as ih =>
    intro hs
    simp only [List.map_cons, principalSum, mul_add]
    rw [hs t List.mem_cons_self, ih (fun u hu => hs u (List.mem_cons_of_mem _ hu))]

theorem quotientTerm_spec (a c : Nat) (ha : rootCheck a = true)
    (hc : SourceDecomposition.inputCheck 0 c = true) (hr : Restricted a (ThetaCourse.rawTree c)) :
    check 0 (quotientTerm c) = true ∧ Theta.Normal 0 (quotientTerm c) ∧ Restricted a (quotientTerm c) ∧
      omegaSequence (finiteBase 0) 1 * denote 0 (quotientTerm c) =
        interpretation 0 (SourceDecomposition.highCode 0 0 c) := by
  have hg := quotientWord_good a c ha hc hr
  have had := Theta.Normalization.buildAtoms_admissible 0 _ _ hg
  refine ⟨Theta.admitted_checked had, Theta.Normalization.buildAtoms_normal 0 _ _ hg
    (quotientWord_normal a c ha hc hr), ?_, ?_⟩
  · apply buildAtoms_restricted
    intro t ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
    exact (high_atom_spec a c ha hc hr u hu).2.2.1
  · rw [quotientTerm, Theta.Normalization.buildAtoms_denote]
    have hv := mul_principalSum_map (omegaSequence (finiteBase 0) 1) atomTerm
      (SourceDecomposition.highWord 0 0 c) (fun t ht => (high_atom_spec a c ha hc hr t ht).2.2.2.2.2)
    exact hv.trans (by
      simpa only [SourceDecomposition.highCode, interpretation_code] using
        (SourceDecomposition.parts_word_values 0 0 c).1.symm)

def unitTest (t : RelativeTerm Nat) : Bool := Theta.equal 0 t unitTerm

theorem unitTest_primrec : Primrec unitTest :=
  Theta.Effective.equal_primrec.comp ((Primrec.const 0).pair (Primrec.id.pair (Primrec.const unitTerm)))

theorem unitTest_exact (t : RelativeTerm Nat) (ht : check 0 t = true) (hn : Theta.Normal 0 t) :
    unitTest t = true ↔ denote 0 t = 1 := by
  simpa only [unitTest, unitTerm_spec.2.2] using
    Theta.equal_correct 0 t unitTerm ht unitTerm_spec.1 hn unitTerm_spec.2.1

def selectUnits (units : Bool) : List (RelativeTerm Nat) → List (RelativeTerm Nat)
  | [] => []
  | t :: as => cond (cond units (unitTest t) (!unitTest t))
      (t :: selectUnits units as) (selectUnits units as)

theorem selectUnits_primrec : Primrec₂ selectUnits := by
  have htest := unitTest_primrec.comp (Primrec.fst.comp Primrec.snd)
  have hkeep := (Primrec.fst.comp Primrec.fst).cond htest (Primrec.not.comp htest)
  have hstep : Primrec₂ (fun p : Bool × List (RelativeTerm Nat) =>
      fun v : RelativeTerm Nat × List (RelativeTerm Nat) =>
        cond (cond p.1 (unitTest v.1) (!unitTest v.1)) (v.1 :: v.2) v.2) :=
    (hkeep.cond (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  have h := Primrec.list_foldr Primrec.snd (Primrec.const []) hstep
  have he : (fun p : Bool × List (RelativeTerm Nat) => p.2.foldr
      (fun t as => cond (cond p.1 (unitTest t) (!unitTest t)) (t :: as) as) []) =
      (fun p => selectUnits p.1 p.2) := by
    funext p
    rcases p with ⟨units, as⟩
    induction as with
    | nil => rfl
    | cons t as ih => simp only [List.foldr_cons, selectUnits, ih]
  rw [he] at h
  exact h.to₂

theorem selectUnits_filter (units : Bool) (as : List (RelativeTerm Nat)) :
    selectUnits units as = as.filter (fun t => cond units (unitTest t) (!unitTest t)) := by
  induction as with
  | nil => rfl
  | cons t as ih =>
    cases h : cond units (unitTest t) (!unitTest t) <;> simp [selectUnits, h, ih]

theorem selectUnits_mem (units : Bool) (as : List (RelativeTerm Nat)) (t : RelativeTerm Nat) :
    t ∈ selectUnits units as ↔ t ∈ as ∧ cond units (unitTest t) (!unitTest t) = true := by
  rw [selectUnits_filter, List.mem_filter]

private theorem selectUnits_all (as : List (RelativeTerm Nat))
    (h : ∀ t ∈ as, unitTest t = true) : selectUnits true as = as ∧ selectUnits false as = [] := by
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

private theorem unit_partition (as : List (RelativeTerm Nat))
    (hn : IsAdditiveNormalForm (as.map (denote 0)))
    (hs : ∀ t ∈ as, check 0 t = true ∧ Theta.Normal 0 t) :
    as = selectUnits false as ++ selectUnits true as := by
  revert hn hs
  induction as with
  | nil => intro hn hs; rfl
  | cons t as ih =>
    intro hn hs
    have hp := List.pairwise_cons.mp hn.2
    have htail : IsAdditiveNormalForm (as.map (denote 0)) :=
      ⟨fun p hm => hn.1 p (List.mem_cons_of_mem _ hm), hp.2⟩
    have ht := hs t List.mem_cons_self
    cases he : unitTest t with
    | false =>
      have hi := ih htail (fun u hu => hs u (List.mem_cons_of_mem _ hu))
      simp only [selectUnits, he, Bool.cond_false, Bool.not_false, Bool.cond_true,
        List.cons_append, ← hi]
    | true =>
      have hv := (unitTest_exact t ht.1 ht.2).mp he
      have hall : ∀ u ∈ as, unitTest u = true := by
        intro u hu
        have hus := hs u (List.mem_cons_of_mem _ hu)
        apply (unitTest_exact u hus.1 hus.2).mpr
        have hupos := (hn.1 _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨u, hu, rfl⟩))).1
        have hule : denote 0 u ≤ 1 := by
          rw [← hv]
          exact hp.1 _ (List.mem_map.mpr ⟨u, hu, rfl⟩)
        exact le_antisymm hule (Order.one_le_iff_pos.mpr hupos)
      have hall' := selectUnits_all as hall
      simp only [selectUnits, he, Bool.cond_true, Bool.not_true, Bool.cond_false,
        hall'.1, hall'.2, List.nil_append]

private theorem selected_normal (units : Bool) (as : List (RelativeTerm Nat))
    (hn : IsAdditiveNormalForm (as.map (denote 0))) :
    IsAdditiveNormalForm ((selectUnits units as).map (denote 0)) := by
  rw [selectUnits_filter]
  have hbase : (as.filter (fun t => cond units (unitTest t) (!unitTest t))).Sublist as := List.filter_sublist
  have hsub := hbase.map (denote 0)
  exact ⟨fun p hp => hn.1 p (hsub.subset hp), hn.2.sublist hsub⟩

private theorem unit_sum (as : List (RelativeTerm Nat))
    (hs : ∀ t ∈ as, check 0 t = true ∧ Theta.Normal 0 t) :
    principalSum ((selectUnits true as).map (denote 0)) = ((selectUnits true as).length : Ordinal.{0}) := by
  have hv : ∀ t ∈ selectUnits true as, denote 0 t = 1 := by
    intro t ht
    have hm := (selectUnits_mem true as t).mp ht
    exact (unitTest_exact t (hs t hm.1).1 (hs t hm.1).2).mp hm.2
  generalize he : selectUnits true as = bs at hv ⊢
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

def limitWord (c : Nat) : List (RelativeTerm Nat) := selectUnits false (quotientWord c)
def finiteOffset (c : Nat) : Nat := (selectUnits true (quotientWord c)).length
def limitTerm (c : Nat) : RelativeTerm Nat := Theta.Normalization.buildAtoms 0 (limitWord c)

theorem limitWord_primrec : Primrec limitWord :=
  selectUnits_primrec.comp (Primrec.const false) quotientWord_primrec

theorem finiteOffset_primrec : Primrec finiteOffset :=
  Primrec.list_length.comp (selectUnits_primrec.comp (Primrec.const true) quotientWord_primrec)

theorem limitTerm_primrec : Primrec limitTerm :=
  Theta.Normalization.Effective.buildAtoms_primrec.comp (Primrec.const 0) limitWord_primrec

theorem limitTerm_spec (a c : Nat) (ha : rootCheck a = true)
    (hc : SourceDecomposition.inputCheck 0 c = true) (hr : Restricted a (ThetaCourse.rawTree c)) :
    check 0 (limitTerm c) = true ∧ Theta.Normal 0 (limitTerm c) ∧ Restricted a (limitTerm c) ∧
      (denote 0 (limitTerm c) = 0 ∨ IsSuccLimit (denote 0 (limitTerm c))) ∧
      omegaSequence (finiteBase 0) 1 * (denote 0 (limitTerm c) + (finiteOffset c : Ordinal.{0})) =
        interpretation 0 (SourceDecomposition.highCode 0 0 c) := by
  have hn := quotientWord_normal a c ha hc hr
  have hs : ∀ t ∈ quotientWord c, check 0 t = true ∧ Theta.Normal 0 t := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
    have h := high_atom_spec a c ha hc hr u hu
    exact ⟨h.1, h.2.1⟩
  have hg := quotientWord_good a c ha hc hr
  have hmem : ∀ t ∈ limitWord c, t ∈ quotientWord c := fun t ht =>
    ((selectUnits_mem false _ t).mp ht).1
  have hgood : Theta.Normalization.GoodAtoms 0 (wordHeight (quotientWord c)) (limitWord c) :=
    fun t ht => hg t (hmem t ht)
  have had := Theta.Normalization.buildAtoms_admissible 0 _ _ hgood
  refine ⟨Theta.admitted_checked had, Theta.Normalization.buildAtoms_normal 0 _ _ hgood
    (selected_normal false _ hn), ?_, ?_, ?_⟩
  · apply buildAtoms_restricted
    intro t ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp (hmem t ht)
    exact (high_atom_spec a c ha hc hr u hu).2.2.1
  · rw [limitTerm, Theta.Normalization.buildAtoms_denote]
    apply principalSum_limit_zero
    intro p hp
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hp
    have hm := (selectUnits_mem false _ t).mp ht
    have hp' := hn.1 _ (List.mem_map.mpr ⟨t, hm.1, rfl⟩)
    refine ⟨lt_of_le_of_ne (Order.one_le_iff_pos.mpr hp'.1) ?_, hp'.2⟩
    intro he
    have hut := (unitTest_exact t (hs t hm.1).1 (hs t hm.1).2).mpr he.symm
    have hnot := hm.2
    simp only [Bool.cond_false, hut, Bool.not_true, Bool.false_eq_true] at hnot
  · have hv : denote 0 (quotientTerm c) = denote 0 (limitTerm c) + (finiteOffset c : Ordinal.{0}) := by
      rw [quotientTerm, Theta.Normalization.buildAtoms_denote, unit_partition (quotientWord c) hn hs,
        List.map_append, principalSum_append, unit_sum _ hs]
      rw [limitTerm, Theta.Normalization.buildAtoms_denote]
      rfl
    rw [← hv]
    exact (quotientTerm_spec a c ha hc hr).2.2.2

def argumentCode (a : Nat) : Nat := Localization.argumentCode a

def deltaCode (a : Nat) : Nat := SourceDecomposition.highCode 0 0 (argumentCode a)

theorem argumentCode_primrec : Primrec argumentCode := Localization.argumentCode_primrec

theorem deltaCode_primrec : Primrec deltaCode :=
  SourceDecomposition.highCode_primrec.comp ((Primrec.const 0).pair ((Primrec.const 0).pair argumentCode_primrec))

theorem argument_accepted (a : Nat) (ha : rootCheck a = true) :
    SourceDecomposition.inputCheck 0 (argumentCode a) = true := by
  obtain ⟨t, he, ht, hn, hs⟩ := (rootCheck_exact a).mp ha
  simp only [argumentCode, he, Localization.argumentCode_theta]
  apply (Theta.acceptedCode_iff 0 _).mpr
  exact ⟨by simpa only [checkCode_code] using argument_checked 0 t ht,
    by simpa only [ThetaCourse.rawTree_code] using hn⟩

theorem root_coefficient_spec (a : Nat) (ha : rootCheck a = true) :
    check 0 (limitTerm (argumentCode a)) = true ∧ Theta.Normal 0 (limitTerm (argumentCode a)) ∧
      Restricted a (limitTerm (argumentCode a)) ∧
      (denote 0 (limitTerm (argumentCode a)) = 0 ∨ IsSuccLimit (denote 0 (limitTerm (argumentCode a)))) ∧
      omegaSequence (finiteBase 0) 1 *
          (denote 0 (limitTerm (argumentCode a)) + (finiteOffset (argumentCode a) : Ordinal.{0})) =
        interpretation 0 (deltaCode a) :=
  limitTerm_spec a _ ha (argument_accepted a ha) (argument_restricted a ha)

def coefficientCode (a : Nat) : Nat := cond (rootCheck a) (limitTerm (argumentCode a)).code 0

def coefficientOffset (a : Nat) : Nat := cond (rootCheck a) (finiteOffset (argumentCode a)) 0

theorem coefficientCode_primrec : Primrec coefficientCode :=
  rootCheck_primrec.cond (code_primrec.comp (limitTerm_primrec.comp argumentCode_primrec)) (Primrec.const 0)

theorem coefficientOffset_primrec : Primrec coefficientOffset :=
  rootCheck_primrec.cond (finiteOffset_primrec.comp argumentCode_primrec) (Primrec.const 0)

theorem coefficientCode_literal (a : Nat) (ha : rootCheck a = true) :
    coefficientCode a = (limitTerm (argumentCode a)).code := by
  simp only [coefficientCode, ha, Bool.cond_true]

theorem coefficientOffset_literal (a : Nat) (ha : rootCheck a = true) :
    coefficientOffset a = finiteOffset (argumentCode a) := by
  simp only [coefficientOffset, ha, Bool.cond_true]

theorem coefficientCode_accepted (a : Nat) (ha : rootCheck a = true) :
    Theta.acceptedCode 0 (coefficientCode a) = true := by
  have hs := root_coefficient_spec a ha
  rw [coefficientCode_literal a ha]
  exact (Theta.acceptedCode_iff 0 _).mpr
    ⟨by simpa only [checkCode_code] using hs.1,
      by simpa only [ThetaCourse.rawTree_code] using hs.2.1⟩

theorem coefficient_iota_input (a : Nat) (ha : rootCheck a = true) : inputCheck a (coefficientCode a) = true := by
  have hs := root_coefficient_spec a ha
  apply (inputCheck_exact a _).mpr
  refine ⟨ha, limitTerm (argumentCode a), coefficientCode_literal a ha, hs.1, hs.2.1, ?_⟩
  exact (restricted_iff_sourceStar a ha _ hs.1 hs.2.1).mp hs.2.2.1

theorem coefficientCode_spec (a : Nat) (ha : rootCheck a = true) :
    Theta.acceptedCode 0 (coefficientCode a) = true ∧ inputCheck a (coefficientCode a) = true ∧
      (interpretation 0 (coefficientCode a) = 0 ∨ IsSuccLimit (interpretation 0 (coefficientCode a))) ∧
      omegaSequence (finiteBase 0) 1 *
          (interpretation 0 (coefficientCode a) + (coefficientOffset a : Ordinal.{0})) =
        interpretation 0 (deltaCode a) := by
  have hs := root_coefficient_spec a ha
  refine ⟨coefficientCode_accepted a ha, coefficient_iota_input a ha, ?_, ?_⟩
  · simpa only [coefficientCode_literal a ha, interpretation_code] using hs.2.2.2.1
  · simpa only [coefficientCode_literal a ha, coefficientOffset_literal a ha, interpretation_code] using hs.2.2.2.2

theorem coefficientCode_rejected (a : Nat) (ha : rootCheck a = false) :
    coefficientCode a = 0 ∧ coefficientOffset a = 0 := by
  constructor
  · simp only [coefficientCode, ha, Bool.cond_false]
  · simp only [coefficientOffset, ha, Bool.cond_false]

theorem coefficient_below_second (a : Nat) (ha : rootCheck a = true) :
    interpretation 0 (coefficientCode a) < omegaSequence (finiteBase 0) 2 := by
  have hs := coefficientCode_spec a ha
  have hΩ : 1 ≤ omegaSequence (finiteBase 0) 1 := Order.one_le_iff_pos.mpr (omegaSequence_isSuccLimit (finiteBase 0) 0).bot_lt
  have hle : interpretation 0 (coefficientCode a) ≤ interpretation 0 (deltaCode a) := by
    calc
      interpretation 0 (coefficientCode a) ≤ interpretation 0 (coefficientCode a) +
          (coefficientOffset a : Ordinal.{0}) := le_self_add
      _ = 1 * (interpretation 0 (coefficientCode a) + (coefficientOffset a : Ordinal.{0})) := (one_mul _).symm
      _ ≤ omegaSequence (finiteBase 0) 1 *
          (interpretation 0 (coefficientCode a) + (coefficientOffset a : Ordinal.{0})) := mul_le_mul' hΩ le_rfl
      _ = interpretation 0 (deltaCode a) := hs.2.2.2
  have hd := (SourceDecomposition.parts_le 0 0 (argumentCode a) (argument_accepted a ha)).1
  obtain ⟨t, he, ht, hn, hhigh⟩ := (rootCheck_exact a).mp ha
  have hsort : interpretation 0 (argumentCode a) < omegaSequence (finiteBase 0) 2 := by
    simpa only [argumentCode, he, Localization.argumentCode_theta, interpretation_code] using
      SourceFixedPoint.checked_theta_sort 0 0 t ht
  exact (hle.trans hd).trans_lt hsort

theorem coefficient_iota_low (a : Nat) (ha : rootCheck a = true) :
    NativeContext.lowCheckCode (alphaCode a) (literalCode a (coefficientCode a)) = true ∧
      NativeContext.Comparison.acceptedCode (alphaCode a) (literalCode a (coefficientCode a)) = true := by
  let t := limitTerm (argumentCode a)
  have hs := root_coefficient_spec a ha
  have hi := coefficient_iota_input a ha
  have hsort : t.outerSort ≤ 2 := (denote_lt_iff_outerSort_le 0 t hs.1 2 (by omega)).mp (by
    simpa only [coefficientCode_literal a ha, interpretation_code] using coefficient_below_second a ha)
  have htransform := transform_checked a ha t hs.1 hs.2.2.1
  have hnormal := transform_normal a ha t hs.1 hs.2.1 hs.2.2.1
  have houter : (transform a t).outerSort ≤ 1 := by
    have h := transform_outerSort a ha t hs.1 hs.2.2.1
    omega
  have he : literalCode a (coefficientCode a) = (transform a t).code := by
    rw [coefficientCode_literal a ha]
    exact literalCode_code a ha t hs.1 hs.2.1 hs.2.2.1
  rw [he]
  refine ⟨?_, (NativeContext.Comparison.acceptedCode_exact _ _).mpr
    ⟨by simpa only [NativeContext.checkCode_code] using htransform,
      by simpa only [ThetaCourse.rawTree_code] using hnormal⟩⟩
  simp only [NativeContext.lowCheckCode_code, NativeContext.lowCheck, htransform, houter,
    decide_true, Bool.true_and]

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.OmegaQuotient
