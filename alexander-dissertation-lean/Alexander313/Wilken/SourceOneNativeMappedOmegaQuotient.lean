import Alexander313.Wilken.SourceOneNativeMappedOmegaQuotientSupport

/-!
# Actual original source-one mapped Omega-one product

The actual ORIGINAL quotient atom algorithm, full source-one iota order
and the genuine alpha-relative minimum formulas prove each atom product.
Real descending ANF and unit stripping assemble the literal divided-head
factorization. Every source check/Normal/restriction and target caller is
derived; no Native base-one source parser or product oracle. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.MappedOmegaQuotient

open OrderSupport OmegaQuotient
open NativeContext.PublicEpsilonIota.MappedOmegaQuotient
  (theta_zero_below_threshold theta_zero_shifted_quotient
   theta_zero_above_threshold principal_above_first_absorbs)

theorem mapped_atom_product (a k : Nat) (ha : rootCheck a = true)
    (t : RelativeTerm Nat) (ht : check 0 (.theta (k + 1) t) = true)
    (hn : Theta.Normal 0 t) (hr : Restricted a (.theta (k + 1) t)) :
    NativeContext.base (alphaCode a) *
        NativeContext.denote (alphaCode a) (transform a (atomTerm (.theta (k + 1) t))) =
      NativeContext.denote (alphaCode a) (transform a (.theta (k + 1) t)) := by
  have hαq := alphaCode_baseCheck a ha
  have hε := ((NativeContext.baseCheck_exact _).mp hαq).2
  have hc := argument_checked (k + 1) t ht
  have hrt := (restricted_theta_succ a k t).mp hr
  have has := atom_spec a k ha t ht hn hr
  cases k with
  | succ k =>
    have hk : (k + 1 + 1 == 1) = false := by
      apply Bool.eq_false_of_not_eq_true
      intro he
      have h := beq_iff_eq.mp he
      omega
    simp only [atomTerm, hk, Bool.cond_false]
    have htc := transform_checked a ha (.theta (k + 1 + 1) t) ht hr
    rw [transform_theta_succ a (k + 1) ha t ht hr] at htc ⊢
    have hp := NativeContext.OmegaQuotient.theta_principal _ (k + 1) (transform a t) htc
    apply principal_above_first_absorbs _ _ hε hp.2
    exact ((omegaSequence_strictMono (NativeContext.base (alphaCode a))).monotone
      (by omega : 1 ≤ k + 1)).trans
        (NativeContext.FixedPoint.checked_theta_range _ (k + 1) _ htc).1
  | zero =>
    simp only [Nat.zero_add] at ht hr hc hrt has ⊢
    by_cases hl : t.outerSort ≤ 1
    · have hi : lowCheckCode 0 t.code = true := by
        simp only [lowCheckCode_code, lowCheck, hc, hl, decide_true, Bool.true_and]
      have hp := lowPowerCode_spec t.code hi
      have hx := (Theta.acceptedLowCode_iff 0 _).mp hp.1
      obtain ⟨u, he, hu⟩ := (lowCheckCode_iff 0 _).mp hx.1
      have hpc : check 0 (ThetaCourse.rawTree (lowPowerCode t.code)) = true := by
        simpa only [← he, ThetaCourse.rawTree_code] using (Bool.and_eq_true.mp hu).1
      have hv : denote 0 (ThetaCourse.rawTree (lowPowerCode t.code)) = Ordinal.omega0 ^ denote 0 t := by
        simpa only [← he, interpretation_code, ThetaCourse.rawTree_code] using hp.2
      have hηα : denote 0 t < NativeContext.base (alphaCode a) := by
        rw [alpha_base a ha]
        exact restricted_low_below a ha t hc hrt hl
      have hpowerα : denote 0 (ThetaCourse.rawTree (lowPowerCode t.code)) < interpretation 0 a := by
        rw [hv, ← alpha_base a ha]
        exact (omegaPower_strictMono hηα).trans_eq hε
      simp only [atomTerm, beq_self_eq_true, Bool.cond_true, hl, decide_true]
      rw [transform_below_value a ha _ hpc hpowerα, hv,
        transform_theta_succ a 0 ha t ht hr]
      change NativeContext.base (alphaCode a) * Ordinal.omega0 ^ denote 0 t =
        globalCollapse (NativeContext.base (alphaCode a)) 0
          (NativeContext.denote (alphaCode a) (transform a t))
      rw [transform_low_value a ha t hc hrt hl]
      apply (theta_zero_below_threshold _ _ hε ?_).symm
      exact hηα.trans (by
        calc
          NativeContext.base (alphaCode a) = NativeContext.base (alphaCode a) * 1 := (mul_one _).symm
          _ < NativeContext.base (alphaCode a) * Ordinal.omega0 :=
            mul_lt_mul_of_pos_left Ordinal.one_lt_omega0 (NativeContext.base_pos _ hαq))
    · have hbase : omegaSequence (finiteBase 0) 1 ≤ denote 0 t := le_of_not_gt (by
        intro h
        exact hl ((denote_lt_iff_outerSort_le 0 t hc 1 (by omega)).mp h))
      have hαle : NativeContext.base (alphaCode a) ≤ NativeContext.denote (alphaCode a) (transform a t) := by
        rw [← mapped_baseTerm a ha]
        exact (transform_le_iff a ha baseTerm t baseTerm_spec.1 hc baseTerm_spec.2.1 hn
          (baseTerm_restricted a) hrt).mpr (by rw [baseTerm_spec.2.2]; exact hbase)
      cases hm : Theta.less 0 t thresholdTerm with
      | true =>
        have hηth : denote 0 t < omegaSequence (finiteBase 0) 1 * Ordinal.omega0 := by
          rw [← thresholdTerm_spec.2.2]
          exact (Theta.less_correct 0 t thresholdTerm hc thresholdTerm_spec.1 hn thresholdTerm_spec.2.1).mp hm
        have hηtarget : NativeContext.denote (alphaCode a) (transform a t) <
            NativeContext.base (alphaCode a) * Ordinal.omega0 := by
          rw [← mapped_thresholdTerm a ha]
          exact (transform_lt_iff a ha t thresholdTerm hc thresholdTerm_spec.1 hn thresholdTerm_spec.2.1 hrt
            (thresholdTerm_restricted a ha)).mpr (by rw [thresholdTerm_spec.2.2]; exact hηth)
        let d := Difference.tree 0 baseTerm.code t.code
        have has' : check 0 (.theta 1 d) = true ∧ Theta.Normal 0 (.theta 1 d) ∧ Restricted a (.theta 1 d) := by
          simpa only [atomTerm, beq_self_eq_true, Bool.cond_true, hl, decide_false,
            Bool.cond_false, hm] using ⟨has.1, has.2.1, has.2.2.1⟩
        simp only [atomTerm, beq_self_eq_true, Bool.cond_true, hl, decide_false,
          Bool.cond_false, hm]
        rw [transform_theta_succ a 0 ha d has'.1 has'.2.2,
          transform_theta_succ a 0 ha t ht hr]
        change NativeContext.base (alphaCode a) * globalCollapse (NativeContext.base (alphaCode a)) 0
            (NativeContext.denote (alphaCode a) (transform a d)) =
          globalCollapse (NativeContext.base (alphaCode a)) 0
            (NativeContext.denote (alphaCode a) (transform a t))
        rw [mapped_subtract_base a ha t hc hn hrt hbase]
        exact theta_zero_shifted_quotient _ _ hε hαle hηtarget
      | false =>
        have hηth : omegaSequence (finiteBase 0) 1 * Ordinal.omega0 ≤ denote 0 t := by
          rw [← thresholdTerm_spec.2.2]
          apply le_of_not_gt
          intro h
          have he := (Theta.less_correct 0 t thresholdTerm hc thresholdTerm_spec.1 hn thresholdTerm_spec.2.1).mpr h
          simp only [hm, Bool.false_eq_true] at he
        have hηtarget : NativeContext.base (alphaCode a) * Ordinal.omega0 ≤
            NativeContext.denote (alphaCode a) (transform a t) := by
          rw [← mapped_thresholdTerm a ha]
          exact (transform_le_iff a ha thresholdTerm t thresholdTerm_spec.1 hc thresholdTerm_spec.2.1 hn
            (thresholdTerm_restricted a ha) hrt).mpr (by rw [thresholdTerm_spec.2.2]; exact hηth)
        simp only [atomTerm, beq_self_eq_true, Bool.cond_true, hl, decide_false,
          Bool.cond_false, hm]
        have htc := transform_checked a ha (.theta 1 t) ht hr
        rw [transform_theta_succ a 0 ha t ht hr] at htc ⊢
        by_cases hlow : NativeContext.denote (alphaCode a) (transform a t) <
            omegaSequence (NativeContext.base (alphaCode a)) 1
        · exact theta_zero_above_threshold _ _ hε hηtarget hlow
        · have hhigh := le_of_not_gt hlow
          have hep := NativeContext.SourceChi.Powers.theta_epsilon_of_high _ (transform a t) htc hhigh
          have htarg := NativeContext.FixedPoint.checked_theta_argument _ 0 (transform a t) htc
          have hlt := NativeContext.SourceChi.Powers.global_high_base_lt _ (NativeContext.base_pos _ hαq)
            (NativeContext.FixedPoint.sourceOrdinal _ 0 (transform a t) htarg)
            (NativeContext.FixedPoint.checked_theta_sort _ 0 (transform a t) htc) hhigh
          exact NativeContext.OmegaQuotient.epsilon_above_absorbs _ _ hε hep hlt

theorem mapped_high_atom_product (a c : Nat) (ha : rootCheck a = true)
    (hc : SourceDecomposition.inputCheck 0 c = true) (hr : Restricted a (ThetaCourse.rawTree c))
    (t : RelativeTerm Nat) (ht : t ∈ SourceDecomposition.highWord 0 0 c) :
    NativeContext.base (alphaCode a) * NativeContext.denote (alphaCode a) (transform a (atomTerm t)) =
      NativeContext.denote (alphaCode a) (transform a t) := by
  have hm := (SourceDecomposition.highWord_mem 0 0 c t).mp ht
  have hs := (SourceDecomposition.word_spec 0 c hc).1 t hm.1
  have hrest := restricted_atoms a (ThetaCourse.rawTree c) t hr hm.1
  rcases SourceDecomposition.word_shape 0 c t hm.1 with ⟨p, rfl⟩ | ⟨k, u, rfl⟩
  · have hb := hm.2
    simp only [SourceDecomposition.above, RelativeTerm.outerSort, Nat.zero_add,
      decide_false, Bool.false_eq_true] at hb
  · cases k with
    | zero =>
      have hb := hm.2
      simp only [SourceDecomposition.above, RelativeTerm.outerSort, Nat.zero_add,
        Nat.lt_irrefl, decide_false, Bool.false_eq_true] at hb
    | succ k => exact mapped_atom_product a k ha u hs.1 hs.2.1 hrest

private theorem mul_principalSum_congr (α : Ordinal.{0})
    (as : List (RelativeTerm Nat)) (f g : RelativeTerm Nat → Ordinal.{0})
    (h : ∀ t ∈ as, α * f t = g t) : α * principalSum (as.map f) = principalSum (as.map g) := by
  revert h
  induction as with
  | nil => intro _; simp only [List.map_nil, principalSum, mul_zero]
  | cons t as ih =>
    intro h
    simp only [List.map_cons, principalSum, mul_add]
    rw [h t List.mem_cons_self, ih (fun u hu => h u (List.mem_cons_of_mem _ hu))]

theorem mapped_quotient_product (a c : Nat) (ha : rootCheck a = true)
    (hc : SourceDecomposition.inputCheck 0 c = true) (hr : Restricted a (ThetaCourse.rawTree c)) :
    NativeContext.base (alphaCode a) * NativeContext.denote (alphaCode a) (transform a (quotientTerm c)) =
      NativeContext.denote (alphaCode a) (transform a (SourceDecomposition.highPartTerm 0 0 c)) := by
  have hg := quotientWord_good a c ha hc hr
  have hgr : ∀ t ∈ quotientWord c, Restricted a t := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
    exact (high_atom_spec a c ha hc hr u hu).2.2.1
  have hhigh := (SourceDecomposition.words_good 0 (ThetaCourse.rawTree c).height 0 c hc le_rfl).1
  have hhighr : ∀ t ∈ SourceDecomposition.highWord 0 0 c, Restricted a t := by
    intro t ht
    exact restricted_atoms a (ThetaCourse.rawTree c) t hr ((SourceDecomposition.highWord_mem 0 0 c t).mp ht).1
  rw [quotientTerm, Addition.transform_buildAtoms_value a _ ha _ hg hgr, quotientWord, List.map_map]
  exact (mul_principalSum_congr _ _ _ _ (fun t ht => mapped_high_atom_product a c ha hc hr t ht)).trans
    (Addition.transform_buildAtoms_value a _ ha _ hhigh hhighr).symm

private theorem principalSum_unit_word (as : List (RelativeTerm Nat))
    (f : RelativeTerm Nat → Ordinal.{0}) (h : ∀ t ∈ as, f t = 1) :
    principalSum (as.map f) = (as.length : Ordinal.{0}) := by
  revert h
  induction as with
  | nil => intro _; simp only [List.map_nil, principalSum, List.length_nil, Nat.cast_zero]
  | cons t as ih =>
    intro h
    simp only [List.map_cons, principalSum, List.length_cons]
    rw [h t List.mem_cons_self, ih (fun u hu => h u (List.mem_cons_of_mem _ hu)),
      ← Nat.cast_one, ← Nat.cast_add]
    exact congrArg (fun n : Nat => (n : Ordinal.{0})) (Nat.add_comm 1 as.length)

theorem mapped_quotient_finite_tail (a c : Nat) (ha : rootCheck a = true)
    (hc : SourceDecomposition.inputCheck 0 c = true) (hr : Restricted a (ThetaCourse.rawTree c)) :
    NativeContext.denote (alphaCode a) (transform a (quotientTerm c)) =
      NativeContext.denote (alphaCode a) (transform a (limitTerm c)) + (finiteOffset c : Ordinal.{0}) := by
  let as := quotientWord c
  have hg := quotientWord_good a c ha hc hr
  have hrq : ∀ t ∈ as, Restricted a t := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
    exact (high_atom_spec a c ha hc hr u hu).2.2.1
  have hs : ∀ t ∈ as, check 0 t = true ∧ Theta.Normal 0 t := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
    have h := high_atom_spec a c ha hc hr u hu
    exact ⟨h.1, h.2.1⟩
  have hw := unit_partition as (quotientWord_normal a c ha hc hr) hs
  have hmem : ∀ t ∈ selectUnits false as, t ∈ as := fun t ht => ((selectUnits_mem false as t).mp ht).1
  have hgl : Theta.Normalization.GoodAtoms 0 (wordHeight as) (selectUnits false as) :=
    fun t ht => hg t (hmem t ht)
  have hunit : principalSum ((selectUnits true as).map
      (fun t => NativeContext.denote (alphaCode a) (transform a t))) =
        ((selectUnits true as).length : Ordinal.{0}) := by
    apply principalSum_unit_word
    intro t ht
    have hm := (selectUnits_mem true as t).mp ht
    have hv := (unitTest_exact t (hs t hm.1).1 (hs t hm.1).2).mp hm.2
    have hb : denote 0 t < interpretation 0 a := by
      rw [hv]
      exact EpsilonOffsets.epsilon_one_lt (root_epsilon a ha)
    exact (transform_below_value a ha t (hs t hm.1).1 hb).trans hv
  rw [quotientTerm, Addition.transform_buildAtoms_value a _ ha _ hg hrq,
    limitTerm, Addition.transform_buildAtoms_value a _ ha _ hgl (fun t ht => hrq t (hmem t ht))]
  change principalSum (as.map (fun t => NativeContext.denote (alphaCode a) (transform a t))) =
    principalSum ((selectUnits false as).map (fun t => NativeContext.denote (alphaCode a) (transform a t))) +
      ((selectUnits true as).length : Ordinal.{0})
  conv_lhs => rw [hw, List.map_append, principalSum_append]
  rw [hunit]

theorem mapped_delta_coefficient_product (a : Nat) (ha : rootCheck a = true) :
    NativeContext.denote (alphaCode a)
        (transform a (SourceDecomposition.highPartTerm 0 0 (argumentCode a))) =
      NativeContext.base (alphaCode a) *
        (NativeContext.denote (alphaCode a) (transform a (limitTerm (argumentCode a))) +
          (coefficientOffset a : Ordinal.{0})) := by
  have hc := argument_accepted a ha
  have hr := argument_restricted a ha
  calc
    NativeContext.denote (alphaCode a) (transform a (SourceDecomposition.highPartTerm 0 0 (argumentCode a))) =
        NativeContext.base (alphaCode a) * NativeContext.denote (alphaCode a)
          (transform a (quotientTerm (argumentCode a))) := (mapped_quotient_product a _ ha hc hr).symm
    _ = _ := by rw [mapped_quotient_finite_tail a _ ha hc hr, coefficientOffset_literal a ha]

theorem delta_iota_input (a : Nat) (ha : rootCheck a = true) : inputCheck a (deltaCode a) = true := by
  have hc := argument_accepted a ha
  have hr := argument_restricted a ha
  have hd := (SourceDecomposition.parts_checked 0 0 _ hc).1
  have hn := (SourceDecomposition.parts_normal 0 0 _ hc).1
  have hrest : Restricted a (SourceDecomposition.highPartTerm 0 0 (argumentCode a)) := by
    apply buildAtoms_restricted
    intro t ht
    exact restricted_atoms a _ t hr ((SourceDecomposition.highWord_mem 0 0 _ t).mp ht).1
  exact (inputCheck_exact a _).mpr ⟨ha, SourceDecomposition.highPartTerm 0 0 _, rfl, hd, hn,
    (restricted_iff_sourceStar a ha _ hd hn).mp hrest⟩

theorem literal_delta_coefficient_product (a : Nat) (ha : rootCheck a = true) :
    NativeContext.interpretation (alphaCode a) (literalCode a (deltaCode a)) =
      NativeContext.base (alphaCode a) *
        (NativeContext.interpretation (alphaCode a) (literalCode a (coefficientCode a)) +
          (coefficientOffset a : Ordinal.{0})) := by
  have hd := delta_iota_input a ha
  have hc := coefficient_iota_input a ha
  have hdh : inputCheck a (SourceDecomposition.highPartTerm 0 0 (argumentCode a)).code = true := by
    simpa only [deltaCode, SourceDecomposition.highCode] using hd
  have hcl : inputCheck a (limitTerm (argumentCode a)).code = true := by
    simpa only [coefficientCode_literal a ha] using hc
  simp only [deltaCode, SourceDecomposition.highCode, coefficientCode_literal a ha,
    literalCode, hdh, hcl, Bool.cond_true, stateCode_code, NativeContext.interpretation_code]
  exact mapped_delta_coefficient_product a ha

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.MappedOmegaQuotient
