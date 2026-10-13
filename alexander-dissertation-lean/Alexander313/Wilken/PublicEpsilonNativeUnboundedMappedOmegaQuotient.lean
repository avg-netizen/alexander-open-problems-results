import Alexander313.Wilken.PublicEpsilonNativeUnboundedMappedOmegaQuotientSupport

/-!
# Genuine mapped Omega-one quotient atoms

Each ORIGINAL admitted Normal restricted positive atom satisfies the target
base product identity. The source theta-one LOW, real middle subtraction,
threshold absorption and higher-index cases are proved separately. Every
comparison, source restriction and target collapse caller is derived from
the unchanged original domain. No iota multiplication oracle. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.MappedOmegaQuotient

open OrderSupport
open PublicEpsilonIota.MappedOmegaQuotient
  (theta_zero_below_threshold theta_zero_shifted_quotient
   theta_zero_above_threshold principal_above_first_absorbs)
open BoundedContextIota.OmegaQuotient (atomTerm)
open Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.OmegaQuotient
  (baseTerm thresholdTerm baseTerm_spec thresholdTerm_spec theta_principal epsilon_above_absorbs)

/-- The actual literal quotient of every original positive atom maps to
its true target-base quotient. This is proved from actual arithmetic and
full original iota order, rather than ordinary additivity alone. -/
theorem mapped_atom_product (q root k : Nat) (ha : rootCheck q root = true)
    (t : RelativeTerm Nat) (ht : check q (.theta (k + 1) t) = true)
    (hn : Comparison.Normal q t) (hr : Restricted q root (.theta (k + 1) t)) :
    base (betaCode q root) *
        denote (betaCode q root) (transform q root (atomTerm q (.theta (k + 1) t))) =
      denote (betaCode q root) (transform q root (.theta (k + 1) t)) := by
  have hq := source_checked q root ha
  have hβq := betaCode_baseCheck q root ha
  have hε := ((baseCheck_exact _).mp hβq).2
  have hc := BaseTransformation.theta_argument_check q (k + 1) t ht
  have hrt := (restricted_theta_succ q root k t).mp hr
  have has := OmegaQuotient.Support.atom_spec q root k ha t ht hn hr
  cases k with
  | succ k =>
    have hk : (k + 1 + 1 == 1) = false := by
      apply Bool.eq_false_of_not_eq_true
      intro he
      have h := beq_iff_eq.mp he
      omega
    simp only [atomTerm, hk, Bool.cond_false]
    have htc := transform_checked q root ha (.theta (k + 1 + 1) t) ht hr
    rw [transform_theta_succ q root (k + 1) ha t ht hr] at htc ⊢
    have hp := theta_principal _ (k + 1) (transform q root t) htc
    apply principal_above_first_absorbs _ _ hε hp.2
    exact ((omegaSequence_strictMono (base (betaCode q root))).monotone
      (by omega : 1 ≤ k + 1)).trans
        (FixedPoint.checked_theta_range _ (k + 1) _ htc).1
  | zero =>
    simp only [Nat.zero_add] at ht hr hc hrt has ⊢
    by_cases hl : t.outerSort ≤ 1
    · have htlow : lowCheckCode q t.code = true := by
        simp only [lowCheckCode_code, lowCheck, hc, hl, decide_true, Bool.true_and]
      have hp := OmegaPowers.powerCode_spec q t.code htlow
      have hv : denote q (ThetaCourse.rawTree (OmegaPowers.powerCode q t.code)) =
          Ordinal.omega0 ^ denote q t := by
        rw [Arithmetic.raw_value q _ ((Comparison.acceptedCode_exact q _).mp hp.2.1).1,
          hp.2.2, interpretation_code]
      have hηβ : denote q t < base (betaCode q root) := by
        rw [beta_base q root ha]
        exact restricted_low_below q root ha t hc hrt hl
      have hpowerβ : denote q (ThetaCourse.rawTree (OmegaPowers.powerCode q t.code)) <
          interpretation q root := by
        rw [hv, ← beta_base q root ha]
        exact (omegaPower_strictMono hηβ).trans_eq hε
      have hpc := Arithmetic.raw_checked q _ ((Comparison.acceptedCode_exact q _).mp hp.2.1).1
      simp only [atomTerm, beq_self_eq_true, Bool.cond_true, hl, decide_true]
      rw [(transform_parameter_value q root ha _ hpc hpowerβ).2, hv,
        transform_theta_succ q root 0 ha t ht hr]
      change base (betaCode q root) * Ordinal.omega0 ^ denote q t =
        globalCollapse (base (betaCode q root)) 0
          (denote (betaCode q root) (transform q root t))
      rw [transform_low_value q root ha t hc hrt hl]
      apply (theta_zero_below_threshold _ _ hε ?_).symm
      exact hηβ.trans (by
        calc
          base (betaCode q root) = base (betaCode q root) * 1 := (mul_one _).symm
          _ < base (betaCode q root) * Ordinal.omega0 :=
            mul_lt_mul_of_pos_left Ordinal.one_lt_omega0 (base_pos _ hβq))
    · have hbase : omegaSequence (base q) 1 ≤ denote q t := le_of_not_gt (by
        intro h
        exact hl ((denote_lt_iff_outerSort_le q t hc 1 (by omega)).mp h))
      have hth := thresholdTerm_spec q hq
      have hb := baseTerm_spec q hq
      have hτle : base (betaCode q root) ≤ denote (betaCode q root) (transform q root t) := by
        rw [← mapped_baseTerm q root ha]
        exact (transform_le_iff q root ha baseTerm t hb.1 hc hb.2.1 hn
          (baseTerm_restricted q root) hrt).mpr (by rw [hb.2.2]; exact hbase)
      cases hm : Comparison.less q t thresholdTerm with
      | true =>
        have hηth : denote q t < omegaSequence (base q) 1 * Ordinal.omega0 := by
          rw [← hth.2.2]
          exact (Comparison.less_correct q t thresholdTerm hc hth.1 hn hth.2.1).mp hm
        have hηtarget : denote (betaCode q root) (transform q root t) <
            base (betaCode q root) * Ordinal.omega0 := by
          rw [← mapped_thresholdTerm q root ha]
          exact (transform_lt_iff q root ha t thresholdTerm hc hth.1 hn hth.2.1 hrt
            (thresholdTerm_restricted q root)).mpr (by rw [hth.2.2]; exact hηth)
        let d := Arithmetic.subtractTerm q baseTerm.code t.code
        have has' : check q (.theta 1 d) = true ∧ Comparison.Normal q (.theta 1 d) ∧
            Restricted q root (.theta 1 d) := by
          simpa only [atomTerm, beq_self_eq_true, Bool.cond_true, hl, decide_false,
            Bool.cond_false, hm] using ⟨has.1, has.2.1, has.2.2.1⟩
        simp only [atomTerm, beq_self_eq_true, Bool.cond_true, hl, decide_false,
          Bool.cond_false, hm]
        rw [transform_theta_succ q root 0 ha d has'.1 has'.2.2,
          transform_theta_succ q root 0 ha t ht hr]
        change base (betaCode q root) * globalCollapse (base (betaCode q root)) 0
            (denote (betaCode q root) (transform q root d)) =
          globalCollapse (base (betaCode q root)) 0
            (denote (betaCode q root) (transform q root t))
        rw [mapped_subtract_base q root ha t hc hn hrt hbase]
        exact theta_zero_shifted_quotient _ _ hε hτle hηtarget
      | false =>
        have hηth : omegaSequence (base q) 1 * Ordinal.omega0 ≤ denote q t := by
          rw [← hth.2.2]
          apply le_of_not_gt
          intro h
          have he := (Comparison.less_correct q t thresholdTerm hc hth.1 hn hth.2.1).mpr h
          simp only [hm, Bool.false_eq_true] at he
        have hηtarget : base (betaCode q root) * Ordinal.omega0 ≤
            denote (betaCode q root) (transform q root t) := by
          rw [← mapped_thresholdTerm q root ha]
          exact (transform_le_iff q root ha thresholdTerm t hth.1 hc hth.2.1 hn
            (thresholdTerm_restricted q root) hrt).mpr (by rw [hth.2.2]; exact hηth)
        simp only [atomTerm, beq_self_eq_true, Bool.cond_true, hl, decide_false,
          Bool.cond_false, hm]
        have htc := transform_checked q root ha (.theta 1 t) ht hr
        rw [transform_theta_succ q root 0 ha t ht hr] at htc ⊢
        by_cases hlow : denote (betaCode q root) (transform q root t) <
            omegaSequence (base (betaCode q root)) 1
        · exact theta_zero_above_threshold _ _ hε hηtarget hlow
        · have hhigh := le_of_not_gt hlow
          have hep := SourceChi.Powers.theta_epsilon_of_high _ (transform q root t) htc hhigh
          have htarg := FixedPoint.checked_theta_argument _ 0 (transform q root t) htc
          have hlt := SourceChi.Powers.global_high_base_lt _ (base_pos _ hβq)
            (FixedPoint.sourceOrdinal _ 0 (transform q root t) htarg)
            (FixedPoint.checked_theta_sort _ 0 (transform q root t) htc) hhigh
          exact epsilon_above_absorbs _ _ hε hep hlt

/-- Every ORIGINAL high-word atom satisfies the product identity, with
its positive index and every restriction derived from that actual word. -/
theorem mapped_high_atom_product (q root c : Nat) (ha : rootCheck q root = true)
    (hc : Decomposition.inputCheck q c = true) (hr : Restricted q root (ThetaCourse.rawTree c))
    (t : RelativeTerm Nat) (ht : t ∈ Decomposition.highWord 0 c) :
    base (betaCode q root) * denote (betaCode q root) (transform q root (atomTerm q t)) =
      denote (betaCode q root) (transform q root t) := by
  have hm := (Decomposition.highWord_mem 0 c t).mp ht
  have hs := (Decomposition.word_spec q c hc).1 t hm.1
  have hrest := OmegaQuotient.Support.atoms_restricted q root (ThetaCourse.rawTree c) hr t hm.1
  rcases Comparison.atoms_shape (ThetaCourse.rawTree c) t hm.1 with ⟨p, rfl⟩ | ⟨k, u, rfl⟩
  · have hb := hm.2
    simp only [Decomposition.above, RelativeTerm.outerSort, Nat.zero_add,
      decide_false, Bool.false_eq_true] at hb
  · cases k with
    | zero =>
      have hb := hm.2
      simp only [Decomposition.above, RelativeTerm.outerSort, Nat.zero_add,
        Nat.lt_irrefl, decide_false, Bool.false_eq_true] at hb
    | succ k => exact mapped_atom_product q root k ha u hs.1 hs.2.1 hrest

private theorem mul_principalSum_congr (β : Ordinal.{0})
    (as : List (RelativeTerm Nat)) (f g : RelativeTerm Nat → Ordinal.{0})
    (h : ∀ t ∈ as, β * f t = g t) :
    β * principalSum (as.map f) = principalSum (as.map g) := by
  revert h
  induction as with
  | nil => intro _; simp only [List.map_nil, principalSum, mul_zero]
  | cons t as ih =>
    intro h
    simp only [List.map_cons, principalSum, mul_add]
    rw [h t List.mem_cons_self, ih (fun u hu => h u (List.mem_cons_of_mem _ hu))]

/-- The actual transformed quotient word multiplies back to the actual
transformed divided head, on the WHOLE original normal restricted domain. -/
theorem mapped_quotient_product (q root c : Nat) (ha : rootCheck q root = true)
    (hc : Decomposition.inputCheck q c = true) (hr : Restricted q root (ThetaCourse.rawTree c)) :
    base (betaCode q root) * denote (betaCode q root)
        (transform q root (BoundedContextIota.OmegaQuotient.quotientTerm q c)) =
      denote (betaCode q root) (transform q root (Decomposition.highPartTerm 0 c)) := by
  have hg := OmegaQuotient.quotientWord_good q root c ha hc hr
  have hgr : ∀ t ∈ BoundedContextIota.OmegaQuotient.quotientWord q c, Restricted q root t := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
    exact (OmegaQuotient.high_atom_spec q root c ha hc hr u hu).2.2.1
  have hhigh := (Decomposition.words_good q (ThetaCourse.rawTree c).height 0 c hc le_rfl).1
  have hhighr : ∀ t ∈ Decomposition.highWord 0 c, Restricted q root t := by
    intro t ht
    exact OmegaQuotient.Support.atoms_restricted q root (ThetaCourse.rawTree c) hr t
      ((Decomposition.highWord_mem 0 c t).mp ht).1
  rw [BoundedContextIota.OmegaQuotient.quotientTerm,
    Addition.transform_buildAtoms_value q root _ ha _ hg hgr,
    BoundedContextIota.OmegaQuotient.quotientWord, List.map_map]
  exact (mul_principalSum_congr _ _ _ _
    (fun t ht => mapped_high_atom_product q root c ha hc hr t ht)).trans
      (Addition.transform_buildAtoms_value q root _ ha _ hhigh hhighr).symm

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

/-- Real unit stripping of the ORIGINAL descending quotient word gives
exactly the mapped zero-or-limit coefficient and the SAME finite offset. -/
theorem mapped_quotient_finite_tail (q root c : Nat) (ha : rootCheck q root = true)
    (hc : Decomposition.inputCheck q c = true) (hr : Restricted q root (ThetaCourse.rawTree c)) :
    denote (betaCode q root) (transform q root (BoundedContextIota.OmegaQuotient.quotientTerm q c)) =
      denote (betaCode q root) (transform q root (BoundedContextIota.OmegaQuotient.limitTerm q c)) +
        (BoundedContextIota.OmegaQuotient.finiteOffset q c : Ordinal.{0}) := by
  let as := BoundedContextIota.OmegaQuotient.quotientWord q c
  have hq := source_checked q root ha
  have hg := OmegaQuotient.quotientWord_good q root c ha hc hr
  have hrq : ∀ t ∈ as, Restricted q root t := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
    exact (OmegaQuotient.high_atom_spec q root c ha hc hr u hu).2.2.1
  have hs : ∀ t ∈ as, check q t = true ∧ Comparison.Normal q t := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
    have h := OmegaQuotient.high_atom_spec q root c ha hc hr u hu
    exact ⟨h.1, h.2.1⟩
  have hw := BoundedContextIota.OmegaQuotient.Support.unit_partition q hq as
    (OmegaQuotient.quotientWord_normal q root c ha hc hr) hs
  have hmem : ∀ t ∈ NativeContext.OmegaQuotient.selectUnits false q as, t ∈ as :=
    fun t ht => ((NativeContext.OmegaQuotient.selectUnits_mem false q as t).mp ht).1
  have hgl : Normalization.GoodAtoms q (NativeContext.OmegaQuotient.wordHeight as)
      (NativeContext.OmegaQuotient.selectUnits false q as) := fun t ht => hg t (hmem t ht)
  have hunit : principalSum ((NativeContext.OmegaQuotient.selectUnits true q as).map
      (fun t => denote (betaCode q root) (transform q root t))) =
        ((NativeContext.OmegaQuotient.selectUnits true q as).length : Ordinal.{0}) := by
    apply principalSum_unit_word
    intro t ht
    have hm := (NativeContext.OmegaQuotient.selectUnits_mem true q as t).mp ht
    have hv := (NativeContext.OmegaQuotient.unitTest_exact q hq t
      (hs t hm.1).1 (hs t hm.1).2).mp hm.2
    have hb : denote q t < interpretation q root := by
      rw [hv, ← beta_base q root ha]
      exact LogEndZero.one_lt_base _ (betaCode_baseCheck q root ha)
    exact (transform_parameter_value q root ha t (hs t hm.1).1 hb).2.trans hv
  rw [BoundedContextIota.OmegaQuotient.quotientTerm,
    Addition.transform_buildAtoms_value q root _ ha _ hg hrq,
    BoundedContextIota.OmegaQuotient.limitTerm,
    Addition.transform_buildAtoms_value q root _ ha _ hgl (fun t ht => hrq t (hmem t ht))]
  change principalSum (as.map (fun t => denote (betaCode q root) (transform q root t))) =
    principalSum ((NativeContext.OmegaQuotient.selectUnits false q as).map
      (fun t => denote (betaCode q root) (transform q root t))) +
        ((NativeContext.OmegaQuotient.selectUnits true q as).length : Ordinal.{0})
  conv_lhs => rw [hw, List.map_append, principalSum_append]
  rw [hunit]

/-- The original root alone yields the genuine mapped divided-head
factorization required by source3.14(a). No coefficient or product oracle. -/
theorem mapped_delta_coefficient_product (q root : Nat) (ha : rootCheck q root = true) :
    denote (betaCode q root)
        (transform q root (Decomposition.highPartTerm 0 (Localization.argumentCode root))) =
      base (betaCode q root) *
        (denote (betaCode q root) (transform q root
          (BoundedContextIota.OmegaQuotient.limitTerm q (Localization.argumentCode root))) +
            (OmegaQuotient.coefficientOffset q root : Ordinal.{0})) := by
  have hc := OmegaQuotient.Support.argument_accepted q root ha
  have hr := argument_restricted q root ha
  calc
    denote (betaCode q root)
        (transform q root (Decomposition.highPartTerm 0 (Localization.argumentCode root))) =
        base (betaCode q root) * denote (betaCode q root)
          (transform q root (BoundedContextIota.OmegaQuotient.quotientTerm q
            (Localization.argumentCode root))) := (mapped_quotient_product q root _ ha hc hr).symm
    _ = _ := by
      rw [mapped_quotient_finite_tail q root _ ha hc hr,
        OmegaQuotient.coefficientOffset_literal q root ha]

/-- The actual divided head retains admission, Normality and full
restriction; the original root derives its literal iota caller. -/
theorem delta_iota_input (q root : Nat) (ha : rootCheck q root = true) :
    inputCheck q root (OmegaQuotient.deltaCode root) = true := by
  have hc := OmegaQuotient.Support.argument_accepted q root ha
  have hr := argument_restricted q root ha
  have hd := (Decomposition.parts_checked q 0 _ hc).1
  have hn := (Decomposition.parts_normal q 0 _ hc).1
  have hrest : Restricted q root (Decomposition.highPartTerm 0 (Localization.argumentCode root)) := by
    apply OmegaQuotient.Support.buildAtoms_restricted
    intro t ht
    exact OmegaQuotient.Support.atoms_restricted q root _ hr t
      ((Decomposition.highWord_mem 0 _ t).mp ht).1
  exact (inputCheck_exact q root _).mpr ⟨ha, Decomposition.highPartTerm 0 _, rfl, hd, hn,
    (restricted_iff_sourceStar q root ha _ hd hn).mp hrest⟩

/-- The REAL guarded literal iota programs satisfy the complete mapped
Omega-one coefficient product equation at the same target beta. -/
theorem literal_delta_coefficient_product (q root : Nat) (ha : rootCheck q root = true) :
    interpretation (betaCode q root) (literalCode q root (OmegaQuotient.deltaCode root)) =
      base (betaCode q root) *
        (interpretation (betaCode q root)
          (literalCode q root (OmegaQuotient.coefficientCode q root)) +
            (OmegaQuotient.coefficientOffset q root : Ordinal.{0})) := by
  have hd := delta_iota_input q root ha
  have hc := OmegaQuotient.coefficient_iota_input q root ha
  have hdh : inputCheck q root
      (Decomposition.highPartTerm 0 (Localization.argumentCode root)).code = true := by
    simpa only [OmegaQuotient.deltaCode, Decomposition.highCode] using hd
  have hcl : inputCheck q root
      (BoundedContextIota.OmegaQuotient.limitTerm q (Localization.argumentCode root)).code = true := by
    simpa only [OmegaQuotient.coefficientCode_literal q root ha] using hc
  simp only [OmegaQuotient.deltaCode, Decomposition.highCode,
    OmegaQuotient.coefficientCode_literal q root ha, literalCode, hdh, hcl,
    Bool.cond_true, stateCode_code, interpretation_code]
  exact mapped_delta_coefficient_product q root ha

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.MappedOmegaQuotient
