import Alexander313.Wilken.PublicEpsilonBoundedPublicReturn
import Alexander313.Wilken.HereditaryNativeSourceChiPowers

/-!
# Genuine iota root and parameter callers at EVERY canonical public epsilon

The literal original q context is retained, including proper epsilon
references selected from the ORIGINAL source-one grammar. The finite source
dictionary selects a genuine SAME-value public return. An original checked
Normal high root beta below its ORIGINAL selected endpoint derives every
small LOW parameter caller and its actual canonical beta. No Native base-one
parser, supplied return or target admission is used. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonIota

abbrev Context := Nat × Nat
abbrev fullList := Iota.fullList

open PublicEpsilonSourceDictionary

def rootCheck (q b : Nat) : Bool :=
  ((Return.inputCheck q b && Comparison.acceptedCode q b) &&
    Localization.rootShape b) &&
      decide (1 < (ThetaCourse.rawTree (Localization.argumentCode b)).outerSort)

theorem rootCheck_primrec : Primrec₂ rootCheck := by
  have hc := Comparison.acceptedCode_primrec
  have hshape := Localization.rootShape_primrec.comp Primrec.snd
  have hhigh := (Primrec.nat_lt.comp (Primrec.const 1)
    (outerSort_primrec.comp (ThetaCourse.rawTree_primrec.comp
      (Localization.argumentCode_primrec.comp Primrec.snd)))).decide
  exact (Primrec.and.comp
    (Primrec.and.comp (Primrec.and.comp Return.inputCheck_primrec hc) hshape) hhigh).to₂

/-- EXACT original canonical epsilon, original admitted Normal high root,
and the genuine selected ORIGINAL source endpoint. -/
theorem rootCheck_exact (q b : Nat) : rootCheck q b = true ↔
    PublicEpsilonSourceDictionary.inputCheck q = true ∧
      (∃ t : RelativeTerm Nat, b = (.theta 0 t).code ∧
        check q (.theta 0 t) = true ∧ Comparison.Normal q t ∧ 1 < t.outerSort) ∧
      interpretation q b < Return.endpoint q := by
  constructor
  · intro h
    obtain ⟨hfirst, hhigh⟩ := Bool.and_eq_true.mp h
    obtain ⟨hchecks, hshape⟩ := Bool.and_eq_true.mp hfirst
    obtain ⟨hbound, hn⟩ := Bool.and_eq_true.mp hchecks
    have hb := (Return.inputCheck_exact q b).mp hbound
    have hc := (Comparison.acceptedCode_exact q b).mp hn
    obtain ⟨v, he, ht⟩ := (checkCode_exact q b).mp hc.1
    obtain ⟨t, hvt⟩ := (Localization.rootShape_code v).mp (by simpa only [← he] using hshape)
    subst v
    refine ⟨hb.1, ⟨t, he.symm, ht, ?_, ?_⟩, hb.2.2⟩
    · simpa only [← he, ThetaCourse.rawTree_code, Comparison.Normal] using hc.2
    · simpa only [← he, Localization.argumentCode_theta, ThetaCourse.rawTree_code] using
        of_decide_eq_true hhigh
  · rintro ⟨hq, ⟨t, rfl, ht, hn, hh⟩, hb⟩
    have hl : lowCheckCode q (.theta 0 t : RelativeTerm Nat).code = true := by
      simp only [lowCheckCode_code, lowCheck, ht, RelativeTerm.outerSort, decide_true, Bool.true_and]
    have hbound := (Return.inputCheck_exact q _).mpr ⟨hq, hl, hb⟩
    have hac : Comparison.acceptedCode q (.theta 0 t : RelativeTerm Nat).code = true :=
      (Comparison.acceptedCode_exact _ _).mpr
        ⟨by simpa only [checkCode_code] using ht,
          by simpa only [ThetaCourse.rawTree_code, Comparison.Normal] using hn⟩
    exact Bool.and_eq_true.mpr ⟨Bool.and_eq_true.mpr ⟨Bool.and_eq_true.mpr ⟨hbound, hac⟩,
      (Localization.rootShape_code _).mpr ⟨t, rfl⟩⟩,
        by simpa only [Localization.argumentCode_theta, ThetaCourse.rawTree_code] using decide_eq_true hh⟩

theorem source_checked (q b : Nat) (ha : rootCheck q b = true) : baseCheck q = true :=
  input_baseCheck q ((rootCheck_exact q b).mp ha).1

theorem root_original (q b : Nat) (ha : rootCheck q b = true) : checkCode (q) b = true := by
  obtain ⟨_, ⟨t, rfl, ht, hn, hh⟩, _⟩ := (rootCheck_exact q b).mp ha
  simpa only [checkCode_code] using ht

theorem root_low (q b : Nat) (ha : rootCheck q b = true) : lowCheckCode (q) b = true := by
  obtain ⟨_, ⟨t, rfl, ht, hn, hh⟩, _⟩ := (rootCheck_exact q b).mp ha
  simp only [lowCheckCode_code, lowCheck, ht, RelativeTerm.outerSort, decide_true, Bool.true_and]

theorem root_base_le (q b : Nat) (ha : rootCheck q b = true) :
    base (q) ≤ interpretation (q) b := by
  obtain ⟨_, ⟨t, rfl, ht, hn, hh⟩, _⟩ := (rootCheck_exact q b).mp ha
  simpa only [interpretation_code] using BaseTransformation.theta_base_le (q) 0 t ht

theorem root_pos (q b : Nat) (ha : rootCheck q b = true) : 0 < interpretation (q) b :=
  (base_pos _ (source_checked q b ha)).trans_le (root_base_le q b ha)

theorem root_epsilon (q b : Nat) (ha : rootCheck q b = true) :
    Ordinal.omega0 ^ interpretation (q) b = interpretation (q) b := by
  obtain ⟨_, ⟨t, he, ht, hn, hh⟩, _⟩ := (rootCheck_exact q b).mp ha
  have hc := BaseTransformation.theta_argument_check _ 0 t ht
  have hhigh : omegaSequence (base (q)) 1 ≤ denote (q) t := by
    apply le_of_not_gt
    intro hl
    have hs := (denote_lt_iff_outerSort_le _ t hc 1 (by omega)).mp hl
    omega
  simpa only [he, interpretation_code] using SourceChi.Powers.theta_epsilon_of_high _ t ht hhigh

theorem root_base_lt (q b : Nat) (ha : rootCheck q b = true) : base q < interpretation q b := by
  obtain ⟨_, ⟨t, he, ht, hn, hh⟩, _⟩ := (rootCheck_exact q b).mp ha
  have hq := source_checked q b ha
  have hac := FixedPoint.checked_theta_argument q 0 t ht
  have hhigh : omegaSequence (base q) 1 ≤ denote q t := by
    apply le_of_not_gt
    intro h
    exact (not_le_of_gt hh) ((denote_lt_iff_outerSort_le q t hac 1 (by omega)).mp h)
  rw [he, interpretation_code]
  exact SourceChi.Powers.global_high_base_lt (base q) (base_pos q hq)
    (FixedPoint.sourceOrdinal q 0 t hac) (FixedPoint.checked_theta_sort q 0 t ht) hhigh


def betaCode (q b : Nat) : Nat := Return.publicCode q b

theorem betaCode_primrec : Primrec₂ betaCode := Return.publicCode_primrec

theorem betaCode_spec (q b : Nat) (ha : rootCheck q b = true) :
    Canonical.check (betaCode q b) = true ∧
      unionInterpretation (betaCode q b) = interpretation q b := by
  have hs := (rootCheck_exact q b).mp ha
  exact Return.publicCode_spec q b
    ((Return.inputCheck_exact q b).mpr ⟨hs.1, root_low q b ha, hs.2.2⟩)

theorem betaCode_baseCheck (q b : Nat) (ha : rootCheck q b = true) : baseCheck (betaCode q b) = true := by
  have hs := betaCode_spec q b ha
  apply (baseCheck_exact _).mpr
  refine ⟨Canonical.check_original hs.1, ?_⟩
  change Ordinal.omega0 ^ unionInterpretation (betaCode q b) = _
  rw [hs.2]
  exact root_epsilon q b ha

theorem beta_base (q b : Nat) (ha : rootCheck q b = true) :
    base (betaCode q b) = interpretation (q) b := (betaCode_spec q b ha).2

def Restricted (q b : Nat) (t : RelativeTerm Nat) : Prop :=
  ∀ u ∈ fullList t, denote (q) u < interpretation (q) b

theorem restricted_sum (q b : Nat) (t u : RelativeTerm Nat) :
    Restricted q b (.sum t u) ↔ Restricted q b t ∧ Restricted q b u := by
  constructor
  · intro h
    exact ⟨fun v hv => h v (List.mem_append_left _ hv), fun v hv => h v (List.mem_append_right _ hv)⟩
  · rintro ⟨ht, hu⟩ v hv
    exact (List.mem_append.mp hv).elim (ht v) (hu v)

theorem restricted_theta_zero (q b : Nat) (t : RelativeTerm Nat) :
    Restricted q b (.theta 0 t) ↔
      denote (q) (.theta 0 t) < interpretation (q) b ∧ Restricted q b t := by
  simp only [Restricted, fullList, RelativeTerm.PrincipalSupport.principalList_theta_same, List.forall_mem_cons]

theorem restricted_theta_succ (q b k : Nat) (t : RelativeTerm Nat) :
    Restricted q b (.theta (k + 1) t) ↔ Restricted q b t := by
  rw [Restricted, fullList,
    RelativeTerm.PrincipalSupport.principalList_theta_higher 0 (k + 1) t (Nat.succ_pos k)]
  rfl

theorem restricted_iff_sourceStar (q b : Nat) (ha : rootCheck q b = true)
    (t : RelativeTerm Nat) (ht : check (q) t = true) (hn : Comparison.Normal (q) t) :
    Restricted q b t ↔ Iota.sourceStar (q) t < interpretation (q) b := by
  rw [Iota.sourceStar, Iota.sourceSupport_fullList _ t ht hn, Finset.sup_lt_iff (root_pos q b ha)]
  simp only [Restricted, List.mem_toFinset, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff]

theorem argument_restricted (q b : Nat) (ha : rootCheck q b = true) :
    Restricted q b (ThetaCourse.rawTree (Localization.argumentCode b)) := by
  obtain ⟨_, ⟨t, he, ht, hn, hh⟩, _⟩ := (rootCheck_exact q b).mp ha
  simp only [he, Localization.argumentCode_theta, ThetaCourse.rawTree_code]
  intro u hu
  let n := SourceOne.PublicCodes.fragment (.theta 0 t)
  have hq := source_checked q b ha
  have had := checked_admissible q (.theta 0 t) ht
  have haa := Comparison.admitted_argument had
  have hua := RelativeTerm.PrincipalSupport.principalList_admissible haa.2 0 hu
  have h := RelativeTerm.PrincipalSupport.principalList_argument_lt (base q) (base_pos q hq)
    parameters n 0 t u had.2 ((Comparison.normal_finite_iff q n hq t haa.2).mpr hn) hu
  rw [← denote_eq_finite q n hq u hua, ← denote_eq_finite q n hq (.theta 0 t) had.2] at h
  simpa only [he, interpretation_code] using h

theorem below_low (q b : Nat) (ha : rootCheck q b = true) (t : RelativeTerm Nat)
    (ht : check (q) t = true) (hb : denote (q) t < interpretation (q) b) :
    lowCheckCode (q) t.code = true := by
  obtain ⟨u, he, hu⟩ := (lowCheckCode_exact _ b).mp (root_low q b ha)
  have hs := Bool.and_eq_true.mp hu
  have hroot : interpretation (q) b < omegaSequence (base (q)) 1 := by
    rw [← he, interpretation_code]
    exact (denote_lt_iff_outerSort_le _ u hs.1 1 (by omega)).mpr (of_decide_eq_true hs.2)
  have hl := (denote_lt_iff_outerSort_le _ t ht 1 (by omega)).mp (hb.trans hroot)
  simp only [lowCheckCode_code, lowCheck, ht, hl, decide_true, Bool.true_and]

def parameterCode (q : Nat) (t : RelativeTerm Nat) : Nat := Return.publicCode q t.code

theorem parameterCode_primrec : Primrec₂ parameterCode :=
  (Return.publicCode_primrec.comp Primrec.fst (code_primrec.comp Primrec.snd)).to₂

/-- The actual original small-value and root bound derive EVERY return
and target-beta parameter caller, including the proper source-one case. -/
theorem parameterCode_spec (q b : Nat) (ha : rootCheck q b = true) (t : RelativeTerm Nat)
    (ht : check q t = true) (hb : denote q t < interpretation q b) :
    parameterCheck (betaCode q b) (parameterCode q t) = true ∧
      parameters (parameterCode q t) = denote q t := by
  have hr := (rootCheck_exact q b).mp ha
  have hi := (Return.inputCheck_exact q t.code).mpr
    ⟨hr.1, below_low q b ha t ht hb,
      by simpa only [interpretation_code] using hb.trans hr.2.2⟩
  have hp := Return.publicCode_spec q t.code hi
  have hv : parameters (parameterCode q t) = denote q t :=
    hp.2.trans (interpretation_code q t)
  refine ⟨(parameterCheck_exact _ _).mpr
    ⟨Canonical.check_original hp.1, Canonical.check_original (betaCode_spec q b ha).1, ?_⟩, hv⟩
  change parameters (parameterCode q t) < unionInterpretation (betaCode q b)
  rw [hv, (betaCode_spec q b ha).2]
  exact hb

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonIota
