import Alexander313.Wilken.HereditaryNativeUniformPublicReturn
import Alexander313.Wilken.PublicEpsilonNativeRootLowCollapseSupport
import Alexander313.Wilken.HereditaryNativeSourceChiPowers

/-!
# Genuine endpoint-free iota callers at every admitted public epsilon

The literal original q is retained, including noncanonical admitted base
spellings and proper source-one references. The actual whole RAW LOW
public return computes beta and each stopped parameter. Original checked
Normal high-root admission derives every hidden caller. No selected source
endpoint, supplied public value, target admission or return oracle.
These source-only candidates are uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota

abbrev Context := Nat × Nat
abbrev fullList := Iota.fullList
abbrev rootCheck := RootLowCollapse.rootCheck

theorem rootCheck_primrec : Primrec₂ rootCheck := RootLowCollapse.rootCheck_primrec

/-- EXACT original checked Normal high root at any admitted original q;
there is no canonical base-spelling or selected endpoint premise. -/
theorem rootCheck_exact (q b : Nat) : rootCheck q b = true ↔
    ∃ t : RelativeTerm Nat, b = (.theta 0 t).code ∧
      check q (.theta 0 t) = true ∧ Comparison.Normal q t ∧ 1 < t.outerSort :=
  RootLowCollapse.rootCheck_exact q b

theorem source_checked (q b : Nat) (ha : rootCheck q b = true) : baseCheck q = true :=
  RootLowCollapse.source_checked q b ha

theorem root_original (q b : Nat) (ha : rootCheck q b = true) : checkCode q b = true :=
  RootLowCollapse.root_original q b ha

theorem root_low (q b : Nat) (ha : rootCheck q b = true) : lowCheckCode q b = true :=
  RootLowCollapse.root_low q b ha

theorem root_base_le (q b : Nat) (ha : rootCheck q b = true) :
    base q ≤ interpretation q b := RootLowCollapse.root_base_le q b ha

theorem root_pos (q b : Nat) (ha : rootCheck q b = true) : 0 < interpretation q b :=
  (base_pos q (source_checked q b ha)).trans_le (root_base_le q b ha)

theorem root_epsilon (q b : Nat) (ha : rootCheck q b = true) :
    Ordinal.omega0 ^ interpretation q b = interpretation q b :=
  RootLowCollapse.root_epsilon q b ha

theorem root_base_lt (q b : Nat) (ha : rootCheck q b = true) : base q < interpretation q b := by
  obtain ⟨t, he, ht, hn, hh⟩ := (rootCheck_exact q b).mp ha
  have hq := source_checked q b ha
  have hac := FixedPoint.checked_theta_argument q 0 t ht
  have hhigh : omegaSequence (base q) 1 ≤ denote q t := by
    apply le_of_not_gt
    intro h
    exact (not_le_of_gt hh) ((denote_lt_iff_outerSort_le q t hac 1 (by omega)).mp h)
  rw [he, interpretation_code]
  exact SourceChi.Powers.global_high_base_lt (base q) (base_pos q hq)
    (FixedPoint.sourceOrdinal q 0 t hac) (FixedPoint.checked_theta_sort q 0 t ht) hhigh

def betaCode (q b : Nat) : Nat := UniformPublicReturn.publicCode q b

theorem betaCode_primrec : Primrec₂ betaCode := UniformPublicReturn.publicCode_primrec

theorem betaCode_spec (q b : Nat) (ha : rootCheck q b = true) :
    Canonical.check (betaCode q b) = true ∧
      unionInterpretation (betaCode q b) = interpretation q b :=
  UniformPublicReturn.publicCode_spec q b
    ((UniformPublicReturn.inputCheck_exact q b).mpr (root_low q b ha))

theorem betaCode_baseCheck (q b : Nat) (ha : rootCheck q b = true) : baseCheck (betaCode q b) = true := by
  have hs := betaCode_spec q b ha
  apply (baseCheck_exact _).mpr
  refine ⟨Canonical.check_original hs.1, ?_⟩
  change Ordinal.omega0 ^ unionInterpretation (betaCode q b) = _
  rw [hs.2]
  exact root_epsilon q b ha

theorem beta_base (q b : Nat) (ha : rootCheck q b = true) :
    base (betaCode q b) = interpretation q b := (betaCode_spec q b ha).2

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
  obtain ⟨t, he, ht, hn, hh⟩ := (rootCheck_exact q b).mp ha
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

def parameterCode (q : Nat) (t : RelativeTerm Nat) : Nat := UniformPublicReturn.publicCode q t.code

theorem parameterCode_primrec : Primrec₂ parameterCode :=
  (UniformPublicReturn.publicCode_primrec.comp Primrec.fst (code_primrec.comp Primrec.snd)).to₂

/-- Actual small-value admission derives every whole LOW return and
target-beta parameter caller, including arbitrary hidden source trees. -/
theorem parameterCode_spec (q b : Nat) (ha : rootCheck q b = true) (t : RelativeTerm Nat)
    (ht : check q t = true) (hb : denote q t < interpretation q b) :
    parameterCheck (betaCode q b) (parameterCode q t) = true ∧
      parameters (parameterCode q t) = denote q t := by
  have hi := (UniformPublicReturn.inputCheck_exact q t.code).mpr (below_low q b ha t ht hb)
  have hp := UniformPublicReturn.publicCode_spec q t.code hi
  have hv : parameters (parameterCode q t) = denote q t :=
    hp.2.trans (interpretation_code q t)
  refine ⟨(parameterCheck_exact _ _).mpr
    ⟨Canonical.check_original hp.1, Canonical.check_original (betaCode_spec q b ha).1, ?_⟩, hv⟩
  change parameters (parameterCode q t) < unionInterpretation (betaCode q b)
  rw [hv, (betaCode_spec q b ha).2]
  exact hb

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota
