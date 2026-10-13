import Alexander313.Wilken.HereditaryNativeBoundedPublicReturnCodes
import Alexander313.Wilken.HereditaryNativeSourceChiPowers

/-!
# Genuine intermediate-context root and parameter callers

An original positive-source root supplies its actual coded-alpha context.
The new beta is an actually checked Normal high theta-zero root in THAT
context, below ORIGINAL alpha-plus. The full bounded SAME-value return
computes its public code and every low-subtree parameter code. Original
full principal restriction supplies its true source-star condition. No
new-root public value, admission, translation or parameter oracle occurs.
This constructs the actual finite callers, not full order or coverage.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.BoundedContextIota

abbrev Context := (Nat × Nat) × Nat
abbrev fullList := Iota.fullList

def sourceCode (s a : Nat) : Nat := Iota.alphaCode s a

theorem sourceCode_primrec : Primrec₂ sourceCode := Iota.alphaCode_primrec

def rootCheck (s a b : Nat) : Bool :=
  ((BoundedPublicReturn.inputCheck s a b && Comparison.acceptedCode (sourceCode s a) b) &&
    Localization.rootShape b) &&
      decide (1 < (ThetaCourse.rawTree (Localization.argumentCode b)).outerSort)

theorem rootCheck_primrec : Primrec (fun p : Context => rootCheck p.1.1 p.1.2 p.2) := by
  have hs := Primrec.fst.comp Primrec.fst
  have ha := Primrec.snd.comp Primrec.fst
  have hq := sourceCode_primrec.comp hs ha
  have hc := Comparison.acceptedCode_primrec.comp hq Primrec.snd
  have hshape := Localization.rootShape_primrec.comp Primrec.snd
  have hhigh := (Primrec.nat_lt.comp (Primrec.const 1)
    (outerSort_primrec.comp (ThetaCourse.rawTree_primrec.comp
      (Localization.argumentCode_primrec.comp Primrec.snd)))).decide
  exact Primrec.and.comp
    (Primrec.and.comp (Primrec.and.comp BoundedPublicReturn.inputCheck_primrec hc) hshape) hhigh

theorem rootCheck_exact (s a b : Nat) : rootCheck s a b = true ↔
    Iota.rootCheck s a = true ∧
      (∃ t : RelativeTerm Nat, b = (.theta 0 t).code ∧
        check (sourceCode s a) (.theta 0 t) = true ∧ Comparison.Normal (sourceCode s a) t ∧
          1 < t.outerSort) ∧
      interpretation (sourceCode s a) b < Iota.AlphaPlus.sourceValue s a := by
  constructor
  · intro h
    obtain ⟨hfirst, hhigh⟩ := Bool.and_eq_true.mp h
    obtain ⟨hchecks, hshape⟩ := Bool.and_eq_true.mp hfirst
    obtain ⟨hbound, hn⟩ := Bool.and_eq_true.mp hchecks
    have hb := (BoundedPublicReturn.inputCheck_exact s a b).mp hbound
    have hc := (Comparison.acceptedCode_exact _ b).mp hn
    obtain ⟨v, he, ht⟩ := (checkCode_exact _ b).mp hc.1
    obtain ⟨t, hvt⟩ := (Localization.rootShape_code v).mp (by simpa only [← he] using hshape)
    subst v
    refine ⟨hb.1, ⟨t, he.symm, ht, ?_, ?_⟩, hb.2.2⟩
    · simpa only [← he, ThetaCourse.rawTree_code, Comparison.Normal] using hc.2
    · simpa only [← he, Localization.argumentCode_theta, ThetaCourse.rawTree_code] using
        of_decide_eq_true hhigh
  · rintro ⟨ha, ⟨t, rfl, ht, hn, hh⟩, hb⟩
    have hl : lowCheckCode (sourceCode s a) (.theta 0 t : RelativeTerm Nat).code = true := by
      simp only [lowCheckCode_code, lowCheck, ht, RelativeTerm.outerSort, decide_true, Bool.true_and]
    have hbound := (BoundedPublicReturn.inputCheck_exact s a _).mpr ⟨ha, hl, hb⟩
    have hac : Comparison.acceptedCode (sourceCode s a) (.theta 0 t : RelativeTerm Nat).code = true :=
      (Comparison.acceptedCode_exact _ _).mpr
        ⟨by simpa only [checkCode_code] using ht,
          by simpa only [ThetaCourse.rawTree_code, Comparison.Normal] using hn⟩
    exact Bool.and_eq_true.mpr ⟨Bool.and_eq_true.mpr ⟨Bool.and_eq_true.mpr ⟨hbound, hac⟩,
      (Localization.rootShape_code _).mpr ⟨t, rfl⟩⟩,
        by simpa only [Localization.argumentCode_theta, ThetaCourse.rawTree_code] using decide_eq_true hh⟩

theorem outer_root (s a b : Nat) (ha : rootCheck s a b = true) : Iota.rootCheck s a = true :=
  ((rootCheck_exact s a b).mp ha).1

theorem sourceCode_checked (s a b : Nat) (ha : rootCheck s a b = true) : baseCheck (sourceCode s a) = true :=
  Iota.alphaCode_baseCheck s a (outer_root s a b ha)

theorem root_original (s a b : Nat) (ha : rootCheck s a b = true) : checkCode (sourceCode s a) b = true := by
  obtain ⟨_, ⟨t, rfl, ht, hn, hh⟩, _⟩ := (rootCheck_exact s a b).mp ha
  simpa only [checkCode_code] using ht

theorem root_low (s a b : Nat) (ha : rootCheck s a b = true) : lowCheckCode (sourceCode s a) b = true := by
  obtain ⟨_, ⟨t, rfl, ht, hn, hh⟩, _⟩ := (rootCheck_exact s a b).mp ha
  simp only [lowCheckCode_code, lowCheck, ht, RelativeTerm.outerSort, decide_true, Bool.true_and]

theorem root_base_le (s a b : Nat) (ha : rootCheck s a b = true) :
    base (sourceCode s a) ≤ interpretation (sourceCode s a) b := by
  obtain ⟨_, ⟨t, rfl, ht, hn, hh⟩, _⟩ := (rootCheck_exact s a b).mp ha
  simpa only [interpretation_code] using BaseTransformation.theta_base_le (sourceCode s a) 0 t ht

theorem root_pos (s a b : Nat) (ha : rootCheck s a b = true) : 0 < interpretation (sourceCode s a) b :=
  (base_pos _ (sourceCode_checked s a b ha)).trans_le (root_base_le s a b ha)

theorem root_epsilon (s a b : Nat) (ha : rootCheck s a b = true) :
    Ordinal.omega0 ^ interpretation (sourceCode s a) b = interpretation (sourceCode s a) b := by
  obtain ⟨_, ⟨t, he, ht, hn, hh⟩, _⟩ := (rootCheck_exact s a b).mp ha
  have hc := BaseTransformation.theta_argument_check _ 0 t ht
  have hhigh : omegaSequence (base (sourceCode s a)) 1 ≤ denote (sourceCode s a) t := by
    apply le_of_not_gt
    intro hl
    have hs := (denote_lt_iff_outerSort_le _ t hc 1 (by omega)).mp hl
    omega
  simpa only [he, interpretation_code] using SourceChi.Powers.theta_epsilon_of_high _ t ht hhigh

def betaCode (s a b : Nat) : Nat := BoundedPublicReturn.publicCode s a b

theorem betaCode_primrec : Primrec (fun p : Context => betaCode p.1.1 p.1.2 p.2) :=
  BoundedPublicReturn.publicCode_primrec

theorem betaCode_spec (s a b : Nat) (ha : rootCheck s a b = true) :
    Canonical.check (betaCode s a b) = true ∧
      unionInterpretation (betaCode s a b) = interpretation (sourceCode s a) b := by
  have hs := (rootCheck_exact s a b).mp ha
  exact BoundedPublicReturn.publicCode_spec s a b
    ((BoundedPublicReturn.inputCheck_exact s a b).mpr ⟨hs.1, root_low s a b ha, hs.2.2⟩)

theorem betaCode_baseCheck (s a b : Nat) (ha : rootCheck s a b = true) : baseCheck (betaCode s a b) = true := by
  have hs := betaCode_spec s a b ha
  apply (baseCheck_exact _).mpr
  refine ⟨Canonical.check_original hs.1, ?_⟩
  change Ordinal.omega0 ^ unionInterpretation (betaCode s a b) = _
  rw [hs.2]
  exact root_epsilon s a b ha

theorem beta_base (s a b : Nat) (ha : rootCheck s a b = true) :
    base (betaCode s a b) = interpretation (sourceCode s a) b := (betaCode_spec s a b ha).2

def Restricted (s a b : Nat) (t : RelativeTerm Nat) : Prop :=
  ∀ u ∈ fullList t, denote (sourceCode s a) u < interpretation (sourceCode s a) b

theorem restricted_sum (s a b : Nat) (t u : RelativeTerm Nat) :
    Restricted s a b (.sum t u) ↔ Restricted s a b t ∧ Restricted s a b u := by
  constructor
  · intro h
    exact ⟨fun v hv => h v (List.mem_append_left _ hv), fun v hv => h v (List.mem_append_right _ hv)⟩
  · rintro ⟨ht, hu⟩ v hv
    exact (List.mem_append.mp hv).elim (ht v) (hu v)

theorem restricted_theta_zero (s a b : Nat) (t : RelativeTerm Nat) :
    Restricted s a b (.theta 0 t) ↔
      denote (sourceCode s a) (.theta 0 t) < interpretation (sourceCode s a) b ∧ Restricted s a b t := by
  simp only [Restricted, fullList, RelativeTerm.PrincipalSupport.principalList_theta_same, List.forall_mem_cons]

theorem restricted_theta_succ (s a b k : Nat) (t : RelativeTerm Nat) :
    Restricted s a b (.theta (k + 1) t) ↔ Restricted s a b t := by
  rw [Restricted, fullList,
    RelativeTerm.PrincipalSupport.principalList_theta_higher 0 (k + 1) t (Nat.succ_pos k)]
  rfl

theorem restricted_iff_sourceStar (s a b : Nat) (ha : rootCheck s a b = true)
    (t : RelativeTerm Nat) (ht : check (sourceCode s a) t = true) (hn : Comparison.Normal (sourceCode s a) t) :
    Restricted s a b t ↔ Iota.sourceStar (sourceCode s a) t < interpretation (sourceCode s a) b := by
  rw [Iota.sourceStar, Iota.sourceSupport_fullList _ t ht hn, Finset.sup_lt_iff (root_pos s a b ha)]
  simp only [Restricted, List.mem_toFinset, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff]

theorem argument_restricted (s a b : Nat) (ha : rootCheck s a b = true) :
    Restricted s a b (ThetaCourse.rawTree (Localization.argumentCode b)) := by
  obtain ⟨_, ⟨t, he, ht, hn, hh⟩, _⟩ := (rootCheck_exact s a b).mp ha
  simp only [he, Localization.argumentCode_theta, ThetaCourse.rawTree_code]
  intro u hu
  let q := sourceCode s a
  let n := SourceOne.PublicCodes.fragment (.theta 0 t)
  have hq := sourceCode_checked s a b ha
  have had := checked_admissible q (.theta 0 t) ht
  have haa := Comparison.admitted_argument had
  have hua := RelativeTerm.PrincipalSupport.principalList_admissible haa.2 0 hu
  have h := RelativeTerm.PrincipalSupport.principalList_argument_lt (base q) (base_pos q hq)
    parameters n 0 t u had.2 ((Comparison.normal_finite_iff q n hq t haa.2).mpr hn) hu
  rw [← denote_eq_finite q n hq u hua, ← denote_eq_finite q n hq (.theta 0 t) had.2] at h
  simpa only [he, interpretation_code] using h

theorem below_low (s a b : Nat) (ha : rootCheck s a b = true) (t : RelativeTerm Nat)
    (ht : check (sourceCode s a) t = true) (hb : denote (sourceCode s a) t < interpretation (sourceCode s a) b) :
    lowCheckCode (sourceCode s a) t.code = true := by
  obtain ⟨u, he, hu⟩ := (lowCheckCode_exact _ b).mp (root_low s a b ha)
  have hs := Bool.and_eq_true.mp hu
  have hroot : interpretation (sourceCode s a) b < omegaSequence (base (sourceCode s a)) 1 := by
    rw [← he, interpretation_code]
    exact (denote_lt_iff_outerSort_le _ u hs.1 1 (by omega)).mpr (of_decide_eq_true hs.2)
  have hl := (denote_lt_iff_outerSort_le _ t ht 1 (by omega)).mp (hb.trans hroot)
  simp only [lowCheckCode_code, lowCheck, ht, hl, decide_true, Bool.true_and]

def parameterCode (s a : Nat) (t : RelativeTerm Nat) : Nat := BoundedPublicReturn.rawPublicCode s a t.code

theorem parameterCode_primrec : Primrec₂ (fun ctx : Nat × Nat => parameterCode ctx.1 ctx.2) :=
  (BoundedPublicReturn.rawPublicCode_primrec.comp (Primrec.fst.pair (code_primrec.comp Primrec.snd))).to₂

theorem parameterCode_spec (s a b : Nat) (ha : rootCheck s a b = true) (t : RelativeTerm Nat)
    (ht : check (sourceCode s a) t = true) (hb : denote (sourceCode s a) t < interpretation (sourceCode s a) b) :
    parameterCheck (betaCode s a b) (parameterCode s a t) = true ∧
      parameters (parameterCode s a t) = denote (sourceCode s a) t := by
  have hr := (rootCheck_exact s a b).mp ha
  have hp := BoundedPublicReturn.rawPublicCode_spec s a t.code hr.1 (below_low s a b ha t ht hb)
    (by simpa only [interpretation_code] using hb.trans hr.2.2)
  have hv : parameters (parameterCode s a t) = denote (sourceCode s a) t :=
    hp.2.trans (interpretation_code _ t)
  refine ⟨(parameterCheck_exact _ _).mpr
    ⟨Canonical.check_original hp.1, Canonical.check_original (betaCode_spec s a b ha).1, ?_⟩, hv⟩
  change parameters (parameterCode s a t) < unionInterpretation (betaCode s a b)
  rw [hv, (betaCode_spec s a b ha).2]
  exact hb

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.BoundedContextIota
