import Alexander313.Wilken.HereditaryNativeSourceZeta
import Alexander313.Wilken.HereditaryNativeBaseTransformationSupport
import Alexander313.Wilken.RelativeTermWeakPrincipalSupport

/-!
# Real restriction and parameter callers for native iota

The source context is the original positive public epsilon contextCode s.
The new epsilon is an originally admitted weak-normal theta-zero term with
nonzero cardinal high part, recognized by its actual argument outer sort.
Its public code is constructed by the existing return and canonicalization.
The full Definition 2.23 principal VALUE support and its zero-default maximum
are derived under weak normality, rather than supplied as a parser contract.
Every subtree below the new base has a real original public parameter code;
its low-return caller bound is derived from the original theta-zero range.
No shifted-collapse naturality, isomorphism or temporary inverse is assumed.
All proofs are uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Iota

open NativePublicBridge (contextCode contextCode_value contextCode_checked)
open scoped Classical

abbrev fullList := RelativeTerm.PrincipalSupport.principalList (Parameter := Nat) 0

def rootCheck (s a : Nat) : Bool := SourceZeta.inputCheck s a &&
  decide (1 < (ThetaCourse.rawTree (Localization.argumentCode a)).outerSort)

theorem rootCheck_primrec : Primrec₂ rootCheck :=
  (Primrec.and.comp SourceZeta.inputCheck_primrec
    ((Primrec.nat_lt.comp (Primrec.const 1) (outerSort_primrec.comp
      (ThetaCourse.rawTree_primrec.comp (Localization.argumentCode_primrec.comp Primrec.snd)))).decide)).to₂

theorem rootCheck_exact (s a : Nat) : rootCheck s a = true ↔
    ∃ t : RelativeTerm Nat, a = (.theta 0 t).code ∧
      check (contextCode s) (.theta 0 t) = true ∧ Comparison.Normal (contextCode s) t ∧
      1 < t.outerSort := by
  simp only [rootCheck, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨ha, hs⟩
    obtain ⟨t, he, ht, hn⟩ := (SourceZeta.inputCheck_exact s a).mp ha
    exact ⟨t, he, ht, hn, by simpa only [he, Localization.argumentCode_theta,
      ThetaCourse.rawTree_code] using hs⟩
  · rintro ⟨t, rfl, ht, hn, hs⟩
    exact ⟨(SourceZeta.inputCheck_exact s _).mpr ⟨t, rfl, ht, hn⟩,
      by simpa only [Localization.argumentCode_theta, ThetaCourse.rawTree_code] using hs⟩

theorem root_original (s a : Nat) (ha : rootCheck s a = true) :
    checkCode (contextCode s) a = true :=
  ((Comparison.acceptedCode_exact _ _).mp
    (Bool.and_eq_true.mp (Bool.and_eq_true.mp ha).1).1).1

theorem root_low (s a : Nat) (ha : rootCheck s a = true) :
    lowCheckCode (contextCode s) a = true := by
  obtain ⟨t, rfl, ht, hn, hs⟩ := (rootCheck_exact s a).mp ha
  simp only [lowCheckCode_code, lowCheck, ht, RelativeTerm.outerSort, decide_true,
    Bool.true_and]

theorem root_base_le (s a : Nat) (ha : rootCheck s a = true) :
    base (contextCode s) ≤ interpretation (contextCode s) a := by
  obtain ⟨t, rfl, ht, hn, hs⟩ := (rootCheck_exact s a).mp ha
  simpa only [interpretation_code] using BaseTransformation.theta_base_le (contextCode s) 0 t ht

def alphaCode (s a : Nat) : Nat := Canonical.canonicalize
  (Nat.pair (s + 1) (NativePublicReturn.rawReturnCode s a))

theorem alphaCode_primrec : Primrec₂ alphaCode :=
  (Canonical.Effective.canonicalize_primrec.comp
    (Primrec₂.natPair.comp (Primrec.succ.comp Primrec.fst) NativePublicReturn.rawReturnCode_primrec)).to₂

theorem alphaCode_spec (s a : Nat) (ha : rootCheck s a = true) :
    Canonical.check (alphaCode s a) = true ∧
      unionInterpretation (alphaCode s a) = interpretation (contextCode s) a := by
  have h := NativePublicReturn.rawReturnCode_union s a (root_low s a ha)
  exact ⟨Canonical.canonicalize_check _ h.1,
    (Canonical.canonicalize_value _ h.1).trans h.2⟩

theorem alphaCode_baseCheck (s a : Nat) (ha : rootCheck s a = true) :
    baseCheck (alphaCode s a) = true := by
  obtain ⟨t, he, ht, hn, hs⟩ := (rootCheck_exact s a).mp ha
  have hpt := NativePublicReturn.returnTerm_checked s (.theta 0 t) ht
  have heps := (Epsilon.theta_epsilon_iff (s + 1) 0 (NativePublicReturn.returnTerm s t)
    hpt).mpr (Or.inl (by simpa only [NativePublicReturn.returnTerm_outerSort] using hs))
  have hv := NativePublicReturn.returnTerm_denote s (.theta 0 t)
    (checked_admissible _ _ ht).1
  have hc := alphaCode_spec s a ha
  apply (baseCheck_exact _).mpr
  refine ⟨Canonical.check_original hc.1, ?_⟩
  change Ordinal.omega0 ^ unionInterpretation (alphaCode s a) = _
  rw [hc.2, he, interpretation_code, ← hv]
  exact heps

theorem root_pos (s a : Nat) (ha : rootCheck s a = true) :
    0 < interpretation (contextCode s) a :=
  (base_pos (contextCode s) (contextCode_checked s)).trans_le (root_base_le s a ha)

theorem payloads_full_node (q : Nat) (t u : RelativeTerm Nat)
    (ht : Payloads q t) (hu : u ∈ fullList t) : Payloads q u := by
  revert ht hu
  induction t with
  | parameter p => intro ht hu; simp [fullList, RelativeTerm.PrincipalSupport.principalList] at hu
  | sum a b iha ihb =>
    intro ht hu
    rcases List.mem_append.mp hu with hu | hu
    · exact iha ht.1 hu
    · exact ihb ht.2 hu
  | theta k a ih =>
    intro ht hu
    cases k with
    | zero =>
      rw [fullList, RelativeTerm.PrincipalSupport.principalList_theta_same] at hu
      rcases List.mem_cons.mp hu with he | hu
      · subst u; exact ht
      · exact ih ht hu
    | succ k =>
      exact ih ht (by simpa only [fullList,
        RelativeTerm.PrincipalSupport.principalList_theta_higher 0 (k + 1) a (Nat.succ_pos k)] using hu)

theorem checked_full_node (q : Nat) (t u : RelativeTerm Nat)
    (ht : check q t = true) (hu : u ∈ fullList t) : check q u = true := by
  have hq := (Bool.and_eq_true.mp ht).1
  have h := checked_admissible q t ht
  have hp := payloads_full_node q t u h.1 hu
  exact Comparison.admitted_checked q _ hq u ⟨hp,
    RelativeTerm.PrincipalSupport.principalList_admissible h.2 0 hu⟩

noncomputable def sourceSupport (q : Nat) (t : RelativeTerm Nat) : Finset Ordinal.{0} :=
  ((t.subtermsAt 0).image (denote q)).filter (fun p =>
    0 < p ∧ Ordinal.IsPrincipal (· + ·) p ∧ base q ≤ p ∧ p < omegaSequence (base q) 1)

noncomputable def sourceStar (q : Nat) (t : RelativeTerm Nat) : Ordinal.{0} :=
  (sourceSupport q t).sup id

theorem sourceSupport_fullList (q : Nat) (t : RelativeTerm Nat)
    (ht : check q t = true) (hn : Comparison.Normal q t) :
    sourceSupport q t = ((fullList t).map (denote q)).toFinset := by
  let n := SourceOne.PublicCodes.fragment t
  have ha := checked_admissible q t ht
  have hq := (Bool.and_eq_true.mp ht).1
  have hsub : (t.subtermsAt 0).image (denote q) =
      (t.subtermsAt 0).image (fun u => u.eval parameters (sourceFiniteCollapse (base q) n)) := by
    apply Finset.image_congr
    intro u hu
    exact denote_eq_finite q n hq u (RelativeTerm.PrincipalSupport.subtermsAt_admissible ha.2 0 hu)
  have hlist : (fullList t).map (denote q) =
      (fullList t).map (fun u => u.eval parameters (sourceFiniteCollapse (base q) n)) := by
    apply List.map_congr_left
    intro u hu
    exact denote_eq_finite q n hq u (RelativeTerm.PrincipalSupport.principalList_admissible ha.2 0 hu)
  unfold sourceSupport
  rw [hsub, hlist]
  simpa only [omegaSequence_zero] using
    RelativeTerm.PrincipalSupport.sourcePrincipalSupport_eq_principalList_weak
      (base q) (base_pos q hq) parameters n 0 t ha.2
      ((Comparison.normal_finite_iff q n hq t ha.2).mpr hn)

def Restricted (s a : Nat) (t : RelativeTerm Nat) : Prop :=
  ∀ u ∈ fullList t, denote (contextCode s) u < interpretation (contextCode s) a

theorem restricted_iff_sourceStar (s a : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (contextCode s) t = true)
    (hn : Comparison.Normal (contextCode s) t) :
    Restricted s a t ↔ sourceStar (contextCode s) t < interpretation (contextCode s) a := by
  rw [sourceStar, sourceSupport_fullList _ t ht hn,
    Finset.sup_lt_iff (root_pos s a ha)]
  simp only [Restricted, List.mem_toFinset, List.mem_map, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff]

def allBelow (q a : Nat) (cs : List Nat) : Bool :=
  cs.foldr (fun c b => Normalization.lessRawCode q c a && b) true

theorem allBelow_exact (q a : Nat) (cs : List Nat) : allBelow q a cs = true ↔
    ∀ c ∈ cs, Normalization.lessRawCode q c a = true := by
  induction cs with
  | nil => simp [allBelow]
  | cons c cs ih =>
    change (Normalization.lessRawCode q c a && allBelow q a cs) = true ↔ _
    rw [Bool.and_eq_true, ih, List.forall_mem_cons]

theorem allBelow_primrec : Primrec (fun p : (Nat × Nat) × List Nat => allBelow p.1.1 p.1.2 p.2) := by
  have hs : Primrec₂ (fun p : (Nat × Nat) × List Nat => fun z : Nat × Bool =>
      Normalization.lessRawCode p.1.1 z.1 p.1.2 && z.2) := by
    exact (Primrec.and.comp (Normalization.Effective.lessRawCode_primrec.comp
      ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
        ((Primrec.fst.comp Primrec.snd).pair (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact Primrec.list_foldr Primrec.snd (Primrec.const true) hs

def restrictionCheck (s a c : Nat) : Bool :=
  allBelow (contextCode s) a (RelativeTerm.PrincipalSupport.listCode 0 c)

theorem restrictionCheck_primrec : Primrec
    (fun p : (Nat × Nat) × Nat => restrictionCheck p.1.1 p.1.2 p.2) :=
  allBelow_primrec.comp (((NativePublicBridge.contextCode_primrec.comp
    (Primrec.fst.comp Primrec.fst)).pair (Primrec.snd.comp Primrec.fst)).pair
      (RelativeTerm.PrincipalSupport.listCode_primrec.comp (Primrec.const 0) Primrec.snd))

theorem restrictionCheck_code (s a : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (contextCode s) t = true) :
    restrictionCheck s a t.code = true ↔ Restricted s a t := by
  rw [restrictionCheck, RelativeTerm.PrincipalSupport.listCode_code, allBelow_exact]
  constructor
  · intro h u hu
    have he := (Normalization.lessRawCode_exact _ _ _).mp
      (h u.code (List.mem_map.mpr ⟨u, hu, rfl⟩))
    simpa only [interpretation_code] using he.2.2
  · intro h c hc
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hc
    exact (Normalization.lessRawCode_exact _ _ _).mpr
      ⟨by simpa only [checkCode_code] using checked_full_node _ t u ht hu,
        root_original s a ha, by simpa only [interpretation_code] using h u hu⟩

def parameterCode (s : Nat) (t : RelativeTerm Nat) : Nat := Canonical.canonicalize
  (Nat.pair (s + 1) (NativePublicReturn.rawReturnCode s t.code))

theorem parameterCode_primrec : Primrec₂ parameterCode :=
  (Canonical.Effective.canonicalize_primrec.comp
    (Primrec₂.natPair.comp (Primrec.succ.comp Primrec.fst)
      (NativePublicReturn.rawReturnCode_primrec.comp Primrec.fst
        (code_primrec.comp Primrec.snd)))).to₂

theorem below_low (s a : Nat) (ha : rootCheck s a = true) (t : RelativeTerm Nat)
    (ht : check (contextCode s) t = true)
    (hsmall : denote (contextCode s) t < interpretation (contextCode s) a) :
    lowCheckCode (contextCode s) t.code = true := by
  have hroot := (root_low s a ha)
  obtain ⟨u, he, hu⟩ := (lowCheckCode_exact _ a).mp hroot
  have hs := Bool.and_eq_true.mp hu
  have hv : interpretation (contextCode s) a < omegaSequence (base (contextCode s)) 1 := by
    rw [← he, interpretation_code]
    exact (denote_lt_iff_outerSort_le _ u hs.1 1 (by omega)).mpr
      (of_decide_eq_true hs.2)
  have hs' := (denote_lt_iff_outerSort_le _ t ht 1 (by omega)).mp (hsmall.trans hv)
  simp only [lowCheckCode_code, lowCheck, ht, hs', decide_true, Bool.true_and]

theorem parameterCode_spec (s a : Nat) (ha : rootCheck s a = true) (t : RelativeTerm Nat)
    (ht : check (contextCode s) t = true)
    (hsmall : denote (contextCode s) t < interpretation (contextCode s) a) :
    parameterCheck (alphaCode s a) (parameterCode s t) = true ∧
      parameters (parameterCode s t) = denote (contextCode s) t := by
  have h := NativePublicReturn.rawReturnCode_union s t.code (below_low s a ha t ht hsmall)
  have hc := Canonical.canonicalize_check _ h.1
  have hv : parameters (parameterCode s t) = denote (contextCode s) t := by
    exact (Canonical.canonicalize_value _ h.1).trans (by simpa only [interpretation_code] using h.2)
  refine ⟨(parameterCheck_exact _ _).mpr ⟨Canonical.check_original hc,
    Canonical.check_original (alphaCode_spec s a ha).1, ?_⟩, hv⟩
  change parameters (parameterCode s t) < unionInterpretation (alphaCode s a)
  rw [hv, (alphaCode_spec s a ha).2]
  exact hsmall

theorem restricted_sum (s a : Nat) (t u : RelativeTerm Nat) :
    Restricted s a (.sum t u) ↔ Restricted s a t ∧ Restricted s a u := by
  constructor
  · intro h
    exact ⟨fun v hv => h v (List.mem_append_left _ hv),
      fun v hv => h v (List.mem_append_right _ hv)⟩
  · rintro ⟨ht, hu⟩ v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact ht v hv
    · exact hu v hv

theorem restricted_theta_zero (s a : Nat) (t : RelativeTerm Nat) :
    Restricted s a (.theta 0 t) ↔
      denote (contextCode s) (.theta 0 t) < interpretation (contextCode s) a ∧ Restricted s a t := by
  simp only [Restricted, fullList, RelativeTerm.PrincipalSupport.principalList_theta_same,
    List.forall_mem_cons]

theorem restricted_theta_succ (s a k : Nat) (t : RelativeTerm Nat) :
    Restricted s a (.theta (k + 1) t) ↔ Restricted s a t := by
  rw [Restricted, fullList,
    RelativeTerm.PrincipalSupport.principalList_theta_higher 0 (k + 1) t (Nat.succ_pos k)]
  rfl

/-- The original constructor supplies the complete restriction of its actual
argument. This uses the proved full principal-support bound, not a caller oracle. -/
theorem argument_restricted (s a : Nat) (ha : rootCheck s a = true) :
    Restricted s a (ThetaCourse.rawTree (Localization.argumentCode a)) := by
  obtain ⟨t, he, ht, hn, hs⟩ := (rootCheck_exact s a).mp ha
  simp only [he, Localization.argumentCode_theta, ThetaCourse.rawTree_code]
  intro u hu
  let q := contextCode s
  let n := SourceOne.PublicCodes.fragment (.theta 0 t)
  have had := checked_admissible q (.theta 0 t) ht
  have haa := Comparison.admitted_argument had
  have hq := contextCode_checked s
  have hua := RelativeTerm.PrincipalSupport.principalList_admissible haa.2 0 hu
  have h := RelativeTerm.PrincipalSupport.principalList_argument_lt
    (base q) (base_pos q hq) parameters n 0 t u had.2
    ((Comparison.normal_finite_iff q n hq t haa.2).mpr hn) hu
  rw [← denote_eq_finite q n hq u hua,
    ← denote_eq_finite q n hq (.theta 0 t) had.2] at h
  simpa only [he, interpretation_code] using h

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Iota
