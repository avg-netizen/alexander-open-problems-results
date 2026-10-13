import Alexander313.Wilken.HereditaryNativeIota
import Alexander313.Wilken.HereditaryThetaNormalizationPrimitive
import Alexander313.Wilken.SourceOneHeightBoundary

/-!
# Genuine original base-one callers for the native iota shift

The original source is the literal hereditary level zero, whose check and
value are exactly SourceOne.PublicCodes. Its original high theta-zero root
is an actual epsilon. Literal tagging at public level zero supplies its
canonical native alpha base and every original low subtree below alpha as
an admitted same-value atomic payload. The source base one is never passed
to the positive-epsilon native source parser. No recoder or caller oracle.
The whole original principal maximum is identified with the real full-depth
list under original Normality. The executing restriction guard therefore
keeps the original Definition 2.45 domain, and the original root derives its
argument caller. Shifted finite admission remains separate from order and
Normal transport. Uncompiled drafts.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota

open ThetaCourse
open scoped Classical

abbrev fullList := RelativeTerm.PrincipalSupport.principalList (Parameter := Nat) 0

def rootCheck (a : Nat) : Bool := SourceZeta.inputCheck 0 a &&
  decide (1 < (rawTree (Localization.argumentCode a)).outerSort)

theorem rootCheck_primrec : Primrec rootCheck :=
  Primrec.and.comp (SourceZeta.inputCheck_primrec.comp (Primrec.const 0) Primrec.id)
    ((Primrec.nat_lt.comp (Primrec.const 1) (outerSort_primrec.comp
      (rawTree_primrec.comp Localization.argumentCode_primrec))).decide)

theorem rootCheck_exact (a : Nat) : rootCheck a = true ↔
    ∃ t : RelativeTerm Nat, a = (.theta 0 t).code ∧ check 0 (.theta 0 t) = true ∧
      Theta.Normal 0 (.theta 0 t) ∧ 1 < t.outerSort := by
  simp only [rootCheck, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨ha, hs⟩
    obtain ⟨t, he, ht, hn⟩ := (SourceZeta.inputCheck_exact 0 a).mp ha
    exact ⟨t, he, ht, hn, by simpa only [he, Localization.argumentCode_theta, rawTree_code] using hs⟩
  · rintro ⟨t, rfl, ht, hn, hs⟩
    exact ⟨(SourceZeta.inputCheck_exact 0 _).mpr ⟨t, rfl, ht, hn⟩,
      by simpa only [Localization.argumentCode_theta, rawTree_code] using hs⟩

theorem root_original (a : Nat) (ha : rootCheck a = true) : checkCode 0 a = true := by
  obtain ⟨t, rfl, ht, hn, hs⟩ := (rootCheck_exact a).mp ha
  simpa only [checkCode_code] using ht

theorem root_low (a : Nat) (ha : rootCheck a = true) : lowCheckCode 0 a = true :=
  Localization.node_low 0 a ((SourceZeta.inputCheck_exact 0 a).mp (Bool.and_eq_true.mp ha).1)

theorem root_epsilon (a : Nat) (ha : rootCheck a = true) :
    Ordinal.omega0 ^ interpretation 0 a = interpretation 0 a := by
  obtain ⟨t, rfl, ht, hn, hs⟩ := (rootCheck_exact a).mp ha
  simpa only [interpretation_code] using (Epsilon.theta_epsilon_iff 0 0 t ht).mpr (Or.inl hs)

theorem root_pos (a : Nat) (ha : rootCheck a = true) : 0 < interpretation 0 a :=
  zero_lt_one.trans (EpsilonOffsets.epsilon_one_lt (root_epsilon a ha))

theorem root_lt_first (a : Nat) (ha : rootCheck a = true) :
    interpretation 0 a < omegaSequence 1 1 :=
  (SourceOne.HeightBoundary.input_spec a (by simpa only [lowCheckCode_zero] using root_low a ha)).2

def alphaCode (a : Nat) : Nat := Canonical.canonicalize (Nat.pair 0 a)

theorem alphaCode_primrec : Primrec alphaCode :=
  Canonical.Effective.canonicalize_primrec.comp (Primrec₂.natPair.comp (Primrec.const 0) Primrec.id)

theorem alphaCode_spec (a : Nat) (ha : rootCheck a = true) :
    Canonical.check (alphaCode a) = true ∧ unionInterpretation (alphaCode a) = interpretation 0 a := by
  have hc : unionCheck (Nat.pair 0 a) = true := by simpa only [unionCheck_pair] using root_low a ha
  exact ⟨Canonical.canonicalize_check _ hc,
    (Canonical.canonicalize_value _ hc).trans (by rw [unionInterpretation_pair])⟩

theorem alphaCode_baseCheck (a : Nat) (ha : rootCheck a = true) :
    NativeContext.baseCheck (alphaCode a) = true := by
  have hs := alphaCode_spec a ha
  apply (NativeContext.baseCheck_exact _).mpr
  refine ⟨Canonical.check_original hs.1, ?_⟩
  change Ordinal.omega0 ^ unionInterpretation (alphaCode a) = unionInterpretation (alphaCode a)
  rw [hs.2]
  exact root_epsilon a ha

/-- Literal public level-zero tagging, canonicalized by the actual public
normalizer; no semantic source representative is selected. -/
def parameterCode (t : RelativeTerm Nat) : Nat := Canonical.canonicalize (Nat.pair 0 t.code)

theorem parameterCode_primrec : Primrec parameterCode :=
  Canonical.Effective.canonicalize_primrec.comp
    (Primrec₂.natPair.comp (Primrec.const 0) code_primrec)

theorem parameterCode_spec (a : Nat) (ha : rootCheck a = true) (t : RelativeTerm Nat)
    (ht : check 0 t = true) (hb : denote 0 t < interpretation 0 a) :
    NativeContext.parameterCheck (alphaCode a) (parameterCode t) = true ∧
      unionInterpretation (parameterCode t) = denote 0 t := by
  have hs : t.outerSort ≤ 1 := (denote_lt_iff_outerSort_le 0 t ht 1 (by omega)).mp
    (by simpa only [finiteBase_zero] using hb.trans (root_lt_first a ha))
  have hl : lowCheck 0 t = true := by
    simp only [lowCheck, ht, hs, decide_true, Bool.true_and]
  have hu : unionCheck (Nat.pair 0 t.code) = true := by
    simpa only [unionCheck_pair, lowCheckCode_code] using hl
  have hc := Canonical.canonicalize_check _ hu
  have hv : unionInterpretation (parameterCode t) = denote 0 t :=
    (Canonical.canonicalize_value _ hu).trans (by rw [unionInterpretation_pair, interpretation_code])
  refine ⟨(NativeContext.parameterCheck_exact _ _).mpr ?_, hv⟩
  refine ⟨Canonical.check_original hc, Canonical.check_original (alphaCode_spec a ha).1, ?_⟩
  change unionInterpretation (parameterCode t) < unionInterpretation (alphaCode a)
  rw [hv, (alphaCode_spec a ha).2]
  exact hb

def small (a : Nat) (t : RelativeTerm Nat) : Bool := Theta.Normalization.lessRawCode 0 t.code a

theorem small_primrec : Primrec₂ small :=
  (Theta.Normalization.Effective.lessRawCode_primrec.comp
    ((Primrec.const 0).pair ((code_primrec.comp Primrec.snd).pair Primrec.fst))).to₂

theorem small_exact (a : Nat) (ha : rootCheck a = true) (t : RelativeTerm Nat)
    (ht : check 0 t = true) : small a t = true ↔ denote 0 t < interpretation 0 a := by
  simpa only [small, interpretation_code] using Theta.Normalization.lessRawCode_correct 0 t.code a
    (by simpa only [checkCode_code] using ht) (root_original a ha)

def Restricted (a : Nat) (t : RelativeTerm Nat) : Prop :=
  ∀ u ∈ fullList t, denote 0 u < interpretation 0 a

theorem restricted_sum (a : Nat) (t u : RelativeTerm Nat) :
    Restricted a (.sum t u) ↔ Restricted a t ∧ Restricted a u := by
  constructor
  · intro h
    exact ⟨fun v hv => h v (List.mem_append_left _ hv),
      fun v hv => h v (List.mem_append_right _ hv)⟩
  · rintro ⟨ht, hu⟩ v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact ht v hv
    · exact hu v hv

theorem restricted_theta_zero (a : Nat) (t : RelativeTerm Nat) :
    Restricted a (.theta 0 t) ↔ denote 0 (.theta 0 t) < interpretation 0 a ∧ Restricted a t := by
  simp only [Restricted, fullList, RelativeTerm.PrincipalSupport.principalList_theta_same,
    List.forall_mem_cons]

theorem restricted_theta_succ (a k : Nat) (t : RelativeTerm Nat) :
    Restricted a (.theta (k + 1) t) ↔ Restricted a t := by
  rw [Restricted, fullList,
    RelativeTerm.PrincipalSupport.principalList_theta_higher 0 (k + 1) t (Nat.succ_pos k)]
  rfl

/-- The printed full principal support at the original source base one. -/
noncomputable def sourceSupport (t : RelativeTerm Nat) : Finset Ordinal.{0} :=
  ((t.subtermsAt 0).image (denote 0)).filter (fun p =>
    0 < p ∧ Ordinal.IsPrincipal (· + ·) p ∧ 1 ≤ p ∧ p < omegaSequence 1 1)

noncomputable def sourceStar (t : RelativeTerm Nat) : Ordinal.{0} :=
  (sourceSupport t).sup id

theorem sourceSupport_fullList (t : RelativeTerm Nat) (ht : check 0 t = true)
    (hn : Theta.Normal 0 t) :
    sourceSupport t = ((fullList t).map (denote 0)).toFinset := by
  simpa only [sourceSupport, fullList, finiteBase_zero, omegaSequence_zero,
    Nat.zero_add] using PrincipalSupport.sourcePrincipalValueSupport_eq_principalList 0 0 t ht hn

theorem restricted_iff_sourceStar (a : Nat) (ha : rootCheck a = true)
    (t : RelativeTerm Nat) (ht : check 0 t = true) (hn : Theta.Normal 0 t) :
    Restricted a t ↔ sourceStar t < interpretation 0 a := by
  rw [sourceStar, sourceSupport_fullList t ht hn, Finset.sup_lt_iff (root_pos a ha)]
  simp only [Restricted, List.mem_toFinset, List.mem_map, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff]

theorem checked_full_node (t u : RelativeTerm Nat) (ht : check 0 t = true)
    (hu : u ∈ fullList t) : check 0 u = true := by
  obtain ⟨n, hn⟩ := (check_iff_finite_admissible 0 t).mp ht
  exact Theta.admitted_checked (PrincipalSupport.principalList_admitted hn 0 hu)

/-- The original proper root itself supplies its whole argument restriction. -/
theorem argument_restricted (a : Nat) (ha : rootCheck a = true) :
    Restricted a (rawTree (Localization.argumentCode a)) := by
  obtain ⟨t, he, ht, hn, hs⟩ := (rootCheck_exact a).mp ha
  simp only [he, Localization.argumentCode_theta, rawTree_code]
  intro u hu
  simpa only [interpretation_code] using PrincipalSupport.principalList_argument_lt 0 0 t u ht
    ((Theta.normal_theta 0 0 t).mp hn) hu

def allBelow (a : Nat) (cs : List Nat) : Bool :=
  cs.foldr (fun c b => Theta.Normalization.lessRawCode 0 c a && b) true

theorem allBelow_exact (a : Nat) (cs : List Nat) : allBelow a cs = true ↔
    ∀ c ∈ cs, Theta.Normalization.lessRawCode 0 c a = true := by
  induction cs with
  | nil => simp [allBelow]
  | cons c cs ih =>
    change (Theta.Normalization.lessRawCode 0 c a && allBelow a cs) = true ↔ _
    rw [Bool.and_eq_true, ih, List.forall_mem_cons]

theorem allBelow_primrec : Primrec₂ allBelow := by
  have hs : Primrec₂ (fun p : Nat × List Nat => fun z : Nat × Bool =>
      Theta.Normalization.lessRawCode 0 z.1 p.1 && z.2) := by
    exact (Primrec.and.comp (Theta.Normalization.Effective.lessRawCode_primrec.comp
      ((Primrec.const 0).pair
        ((Primrec.fst.comp Primrec.snd).pair (Primrec.fst.comp Primrec.fst))))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.list_foldr Primrec.snd (Primrec.const true) hs).to₂

def restrictionCheck (a c : Nat) : Bool :=
  allBelow a (RelativeTerm.PrincipalSupport.listCode 0 c)

theorem restrictionCheck_primrec : Primrec₂ restrictionCheck :=
  (allBelow_primrec.comp Primrec.fst
    (RelativeTerm.PrincipalSupport.listCode_primrec.comp (Primrec.const 0) Primrec.snd)).to₂

theorem restrictionCheck_code (a : Nat) (ha : rootCheck a = true) (t : RelativeTerm Nat)
    (ht : check 0 t = true) : restrictionCheck a t.code = true ↔ Restricted a t := by
  rw [restrictionCheck, RelativeTerm.PrincipalSupport.listCode_code, allBelow_exact]
  constructor
  · intro h u hu
    have hc := h u.code (List.mem_map.mpr ⟨u, hu, rfl⟩)
    have he := (Theta.Normalization.lessRawCode_correct 0 u.code a
      (by simpa only [checkCode_code] using checked_full_node t u ht hu)
      (root_original a ha)).mp hc
    simpa only [interpretation_code] using he
  · intro h c hc
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hc
    exact (Theta.Normalization.lessRawCode_correct 0 u.code a
      (by simpa only [checkCode_code] using checked_full_node t u ht hu)
      (root_original a ha)).mpr (by simpa only [interpretation_code] using h u hu)

def inputCheck (a c : Nat) : Bool :=
  (rootCheck a && Theta.acceptedCode 0 c) && restrictionCheck a c

theorem inputCheck_primrec : Primrec₂ inputCheck :=
  (Primrec.and.comp (Primrec.and.comp (rootCheck_primrec.comp Primrec.fst)
    (Theta.Effective.acceptedCode_primrec.comp (Primrec.const 0) Primrec.snd))
    restrictionCheck_primrec).to₂

/-- The actual original Definition 2.45 source-one domain, with its full
printed principal maximum and original hereditary Normal check. -/
theorem inputCheck_exact (a c : Nat) : inputCheck a c = true ↔
    rootCheck a = true ∧ ∃ t : RelativeTerm Nat, c = t.code ∧ check 0 t = true ∧
      Theta.Normal 0 t ∧ sourceStar t < interpretation 0 a := by
  constructor
  · intro h
    obtain ⟨hpair, hr⟩ := Bool.and_eq_true.mp h
    obtain ⟨ha, hc⟩ := Bool.and_eq_true.mp hpair
    have hn := (Theta.acceptedCode_iff 0 c).mp hc
    obtain ⟨t, he, ht⟩ := (checkCode_iff 0 c).mp hn.1
    have hnt : Theta.Normal 0 t := by simpa only [← he, rawTree_code] using hn.2
    exact ⟨ha, t, he.symm, ht, hnt, (restricted_iff_sourceStar a ha t ht hnt).mp
      ((restrictionCheck_code a ha t ht).mp (by simpa only [he] using hr))⟩
  · rintro ⟨ha, t, rfl, ht, hn, hs⟩
    exact Bool.and_eq_true.mpr ⟨Bool.and_eq_true.mpr ⟨ha,
      (Theta.acceptedCode_iff 0 _).mpr ⟨by simpa only [checkCode_code] using ht,
        by simpa only [rawTree_code] using hn⟩⟩,
      (restrictionCheck_code a ha t ht).mpr ((restricted_iff_sourceStar a ha t ht hn).mpr hs)⟩

theorem argument_inputCheck (a : Nat) (ha : rootCheck a = true) :
    inputCheck a (Localization.argumentCode a) = true := by
  have hnode := (SourceZeta.inputCheck_exact 0 a).mp (Bool.and_eq_true.mp ha).1
  have hc := Localization.node_argument 0 a hnode
  obtain ⟨t, he, ht⟩ := (checkCode_iff 0 _).mp hc.1
  have hr : Restricted a t := by
    simpa only [← he, rawTree_code] using argument_restricted a ha
  have hrestriction : restrictionCheck a (Localization.argumentCode a) = true := by
    simpa only [he] using (restrictionCheck_code a ha t ht).mpr hr
  exact Bool.and_eq_true.mpr ⟨Bool.and_eq_true.mpr ⟨ha,
    (Theta.acceptedCode_iff 0 _).mpr hc⟩,
    hrestriction⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota
