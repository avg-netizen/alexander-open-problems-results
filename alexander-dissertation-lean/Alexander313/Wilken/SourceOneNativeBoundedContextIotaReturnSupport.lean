import Alexander313.Wilken.PublicEpsilonNativeIotaOrderInduction
import Alexander313.Wilken.SourceOneNativeBoundedPublicReturnCodes

/-!
# Genuine original source-one return callers for intermediate iota

The original outer source-one root identifies the selected uniform public
endpoint by actual collapse injectivity. The intermediate original Normal
root derives its real finite SAME-value source-one return, its literal
zero-index shape, high caller, and canonical beta identity. Every hidden
principal node of returned restricted trees stays below beta. No native
base-one parser, representative, return, restriction or commutation oracle.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.BoundedContextReturn

/-- Equal actual original high roots have the same ORIGINAL successor
endpoint. The argument equality is derived from real collapse injectivity. -/
theorem sourceAlphaPlus_eq_of_root_value (a d : Nat)
    (ha : rootCheck a = true) (hd : rootCheck d = true)
    (he : interpretation 0 a = interpretation 0 d) :
    Enclosure.sourceAlphaPlus a = Enclosure.sourceAlphaPlus d := by
  obtain ⟨t, htcode, ht, hnt, hst⟩ := (rootCheck_exact a).mp ha
  obtain ⟨u, hucode, hu, hnu, hsu⟩ := (rootCheck_exact d).mp hd
  have htc := SourceFixedPoint.checked_theta_argument 0 0 t ht
  have huc := SourceFixedPoint.checked_theta_argument 0 0 u hu
  have hv : globalCollapse (finiteBase 0) 0 (denote 0 t) =
      globalCollapse (finiteBase 0) 0 (denote 0 u) := by
    simpa only [htcode, hucode, interpretation_code, denote, RelativeTerm.eval] using he
  have harg := (globalCollapse_eq_iff (finiteBase 0) (finiteBase_pos 0) 0
    (SourceFixedPoint.sourceOrdinal 0 0 t htc)
    (SourceFixedPoint.sourceOrdinal 0 0 u huc)
    (SourceFixedPoint.checked_theta_sort 0 0 t ht)
    (SourceFixedPoint.checked_theta_sort 0 0 u hu)).mp hv
  simp only [Enclosure.sourceAlphaPlus, Lambda.argumentCode, OmegaQuotient.argumentCode,
    htcode, hucode, Localization.argumentCode_theta, interpretation_code]
  rw [harg]

/-- The uniform dictionary selects the SAME actual endpoint as the
original source-one outer root; no minimal stored public level is assumed. -/
theorem selected_endpoint (a : Nat) (ha : rootCheck a = true) :
    PublicEpsilonSourceDictionary.Return.endpoint (alphaCode a) = Enclosure.sourceAlphaPlus a := by
  have hs := alphaCode_spec a ha
  have hq : PublicEpsilonSourceDictionary.inputCheck (alphaCode a) = true :=
    (PublicEpsilonSourceDictionary.inputCheck_exact _).mpr
      ⟨hs.1, by rw [hs.2]; exact root_epsilon a ha⟩
  have hl : PublicEpsilonSourceDictionary.level (alphaCode a) = 0 := by
    apply Nat.eq_zero_of_not_pos
    intro hp
    have h := (PublicEpsilonSourceDictionary.level_bound _ hs.1).2.2 0 hp
    have hb : unionInterpretation (alphaCode a) < finiteBase (0 + 1) := by
      rw [hs.2]
      exact (lt_nextBase_iff_code 0 _).mpr ⟨a, root_low a ha, rfl⟩
    exact (not_le_of_gt hb) h
  have hb : PublicEpsilonSourceDictionary.basePoint (alphaCode a) = false := by
    apply Bool.eq_false_of_not_eq_true
    intro h
    have he := (PublicEpsilonSourceDictionary.basePoint_exact _ hs.1).mp h
    rw [hl, finiteBase_zero, hs.2] at he
    exact (ne_of_gt (EpsilonOffsets.epsilon_one_lt (root_epsilon a ha))) he
  have hd := PublicEpsilonSourceDictionary.source_one_spec _ hq hl
  have he := sourceAlphaPlus_eq_of_root_value a
    (PublicEpsilonSourceDictionary.sourceRootCode (alphaCode a)) ha hd.1 (hs.2.symm.trans hd.2.1.symm)
  simp only [PublicEpsilonSourceDictionary.Return.endpoint, hb, hl, Bool.false_eq_true,
    if_false, if_pos rfl]
  exact he.symm

/-- The original bounded high-root domain supplies the generic literal-q
caller. Its bound is the ORIGINAL source-one successor endpoint. -/
theorem intermediate_root_caller (a : Nat) (ha : rootCheck a = true)
    (t : RelativeTerm Nat) (ht : NativeContext.check (alphaCode a) (.theta 0 t) = true)
    (hn : NativeContext.Comparison.Normal (alphaCode a) t) (hh : 1 < t.outerSort)
    (hv : NativeContext.denote (alphaCode a) (.theta 0 t) < Enclosure.sourceAlphaPlus a) :
    NativeContext.PublicEpsilonIota.rootCheck (alphaCode a) (.theta 0 t : RelativeTerm Nat).code = true := by
  have hs := alphaCode_spec a ha
  have hq : PublicEpsilonSourceDictionary.inputCheck (alphaCode a) = true :=
    (PublicEpsilonSourceDictionary.inputCheck_exact _).mpr
      ⟨hs.1, by rw [hs.2]; exact root_epsilon a ha⟩
  apply (NativeContext.PublicEpsilonIota.rootCheck_exact _ _).mpr
  refine ⟨hq, ⟨t, rfl, ht, hn, hh⟩, ?_⟩
  rw [NativeContext.interpretation_code, selected_endpoint a ha]
  exact hv

/-- The genuine generic root bound is the original source-one outer bound. -/
theorem intermediate_bound (a b : Nat) (ha : rootCheck a = true)
    (hb : NativeContext.PublicEpsilonIota.rootCheck (alphaCode a) b = true) :
    NativeContext.interpretation (alphaCode a) b < Enclosure.sourceAlphaPlus a := by
  rw [← selected_endpoint a ha]
  exact ((NativeContext.PublicEpsilonIota.rootCheck_exact _ _).mp hb).2.2

def returnedTerm (a : Nat) (t : RelativeTerm Nat) : RelativeTerm Nat :=
  ThetaCourse.rawTree (BoundedPublicReturn.sourceTermCode a t)

def returnedRoot (a b : Nat) : Nat :=
  BoundedPublicReturn.sourceTermCode a (ThetaCourse.rawTree b)

theorem returnedTerm_primrec : Primrec₂ returnedTerm :=
  ThetaCourse.rawTree_primrec.comp₂ BoundedPublicReturn.sourceTermCode_primrec

theorem returnedRoot_primrec : Primrec₂ returnedRoot :=
  BoundedPublicReturn.sourceTermCode_primrec.comp Primrec.fst
    (ThetaCourse.rawTree_primrec.comp Primrec.snd)

/-- Every original beta-restricted hidden call is below the actual outer
endpoint, so the real finite return executes without an added caller. -/
theorem sourceTermCode_spec (a b : Nat) (ha : rootCheck a = true)
    (hb : NativeContext.PublicEpsilonIota.rootCheck (alphaCode a) b = true)
    (t : RelativeTerm Nat) (ht : NativeContext.check (alphaCode a) t = true)
    (hn : NativeContext.Comparison.Normal (alphaCode a) t)
    (hr : NativeContext.PublicEpsilonIota.Restricted (alphaCode a) b t) :
    Theta.acceptedCode 0 (BoundedPublicReturn.sourceTermCode a t) = true ∧
      interpretation 0 (BoundedPublicReturn.sourceTermCode a t) = NativeContext.denote (alphaCode a) t := by
  apply BoundedPublicReturn.sourceTermCode_spec a ha t ht hn
  intro u hu
  exact (hr u hu).trans (intermediate_bound a b ha hb)

theorem returnedTerm_spec (a b : Nat) (ha : rootCheck a = true)
    (hb : NativeContext.PublicEpsilonIota.rootCheck (alphaCode a) b = true)
    (t : RelativeTerm Nat) (ht : NativeContext.check (alphaCode a) t = true)
    (hn : NativeContext.Comparison.Normal (alphaCode a) t)
    (hr : NativeContext.PublicEpsilonIota.Restricted (alphaCode a) b t) :
    check 0 (returnedTerm a t) = true ∧ Theta.Normal 0 (returnedTerm a t) ∧
      denote 0 (returnedTerm a t) = NativeContext.denote (alphaCode a) t := by
  have hs := sourceTermCode_spec a b ha hb t ht hn hr
  have hc := (Theta.acceptedCode_iff 0 _).mp hs.1
  have hct : check 0 (returnedTerm a t) = true := by
    obtain ⟨v, he, hv⟩ := (checkCode_iff 0 _).mp hc.1
    simpa only [returnedTerm, ← he, ThetaCourse.rawTree_code] using hv
  have hv : denote 0 (returnedTerm a t) = NativeContext.denote (alphaCode a) t := by
    exact (SourceDecomposition.input_value 0 _ hs.1).symm.trans hs.2
  exact ⟨hct, hc.2, hv⟩

private theorem sourceTermCode_low_triple (a : Nat) (ha : rootCheck a = true)
    (t : RelativeTerm Nat) (ht : NativeContext.check (alphaCode a) t = true)
    (hn : NativeContext.Comparison.Normal (alphaCode a) t) (hl : t.outerSort ≤ 1)
    (hb : NativeContext.denote (alphaCode a) t < Enclosure.sourceAlphaPlus a) :
    Theta.acceptedCode 0 (BoundedPublicReturn.sourceTermCode a t) = true ∧
      lowCheckCode 0 (BoundedPublicReturn.sourceTermCode a t) = true ∧
      interpretation 0 (BoundedPublicReturn.sourceTermCode a t) = NativeContext.denote (alphaCode a) t := by
  have hs := BoundedPublicReturn.sourceTermCode_low_spec a ha t ht hn hl hb
  have hc := (Theta.acceptedLowCode_iff 0 _).mp hs.1
  have hchecked : checkCode 0 (BoundedPublicReturn.sourceTermCode a t) = true := by
    obtain ⟨v, he, hv⟩ := (lowCheckCode_iff 0 _).mp hc.1
    simpa only [← he, checkCode_code] using (Bool.and_eq_true.mp hv).1
  exact ⟨(Theta.acceptedCode_iff 0 _).mpr ⟨hchecked, hc.2⟩, hc.1, hs.2⟩

theorem returnedRoot_spec (a b : Nat) (ha : rootCheck a = true)
    (hb : NativeContext.PublicEpsilonIota.rootCheck (alphaCode a) b = true) :
    Theta.acceptedCode 0 (returnedRoot a b) = true ∧ lowCheckCode 0 (returnedRoot a b) = true ∧
      interpretation 0 (returnedRoot a b) = NativeContext.interpretation (alphaCode a) b := by
  obtain ⟨hq, ⟨t, he, ht, hn, hh⟩, hbound⟩ :=
    (NativeContext.PublicEpsilonIota.rootCheck_exact _ _).mp hb
  have hs := sourceTermCode_low_triple a ha (.theta 0 t) ht hn (by decide)
    (by simpa only [he, NativeContext.interpretation_code] using intermediate_bound a b ha hb)
  simpa only [returnedRoot, he, ThetaCourse.rawTree_code, NativeContext.interpretation_code] using hs

theorem returnedRoot_shape (a b : Nat) (ha : rootCheck a = true)
    (hb : NativeContext.PublicEpsilonIota.rootCheck (alphaCode a) b = true) :
    ∃ t : RelativeTerm Nat, returnedRoot a b = (.theta 0 t).code := by
  obtain ⟨hq, ⟨t, he, ht, hn, hh⟩, hbound⟩ :=
    (NativeContext.PublicEpsilonIota.rootCheck_exact _ _).mp hb
  have htarg := NativeContext.BaseTransformation.theta_argument_check (alphaCode a) 0 t ht
  have hr : NativeContext.PublicEpsilonIota.Restricted (alphaCode a) b t := by
    simpa only [he, Localization.argumentCode_theta, ThetaCourse.rawTree_code] using
      NativeContext.PublicEpsilonIota.argument_restricted (alphaCode a) b hb
  let c := BoundedPublicReturn.sourceTermCode a t
  have hc := sourceTermCode_spec a b ha hb t htarg hn hr
  have hhigh : omegaSequence (finiteBase 0) 1 ≤ interpretation 0 c := by
    rw [hc.2, finiteBase_zero, HeightSupport.root_omegaSequence_succ a 0 ha]
    apply le_of_not_gt
    intro h
    exact (not_le_of_gt hh) ((NativeContext.denote_lt_iff_outerSort_le _ t htarg 1 (by omega)).mp h)
  have hΩ : 0 < omegaSequence (finiteBase 0) 1 :=
    (omegaSequence_isSuccLimit (finiteBase 0) 0).bot_lt
  have hpos : 0 < interpretation 0 (SourceDecomposition.highCode 0 0 c) := by
    rw [(SourceDecomposition.parts_code_value 0 0 c hc.1).1]
    exact mul_pos hΩ ((Ordinal.div_pos hΩ.ne').mpr hhigh)
  have hz : SourceFixedPoint.zeroCheck 0 (SourceDecomposition.highCode 0 0 c) = false := by
    apply Bool.eq_false_of_not_eq_true
    intro hz
    exact (ne_of_gt hpos) ((SourceFixedPoint.zeroCheck_exact 0 _
      (SourceDecomposition.parts_accepted 0 0 c hc.1).1).mp hz)
  have hroot : returnedRoot a b = BoundedPublicReturn.zeroCode a c := by
    simpa only [returnedRoot, he, ThetaCourse.rawTree_code, BoundedPublicReturn.sourceTermCode_theta,
      BoundedPublicReturn.thetaCode, beq_self_eq_true, Bool.cond_true]
  rw [hroot]
  simp only [BoundedPublicReturn.zeroCode, hz, Bool.cond_false]
  cases h : Theta.Normalization.lessRawCode 0 a
      (BoundedPublicReturn.nodeCode 0 (SourceDecomposition.highCode 0 0 c)) with
  | true => exact ⟨ThetaCourse.rawTree c, rfl⟩
  | false => exact ⟨ThetaCourse.rawTree (BoundedPublicReturn.shiftedArgument a c), rfl⟩

theorem returnedRoot_iota_caller (a b : Nat) (ha : rootCheck a = true)
    (hb : NativeContext.PublicEpsilonIota.rootCheck (alphaCode a) b = true) :
    rootCheck (returnedRoot a b) = true := by
  have hs := returnedRoot_spec a b ha hb
  obtain ⟨t, he⟩ := returnedRoot_shape a b ha hb
  have hc := (Theta.acceptedCode_iff 0 _).mp hs.1
  have ht : check 0 (.theta 0 t) = true := by simpa only [he, checkCode_code] using hc.1
  have hn : Theta.Normal 0 (.theta 0 t) := by simpa only [he, ThetaCourse.rawTree_code] using hc.2
  have hv : denote 0 (.theta 0 t) = NativeContext.interpretation (alphaCode a) b := by
    rw [← interpretation_code, ← he]
    exact hs.2.2
  have heps := NativeContext.PublicEpsilonIota.root_epsilon (alphaCode a) b hb
  have hh : 1 < t.outerSort := by
    have heps' : Ordinal.omega0 ^ denote 0 (.theta 0 t) = denote 0 (.theta 0 t) := by
      rw [hv]; exact heps
    rcases (Epsilon.theta_epsilon_iff 0 0 t ht).mp heps' with hh | ⟨_, hfalse⟩
    · exact hh
    · omega
  exact (rootCheck_exact _).mpr ⟨t, he, ht, hn, hh⟩

theorem returnedRoot_alphaCode (a b : Nat) (ha : rootCheck a = true)
    (hb : NativeContext.PublicEpsilonIota.rootCheck (alphaCode a) b = true) :
    alphaCode (returnedRoot a b) = NativeContext.PublicEpsilonIota.betaCode (alphaCode a) b := by
  have hs := alphaCode_spec _ (returnedRoot_iota_caller a b ha hb)
  have ht := NativeContext.PublicEpsilonIota.betaCode_spec _ _ hb
  exact Canonical.check_value_injective _ _ hs.1 ht.1
    (hs.2.trans ((returnedRoot_spec a b ha hb).2.2.trans ht.2.symm))

def FullBelow (β : Ordinal.{0}) (t : RelativeTerm Nat) : Prop :=
  ∀ u ∈ fullList t, denote 0 u < β

theorem fullBelow_sum (β : Ordinal.{0}) (t u : RelativeTerm Nat) :
    FullBelow β (.sum t u) ↔ FullBelow β t ∧ FullBelow β u := by
  constructor
  · intro h
    exact ⟨fun v hv => h v (List.mem_append_left _ hv),
      fun v hv => h v (List.mem_append_right _ hv)⟩
  · rintro ⟨ht, hu⟩ v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact ht v hv
    · exact hu v hv

theorem fullBelow_theta_zero (β : Ordinal.{0}) (t : RelativeTerm Nat) :
    FullBelow β (.theta 0 t) ↔ denote 0 (.theta 0 t) < β ∧ FullBelow β t := by
  simp only [FullBelow, fullList, RelativeTerm.PrincipalSupport.principalList_theta_same,
    List.forall_mem_cons]

theorem fullBelow_theta_succ (β : Ordinal.{0}) (k : Nat) (t : RelativeTerm Nat) :
    FullBelow β (.theta (k + 1) t) ↔ FullBelow β t := by
  rw [FullBelow, fullList,
    RelativeTerm.PrincipalSupport.principalList_theta_higher 0 (k + 1) t (Nat.succ_pos k)]
  rfl

private theorem atoms_fullBelow (β : Ordinal.{0}) (t : RelativeTerm Nat)
    (hr : FullBelow β t) (u : RelativeTerm Nat) (hu : u ∈ Theta.atoms 0 t) :
    FullBelow β u := by
  revert hr hu
  induction t with
  | parameter p =>
    intro hr hu
    simp only [Theta.atoms_parameter_zero, List.not_mem_nil] at hu
  | sum t v iht ihv =>
    intro hr hu
    have hs := (fullBelow_sum β t v).mp hr
    rw [Theta.atoms_sum] at hu
    rcases List.mem_append.mp hu with hu | hu
    · exact iht hs.1 hu
    · exact ihv hs.2 hu
  | theta k t ih =>
    intro hr hu
    rw [Theta.atoms_theta] at hu
    exact (List.mem_singleton.mp hu).symm ▸ hr

private theorem buildRev_fullBelow (β : Ordinal.{0}) (as : List (RelativeTerm Nat))
    (hr : ∀ t ∈ as, FullBelow β t) : FullBelow β (Theta.Normalization.buildRev 0 as) := by
  revert hr
  induction as with
  | nil =>
    intro _ u hu
    simp only [Theta.Normalization.buildRev, Theta.Normalization.zeroTree, fullList,
      RelativeTerm.PrincipalSupport.principalList, List.not_mem_nil] at hu
  | cons t as ih =>
    intro hr
    exact (fullBelow_sum β _ _).mpr
      ⟨ih (fun u hu => hr u (List.mem_cons_of_mem _ hu)), hr t List.mem_cons_self⟩

private theorem buildAtoms_fullBelow (β : Ordinal.{0}) (as : List (RelativeTerm Nat))
    (hr : ∀ t ∈ as, FullBelow β t) : FullBelow β (Theta.Normalization.buildAtoms 0 as) :=
  buildRev_fullBelow β as.reverse (fun t ht => hr t (List.mem_reverse.mp ht))

/-- The actual ORIGINAL level-zero normalizer preserves all hidden cuts. -/
theorem normalize_fullBelow (β : Ordinal.{0}) (t : RelativeTerm Nat)
    (ht : check 0 t = true) (hr : FullBelow β t) :
    FullBelow β (Theta.Normalization.normalize 0 t) := by
  revert ht hr
  induction t with
  | parameter p =>
    intro ht hr u hu
    simp only [Theta.Normalization.normalize_parameter_zero, fullList,
      RelativeTerm.PrincipalSupport.principalList, List.not_mem_nil] at hu
  | sum t u iht ihu =>
    intro ht hr
    have hc := OrderSupport.sum_checks t u ht
    have hs := (fullBelow_sum β t u).mp hr
    rw [Theta.Normalization.normalize_sum]
    apply buildAtoms_fullBelow
    intro v hv
    have hm := Theta.Normalization.normalizeAtoms_mem 0 v _ hv
    rcases List.mem_append.mp hm with hm | hm
    · exact atoms_fullBelow β _ (iht hc.1 hs.1) v hm
    · exact atoms_fullBelow β _ (ihu hc.2 hs.2) v hm
  | theta k t ih =>
    intro ht hr
    have hc := OrderSupport.argument_checked k t ht
    rw [Theta.Normalization.normalize_theta]
    cases k with
    | zero =>
      have hs := (fullBelow_theta_zero β t).mp hr
      apply (fullBelow_theta_zero β _).mpr
      refine ⟨?_, ih hc hs.2⟩
      have hv := (Theta.Normalization.normalizeCode_checked 0 t.code
        (by simpa only [checkCode_code] using hc)).2.2
      have he : denote 0 (Theta.Normalization.normalize 0 t) = denote 0 t := by
        simpa only [Theta.Normalization.normalizeCode_code, interpretation_code] using hv
      change globalCollapse (finiteBase 0) 0 (denote 0 (Theta.Normalization.normalize 0 t)) < _
      rw [he]
      exact hs.1
    | succ k =>
      exact (fullBelow_theta_succ β k _).mpr
        (ih hc ((fullBelow_theta_succ β k t).mp hr))

/-- The real source-one normalized addition introduces no new hidden value. -/
theorem normalizedSumCode_fullBelow (c d : Nat) (β : Ordinal.{0})
    (hc : checkCode 0 c = true) (hd : checkCode 0 d = true)
    (hrc : FullBelow β (ThetaCourse.rawTree c)) (hrd : FullBelow β (ThetaCourse.rawTree d)) :
    FullBelow β (ThetaCourse.rawTree (Addition.normalizedSumCode 0 c d)) := by
  obtain ⟨t, rfl, ht⟩ := (checkCode_iff 0 c).mp hc
  obtain ⟨u, rfl, hu⟩ := (checkCode_iff 0 d).mp hd
  have hsum : check 0 (.sum t u) = true := by
    simpa only [Addition.sumCode_code, checkCode_code] using
      (Addition.sumCode_checked 0 t.code u.code (by simpa only [checkCode_code] using ht)
        (by simpa only [checkCode_code] using hu)).1
  have hs := normalize_fullBelow β (.sum t u) hsum
    ((fullBelow_sum β t u).mpr
      ⟨by simpa only [ThetaCourse.rawTree_code] using hrc,
        by simpa only [ThetaCourse.rawTree_code] using hrd⟩)
  simpa only [Addition.normalizedSumCode, Addition.sumCode_code,
    Theta.Normalization.normalizeCode_code, ThetaCourse.rawTree_code] using hs

/-- Original LOW Normality bounds EVERY hidden node by the real value. -/
theorem lowCode_fullBelow (c : Nat) (β : Ordinal.{0})
    (hc : lowCheckCode 0 c = true) (hn : Theta.acceptedCode 0 c = true)
    (hb : interpretation 0 c < β) : FullBelow β (ThetaCourse.rawTree c) := by
  have ha := SourceDecomposition.input_tree 0 c hn
  obtain ⟨t, he, hl⟩ := (lowCheckCode_iff 0 c).mp hc
  have hlow : (ThetaCourse.rawTree c).outerSort ≤ 1 := by
    simpa only [← he, ThetaCourse.rawTree_code] using of_decide_eq_true (Bool.and_eq_true.mp hl).2
  intro u hu
  have h := Inverse.fullList_value_le_low _ u ha.1 ha.2 hlow hu
  rw [← SourceDecomposition.input_value 0 c hn] at h
  exact h.trans_lt hb

private theorem sourceTermCode_low_fullBelow (a b : Nat) (ha : rootCheck a = true)
    (hb : NativeContext.PublicEpsilonIota.rootCheck (alphaCode a) b = true)
    (t : RelativeTerm Nat) (ht : NativeContext.check (alphaCode a) t = true)
    (hn : NativeContext.Comparison.Normal (alphaCode a) t) (hl : t.outerSort ≤ 1)
    (hv : NativeContext.denote (alphaCode a) t < NativeContext.interpretation (alphaCode a) b) :
    FullBelow (NativeContext.interpretation (alphaCode a) b)
      (ThetaCourse.rawTree (BoundedPublicReturn.sourceTermCode a t)) := by
  have hs := sourceTermCode_low_triple a ha t ht hn hl
    (hv.trans (intermediate_bound a b ha hb))
  exact lowCode_fullBelow _ _ hs.2.1 hs.1 (hs.2.2.trans_lt hv)

/-- Genuine finite return preserves the ENTIRE original beta restriction. -/
theorem sourceTermCode_restricted (a b : Nat) (ha : rootCheck a = true)
    (hb : NativeContext.PublicEpsilonIota.rootCheck (alphaCode a) b = true)
    (t : RelativeTerm Nat) (ht : NativeContext.check (alphaCode a) t = true)
    (hn : NativeContext.Comparison.Normal (alphaCode a) t)
    (hr : NativeContext.PublicEpsilonIota.Restricted (alphaCode a) b t) :
    FullBelow (NativeContext.interpretation (alphaCode a) b) (returnedTerm a t) := by
  revert ht hn hr
  induction t with
  | parameter p =>
    intro ht hn hr
    have hp := NativeContext.checked_parameters (alphaCode a) (.parameter p) ht p
      (by simp [RelativeTerm.parameters])
    exact sourceTermCode_low_fullBelow a b ha hb (.parameter p) ht hn (by simp [RelativeTerm.outerSort])
      (hp.2.trans_le (NativeContext.PublicEpsilonIota.root_base_le (alphaCode a) b hb))
  | sum t u iht ihu =>
    intro ht hn hr
    have hc := NativeContext.BaseTransformation.sum_checks (alphaCode a) t u ht
    have hs := (NativeContext.PublicEpsilonIota.restricted_sum (alphaCode a) b t u).mp hr
    have hst := sourceTermCode_spec a b ha hb t hc.1 hn.1 hs.1
    have hsu := sourceTermCode_spec a b ha hb u hc.2 hn.2.1 hs.2
    change FullBelow _ (ThetaCourse.rawTree (BoundedPublicReturn.sourceTermCode a (.sum t u)))
    rw [BoundedPublicReturn.sourceTermCode_sum]
    exact normalizedSumCode_fullBelow _ _ _
      ((Theta.acceptedCode_iff 0 _).mp hst.1).1
      ((Theta.acceptedCode_iff 0 _).mp hsu.1).1
      (iht hc.1 hn.1 hs.1) (ihu hc.2 hn.2.1 hs.2)
  | theta k t ih =>
    intro ht hn hr
    cases k with
    | zero =>
      exact sourceTermCode_low_fullBelow a b ha hb (.theta 0 t) ht hn (by simp [RelativeTerm.outerSort])
        ((NativeContext.PublicEpsilonIota.restricted_theta_zero (alphaCode a) b t).mp hr).1
    | succ k =>
      have hc := NativeContext.BaseTransformation.theta_argument_check (alphaCode a) (k + 1) t ht
      have hrt := (NativeContext.PublicEpsilonIota.restricted_theta_succ (alphaCode a) b k t).mp hr
      have h := ih hc hn hrt
      have hk : (k + 1 == 0) = false := by simp
      change FullBelow _ (ThetaCourse.rawTree (BoundedPublicReturn.sourceTermCode a (.theta (k + 1) t)))
      rw [BoundedPublicReturn.sourceTermCode_theta]
      simpa only [BoundedPublicReturn.thetaCode, hk, Bool.cond_false,
        BoundedPublicReturn.nodeCode, ThetaCourse.rawTree_code, fullBelow_theta_succ] using h

/-- The real returned beta value changes the derived scalar cut to the
original source-one source-star domain. -/
theorem returnedTerm_restricted (a b : Nat) (ha : rootCheck a = true)
    (hb : NativeContext.PublicEpsilonIota.rootCheck (alphaCode a) b = true)
    (t : RelativeTerm Nat) (ht : NativeContext.check (alphaCode a) t = true)
    (hn : NativeContext.Comparison.Normal (alphaCode a) t)
    (hr : NativeContext.PublicEpsilonIota.Restricted (alphaCode a) b t) :
    Restricted (returnedRoot a b) (returnedTerm a t) := by
  intro u hu
  rw [(returnedRoot_spec a b ha hb).2.2]
  exact sourceTermCode_restricted a b ha hb t ht hn hr u hu

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.BoundedContextReturn
