import Alexander313.Wilken.SourceOneNativeIota
import Alexander313.Wilken.HereditaryNativeIotaOrderInductionSupport

/-!
# Actual original source-one domains for full iota order transport

The source atoms are literal thetaAtoms: original parameters are zero and
are omitted, rather than parsed as native public payloads. Actual hereditary
level-zero checks/Normality derive their original ANF and every exposed
query caller. The real epsilon root and original full principal restriction
derive the cutoff and exact exposed-support shift. Native checks appear
only on the actual alpha target. No order or Normal transport oracle occurs.
Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.OrderSupport

theorem sum_checks (t u : RelativeTerm Nat) (ht : check 0 (.sum t u) = true) :
    check 0 t = true ∧ check 0 u = true := by
  obtain ⟨n, hn⟩ := (check_iff_finite_admissible 0 (.sum t u)).mp ht
  cases hn.2 with
  | sum ht' hu' => exact ⟨Theta.admitted_checked ⟨hn.1.1, ht'⟩, Theta.admitted_checked ⟨hn.1.2, hu'⟩⟩

theorem argument_checked (k : Nat) (t : RelativeTerm Nat)
    (ht : check 0 (.theta k t) = true) : check 0 t = true := by
  obtain ⟨n, hn⟩ := (check_iff_finite_admissible 0 (.theta k t)).mp ht
  exact Theta.admitted_checked (Theta.admitted_theta_argument hn)

theorem alpha_base (a : Nat) (ha : rootCheck a = true) :
    NativeContext.base (alphaCode a) = interpretation 0 a := (alphaCode_spec a ha).2

theorem root_additive (a : Nat) (ha : rootCheck a = true) :
    Ordinal.IsPrincipal (· + ·) (interpretation 0 a) := by
  rw [← root_epsilon a ha]
  exact Ordinal.isPrincipal_add_omega0_opow _

theorem restricted_low_below (a : Nat) (ha : rootCheck a = true) (t : RelativeTerm Nat)
    (ht : check 0 t = true) (hr : Restricted a t) (hl : t.outerSort ≤ 1) :
    denote 0 t < interpretation 0 a := by
  revert ht hr hl
  induction t with
  | parameter p =>
    intro ht hr hl
    have hp : parameterCheck 0 p = true := ht
    have h : denote 0 (.parameter p) < 1 := by
      simpa only [denote, RelativeTerm.eval, finiteBase_zero] using parameter_sound 0 p hp
    exact h.trans (EpsilonOffsets.epsilon_one_lt (root_epsilon a ha))
  | sum t u iht ihu =>
    intro ht hr hl
    have hc := sum_checks t u ht
    have hs := (restricted_sum a t u).mp hr
    exact root_additive a ha (iht hc.1 hs.1 ((le_max_left _ _).trans hl))
      (ihu hc.2 hs.2 ((le_max_right _ _).trans hl))
  | theta k t ih =>
    intro ht hr hl
    have hk : k = 0 := by simp only [RelativeTerm.outerSort] at hl; omega
    subst k
    exact ((restricted_theta_zero a t).mp hr).1

theorem restricted_below_iff_outerSort (a : Nat) (ha : rootCheck a = true)
    (t : RelativeTerm Nat) (ht : check 0 t = true) (hr : Restricted a t) :
    denote 0 t < interpretation 0 a ↔ t.outerSort ≤ 1 := by
  constructor
  · intro h
    apply (denote_lt_iff_outerSort_le 0 t ht 1 (by omega)).mp
    simpa only [finiteBase_zero] using h.trans (root_lt_first a ha)
  · exact restricted_low_below a ha t ht hr

theorem small_iff_outerSort (a : Nat) (ha : rootCheck a = true)
    (t : RelativeTerm Nat) (ht : check 0 t = true) (hr : Restricted a t) :
    small a t = true ↔ t.outerSort ≤ 1 :=
  (small_exact a ha t ht).trans (restricted_below_iff_outerSort a ha t ht hr)

theorem transform_low (a : Nat) (ha : rootCheck a = true) (t : RelativeTerm Nat)
    (ht : check 0 t = true) (hr : Restricted a t) (hl : t.outerSort ≤ 1) :
    transform a t = .parameter (parameterCode t) :=
  transform_below a ha t ht (restricted_low_below a ha t ht hr hl)

theorem transform_low_value (a : Nat) (ha : rootCheck a = true) (t : RelativeTerm Nat)
    (ht : check 0 t = true) (hr : Restricted a t) (hl : t.outerSort ≤ 1) :
    NativeContext.denote (alphaCode a) (transform a t) = denote 0 t :=
  transform_below_value a ha t ht (restricted_low_below a ha t ht hr hl)

theorem transform_low_normal (a : Nat) (ha : rootCheck a = true) (t : RelativeTerm Nat)
    (ht : check 0 t = true) (hr : Restricted a t) (hl : t.outerSort ≤ 1) :
    NativeContext.Comparison.Normal (alphaCode a) (transform a t) := by
  rw [transform_low a ha t ht hr hl]
  trivial

theorem transform_theta_succ (a k : Nat) (ha : rootCheck a = true) (t : RelativeTerm Nat)
    (ht : check 0 (.theta (k + 1) t) = true) (hr : Restricted a (.theta (k + 1) t)) :
    transform a (.theta (k + 1) t) = .theta k (transform a t) := by
  have hf : small a (.theta (k + 1) t) = false := by
    cases h : small a (.theta (k + 1) t) with
    | false => rfl
    | true =>
      have hs := (small_iff_outerSort a ha _ ht hr).mp h
      simp only [RelativeTerm.outerSort] at hs
      omega
  simp only [transform, hf, Bool.cond_false, Nat.add_sub_cancel]

theorem transform_add (a : Nat) (ha : rootCheck a = true) (t u : RelativeTerm Nat)
    (ht : check 0 t = true) (hu : check 0 u = true) :
    NativeContext.denote (alphaCode a) (transform a (.sum t u)) =
      NativeContext.denote (alphaCode a) (transform a t) +
        NativeContext.denote (alphaCode a) (transform a u) := by
  have hc : check 0 (.sum t u) = true := by
    let n := max (SourceOne.PublicCodes.fragment t) (SourceOne.PublicCodes.fragment u)
    have htn := Theta.checked_admissible 0 n t ht
      ((SourceOne.PublicCodes.height_le_fragment t).trans (le_max_left _ _))
    have hun := Theta.checked_admissible 0 n u hu
      ((SourceOne.PublicCodes.height_le_fragment u).trans (le_max_right _ _))
    exact Theta.admitted_checked ⟨⟨htn.1, hun.1⟩, .sum htn.2 hun.2⟩
  cases h : small a (.sum t u) with
  | false => simp only [transform, h, Bool.cond_false]; rfl
  | true =>
    have hs := (small_exact a ha (.sum t u) hc).mp h
    have hst : denote 0 t < interpretation 0 a := le_self_add.trans_lt hs
    have hsu : denote 0 u < interpretation 0 a := le_add_self.trans_lt hs
    rw [transform_below_value a ha (.sum t u) hc hs,
      transform_below_value a ha t ht hst, transform_below_value a ha u hu hsu]
    rfl

theorem transform_ge_base (a : Nat) (ha : rootCheck a = true) (t : RelativeTerm Nat)
    (ht : check 0 t = true) (hr : Restricted a t) (hs : interpretation 0 a ≤ denote 0 t) :
    NativeContext.base (alphaCode a) ≤ NativeContext.denote (alphaCode a) (transform a t) := by
  revert ht hr hs
  induction t with
  | parameter p =>
    intro ht hr hs
    exact False.elim ((restricted_low_below a ha (.parameter p) ht hr (Nat.zero_le _)).not_ge hs)
  | sum t u iht ihu =>
    intro ht hr hs
    have hc := sum_checks t u ht
    have hrs := (restricted_sum a t u).mp hr
    rw [transform_add a ha t u hc.1 hc.2]
    by_cases ht' : interpretation 0 a ≤ denote 0 t
    · exact (iht hc.1 hrs.1 ht').trans le_self_add
    · have hu' : interpretation 0 a ≤ denote 0 u := by
        by_contra hu'
        exact (root_additive a ha (lt_of_not_ge ht') (lt_of_not_ge hu')).not_ge hs
      exact (ihu hc.2 hrs.2 hu').trans le_add_self
  | theta k t ih =>
    intro ht hr hs
    cases k with
    | zero => exact False.elim (((restricted_theta_zero a t).mp hr).1.not_ge hs)
    | succ k =>
      have hc := transform_checked a ha (.theta (k + 1) t) ht hr
      rw [transform_theta_succ a k ha t ht hr] at hc ⊢
      exact NativeContext.BaseTransformation.theta_base_le _ k _ hc

theorem transform_low_lt_iff (a : Nat) (ha : rootCheck a = true) (t u : RelativeTerm Nat)
    (ht : check 0 t = true) (hu : check 0 u = true) (hrt : Restricted a t) (hru : Restricted a u)
    (hlt : t.outerSort ≤ 1) (hlu : u.outerSort ≤ 1) :
    NativeContext.denote (alphaCode a) (transform a t) < NativeContext.denote (alphaCode a) (transform a u) ↔
      denote 0 t < denote 0 u := by
  rw [transform_low_value a ha t ht hrt hlt, transform_low_value a ha u hu hru hlu]

theorem transform_low_high_lt (a : Nat) (ha : rootCheck a = true) (t u : RelativeTerm Nat)
    (ht : check 0 t = true) (hu : check 0 u = true) (hrt : Restricted a t) (hru : Restricted a u)
    (hlt : t.outerSort ≤ 1) (hhu : 1 < u.outerSort) :
    denote 0 t < denote 0 u ∧
      NativeContext.denote (alphaCode a) (transform a t) < NativeContext.denote (alphaCode a) (transform a u) := by
  have hb := restricted_low_below a ha t ht hrt hlt
  have hu' : interpretation 0 a ≤ denote 0 u := by
    apply le_of_not_gt
    intro h
    have hl := (restricted_below_iff_outerSort a ha u hu hru).mp h
    omega
  refine ⟨hb.trans_le hu', ?_⟩
  rw [transform_low_value a ha t ht hrt hlt]
  exact (hb.trans_eq (alpha_base a ha).symm).trans_le (transform_ge_base a ha u hu hru hu')

theorem transform_shifted_level_lt (a k l : Nat) (ha : rootCheck a = true) (t u : RelativeTerm Nat)
    (ht : check 0 (.theta (k + 1) t) = true) (hu : check 0 (.theta (l + 1) u) = true)
    (hrt : Restricted a (.theta (k + 1) t)) (hru : Restricted a (.theta (l + 1) u)) (hkl : k < l) :
    denote 0 (.theta (k + 1) t) < denote 0 (.theta (l + 1) u) ∧
      NativeContext.denote (alphaCode a) (transform a (.theta (k + 1) t)) <
        NativeContext.denote (alphaCode a) (transform a (.theta (l + 1) u)) := by
  let n := max (SourceOne.PublicCodes.fragment (.theta (k + 1) t))
    (SourceOne.PublicCodes.fragment (.theta (l + 1) u))
  have htn := Theta.checked_admissible 0 n (.theta (k + 1) t) ht
    ((SourceOne.PublicCodes.height_le_fragment _).trans (le_max_left _ _))
  have hun := Theta.checked_admissible 0 n (.theta (l + 1) u) hu
    ((SourceOne.PublicCodes.height_le_fragment _).trans (le_max_right _ _))
  have hs := Theta.theta_lt_of_level_lt 0 n (k + 1) (l + 1) t u htn hun (by omega)
  rw [← denote_eq_finite 0 n _ htn.2, ← denote_eq_finite 0 n _ hun.2] at hs
  have hct := transform_checked a ha (.theta (k + 1) t) ht hrt
  have hcu := transform_checked a ha (.theta (l + 1) u) hu hru
  rw [transform_theta_succ a k ha t ht hrt] at hct
  rw [transform_theta_succ a l ha u hu hru] at hcu
  refine ⟨hs, ?_⟩
  rw [transform_theta_succ a k ha t ht hrt, transform_theta_succ a l ha u hu hru]
  have hp := NativeContext.FixedPoint.checked_theta_range _ k _ hct
  have hq := NativeContext.FixedPoint.checked_theta_range _ l _ hcu
  exact hp.2.trans_le (((omegaSequence_strictMono (NativeContext.base (alphaCode a))).monotone
    (Nat.succ_le_of_lt hkl)).trans hq.1)

theorem transform_exposedThetaList (a m : Nat) (ha : rootCheck a = true) (t : RelativeTerm Nat)
    (ht : check 0 t = true) (hr : Restricted a t) :
    exposedThetaList m (transform a t) = (exposedThetaList (m + 1) t).map (transform a) := by
  revert ht hr
  induction t with
  | parameter p => intro ht hr; rfl
  | sum t u iht ihu =>
    intro ht hr
    have hc := sum_checks t u ht
    have hs := (restricted_sum a t u).mp hr
    cases h : small a (.sum t u) with
    | true =>
      have hl := (small_iff_outerSort a ha _ ht hr).mp h
      rw [NativeContext.Iota.exposedThetaList_low (m + 1) (by omega) (.sum t u) hl]
      simp only [transform, h, Bool.cond_true, exposedThetaList, List.map_nil]
    | false =>
      simp only [transform, h, Bool.cond_false, exposedThetaList, List.map_append, iht hc.1 hs.1, ihu hc.2 hs.2]
  | theta k t ih =>
    intro ht hr
    cases k with
    | zero =>
      rw [transform_low a ha (.theta 0 t) ht hr le_rfl,
        NativeContext.Iota.exposedThetaList_low (m + 1) (by omega) (.theta 0 t) le_rfl]
      rfl
    | succ k =>
      have hc := argument_checked (k + 1) t ht
      have hs := (restricted_theta_succ a k t).mp hr
      rw [transform_theta_succ a k ha t ht hr]
      by_cases he : k = m
      · subst k
        simp only [exposedThetaList, if_pos rfl, List.map_cons, List.map_nil, transform_theta_succ a m ha t ht hr]
      · have he' : k + 1 ≠ m + 1 := by omega
        by_cases hm : m < k
        · have hm' : m + 1 < k + 1 := by omega
          simp only [exposedThetaList, if_neg he, if_neg he', if_pos hm, if_pos hm', ih hc hs]
        · have hm' : ¬m + 1 < k + 1 := by omega
          simp only [exposedThetaList, if_neg he, if_neg he', if_neg hm, if_neg hm', List.map_nil]

theorem restricted_argument (a k : Nat) (t : RelativeTerm Nat) (hr : Restricted a (.theta k t)) :
    Restricted a t := by
  cases k with
  | zero => exact ((restricted_theta_zero a t).mp hr).2
  | succ k => exact (restricted_theta_succ a k t).mp hr

theorem restricted_atoms (a : Nat) (t x : RelativeTerm Nat) (hr : Restricted a t)
    (hx : x ∈ thetaAtoms t) : Restricted a x := by
  revert hr hx
  induction t with
  | parameter p => intro hr hx; simp only [thetaAtoms, List.not_mem_nil] at hx
  | sum t u iht ihu =>
    intro hr hx
    have hs := (restricted_sum a t u).mp hr
    rcases List.mem_append.mp hx with hx | hx
    · exact iht hs.1 hx
    · exact ihu hs.2 hx
  | theta k t ih =>
    intro hr hx
    have he : x = .theta k t := List.mem_singleton.mp hx
    subst x
    exact hr

theorem restricted_exposed (a m : Nat) (t x : RelativeTerm Nat) (hr : Restricted a t)
    (hx : x ∈ exposedThetaList m t) : Restricted a x := by
  revert hr hx
  induction t with
  | parameter p => intro hr hx; simp only [exposedThetaList, List.not_mem_nil] at hx
  | sum t u iht ihu =>
    intro hr hx
    have hs := (restricted_sum a t u).mp hr
    rcases List.mem_append.mp hx with hx | hx
    · exact iht hs.1 hx
    · exact ihu hs.2 hx
  | theta k t ih =>
    intro hr hx
    by_cases he : k = m
    · have hx' : x = .theta k t := by simpa only [exposedThetaList, if_pos he, List.mem_singleton] using hx
      subst x; exact hr
    · by_cases hm : m < k
      · exact ih (restricted_argument a k t hr)
          (by simpa only [exposedThetaList, if_neg he, if_pos hm] using hx)
      · simp only [exposedThetaList, if_neg he, if_neg hm, List.not_mem_nil] at hx

theorem atoms_checked_normal (t x : RelativeTerm Nat) (ht : check 0 t = true)
    (hn : Theta.Normal 0 t) (hx : x ∈ thetaAtoms t) : check 0 x = true ∧ Theta.Normal 0 x := by
  have hs := (Theta.atoms_spec 0 (SourceOne.PublicCodes.fragment t) t
    ((finiteCheck_iff 0 _ t).mp ht) hn).1 x hx
  exact ⟨Theta.admitted_checked hs.1, hs.2⟩

theorem exposed_checked_normal (m : Nat) (t x : RelativeTerm Nat) (ht : check 0 t = true)
    (hn : Theta.Normal 0 t) (hx : x ∈ exposedThetaList m t) : check 0 x = true ∧ Theta.Normal 0 x := by
  have had := (finiteCheck_iff 0 (SourceOne.PublicCodes.fragment t) t).mp ht
  exact ⟨Theta.admitted_checked (Theta.admitted_exposedThetaList had m hx), hn.exposedThetaList m hx⟩

theorem source_atoms_anf (t : RelativeTerm Nat) (ht : check 0 t = true) (hn : Theta.Normal 0 t) :
    (thetaAtoms t).map (denote 0) = canonicalANF (denote 0 t) :=
  Theta.atoms_denote_anf 0 (SourceOne.PublicCodes.fragment t) t ((finiteCheck_iff 0 _ t).mp ht) hn

theorem source_atoms_normal (t : RelativeTerm Nat) (ht : check 0 t = true) (hn : Theta.Normal 0 t) :
    IsAdditiveNormalForm ((thetaAtoms t).map (denote 0)) := by
  rw [source_atoms_anf t ht hn]; exact canonicalANF_normal _

theorem source_atoms_value (t : RelativeTerm Nat) (ht : check 0 t = true) (hn : Theta.Normal 0 t) :
    principalSum ((thetaAtoms t).map (denote 0)) = denote 0 t := by
  rw [source_atoms_anf t ht hn, principalSum_canonicalANF]

theorem mapped_atoms_low (a : Nat) (ha : rootCheck a = true) (t : RelativeTerm Nat)
    (ht : check 0 t = true) (hn : Theta.Normal 0 t) (hr : Restricted a t) (hl : t.outerSort ≤ 1) :
    (thetaAtoms t).map (fun x => NativeContext.denote (alphaCode a) (transform a x)) =
      (thetaAtoms t).map (denote 0) := by
  apply List.map_congr_left
  intro x hx
  have hc := (atoms_checked_normal t x ht hn hx).1
  have hb : denote 0 x ≤ denote 0 t := by
    apply canonicalANF_mem_le
    rw [← source_atoms_anf t ht hn]
    exact List.mem_map.mpr ⟨x, hx, rfl⟩
  exact transform_below_value a ha x hc (hb.trans_lt (restricted_low_below a ha t ht hr hl))

theorem mapped_atoms_value (a : Nat) (ha : rootCheck a = true) (t : RelativeTerm Nat)
    (ht : check 0 t = true) (hn : Theta.Normal 0 t) (hr : Restricted a t) :
    principalSum ((thetaAtoms t).map (fun x => NativeContext.denote (alphaCode a) (transform a x))) =
      NativeContext.denote (alphaCode a) (transform a t) := by
  revert ht hn hr
  induction t with
  | parameter p =>
    intro ht hn hr
    rw [mapped_atoms_low a ha (.parameter p) ht hn hr (Nat.zero_le _),
      source_atoms_value (.parameter p) ht hn, transform_low_value a ha (.parameter p) ht hr (Nat.zero_le _)]
  | sum t u iht ihu =>
    intro ht hn hr
    have hc := sum_checks t u ht
    have hs := (restricted_sum a t u).mp hr
    rw [thetaAtoms, List.map_append, principalSum_append, iht hc.1 hn.1 hs.1,
      ihu hc.2 hn.2.1 hs.2, transform_add a ha t u hc.1 hc.2]
  | theta k t ih =>
    intro ht hn hr
    simp only [thetaAtoms, List.map_cons, List.map_nil, principalSum, add_zero]

theorem checked_source_theta_lt_iff_exposed (k : Nat) (t u : RelativeTerm Nat)
    (ht : check 0 (.theta k t) = true) (hu : check 0 (.theta k u) = true)
    (hnt : Theta.Normal 0 t) (hnu : Theta.Normal 0 u) :
    denote 0 (.theta k t) < denote 0 (.theta k u) ↔
      (denote 0 t < denote 0 u ∧ ∀ x ∈ exposedThetaList k t, denote 0 x < denote 0 (.theta k u)) ∨
      ∃ x ∈ exposedThetaList k u, denote 0 (.theta k t) ≤ denote 0 x := by
  let n := max (SourceOne.PublicCodes.fragment (.theta k t)) (SourceOne.PublicCodes.fragment (.theta k u))
  have htn := Theta.checked_admissible 0 n (.theta k t) ht
    ((SourceOne.PublicCodes.height_le_fragment _).trans (le_max_left _ _))
  have hun := Theta.checked_admissible 0 n (.theta k u) hu
    ((SourceOne.PublicCodes.height_le_fragment _).trans (le_max_right _ _))
  exact Theta.theta_global_lt_iff_exposed 0 n k t u htn hun hnt hnu

/-- A sum's actual final-principal clause transports once its smaller atom
comparisons and its two real target principal words have been established. -/
theorem mapped_normalSum (a : Nat) (ha : rootCheck a = true)
    (t u : RelativeTerm Nat) (ht : check 0 t = true)
    (hu : check 0 u = true)
    (hnt : Theta.Normal 0 t) (hnu : Theta.Normal 0 u)
    (hrt : Restricted a t) (hru : Restricted a u)
    (hs : SourceNormalSum (denote 0 t + denote 0 u)
      (denote 0 t) (denote 0 u))
    (htw : IsAdditiveNormalForm ((thetaAtoms t).map
      (fun x => NativeContext.denote (alphaCode a) (transform a x))))
    (huw : IsAdditiveNormalForm ((thetaAtoms u).map
      (fun x => NativeContext.denote (alphaCode a) (transform a x))))
    (hcross : ∀ x ∈ thetaAtoms t, ∀ y ∈ thetaAtoms u,
      denote 0 y ≤ denote 0 x →
      NativeContext.denote (alphaCode a) (transform a y) ≤ NativeContext.denote (alphaCode a) (transform a x)) :
    SourceNormalSum
      (NativeContext.denote (alphaCode a) (transform a t) + NativeContext.denote (alphaCode a) (transform a u))
      (NativeContext.denote (alphaCode a) (transform a t))
      (NativeContext.denote (alphaCode a) (transform a u)) := by
  have hsource := (NativeContext.Iota.OrderInduction.normalSum_words_iff (denote 0)
    (thetaAtoms t) (thetaAtoms u) (source_atoms_normal t ht hnt)
    (source_atoms_normal u hu hnu)).mp (by
      simpa only [source_atoms_value t ht hnt, source_atoms_value u hu hnu] using hs)
  have hshape : (thetaAtoms t = [] ∧ thetaAtoms u = []) ∨
      ∃ y, thetaAtoms u = [y] ∧ ∀ x ∈ thetaAtoms t,
        NativeContext.denote (alphaCode a) (transform a y) ≤ NativeContext.denote (alphaCode a) (transform a x) := by
    rcases hsource with hz | ⟨y, hy, hle⟩
    · exact Or.inl hz
    · refine Or.inr ⟨y, hy, ?_⟩
      intro x hx
      exact hcross x hx y (by rw [hy]; exact List.mem_singleton_self _) (hle x hx)
  have htarget := (NativeContext.Iota.OrderInduction.normalSum_words_iff
    (fun x => NativeContext.denote (alphaCode a) (transform a x))
    (thetaAtoms t) (thetaAtoms u) htw huw).mpr hshape
  simpa only [mapped_atoms_value a ha t ht hnt hrt,
    mapped_atoms_value a ha u hu hnu hru] using htarget

/-- Compare the same finite source atom words in the two real contexts.
The caller proves both atom directions by a smaller-size induction. -/
theorem mapped_word_lt_iff (a : Nat) (ha : rootCheck a = true)
    (t u : RelativeTerm Nat) (ht : check 0 t = true)
    (hu : check 0 u = true)
    (hnt : Theta.Normal 0 t) (hnu : Theta.Normal 0 u)
    (hrt : Restricted a t) (hru : Restricted a u)
    (htw : IsAdditiveNormalForm ((thetaAtoms t).map
      (fun x => NativeContext.denote (alphaCode a) (transform a x))))
    (huw : IsAdditiveNormalForm ((thetaAtoms u).map
      (fun x => NativeContext.denote (alphaCode a) (transform a x))))
    (hc : ∀ x ∈ thetaAtoms t, ∀ y ∈ thetaAtoms u,
      (NativeContext.denote (alphaCode a) (transform a x) < NativeContext.denote (alphaCode a) (transform a y) ↔
        denote 0 x < denote 0 y) ∧
      (NativeContext.denote (alphaCode a) (transform a y) < NativeContext.denote (alphaCode a) (transform a x) ↔
        denote 0 y < denote 0 x)) :
    NativeContext.denote (alphaCode a) (transform a t) < NativeContext.denote (alphaCode a) (transform a u) ↔
      denote 0 t < denote 0 u := by
  have hsource : ∀ x ∈ thetaAtoms t, ∀ y ∈ thetaAtoms u,
      (Theta.less 0 x y = true ↔ denote 0 x < denote 0 y) ∧
      (Theta.less 0 y x = true ↔ denote 0 y < denote 0 x) := by
    intro x hx y hy
    have hxc := atoms_checked_normal t x ht hnt hx
    have hyc := atoms_checked_normal u y hu hnu hy
    exact ⟨Theta.less_correct _ x y hxc.1 hyc.1 hxc.2 hyc.2,
      Theta.less_correct _ y x hyc.1 hxc.1 hyc.2 hxc.2⟩
  have htarget : ∀ x ∈ thetaAtoms t, ∀ y ∈ thetaAtoms u,
      (Theta.less 0 x y = true ↔
        NativeContext.denote (alphaCode a) (transform a x) < NativeContext.denote (alphaCode a) (transform a y)) ∧
      (Theta.less 0 y x = true ↔
        NativeContext.denote (alphaCode a) (transform a y) < NativeContext.denote (alphaCode a) (transform a x)) := by
    intro x hx y hy
    exact ⟨(hsource x hx y hy).1.trans (hc x hx y hy).1.symm,
      (hsource x hx y hy).2.trans (hc x hx y hy).2.symm⟩
  have hs := Theta.lexLT_correct (Theta.less 0) (denote 0)
    (thetaAtoms t) (thetaAtoms u) (source_atoms_normal t ht hnt)
    (source_atoms_normal u hu hnu) hsource
  have hv := Theta.lexLT_correct (Theta.less 0)
    (fun x => NativeContext.denote (alphaCode a) (transform a x))
    (thetaAtoms t) (thetaAtoms u) htw huw htarget
  rw [source_atoms_value t ht hnt, source_atoms_value u hu hnu] at hs
  rw [mapped_atoms_value a ha t ht hnt hrt, mapped_atoms_value a ha u hu hnu hru] at hv
  exact hv.symm.trans hs

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.OrderSupport
