import Alexander313.Wilken.HereditaryNativeBoundedContextIota
import Alexander313.Wilken.HereditaryNativeIotaOrderInductionSupport

/-!
# Real intermediate-context principal words and recursive comparison callers

The source base is the computed outer alpha, and the new root/public beta
are computed by the genuine bounded SAME-value return. Actual source/target
admission, full original restriction and the true epsilon cutoff derive the
shifted exposed lists, low values and every smaller atom/query domain.
Only existing GENERIC checker, principal-word and exposed-comparison facts
are reused. No target Normality, full order or collapse equation is assumed.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.BoundedContextIota.OrderSupport

open Iota (exposedThetaList_low)
open Iota.OrderInduction (atoms_checked_normal atoms_sum_size_lt exposed_checked_normal
  source_atoms_anf source_atoms_normal source_atoms_value checked_theta_pos_principal
  normalSum_words_iff checked_theta_lt_iff_exposed)

theorem root_additive (s a root : Nat) (ha : rootCheck s a root = true) :
    Ordinal.IsPrincipal (· + ·) (interpretation (sourceCode s a) root) := by
  rw [← beta_base s a root ha]
  exact BaseTransformation.base_additive _ (betaCode_baseCheck s a root ha)

theorem root_below_first_cardinal (s a root : Nat) (ha : rootCheck s a root = true) :
    interpretation (sourceCode s a) root < omegaSequence (base (sourceCode s a)) 1 := by
  obtain ⟨_, ⟨t, rfl, ht, hn, hs⟩, _⟩ := (rootCheck_exact s a root).mp ha
  rw [interpretation_code]
  exact (denote_lt_iff_outerSort_le _ (.theta 0 t) ht 1 (by omega)).mpr le_rfl

theorem restricted_low_below (s a root : Nat) (ha : rootCheck s a root = true)
    (t : RelativeTerm Nat) (ht : check (sourceCode s a) t = true)
    (hr : Restricted s a root t) (hl : t.outerSort ≤ 1) :
    denote (sourceCode s a) t < interpretation (sourceCode s a) root := by
  revert ht hr hl
  induction t with
  | parameter p =>
    intro ht hr hl
    have hp := checked_parameters _ (.parameter p) ht p (by simp [RelativeTerm.parameters])
    exact hp.2.trans_le (root_base_le s a root ha)
  | sum t u iht ihu =>
    intro ht hr hl
    have hc := BaseTransformation.sum_checks _ t u ht
    have hs := (restricted_sum s a root t u).mp hr
    have hlt : t.outerSort ≤ 1 := (le_max_left _ _).trans hl
    have hlu : u.outerSort ≤ 1 := (le_max_right _ _).trans hl
    exact root_additive s a root ha (iht hc.1 hs.1 hlt) (ihu hc.2 hs.2 hlu)
  | theta k t ih =>
    intro ht hr hl
    have hk : k = 0 := by simp only [outerSort] at hl; omega
    subst k
    exact ((restricted_theta_zero s a root t).mp hr).1

theorem restricted_below_iff_outerSort (s a root : Nat) (ha : rootCheck s a root = true)
    (t : RelativeTerm Nat) (ht : check (sourceCode s a) t = true)
    (hr : Restricted s a root t) :
    denote (sourceCode s a) t < interpretation (sourceCode s a) root ↔ t.outerSort ≤ 1 := by
  constructor
  · intro hs
    exact (denote_lt_iff_outerSort_le _ t ht 1 (by omega)).mp
      (hs.trans (root_below_first_cardinal s a root ha))
  · exact restricted_low_below s a root ha t ht hr

theorem small_iff_outerSort (s a root : Nat) (ha : rootCheck s a root = true)
    (t : RelativeTerm Nat) (ht : check (sourceCode s a) t = true)
    (hr : Restricted s a root t) : small s a root t = true ↔ t.outerSort ≤ 1 :=
  (small_exact s a root ha t ht).trans (restricted_below_iff_outerSort s a root ha t ht hr)

theorem transform_low (s a root : Nat) (ha : rootCheck s a root = true)
    (t : RelativeTerm Nat) (ht : check (sourceCode s a) t = true)
    (hr : Restricted s a root t) (hl : t.outerSort ≤ 1) :
    transform s a root t = .parameter (parameterCode s a t) :=
  transform_below s a root ha t ht (restricted_low_below s a root ha t ht hr hl)

theorem transform_low_value (s a root : Nat) (ha : rootCheck s a root = true)
    (t : RelativeTerm Nat) (ht : check (sourceCode s a) t = true)
    (hr : Restricted s a root t) (hl : t.outerSort ≤ 1) :
    denote (betaCode s a root) (transform s a root t) = denote (sourceCode s a) t :=
  (transform_parameter_value s a root ha t ht (restricted_low_below s a root ha t ht hr hl)).2

theorem transform_low_normal (s a root : Nat) (ha : rootCheck s a root = true)
    (t : RelativeTerm Nat) (ht : check (sourceCode s a) t = true)
    (hr : Restricted s a root t) (hl : t.outerSort ≤ 1) :
    Comparison.Normal (betaCode s a root) (transform s a root t) := by
  rw [transform_low s a root ha t ht hr hl]
  trivial

theorem transform_theta_succ (s a root k : Nat) (ha : rootCheck s a root = true)
    (t : RelativeTerm Nat) (ht : check (sourceCode s a) (.theta (k + 1) t) = true)
    (hr : Restricted s a root (.theta (k + 1) t)) :
    transform s a root (.theta (k + 1) t) = .theta k (transform s a root t) := by
  have hf : small s a root (.theta (k + 1) t) = false := by
    cases h : small s a root (.theta (k + 1) t) with
    | false => rfl
    | true =>
      have hs := (small_iff_outerSort s a root ha _ ht hr).mp h
      simp only [outerSort] at hs
      omega
  simp only [transform, hf, Bool.cond_false, Nat.add_sub_cancel]

theorem transform_exposedThetaList (s a root m : Nat) (ha : rootCheck s a root = true)
    (t : RelativeTerm Nat) (ht : check (sourceCode s a) t = true)
    (hr : Restricted s a root t) :
    exposedThetaList m (transform s a root t) =
      (exposedThetaList (m + 1) t).map (transform s a root) := by
  revert ht hr
  induction t with
  | parameter p => intro ht hr; rfl
  | sum t u iht ihu =>
    intro ht hr
    have hc := BaseTransformation.sum_checks _ t u ht
    have hs := (restricted_sum s a root t u).mp hr
    cases h : small s a root (.sum t u) with
    | true =>
      have hl := (small_iff_outerSort s a root ha _ ht hr).mp h
      rw [exposedThetaList_low (m + 1) (by omega) (.sum t u) hl]
      simp only [transform, h, Bool.cond_true, exposedThetaList, List.map_nil]
    | false =>
      simp only [transform, h, Bool.cond_false, exposedThetaList, List.map_append,
        iht hc.1 hs.1, ihu hc.2 hs.2]
  | theta k t ih =>
    intro ht hr
    cases k with
    | zero =>
      rw [transform_low s a root ha (.theta 0 t) ht hr le_rfl,
        exposedThetaList_low (m + 1) (by omega) (.theta 0 t) le_rfl]
      rfl
    | succ k =>
      have hc := BaseTransformation.theta_argument_check _ (k + 1) t ht
      have hs := (restricted_theta_succ s a root k t).mp hr
      rw [transform_theta_succ s a root k ha t ht hr]
      by_cases he : k = m
      · subst k
        simp only [exposedThetaList, if_pos rfl, List.map_cons, List.map_nil,
          transform_theta_succ s a root m ha t ht hr]
      · have he' : k + 1 ≠ m + 1 := by omega
        by_cases hm : m < k
        · have hm' : m + 1 < k + 1 := by omega
          simp only [exposedThetaList, if_neg he, if_neg he', if_pos hm, if_pos hm', ih hc hs]
        · have hm' : ¬m + 1 < k + 1 := by omega
          simp only [exposedThetaList, if_neg he, if_neg he', if_neg hm, if_neg hm', List.map_nil]

theorem transform_ge_base (s a root : Nat) (ha : rootCheck s a root = true)
    (t : RelativeTerm Nat) (ht : check (sourceCode s a) t = true)
    (hr : Restricted s a root t)
    (hs : interpretation (sourceCode s a) root ≤ denote (sourceCode s a) t) :
    base (betaCode s a root) ≤ denote (betaCode s a root) (transform s a root t) := by
  revert ht hr hs
  induction t with
  | parameter p =>
    intro ht hr hs
    have hlow := restricted_low_below s a root ha (.parameter p) ht hr (by exact Nat.zero_le _)
    exact False.elim (hlow.not_ge hs)
  | sum t u iht ihu =>
    intro ht hr hs
    have hc := BaseTransformation.sum_checks _ t u ht
    have hr' := (restricted_sum s a root t u).mp hr
    have hf : small s a root (.sum t u) = false := by
      cases h : small s a root (.sum t u) with
      | false => rfl
      | true => exact False.elim (((small_exact s a root ha _ ht).mp h).not_ge hs)
    simp only [transform, hf, Bool.cond_false]
    change base (betaCode s a root) ≤
      denote (betaCode s a root) (transform s a root t) + denote (betaCode s a root) (transform s a root u)
    by_cases ht' : interpretation (sourceCode s a) root ≤ denote (sourceCode s a) t
    · exact (iht hc.1 hr'.1 ht').trans le_self_add
    · have hu' : interpretation (sourceCode s a) root ≤ denote (sourceCode s a) u := by
        by_contra hu'
        exact (root_additive s a root ha (lt_of_not_ge ht') (lt_of_not_ge hu')).not_ge hs
      exact (ihu hc.2 hr'.2 hu').trans le_add_self
  | theta k t ih =>
    intro ht hr hs
    cases k with
    | zero => exact False.elim (((restricted_theta_zero s a root t).mp hr).1.not_ge hs)
    | succ k =>
      have hct := transform_checked s a root ha (.theta (k + 1) t) ht hr
      rw [transform_theta_succ s a root k ha t ht hr] at hct ⊢
      exact BaseTransformation.theta_base_le _ k _ hct

theorem transform_below_base_iff (s a root : Nat) (ha : rootCheck s a root = true)
    (t : RelativeTerm Nat) (ht : check (sourceCode s a) t = true)
    (hr : Restricted s a root t) :
    denote (betaCode s a root) (transform s a root t) < base (betaCode s a root) ↔
      denote (sourceCode s a) t < interpretation (sourceCode s a) root := by
  constructor
  · intro h
    by_contra hs
    exact h.not_ge (transform_ge_base s a root ha t ht hr (le_of_not_gt hs))
  · intro h
    rw [(transform_parameter_value s a root ha t ht h).2, beta_base s a root ha]
    exact h

theorem transform_add (s a root : Nat) (ha : rootCheck s a root = true)
    (t u : RelativeTerm Nat) (ht : check (sourceCode s a) t = true)
    (hu : check (sourceCode s a) u = true) :
    denote (betaCode s a root) (transform s a root (.sum t u)) =
      denote (betaCode s a root) (transform s a root t) + denote (betaCode s a root) (transform s a root u) := by
  have hc : check (sourceCode s a) (.sum t u) = true := by
    apply (check_exact _ _).mpr
    let n := max (SourceOne.PublicCodes.fragment t) (SourceOne.PublicCodes.fragment u)
    have htn := Comparison.checked_admissible _ n t ht
      ((SourceOne.PublicCodes.height_le_fragment t).trans (le_max_left _ _))
    have hun := Comparison.checked_admissible _ n u hu
      ((SourceOne.PublicCodes.height_le_fragment u).trans (le_max_right _ _))
    exact ⟨sourceCode_checked s a root ha, n, ⟨⟨htn.1, hun.1⟩, .sum htn.2 hun.2⟩⟩
  cases h : small s a root (.sum t u) with
  | false => simp only [transform, h, Bool.cond_false]; rfl
  | true =>
    have hs := (small_exact s a root ha (.sum t u) hc).mp h
    have hst : denote (sourceCode s a) t < interpretation (sourceCode s a) root :=
      le_self_add.trans_lt hs
    have hsu : denote (sourceCode s a) u < interpretation (sourceCode s a) root :=
      le_add_self.trans_lt hs
    rw [(transform_parameter_value s a root ha (.sum t u) hc hs).2,
      (transform_parameter_value s a root ha t ht hst).2,
      (transform_parameter_value s a root ha u hu hsu).2]
    rfl

theorem transform_low_lt_iff (s a root : Nat) (ha : rootCheck s a root = true)
    (t u : RelativeTerm Nat) (ht : check (sourceCode s a) t = true)
    (hu : check (sourceCode s a) u = true) (hrt : Restricted s a root t)
    (hru : Restricted s a root u) (hlt : t.outerSort ≤ 1) (hlu : u.outerSort ≤ 1) :
    denote (betaCode s a root) (transform s a root t) < denote (betaCode s a root) (transform s a root u) ↔
      denote (sourceCode s a) t < denote (sourceCode s a) u := by
  rw [transform_low_value s a root ha t ht hrt hlt, transform_low_value s a root ha u hu hru hlu]

theorem transform_low_high_lt (s a root : Nat) (ha : rootCheck s a root = true)
    (t u : RelativeTerm Nat) (ht : check (sourceCode s a) t = true)
    (hu : check (sourceCode s a) u = true) (hrt : Restricted s a root t)
    (hru : Restricted s a root u) (hlt : t.outerSort ≤ 1) (hhu : 1 < u.outerSort) :
    denote (sourceCode s a) t < denote (sourceCode s a) u ∧
      denote (betaCode s a root) (transform s a root t) < denote (betaCode s a root) (transform s a root u) := by
  have hts := restricted_low_below s a root ha t ht hrt hlt
  have hus : interpretation (sourceCode s a) root ≤ denote (sourceCode s a) u := by
    apply le_of_not_gt
    intro h
    have hl := (restricted_below_iff_outerSort s a root ha u hu hru).mp h
    omega
  exact ⟨hts.trans_le hus, ((transform_below_base_iff s a root ha t ht hrt).mpr hts).trans_le
    (transform_ge_base s a root ha u hu hru hus)⟩

theorem transform_shifted_level_lt (s a root k l : Nat) (ha : rootCheck s a root = true)
    (t u : RelativeTerm Nat) (ht : check (sourceCode s a) (.theta (k + 1) t) = true)
    (hu : check (sourceCode s a) (.theta (l + 1) u) = true)
    (hrt : Restricted s a root (.theta (k + 1) t))
    (hru : Restricted s a root (.theta (l + 1) u)) (hkl : k < l) :
    denote (sourceCode s a) (.theta (k + 1) t) < denote (sourceCode s a) (.theta (l + 1) u) ∧
      denote (betaCode s a root) (transform s a root (.theta (k + 1) t)) <
        denote (betaCode s a root) (transform s a root (.theta (l + 1) u)) := by
  have source_lt (q i j : Nat) (x y : RelativeTerm Nat)
      (hx : check q (.theta i x) = true) (hy : check q (.theta j y) = true)
      (hij : i < j) : denote q (.theta i x) < denote q (.theta j y) := by
    let n := max (SourceOne.PublicCodes.fragment (.theta i x))
      (SourceOne.PublicCodes.fragment (.theta j y))
    have hxn := Comparison.checked_admissible q n (.theta i x) hx
      ((SourceOne.PublicCodes.height_le_fragment _).trans (le_max_left _ _))
    have hyn := Comparison.checked_admissible q n (.theta j y) hy
      ((SourceOne.PublicCodes.height_le_fragment _).trans (le_max_right _ _))
    rw [denote_eq_finite q n (Bool.and_eq_true.mp hx).1 _ hxn.2,
      denote_eq_finite q n (Bool.and_eq_true.mp hx).1 _ hyn.2]
    exact Comparison.theta_lt_of_level_lt q n i j x y hxn hyn hij
  have hct := transform_checked s a root ha (.theta (k + 1) t) ht hrt
  have hcu := transform_checked s a root ha (.theta (l + 1) u) hu hru
  rw [transform_theta_succ s a root k ha t ht hrt] at hct
  rw [transform_theta_succ s a root l ha u hu hru] at hcu
  refine ⟨source_lt _ (k + 1) (l + 1) t u ht hu (by omega), ?_⟩
  rw [transform_theta_succ s a root k ha t ht hrt, transform_theta_succ s a root l ha u hu hru]
  exact source_lt _ k l _ _ hct hcu hkl

theorem restricted_argument (s a root k : Nat) (t : RelativeTerm Nat)
    (hr : Restricted s a root (.theta k t)) : Restricted s a root t := by
  cases k with
  | zero => exact ((restricted_theta_zero s a root t).mp hr).2
  | succ k => exact (restricted_theta_succ s a root k t).mp hr

theorem restricted_atoms (s a root : Nat) (t x : RelativeTerm Nat)
    (hr : Restricted s a root t) (hx : x ∈ Comparison.atoms t) : Restricted s a root x := by
  revert hr hx
  induction t with
  | parameter p =>
    intro hr hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    simp only [Restricted, fullList, RelativeTerm.PrincipalSupport.principalList,
      List.not_mem_nil, false_implies, implies_true, forall_const]
  | sum t u iht ihu =>
    intro hr hx
    have hs := (restricted_sum s a root t u).mp hr
    rcases List.mem_append.mp hx with hx | hx
    · exact iht hs.1 hx
    · exact ihu hs.2 hx
  | theta k t ih =>
    intro hr hx
    have he : x = .theta k t := List.mem_singleton.mp hx
    subst x
    exact hr

theorem restricted_exposed (s a root m : Nat) (t x : RelativeTerm Nat)
    (hr : Restricted s a root t) (hx : x ∈ exposedThetaList m t) : Restricted s a root x := by
  revert hr hx
  induction t with
  | parameter p => intro hr hx; simp only [exposedThetaList, List.not_mem_nil] at hx
  | sum t u iht ihu =>
    intro hr hx
    have hs := (restricted_sum s a root t u).mp hr
    rcases List.mem_append.mp hx with hx | hx
    · exact iht hs.1 hx
    · exact ihu hs.2 hx
  | theta k t ih =>
    intro hr hx
    by_cases he : k = m
    · have hx' : x = .theta k t := by
        simpa only [exposedThetaList, if_pos he, List.mem_singleton] using hx
      subst x
      exact hr
    · by_cases hm : m < k
      · exact ih (restricted_argument s a root k t hr)
          (by simpa only [exposedThetaList, if_neg he, if_pos hm] using hx)
      · simp only [exposedThetaList, if_neg he, if_neg hm, List.not_mem_nil] at hx

theorem mapped_atoms_low (s a root : Nat) (ha : rootCheck s a root = true)
    (t : RelativeTerm Nat) (ht : check (sourceCode s a) t = true)
    (hn : Comparison.Normal (sourceCode s a) t) (hr : Restricted s a root t)
    (hl : t.outerSort ≤ 1) :
    (Comparison.atoms t).map (fun x => denote (betaCode s a root) (transform s a root x)) =
      (Comparison.atoms t).map (denote (sourceCode s a)) := by
  apply List.map_congr_left
  intro x hx
  have hxc := (atoms_checked_normal _ t x ht hn hx).1
  have hval : denote (sourceCode s a) x ≤ denote (sourceCode s a) t := by
    apply canonicalANF_mem_le
    rw [← source_atoms_anf _ t ht hn]
    exact List.mem_map.mpr ⟨x, hx, rfl⟩
  exact (transform_parameter_value s a root ha x hxc
    (hval.trans_lt (restricted_low_below s a root ha t ht hr hl))).2

theorem mapped_atoms_value (s a root : Nat) (ha : rootCheck s a root = true)
    (t : RelativeTerm Nat) (ht : check (sourceCode s a) t = true)
    (hn : Comparison.Normal (sourceCode s a) t) (hr : Restricted s a root t) :
    principalSum ((Comparison.atoms t).map
      (fun x => denote (betaCode s a root) (transform s a root x))) =
      denote (betaCode s a root) (transform s a root t) := by
  revert ht hn hr
  induction t with
  | parameter p =>
    intro ht hn hr
    rw [mapped_atoms_low s a root ha (.parameter p) ht hn hr (Nat.zero_le _),
      source_atoms_value _ (.parameter p) ht hn,
      transform_low_value s a root ha (.parameter p) ht hr (Nat.zero_le _)]
  | sum t u iht ihu =>
    intro ht hn hr
    have hc := BaseTransformation.sum_checks _ t u ht
    have hs := (restricted_sum s a root t u).mp hr
    rw [Comparison.atoms, List.map_append, principalSum_append,
      iht hc.1 hn.1 hs.1, ihu hc.2 hn.2.1 hs.2, transform_add s a root ha t u hc.1 hc.2]
  | theta k t ih =>
    intro ht hn hr
    simp only [Comparison.atoms, List.map_cons, List.map_nil, principalSum, add_zero]

theorem mapped_normalSum (s a root : Nat) (ha : rootCheck s a root = true)
    (t u : RelativeTerm Nat) (ht : check (sourceCode s a) t = true)
    (hu : check (sourceCode s a) u = true)
    (hnt : Comparison.Normal (sourceCode s a) t) (hnu : Comparison.Normal (sourceCode s a) u)
    (hrt : Restricted s a root t) (hru : Restricted s a root u)
    (hs : SourceNormalSum (denote (sourceCode s a) t + denote (sourceCode s a) u)
      (denote (sourceCode s a) t) (denote (sourceCode s a) u))
    (htw : IsAdditiveNormalForm ((Comparison.atoms t).map
      (fun x => denote (betaCode s a root) (transform s a root x))))
    (huw : IsAdditiveNormalForm ((Comparison.atoms u).map
      (fun x => denote (betaCode s a root) (transform s a root x))))
    (hcross : ∀ x ∈ Comparison.atoms t, ∀ y ∈ Comparison.atoms u,
      denote (sourceCode s a) y ≤ denote (sourceCode s a) x →
      denote (betaCode s a root) (transform s a root y) ≤ denote (betaCode s a root) (transform s a root x)) :
    SourceNormalSum
      (denote (betaCode s a root) (transform s a root t) + denote (betaCode s a root) (transform s a root u))
      (denote (betaCode s a root) (transform s a root t))
      (denote (betaCode s a root) (transform s a root u)) := by
  have hsource := (normalSum_words_iff (denote (sourceCode s a))
    (Comparison.atoms t) (Comparison.atoms u) (source_atoms_normal _ t ht hnt)
    (source_atoms_normal _ u hu hnu)).mp (by
      simpa only [source_atoms_value _ t ht hnt, source_atoms_value _ u hu hnu] using hs)
  have hshape : (Comparison.atoms t = [] ∧ Comparison.atoms u = []) ∨
      ∃ y, Comparison.atoms u = [y] ∧ ∀ x ∈ Comparison.atoms t,
        denote (betaCode s a root) (transform s a root y) ≤ denote (betaCode s a root) (transform s a root x) := by
    rcases hsource with hz | ⟨y, hy, hle⟩
    · exact Or.inl hz
    · refine Or.inr ⟨y, hy, ?_⟩
      intro x hx
      exact hcross x hx y (by rw [hy]; exact List.mem_singleton_self _) (hle x hx)
  have htarget := (normalSum_words_iff
    (fun x => denote (betaCode s a root) (transform s a root x))
    (Comparison.atoms t) (Comparison.atoms u) htw huw).mpr hshape
  simpa only [mapped_atoms_value s a root ha t ht hnt hrt,
    mapped_atoms_value s a root ha u hu hnu hru] using htarget

theorem mapped_word_lt_iff (s a root : Nat) (ha : rootCheck s a root = true)
    (t u : RelativeTerm Nat) (ht : check (sourceCode s a) t = true)
    (hu : check (sourceCode s a) u = true)
    (hnt : Comparison.Normal (sourceCode s a) t) (hnu : Comparison.Normal (sourceCode s a) u)
    (hrt : Restricted s a root t) (hru : Restricted s a root u)
    (htw : IsAdditiveNormalForm ((Comparison.atoms t).map
      (fun x => denote (betaCode s a root) (transform s a root x))))
    (huw : IsAdditiveNormalForm ((Comparison.atoms u).map
      (fun x => denote (betaCode s a root) (transform s a root x))))
    (hc : ∀ x ∈ Comparison.atoms t, ∀ y ∈ Comparison.atoms u,
      (denote (betaCode s a root) (transform s a root x) < denote (betaCode s a root) (transform s a root y) ↔
        denote (sourceCode s a) x < denote (sourceCode s a) y) ∧
      (denote (betaCode s a root) (transform s a root y) < denote (betaCode s a root) (transform s a root x) ↔
        denote (sourceCode s a) y < denote (sourceCode s a) x)) :
    denote (betaCode s a root) (transform s a root t) < denote (betaCode s a root) (transform s a root u) ↔
      denote (sourceCode s a) t < denote (sourceCode s a) u := by
  have hsource : ∀ x ∈ Comparison.atoms t, ∀ y ∈ Comparison.atoms u,
      (Comparison.less (sourceCode s a) x y = true ↔ denote (sourceCode s a) x < denote (sourceCode s a) y) ∧
      (Comparison.less (sourceCode s a) y x = true ↔ denote (sourceCode s a) y < denote (sourceCode s a) x) := by
    intro x hx y hy
    have hxc := atoms_checked_normal _ t x ht hnt hx
    have hyc := atoms_checked_normal _ u y hu hnu hy
    exact ⟨Comparison.less_correct _ x y hxc.1 hyc.1 hxc.2 hyc.2,
      Comparison.less_correct _ y x hyc.1 hxc.1 hyc.2 hxc.2⟩
  have htarget : ∀ x ∈ Comparison.atoms t, ∀ y ∈ Comparison.atoms u,
      (Comparison.less (sourceCode s a) x y = true ↔
        denote (betaCode s a root) (transform s a root x) < denote (betaCode s a root) (transform s a root y)) ∧
      (Comparison.less (sourceCode s a) y x = true ↔
        denote (betaCode s a root) (transform s a root y) < denote (betaCode s a root) (transform s a root x)) := by
    intro x hx y hy
    exact ⟨(hsource x hx y hy).1.trans (hc x hx y hy).1.symm,
      (hsource x hx y hy).2.trans (hc x hx y hy).2.symm⟩
  have hs := Theta.lexLT_correct (Comparison.less (sourceCode s a)) (denote (sourceCode s a))
    (Comparison.atoms t) (Comparison.atoms u) (source_atoms_normal _ t ht hnt)
    (source_atoms_normal _ u hu hnu) hsource
  have hv := Theta.lexLT_correct (Comparison.less (sourceCode s a))
    (fun x => denote (betaCode s a root) (transform s a root x))
    (Comparison.atoms t) (Comparison.atoms u) htw huw htarget
  rw [source_atoms_value _ t ht hnt, source_atoms_value _ u hu hnu] at hs
  rw [mapped_atoms_value s a root ha t ht hnt hrt, mapped_atoms_value s a root ha u hu hnu hru] at hv
  exact hv.symm.trans hs

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.BoundedContextIota.OrderSupport
