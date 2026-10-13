import Alexander313.Wilken.PublicEpsilonNativeIota
import Alexander313.Wilken.HereditaryNativeIotaOrderInductionSupport

/-!
# Genuine principal words and recursive comparison callers at every public epsilon

The source is the LITERAL original canonical epsilon q, including proper
source-one references. The actual uniform finite return computes beta and
all stopped LOW parameters below the genuinely selected original endpoint.
Source admission and complete original restriction derive exposed-list
shifts and every atom/query caller. Only actual GENERIC native comparison
and principal-word APIs are used; no fixed-source iota instance or target
Normal/order/collapse oracle is assumed. Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonIota.OrderSupport

open Iota (exposedThetaList_low)
open Iota.OrderInduction (atoms_checked_normal atoms_sum_size_lt exposed_checked_normal
  source_atoms_anf source_atoms_normal source_atoms_value checked_theta_pos_principal
  normalSum_words_iff checked_theta_lt_iff_exposed)

theorem root_additive (q root : Nat) (ha : rootCheck q root = true) :
    Ordinal.IsPrincipal (· + ·) (interpretation (q) root) := by
  rw [← beta_base q root ha]
  exact BaseTransformation.base_additive _ (betaCode_baseCheck q root ha)

theorem root_below_first_cardinal (q root : Nat) (ha : rootCheck q root = true) :
    interpretation (q) root < omegaSequence (base (q)) 1 := by
  obtain ⟨_, ⟨t, rfl, ht, hn, hs⟩, _⟩ := (rootCheck_exact q root).mp ha
  rw [interpretation_code]
  exact (denote_lt_iff_outerSort_le _ (.theta 0 t) ht 1 (by omega)).mpr le_rfl

theorem restricted_low_below (q root : Nat) (ha : rootCheck q root = true)
    (t : RelativeTerm Nat) (ht : check (q) t = true)
    (hr : Restricted q root t) (hl : t.outerSort ≤ 1) :
    denote (q) t < interpretation (q) root := by
  revert ht hr hl
  induction t with
  | parameter p =>
    intro ht hr hl
    have hp := checked_parameters _ (.parameter p) ht p (by simp [RelativeTerm.parameters])
    exact hp.2.trans_le (root_base_le q root ha)
  | sum t u iht ihu =>
    intro ht hr hl
    have hc := BaseTransformation.sum_checks _ t u ht
    have hs := (restricted_sum q root t u).mp hr
    have hlt : t.outerSort ≤ 1 := (le_max_left _ _).trans hl
    have hlu : u.outerSort ≤ 1 := (le_max_right _ _).trans hl
    exact root_additive q root ha (iht hc.1 hs.1 hlt) (ihu hc.2 hs.2 hlu)
  | theta k t ih =>
    intro ht hr hl
    have hk : k = 0 := by simp only [outerSort] at hl; omega
    subst k
    exact ((restricted_theta_zero q root t).mp hr).1

theorem restricted_below_iff_outerSort (q root : Nat) (ha : rootCheck q root = true)
    (t : RelativeTerm Nat) (ht : check (q) t = true)
    (hr : Restricted q root t) :
    denote (q) t < interpretation (q) root ↔ t.outerSort ≤ 1 := by
  constructor
  · intro hs
    exact (denote_lt_iff_outerSort_le _ t ht 1 (by omega)).mp
      (hs.trans (root_below_first_cardinal q root ha))
  · exact restricted_low_below q root ha t ht hr

theorem small_iff_outerSort (q root : Nat) (ha : rootCheck q root = true)
    (t : RelativeTerm Nat) (ht : check (q) t = true)
    (hr : Restricted q root t) : small q root t = true ↔ t.outerSort ≤ 1 :=
  (small_exact q root ha t ht).trans (restricted_below_iff_outerSort q root ha t ht hr)

theorem transform_low (q root : Nat) (ha : rootCheck q root = true)
    (t : RelativeTerm Nat) (ht : check (q) t = true)
    (hr : Restricted q root t) (hl : t.outerSort ≤ 1) :
    transform q root t = .parameter (parameterCode q t) :=
  transform_below q root ha t ht (restricted_low_below q root ha t ht hr hl)

theorem transform_low_value (q root : Nat) (ha : rootCheck q root = true)
    (t : RelativeTerm Nat) (ht : check (q) t = true)
    (hr : Restricted q root t) (hl : t.outerSort ≤ 1) :
    denote (betaCode q root) (transform q root t) = denote (q) t :=
  (transform_parameter_value q root ha t ht (restricted_low_below q root ha t ht hr hl)).2

theorem transform_low_normal (q root : Nat) (ha : rootCheck q root = true)
    (t : RelativeTerm Nat) (ht : check (q) t = true)
    (hr : Restricted q root t) (hl : t.outerSort ≤ 1) :
    Comparison.Normal (betaCode q root) (transform q root t) := by
  rw [transform_low q root ha t ht hr hl]
  trivial

theorem transform_theta_succ (q root k : Nat) (ha : rootCheck q root = true)
    (t : RelativeTerm Nat) (ht : check (q) (.theta (k + 1) t) = true)
    (hr : Restricted q root (.theta (k + 1) t)) :
    transform q root (.theta (k + 1) t) = .theta k (transform q root t) := by
  have hf : small q root (.theta (k + 1) t) = false := by
    cases h : small q root (.theta (k + 1) t) with
    | false => rfl
    | true =>
      have hs := (small_iff_outerSort q root ha _ ht hr).mp h
      simp only [outerSort] at hs
      omega
  simp only [transform, hf, Bool.cond_false, Nat.add_sub_cancel]

theorem transform_exposedThetaList (q root m : Nat) (ha : rootCheck q root = true)
    (t : RelativeTerm Nat) (ht : check (q) t = true)
    (hr : Restricted q root t) :
    exposedThetaList m (transform q root t) =
      (exposedThetaList (m + 1) t).map (transform q root) := by
  revert ht hr
  induction t with
  | parameter p => intro ht hr; rfl
  | sum t u iht ihu =>
    intro ht hr
    have hc := BaseTransformation.sum_checks _ t u ht
    have hs := (restricted_sum q root t u).mp hr
    cases h : small q root (.sum t u) with
    | true =>
      have hl := (small_iff_outerSort q root ha _ ht hr).mp h
      rw [exposedThetaList_low (m + 1) (by omega) (.sum t u) hl]
      simp only [transform, h, Bool.cond_true, exposedThetaList, List.map_nil]
    | false =>
      simp only [transform, h, Bool.cond_false, exposedThetaList, List.map_append,
        iht hc.1 hs.1, ihu hc.2 hs.2]
  | theta k t ih =>
    intro ht hr
    cases k with
    | zero =>
      rw [transform_low q root ha (.theta 0 t) ht hr le_rfl,
        exposedThetaList_low (m + 1) (by omega) (.theta 0 t) le_rfl]
      rfl
    | succ k =>
      have hc := BaseTransformation.theta_argument_check _ (k + 1) t ht
      have hs := (restricted_theta_succ q root k t).mp hr
      rw [transform_theta_succ q root k ha t ht hr]
      by_cases he : k = m
      · subst k
        simp only [exposedThetaList, if_pos rfl, List.map_cons, List.map_nil,
          transform_theta_succ q root m ha t ht hr]
      · have he' : k + 1 ≠ m + 1 := by omega
        by_cases hm : m < k
        · have hm' : m + 1 < k + 1 := by omega
          simp only [exposedThetaList, if_neg he, if_neg he', if_pos hm, if_pos hm', ih hc hs]
        · have hm' : ¬m + 1 < k + 1 := by omega
          simp only [exposedThetaList, if_neg he, if_neg he', if_neg hm, if_neg hm', List.map_nil]

theorem transform_ge_base (q root : Nat) (ha : rootCheck q root = true)
    (t : RelativeTerm Nat) (ht : check (q) t = true)
    (hr : Restricted q root t)
    (hs : interpretation (q) root ≤ denote (q) t) :
    base (betaCode q root) ≤ denote (betaCode q root) (transform q root t) := by
  revert ht hr hs
  induction t with
  | parameter p =>
    intro ht hr hs
    have hlow := restricted_low_below q root ha (.parameter p) ht hr (by exact Nat.zero_le _)
    exact False.elim (hlow.not_ge hs)
  | sum t u iht ihu =>
    intro ht hr hs
    have hc := BaseTransformation.sum_checks _ t u ht
    have hr' := (restricted_sum q root t u).mp hr
    have hf : small q root (.sum t u) = false := by
      cases h : small q root (.sum t u) with
      | false => rfl
      | true => exact False.elim (((small_exact q root ha _ ht).mp h).not_ge hs)
    simp only [transform, hf, Bool.cond_false]
    change base (betaCode q root) ≤
      denote (betaCode q root) (transform q root t) + denote (betaCode q root) (transform q root u)
    by_cases ht' : interpretation (q) root ≤ denote (q) t
    · exact (iht hc.1 hr'.1 ht').trans le_self_add
    · have hu' : interpretation (q) root ≤ denote (q) u := by
        by_contra hu'
        exact (root_additive q root ha (lt_of_not_ge ht') (lt_of_not_ge hu')).not_ge hs
      exact (ihu hc.2 hr'.2 hu').trans le_add_self
  | theta k t ih =>
    intro ht hr hs
    cases k with
    | zero => exact False.elim (((restricted_theta_zero q root t).mp hr).1.not_ge hs)
    | succ k =>
      have hct := transform_checked q root ha (.theta (k + 1) t) ht hr
      rw [transform_theta_succ q root k ha t ht hr] at hct ⊢
      exact BaseTransformation.theta_base_le _ k _ hct

theorem transform_below_base_iff (q root : Nat) (ha : rootCheck q root = true)
    (t : RelativeTerm Nat) (ht : check (q) t = true)
    (hr : Restricted q root t) :
    denote (betaCode q root) (transform q root t) < base (betaCode q root) ↔
      denote (q) t < interpretation (q) root := by
  constructor
  · intro h
    by_contra hs
    exact h.not_ge (transform_ge_base q root ha t ht hr (le_of_not_gt hs))
  · intro h
    rw [(transform_parameter_value q root ha t ht h).2, beta_base q root ha]
    exact h

theorem transform_add (q root : Nat) (ha : rootCheck q root = true)
    (t u : RelativeTerm Nat) (ht : check (q) t = true)
    (hu : check (q) u = true) :
    denote (betaCode q root) (transform q root (.sum t u)) =
      denote (betaCode q root) (transform q root t) + denote (betaCode q root) (transform q root u) := by
  have hc : check (q) (.sum t u) = true := by
    apply (check_exact _ _).mpr
    let n := max (SourceOne.PublicCodes.fragment t) (SourceOne.PublicCodes.fragment u)
    have htn := Comparison.checked_admissible _ n t ht
      ((SourceOne.PublicCodes.height_le_fragment t).trans (le_max_left _ _))
    have hun := Comparison.checked_admissible _ n u hu
      ((SourceOne.PublicCodes.height_le_fragment u).trans (le_max_right _ _))
    exact ⟨source_checked q root ha, n, ⟨⟨htn.1, hun.1⟩, .sum htn.2 hun.2⟩⟩
  cases h : small q root (.sum t u) with
  | false => simp only [transform, h, Bool.cond_false]; rfl
  | true =>
    have hs := (small_exact q root ha (.sum t u) hc).mp h
    have hst : denote (q) t < interpretation (q) root :=
      le_self_add.trans_lt hs
    have hsu : denote (q) u < interpretation (q) root :=
      le_add_self.trans_lt hs
    rw [(transform_parameter_value q root ha (.sum t u) hc hs).2,
      (transform_parameter_value q root ha t ht hst).2,
      (transform_parameter_value q root ha u hu hsu).2]
    rfl

theorem transform_low_lt_iff (q root : Nat) (ha : rootCheck q root = true)
    (t u : RelativeTerm Nat) (ht : check (q) t = true)
    (hu : check (q) u = true) (hrt : Restricted q root t)
    (hru : Restricted q root u) (hlt : t.outerSort ≤ 1) (hlu : u.outerSort ≤ 1) :
    denote (betaCode q root) (transform q root t) < denote (betaCode q root) (transform q root u) ↔
      denote (q) t < denote (q) u := by
  rw [transform_low_value q root ha t ht hrt hlt, transform_low_value q root ha u hu hru hlu]

theorem transform_low_high_lt (q root : Nat) (ha : rootCheck q root = true)
    (t u : RelativeTerm Nat) (ht : check (q) t = true)
    (hu : check (q) u = true) (hrt : Restricted q root t)
    (hru : Restricted q root u) (hlt : t.outerSort ≤ 1) (hhu : 1 < u.outerSort) :
    denote (q) t < denote (q) u ∧
      denote (betaCode q root) (transform q root t) < denote (betaCode q root) (transform q root u) := by
  have hts := restricted_low_below q root ha t ht hrt hlt
  have hus : interpretation (q) root ≤ denote (q) u := by
    apply le_of_not_gt
    intro h
    have hl := (restricted_below_iff_outerSort q root ha u hu hru).mp h
    omega
  exact ⟨hts.trans_le hus, ((transform_below_base_iff q root ha t ht hrt).mpr hts).trans_le
    (transform_ge_base q root ha u hu hru hus)⟩

theorem transform_shifted_level_lt (q root k l : Nat) (ha : rootCheck q root = true)
    (t u : RelativeTerm Nat) (ht : check (q) (.theta (k + 1) t) = true)
    (hu : check (q) (.theta (l + 1) u) = true)
    (hrt : Restricted q root (.theta (k + 1) t))
    (hru : Restricted q root (.theta (l + 1) u)) (hkl : k < l) :
    denote (q) (.theta (k + 1) t) < denote (q) (.theta (l + 1) u) ∧
      denote (betaCode q root) (transform q root (.theta (k + 1) t)) <
        denote (betaCode q root) (transform q root (.theta (l + 1) u)) := by
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
  have hct := transform_checked q root ha (.theta (k + 1) t) ht hrt
  have hcu := transform_checked q root ha (.theta (l + 1) u) hu hru
  rw [transform_theta_succ q root k ha t ht hrt] at hct
  rw [transform_theta_succ q root l ha u hu hru] at hcu
  refine ⟨source_lt _ (k + 1) (l + 1) t u ht hu (by omega), ?_⟩
  rw [transform_theta_succ q root k ha t ht hrt, transform_theta_succ q root l ha u hu hru]
  exact source_lt _ k l _ _ hct hcu hkl

theorem restricted_argument (q root k : Nat) (t : RelativeTerm Nat)
    (hr : Restricted q root (.theta k t)) : Restricted q root t := by
  cases k with
  | zero => exact ((restricted_theta_zero q root t).mp hr).2
  | succ k => exact (restricted_theta_succ q root k t).mp hr

theorem restricted_atoms (q root : Nat) (t x : RelativeTerm Nat)
    (hr : Restricted q root t) (hx : x ∈ Comparison.atoms t) : Restricted q root x := by
  revert hr hx
  induction t with
  | parameter p =>
    intro hr hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    simp only [Restricted, fullList, RelativeTerm.PrincipalSupport.principalList,
      List.not_mem_nil, false_implies, implies_true, forall_const]
  | sum t u iht ihu =>
    intro hr hx
    have hs := (restricted_sum q root t u).mp hr
    rcases List.mem_append.mp hx with hx | hx
    · exact iht hs.1 hx
    · exact ihu hs.2 hx
  | theta k t ih =>
    intro hr hx
    have he : x = .theta k t := List.mem_singleton.mp hx
    subst x
    exact hr

theorem restricted_exposed (q root m : Nat) (t x : RelativeTerm Nat)
    (hr : Restricted q root t) (hx : x ∈ exposedThetaList m t) : Restricted q root x := by
  revert hr hx
  induction t with
  | parameter p => intro hr hx; simp only [exposedThetaList, List.not_mem_nil] at hx
  | sum t u iht ihu =>
    intro hr hx
    have hs := (restricted_sum q root t u).mp hr
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
      · exact ih (restricted_argument q root k t hr)
          (by simpa only [exposedThetaList, if_neg he, if_pos hm] using hx)
      · simp only [exposedThetaList, if_neg he, if_neg hm, List.not_mem_nil] at hx

theorem mapped_atoms_low (q root : Nat) (ha : rootCheck q root = true)
    (t : RelativeTerm Nat) (ht : check (q) t = true)
    (hn : Comparison.Normal (q) t) (hr : Restricted q root t)
    (hl : t.outerSort ≤ 1) :
    (Comparison.atoms t).map (fun x => denote (betaCode q root) (transform q root x)) =
      (Comparison.atoms t).map (denote (q)) := by
  apply List.map_congr_left
  intro x hx
  have hxc := (atoms_checked_normal _ t x ht hn hx).1
  have hval : denote (q) x ≤ denote (q) t := by
    apply canonicalANF_mem_le
    rw [← source_atoms_anf _ t ht hn]
    exact List.mem_map.mpr ⟨x, hx, rfl⟩
  exact (transform_parameter_value q root ha x hxc
    (hval.trans_lt (restricted_low_below q root ha t ht hr hl))).2

theorem mapped_atoms_value (q root : Nat) (ha : rootCheck q root = true)
    (t : RelativeTerm Nat) (ht : check (q) t = true)
    (hn : Comparison.Normal (q) t) (hr : Restricted q root t) :
    principalSum ((Comparison.atoms t).map
      (fun x => denote (betaCode q root) (transform q root x))) =
      denote (betaCode q root) (transform q root t) := by
  revert ht hn hr
  induction t with
  | parameter p =>
    intro ht hn hr
    rw [mapped_atoms_low q root ha (.parameter p) ht hn hr (Nat.zero_le _),
      source_atoms_value _ (.parameter p) ht hn,
      transform_low_value q root ha (.parameter p) ht hr (Nat.zero_le _)]
  | sum t u iht ihu =>
    intro ht hn hr
    have hc := BaseTransformation.sum_checks _ t u ht
    have hs := (restricted_sum q root t u).mp hr
    rw [Comparison.atoms, List.map_append, principalSum_append,
      iht hc.1 hn.1 hs.1, ihu hc.2 hn.2.1 hs.2, transform_add q root ha t u hc.1 hc.2]
  | theta k t ih =>
    intro ht hn hr
    simp only [Comparison.atoms, List.map_cons, List.map_nil, principalSum, add_zero]

theorem mapped_normalSum (q root : Nat) (ha : rootCheck q root = true)
    (t u : RelativeTerm Nat) (ht : check (q) t = true)
    (hu : check (q) u = true)
    (hnt : Comparison.Normal (q) t) (hnu : Comparison.Normal (q) u)
    (hrt : Restricted q root t) (hru : Restricted q root u)
    (hs : SourceNormalSum (denote (q) t + denote (q) u)
      (denote (q) t) (denote (q) u))
    (htw : IsAdditiveNormalForm ((Comparison.atoms t).map
      (fun x => denote (betaCode q root) (transform q root x))))
    (huw : IsAdditiveNormalForm ((Comparison.atoms u).map
      (fun x => denote (betaCode q root) (transform q root x))))
    (hcross : ∀ x ∈ Comparison.atoms t, ∀ y ∈ Comparison.atoms u,
      denote (q) y ≤ denote (q) x →
      denote (betaCode q root) (transform q root y) ≤ denote (betaCode q root) (transform q root x)) :
    SourceNormalSum
      (denote (betaCode q root) (transform q root t) + denote (betaCode q root) (transform q root u))
      (denote (betaCode q root) (transform q root t))
      (denote (betaCode q root) (transform q root u)) := by
  have hsource := (normalSum_words_iff (denote (q))
    (Comparison.atoms t) (Comparison.atoms u) (source_atoms_normal _ t ht hnt)
    (source_atoms_normal _ u hu hnu)).mp (by
      simpa only [source_atoms_value _ t ht hnt, source_atoms_value _ u hu hnu] using hs)
  have hshape : (Comparison.atoms t = [] ∧ Comparison.atoms u = []) ∨
      ∃ y, Comparison.atoms u = [y] ∧ ∀ x ∈ Comparison.atoms t,
        denote (betaCode q root) (transform q root y) ≤ denote (betaCode q root) (transform q root x) := by
    rcases hsource with hz | ⟨y, hy, hle⟩
    · exact Or.inl hz
    · refine Or.inr ⟨y, hy, ?_⟩
      intro x hx
      exact hcross x hx y (by rw [hy]; exact List.mem_singleton_self _) (hle x hx)
  have htarget := (normalSum_words_iff
    (fun x => denote (betaCode q root) (transform q root x))
    (Comparison.atoms t) (Comparison.atoms u) htw huw).mpr hshape
  simpa only [mapped_atoms_value q root ha t ht hnt hrt,
    mapped_atoms_value q root ha u hu hnu hru] using htarget

theorem mapped_word_lt_iff (q root : Nat) (ha : rootCheck q root = true)
    (t u : RelativeTerm Nat) (ht : check (q) t = true)
    (hu : check (q) u = true)
    (hnt : Comparison.Normal (q) t) (hnu : Comparison.Normal (q) u)
    (hrt : Restricted q root t) (hru : Restricted q root u)
    (htw : IsAdditiveNormalForm ((Comparison.atoms t).map
      (fun x => denote (betaCode q root) (transform q root x))))
    (huw : IsAdditiveNormalForm ((Comparison.atoms u).map
      (fun x => denote (betaCode q root) (transform q root x))))
    (hc : ∀ x ∈ Comparison.atoms t, ∀ y ∈ Comparison.atoms u,
      (denote (betaCode q root) (transform q root x) < denote (betaCode q root) (transform q root y) ↔
        denote (q) x < denote (q) y) ∧
      (denote (betaCode q root) (transform q root y) < denote (betaCode q root) (transform q root x) ↔
        denote (q) y < denote (q) x)) :
    denote (betaCode q root) (transform q root t) < denote (betaCode q root) (transform q root u) ↔
      denote (q) t < denote (q) u := by
  have hsource : ∀ x ∈ Comparison.atoms t, ∀ y ∈ Comparison.atoms u,
      (Comparison.less (q) x y = true ↔ denote (q) x < denote (q) y) ∧
      (Comparison.less (q) y x = true ↔ denote (q) y < denote (q) x) := by
    intro x hx y hy
    have hxc := atoms_checked_normal _ t x ht hnt hx
    have hyc := atoms_checked_normal _ u y hu hnu hy
    exact ⟨Comparison.less_correct _ x y hxc.1 hyc.1 hxc.2 hyc.2,
      Comparison.less_correct _ y x hyc.1 hxc.1 hyc.2 hxc.2⟩
  have htarget : ∀ x ∈ Comparison.atoms t, ∀ y ∈ Comparison.atoms u,
      (Comparison.less (q) x y = true ↔
        denote (betaCode q root) (transform q root x) < denote (betaCode q root) (transform q root y)) ∧
      (Comparison.less (q) y x = true ↔
        denote (betaCode q root) (transform q root y) < denote (betaCode q root) (transform q root x)) := by
    intro x hx y hy
    exact ⟨(hsource x hx y hy).1.trans (hc x hx y hy).1.symm,
      (hsource x hx y hy).2.trans (hc x hx y hy).2.symm⟩
  have hs := Theta.lexLT_correct (Comparison.less (q)) (denote (q))
    (Comparison.atoms t) (Comparison.atoms u) (source_atoms_normal _ t ht hnt)
    (source_atoms_normal _ u hu hnu) hsource
  have hv := Theta.lexLT_correct (Comparison.less (q))
    (fun x => denote (betaCode q root) (transform q root x))
    (Comparison.atoms t) (Comparison.atoms u) htw huw htarget
  rw [source_atoms_value _ t ht hnt, source_atoms_value _ u hu hnu] at hs
  rw [mapped_atoms_value q root ha t ht hnt hrt, mapped_atoms_value q root ha u hu hnu hru] at hv
  exact hv.symm.trans hs

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonIota.OrderSupport
