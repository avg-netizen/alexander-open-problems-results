import Alexander313.Wilken.HereditaryNativeIotaOrderInductionSupport

/-!
# Simultaneous genuine semantic order and Normal transport for iota

The induction runs on actual finite native syntax. Its simultaneous invariant
contains target weak Normality, the mapped source principal word's ANF, and
both-context strict comparison for smaller pairs. High equal-level theta
comparisons use the real source-star/exposed-list comparison theorem; every
query has smaller size even when its other operand is the whole theta root.
No shifted-collapse naturality, semantic oracle, supplied target Normality,
inverse or coverage premise occurs in the resulting transport theorems.

The source remains the original contextCode s at the actual high theta-zero
root and the original checked Normal Restricted domain. Source-only candidates;
external compilation and kernel checking are still required.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Iota

open NativePublicBridge (contextCode contextCode_checked)
open OrderInduction

private theorem simultaneous (s a : Nat) (ha : rootCheck s a = true) (fuel : Nat) :
    (∀ t : RelativeTerm Nat, t.size ≤ fuel → check (contextCode s) t = true →
      Comparison.Normal (contextCode s) t → Restricted s a t →
      Comparison.Normal (alphaCode s a) (transform s a t) ∧
      IsAdditiveNormalForm ((Comparison.atoms t).map
        (fun x => denote (alphaCode s a) (transform s a x)))) ∧
    (∀ t u : RelativeTerm Nat, t.size + u.size ≤ fuel →
      check (contextCode s) t = true → check (contextCode s) u = true →
      Comparison.Normal (contextCode s) t → Comparison.Normal (contextCode s) u →
      Restricted s a t → Restricted s a u →
      (denote (alphaCode s a) (transform s a t) < denote (alphaCode s a) (transform s a u) ↔
        denote (contextCode s) t < denote (contextCode s) u)) := by
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    have hnormal : ∀ t : RelativeTerm Nat, t.size ≤ fuel → check (contextCode s) t = true →
        Comparison.Normal (contextCode s) t → Restricted s a t →
        Comparison.Normal (alphaCode s a) (transform s a t) ∧
        IsAdditiveNormalForm ((Comparison.atoms t).map
          (fun x => denote (alphaCode s a) (transform s a x))) := by
      intro t hsize ht hn hr
      by_cases hl : t.outerSort ≤ 1
      · refine ⟨transform_low_normal s a ha t ht hr hl, ?_⟩
        rw [mapped_atoms_low s a ha t ht hn hr hl]
        exact source_atoms_normal _ t ht hn
      · cases t with
        | parameter p => exact False.elim (hl (Nat.zero_le _))
        | sum t u =>
          have hc := BaseTransformation.sum_checks _ t u ht
          have hrs := (restricted_sum s a t u).mp hr
          have hts : t.size < fuel := (RelativeTerm.sum_left_size_lt t u).trans_le hsize
          have hus : u.size < fuel := (RelativeTerm.sum_right_size_lt t u).trans_le hsize
          have htc := (ih t.size hts).1 t le_rfl hc.1 hn.1 hrs.1
          have huc := (ih u.size hus).1 u le_rfl hc.2 hn.2.1 hrs.2
          have hs : SourceNormalSum (denote (contextCode s) t + denote (contextCode s) u)
              (denote (contextCode s) t) (denote (contextCode s) u) := hn.2.2
          have hcross : ∀ x ∈ Comparison.atoms t, ∀ y ∈ Comparison.atoms u,
              denote (contextCode s) y ≤ denote (contextCode s) x →
              denote (alphaCode s a) (transform s a y) ≤ denote (alphaCode s a) (transform s a x) := by
            intro x hx y hy hle
            have hxc := atoms_checked_normal _ t x hc.1 hn.1 hx
            have hyc := atoms_checked_normal _ u y hc.2 hn.2.1 hy
            have hxr := restricted_atoms s a t x hrs.1 hx
            have hyr := restricted_atoms s a u y hrs.2 hy
            have hxs := Comparison.atoms_size_le t x hx
            have hys := Comparison.atoms_size_le u y hy
            have hb : x.size + y.size < fuel := by
              simp only [RelativeTerm.size] at hsize
              omega
            have ho := (ih (x.size + y.size) hb).2 x y le_rfl hxc.1 hyc.1 hxc.2 hyc.2 hxr hyr
            exact le_of_not_gt (fun h => (ho.mp h).not_ge hle)
          have hsum := mapped_normalSum s a ha t u hc.1 hc.2 hn.1 hn.2.1 hrs.1 hrs.2
            hs htc.2 huc.2 hcross
          have hf : small s a (.sum t u) = false := by
            cases he : small s a (.sum t u) with
            | false => rfl
            | true => exact False.elim (hl ((small_iff_outerSort s a ha _ ht hr).mp he))
          have he : transform s a (.sum t u) = .sum (transform s a t) (transform s a u) := by
            simp only [transform, hf, Bool.cond_false]
          refine ⟨?_, ?_⟩
          · rw [he]
            exact ⟨htc.1, huc.1, hsum⟩
          · have hw := sourceNormalSum_canonical_concat hsum
            rw [canonicalANF_eq_of_normal htc.2 (mapped_atoms_value s a ha t hc.1 hn.1 hrs.1),
              canonicalANF_eq_of_normal huc.2 (mapped_atoms_value s a ha u hc.2 hn.2.1 hrs.2)] at hw
            simpa only [Comparison.atoms, List.map_append] using hw
        | theta k t =>
          cases k with
          | zero => exact False.elim (hl le_rfl)
          | succ k =>
            have htc := BaseTransformation.theta_argument_check _ (k + 1) t ht
            have htr := (restricted_theta_succ s a k t).mp hr
            have hts : t.size < fuel := (RelativeTerm.theta_arg_size_lt (k + 1) t).trans_le hsize
            have hc := (ih t.size hts).1 t le_rfl htc hn htr
            have htt := transform_checked s a ha (.theta (k + 1) t) ht hr
            rw [transform_theta_succ s a k ha t ht hr] at htt ⊢
            refine ⟨hc.1, ?_⟩
            have hp := checked_theta_pos_principal _ k (transform s a t) htt
            simpa only [Comparison.atoms, List.map_cons, List.map_nil,
              transform_theta_succ s a k ha t ht hr] using additiveNormalForm_singleton hp.1 hp.2
    refine ⟨hnormal, ?_⟩
    intro t u hsize ht hu hnt hnu hrt hru
    have hts : t.size ≤ fuel := by omega
    have hus : u.size ≤ fuel := by omega
    have htc := hnormal t hts ht hnt hrt
    have huc := hnormal u hus hu hnu hru
    have lex_case (x y : RelativeTerm Nat)
        (hx : check (contextCode s) x = true) (hy : check (contextCode s) y = true)
        (hnx : Comparison.Normal (contextCode s) x) (hny : Comparison.Normal (contextCode s) y)
        (hrx : Restricted s a x) (hry : Restricted s a y)
        (hxw : IsAdditiveNormalForm ((Comparison.atoms x).map
          (fun z => denote (alphaCode s a) (transform s a z))))
        (hyw : IsAdditiveNormalForm ((Comparison.atoms y).map
          (fun z => denote (alphaCode s a) (transform s a z))))
        (hsmall : ∀ b ∈ Comparison.atoms x, ∀ c ∈ Comparison.atoms y, b.size + c.size < fuel) :
        denote (alphaCode s a) (transform s a x) < denote (alphaCode s a) (transform s a y) ↔
          denote (contextCode s) x < denote (contextCode s) y := by
      apply mapped_word_lt_iff s a ha x y hx hy hnx hny hrx hry hxw hyw
      intro b hb c hc
      have hbc := atoms_checked_normal _ x b hx hnx hb
      have hcc := atoms_checked_normal _ y c hy hny hc
      have hbr := restricted_atoms s a x b hrx hb
      have hcr := restricted_atoms s a y c hry hc
      have hi := (ih (b.size + c.size) (hsmall b hb c hc)).2
      exact ⟨hi b c le_rfl hbc.1 hcc.1 hbc.2 hcc.2 hbr hcr,
        hi c b (by omega) hcc.1 hbc.1 hcc.2 hbc.2 hcr hbr⟩
    by_cases hlt : t.outerSort ≤ 1
    · by_cases hlu : u.outerSort ≤ 1
      · exact transform_low_lt_iff s a ha t u ht hu hrt hru hlt hlu
      · have hp := transform_low_high_lt s a ha t u ht hu hrt hru hlt (by omega)
        exact ⟨fun _ => hp.1, fun _ => hp.2⟩
    · by_cases hlu : u.outerSort ≤ 1
      · have hp := transform_low_high_lt s a ha u t hu ht hru hrt hlu (by omega)
        exact ⟨fun h => False.elim (h.not_ge hp.2.le),
          fun h => False.elim (h.not_ge hp.1.le)⟩
      · cases t with
        | parameter p => exact False.elim (hlt (Nat.zero_le _))
        | sum t v =>
          apply lex_case (.sum t v) u ht hu hnt hnu hrt hru htc.2 huc.2
          intro x hx y hy
          have hxs := atoms_sum_size_lt t v x hx
          have hys := Comparison.atoms_size_le u y hy
          omega
        | theta k t =>
          cases k with
          | zero => exact False.elim (hlt le_rfl)
          | succ k =>
            cases u with
            | parameter p => exact False.elim (hlu (Nat.zero_le _))
            | sum u v =>
              apply lex_case (.theta (k + 1) t) (.sum u v) ht hu hnt hnu hrt hru htc.2 huc.2
              intro x hx y hy
              have hxs := Comparison.atoms_size_le (.theta (k + 1) t) x hx
              have hys := atoms_sum_size_lt u v y hy
              omega
            | theta l u =>
              cases l with
              | zero => exact False.elim (hlu le_rfl)
              | succ l =>
                by_cases hkl : k < l
                · have hp := transform_shifted_level_lt s a k l ha t u ht hu hrt hru hkl
                  exact ⟨fun _ => hp.1, fun _ => hp.2⟩
                · by_cases hlk : l < k
                  · have hp := transform_shifted_level_lt s a l k ha u t hu ht hru hrt hlk
                    exact ⟨fun h => False.elim (h.not_ge hp.2.le),
                      fun h => False.elim (h.not_ge hp.1.le)⟩
                  · have he : l = k := by omega
                    subst l
                    have hta := BaseTransformation.theta_argument_check _ (k + 1) t ht
                    have hua := BaseTransformation.theta_argument_check _ (k + 1) u hu
                    have htr := (restricted_theta_succ s a k t).mp hrt
                    have hur := (restricted_theta_succ s a k u).mp hru
                    have hnt' : Comparison.Normal (contextCode s) t := hnt
                    have hnu' : Comparison.Normal (contextCode s) u := hnu
                    have hb : t.size + u.size < fuel := by
                      simp only [RelativeTerm.size] at hsize
                      omega
                    have hab := (ih (t.size + u.size) hb).2 t u le_rfl hta hua hnt' hnu' htr hur
                    have htt := transform_checked s a ha (.theta (k + 1) t) ht hrt
                    have hut := transform_checked s a ha (.theta (k + 1) u) hu hru
                    rw [transform_theta_succ s a k ha t ht hrt] at htt htc
                    rw [transform_theta_succ s a k ha u hu hru] at hut huc
                    have htn : Comparison.Normal (alphaCode s a) (transform s a t) := htc.1
                    have hun : Comparison.Normal (alphaCode s a) (transform s a u) := huc.1
                    have hall :
                        (∀ x ∈ exposedThetaList k (transform s a t),
                          denote (alphaCode s a) x < denote (alphaCode s a) (.theta k (transform s a u))) ↔
                        ∀ x ∈ exposedThetaList (k + 1) t,
                          denote (contextCode s) x < denote (contextCode s) (.theta (k + 1) u) := by
                      rw [transform_exposedThetaList s a k ha t hta htr]
                      constructor
                      · intro hh x hx
                        have hxc := exposed_checked_normal _ (k + 1) t x hta hnt' hx
                        have hxr := restricted_exposed s a (k + 1) t x htr hx
                        have hxs := exposedTheta_size_le (k + 1) t x
                          ((mem_exposedThetaList_iff (k + 1) t x).mp hx)
                        have hsmall : x.size + (.theta (k + 1) u : RelativeTerm Nat).size < fuel := by
                          simp only [RelativeTerm.size] at hsize ⊢
                          omega
                        have ho := (ih (x.size + (.theta (k + 1) u : RelativeTerm Nat).size) hsmall).2
                          x (.theta (k + 1) u) le_rfl hxc.1 hu hxc.2 hnu hxr hru
                        apply ho.mp
                        rw [transform_theta_succ s a k ha u hu hru]
                        exact hh _ (List.mem_map.mpr ⟨x, hx, rfl⟩)
                      · intro hh z hz
                        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
                        have hxc := exposed_checked_normal _ (k + 1) t x hta hnt' hx
                        have hxr := restricted_exposed s a (k + 1) t x htr hx
                        have hxs := exposedTheta_size_le (k + 1) t x
                          ((mem_exposedThetaList_iff (k + 1) t x).mp hx)
                        have hsmall : x.size + (.theta (k + 1) u : RelativeTerm Nat).size < fuel := by
                          simp only [RelativeTerm.size] at hsize ⊢
                          omega
                        have ho := (ih (x.size + (.theta (k + 1) u : RelativeTerm Nat).size) hsmall).2
                          x (.theta (k + 1) u) le_rfl hxc.1 hu hxc.2 hnu hxr hru
                        have hv := ho.mpr (hh x hx)
                        simpa only [transform_theta_succ s a k ha u hu hru] using hv
                    have hany :
                        (∃ x ∈ exposedThetaList k (transform s a u),
                          denote (alphaCode s a) (.theta k (transform s a t)) ≤ denote (alphaCode s a) x) ↔
                        ∃ x ∈ exposedThetaList (k + 1) u,
                          denote (contextCode s) (.theta (k + 1) t) ≤ denote (contextCode s) x := by
                      rw [transform_exposedThetaList s a k ha u hua hur]
                      constructor
                      · rintro ⟨z, hz, hv⟩
                        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
                        have hxc := exposed_checked_normal _ (k + 1) u x hua hnu' hx
                        have hxr := restricted_exposed s a (k + 1) u x hur hx
                        have hxs := exposedTheta_size_le (k + 1) u x
                          ((mem_exposedThetaList_iff (k + 1) u x).mp hx)
                        have hsmall : x.size + (.theta (k + 1) t : RelativeTerm Nat).size < fuel := by
                          simp only [RelativeTerm.size] at hsize ⊢
                          omega
                        have ho := (ih (x.size + (.theta (k + 1) t : RelativeTerm Nat).size) hsmall).2
                          x (.theta (k + 1) t) le_rfl hxc.1 ht hxc.2 hnt hxr hrt
                        refine ⟨x, hx, le_of_not_gt ?_⟩
                        intro h
                        have hv' := ho.mpr h
                        rw [transform_theta_succ s a k ha t ht hrt] at hv'
                        exact hv'.not_ge hv
                      · rintro ⟨x, hx, hv⟩
                        have hxc := exposed_checked_normal _ (k + 1) u x hua hnu' hx
                        have hxr := restricted_exposed s a (k + 1) u x hur hx
                        have hxs := exposedTheta_size_le (k + 1) u x
                          ((mem_exposedThetaList_iff (k + 1) u x).mp hx)
                        have hsmall : x.size + (.theta (k + 1) t : RelativeTerm Nat).size < fuel := by
                          simp only [RelativeTerm.size] at hsize ⊢
                          omega
                        have ho := (ih (x.size + (.theta (k + 1) t : RelativeTerm Nat).size) hsmall).2
                          x (.theta (k + 1) t) le_rfl hxc.1 ht hxc.2 hnt hxr hrt
                        refine ⟨transform s a x, List.mem_map.mpr ⟨x, hx, rfl⟩, le_of_not_gt ?_⟩
                        intro h
                        have hv' : denote (alphaCode s a) (transform s a x) <
                            denote (alphaCode s a) (transform s a (.theta (k + 1) t)) := by
                          simpa only [transform_theta_succ s a k ha t ht hrt] using h
                        exact (ho.mp hv').not_ge hv
                    rw [transform_theta_succ s a k ha t ht hrt,
                      transform_theta_succ s a k ha u hu hru,
                      checked_theta_lt_iff_exposed _ k _ _ htt hut htn hun,
                      hab, hall, hany,
                      checked_theta_lt_iff_exposed _ (k + 1) t u ht hu hnt' hnu']

/-- Full weak Normal transport on the ORIGINAL checked Normal restricted
source, with no low-argument or target-Normal guard. -/
theorem transform_normal (s a : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (contextCode s) t = true)
    (hn : Comparison.Normal (contextCode s) t) (hr : Restricted s a t) :
    Comparison.Normal (alphaCode s a) (transform s a t) :=
  ((simultaneous s a ha t.size).1 t le_rfl ht hn hr).1

/-- Arbitrary high arguments and all exposed recursive comparison queries
are included. The genuine transform preserves AND reflects strict order. -/
theorem transform_lt_iff (s a : Nat) (ha : rootCheck s a = true)
    (t u : RelativeTerm Nat) (ht : check (contextCode s) t = true)
    (hu : check (contextCode s) u = true)
    (hnt : Comparison.Normal (contextCode s) t) (hnu : Comparison.Normal (contextCode s) u)
    (hrt : Restricted s a t) (hru : Restricted s a u) :
    denote (alphaCode s a) (transform s a t) < denote (alphaCode s a) (transform s a u) ↔
      denote (contextCode s) t < denote (contextCode s) u :=
  (simultaneous s a ha (t.size + u.size)).2 t u le_rfl ht hu hnt hnu hrt hru

theorem transform_le_iff (s a : Nat) (ha : rootCheck s a = true)
    (t u : RelativeTerm Nat) (ht : check (contextCode s) t = true)
    (hu : check (contextCode s) u = true)
    (hnt : Comparison.Normal (contextCode s) t) (hnu : Comparison.Normal (contextCode s) u)
    (hrt : Restricted s a t) (hru : Restricted s a u) :
    denote (alphaCode s a) (transform s a t) ≤ denote (alphaCode s a) (transform s a u) ↔
      denote (contextCode s) t ≤ denote (contextCode s) u := by
  simpa only [not_lt] using not_congr (transform_lt_iff s a ha u t hu ht hnu hnt hru hrt)

/-- Presentation independence follows from the proved two strict-order
directions; equality is not a semantic hypothesis of the induction. -/
theorem transform_eq_iff (s a : Nat) (ha : rootCheck s a = true)
    (t u : RelativeTerm Nat) (ht : check (contextCode s) t = true)
    (hu : check (contextCode s) u = true)
    (hnt : Comparison.Normal (contextCode s) t) (hnu : Comparison.Normal (contextCode s) u)
    (hrt : Restricted s a t) (hru : Restricted s a u) :
    denote (alphaCode s a) (transform s a t) = denote (alphaCode s a) (transform s a u) ↔
      denote (contextCode s) t = denote (contextCode s) u := by
  have htu := transform_le_iff s a ha t u ht hu hnt hnu hrt hru
  have hut := transform_le_iff s a ha u t hu ht hnu hnt hru hrt
  constructor
  · intro h
    exact le_antisymm (htu.mp h.le) (hut.mp h.symm.le)
  · intro h
    exact le_antisymm (htu.mpr h.le) (hut.mpr h.symm.le)

/-- The actual transformed source principal word is the actual target's
canonical ANF, even when the transform atomizes a whole low subtree. -/
theorem transform_atoms_anf (s a : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (contextCode s) t = true)
    (hn : Comparison.Normal (contextCode s) t) (hr : Restricted s a t) :
    (Comparison.atoms t).map (fun x => denote (alphaCode s a) (transform s a x)) =
      canonicalANF (denote (alphaCode s a) (transform s a t)) :=
  (canonicalANF_eq_of_normal ((simultaneous s a ha t.size).1 t le_rfl ht hn hr).2
    (mapped_atoms_value s a ha t ht hn hr)).symm

/-- The real source final-principal binary sum condition transports on all
original normal restricted sums, including sums that become one parameter. -/
theorem transform_source_normal_sum (s a : Nat) (ha : rootCheck s a = true)
    (t u : RelativeTerm Nat) (ht : check (contextCode s) t = true)
    (hu : check (contextCode s) u = true)
    (hnt : Comparison.Normal (contextCode s) t) (hnu : Comparison.Normal (contextCode s) u)
    (hrt : Restricted s a t) (hru : Restricted s a u)
    (hs : SourceNormalSum (denote (contextCode s) t + denote (contextCode s) u)
      (denote (contextCode s) t) (denote (contextCode s) u)) :
    SourceNormalSum
      (denote (alphaCode s a) (transform s a (.sum t u)))
      (denote (alphaCode s a) (transform s a t))
      (denote (alphaCode s a) (transform s a u)) := by
  rw [transform_add s a ha t u ht hu]
  apply mapped_normalSum s a ha t u ht hu hnt hnu hrt hru hs
  · rw [transform_atoms_anf s a ha t ht hnt hrt]
    exact canonicalANF_normal _
  · rw [transform_atoms_anf s a ha u hu hnu hru]
    exact canonicalANF_normal _
  · intro x hx y hy hle
    have hxc := atoms_checked_normal _ t x ht hnt hx
    have hyc := atoms_checked_normal _ u y hu hnu hy
    exact (transform_le_iff s a ha y x hyc.1 hxc.1 hyc.2 hxc.2
      (restricted_atoms s a u y hru hy) (restricted_atoms s a t x hrt hx)).mpr hle

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Iota
