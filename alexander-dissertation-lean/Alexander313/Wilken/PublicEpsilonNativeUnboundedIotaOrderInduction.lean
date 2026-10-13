import Alexander313.Wilken.PublicEpsilonNativeUnboundedIotaOrderSupport

/-!
# Full original Normal and order induction at every admitted public epsilon without an endpoint

Simultaneous finite-size induction derives actual target weak Normality,
the mapped source canonical ANF and arbitrary pair order. Equal high levels
use the real generic native exposed comparator with strictly smaller
original support queries. Every actual target parameter comes from the
uniform SAME-value public return, including proper source-one references.
Only ORIGINAL checked weak Normal terms with full source-star restriction
are inputs. No target Normal/order, inverse or Mu-invariance oracle is used.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota

open OrderSupport
open Iota.OrderInduction (atoms_checked_normal atoms_sum_size_lt exposed_checked_normal
  source_atoms_anf source_atoms_normal source_atoms_value checked_theta_pos_principal
  checked_theta_lt_iff_exposed)

private theorem simultaneous (q root : Nat) (ha : rootCheck q root = true) (fuel : Nat) :
    (∀ t : RelativeTerm Nat, t.size ≤ fuel → check (q) t = true →
      Comparison.Normal (q) t → Restricted q root t →
      Comparison.Normal (betaCode q root) (transform q root t) ∧
      IsAdditiveNormalForm ((Comparison.atoms t).map
        (fun x => denote (betaCode q root) (transform q root x)))) ∧
    (∀ t u : RelativeTerm Nat, t.size + u.size ≤ fuel →
      check (q) t = true → check (q) u = true →
      Comparison.Normal (q) t → Comparison.Normal (q) u →
      Restricted q root t → Restricted q root u →
      (denote (betaCode q root) (transform q root t) < denote (betaCode q root) (transform q root u) ↔
        denote (q) t < denote (q) u)) := by
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    have hnormal : ∀ t : RelativeTerm Nat, t.size ≤ fuel → check (q) t = true →
        Comparison.Normal (q) t → Restricted q root t →
        Comparison.Normal (betaCode q root) (transform q root t) ∧
        IsAdditiveNormalForm ((Comparison.atoms t).map
          (fun x => denote (betaCode q root) (transform q root x))) := by
      intro t hsize ht hn hr
      by_cases hl : t.outerSort ≤ 1
      · refine ⟨transform_low_normal q root ha t ht hr hl, ?_⟩
        rw [mapped_atoms_low q root ha t ht hn hr hl]
        exact source_atoms_normal _ t ht hn
      · cases t with
        | parameter p => exact False.elim (hl (Nat.zero_le _))
        | sum t u =>
          have hc := BaseTransformation.sum_checks _ t u ht
          have hrs := (restricted_sum q root t u).mp hr
          have hts : t.size < fuel := (RelativeTerm.sum_left_size_lt t u).trans_le hsize
          have hus : u.size < fuel := (RelativeTerm.sum_right_size_lt t u).trans_le hsize
          have htc := (ih t.size hts).1 t le_rfl hc.1 hn.1 hrs.1
          have huc := (ih u.size hus).1 u le_rfl hc.2 hn.2.1 hrs.2
          have hs : SourceNormalSum (denote (q) t + denote (q) u)
              (denote (q) t) (denote (q) u) := hn.2.2
          have hcross : ∀ x ∈ Comparison.atoms t, ∀ y ∈ Comparison.atoms u,
              denote (q) y ≤ denote (q) x →
              denote (betaCode q root) (transform q root y) ≤ denote (betaCode q root) (transform q root x) := by
            intro x hx y hy hle
            have hxc := atoms_checked_normal _ t x hc.1 hn.1 hx
            have hyc := atoms_checked_normal _ u y hc.2 hn.2.1 hy
            have hxr := restricted_atoms q root t x hrs.1 hx
            have hyr := restricted_atoms q root u y hrs.2 hy
            have hxs := Comparison.atoms_size_le t x hx
            have hys := Comparison.atoms_size_le u y hy
            have hb : x.size + y.size < fuel := by
              simp only [RelativeTerm.size] at hsize
              omega
            have ho := (ih (x.size + y.size) hb).2 x y le_rfl hxc.1 hyc.1 hxc.2 hyc.2 hxr hyr
            exact le_of_not_gt (fun h => (ho.mp h).not_ge hle)
          have hsum := mapped_normalSum q root ha t u hc.1 hc.2 hn.1 hn.2.1 hrs.1 hrs.2
            hs htc.2 huc.2 hcross
          have hf : small q root (.sum t u) = false := by
            cases he : small q root (.sum t u) with
            | false => rfl
            | true => exact False.elim (hl ((small_iff_outerSort q root ha _ ht hr).mp he))
          have he : transform q root (.sum t u) = .sum (transform q root t) (transform q root u) := by
            simp only [transform, hf, Bool.cond_false]
          refine ⟨?_, ?_⟩
          · rw [he]
            exact ⟨htc.1, huc.1, hsum⟩
          · have hw := sourceNormalSum_canonical_concat hsum
            rw [canonicalANF_eq_of_normal htc.2 (mapped_atoms_value q root ha t hc.1 hn.1 hrs.1),
              canonicalANF_eq_of_normal huc.2 (mapped_atoms_value q root ha u hc.2 hn.2.1 hrs.2)] at hw
            simpa only [Comparison.atoms, List.map_append] using hw
        | theta k t =>
          cases k with
          | zero => exact False.elim (hl le_rfl)
          | succ k =>
            have htc := BaseTransformation.theta_argument_check _ (k + 1) t ht
            have htr := (restricted_theta_succ q root k t).mp hr
            have hts : t.size < fuel := (RelativeTerm.theta_arg_size_lt (k + 1) t).trans_le hsize
            have hc := (ih t.size hts).1 t le_rfl htc hn htr
            have htt := transform_checked q root ha (.theta (k + 1) t) ht hr
            rw [transform_theta_succ q root k ha t ht hr] at htt ⊢
            refine ⟨hc.1, ?_⟩
            have hp := checked_theta_pos_principal _ k (transform q root t) htt
            simpa only [Comparison.atoms, List.map_cons, List.map_nil,
              transform_theta_succ q root k ha t ht hr] using additiveNormalForm_singleton hp.1 hp.2
    refine ⟨hnormal, ?_⟩
    intro t u hsize ht hu hnt hnu hrt hru
    have hts : t.size ≤ fuel := by omega
    have hus : u.size ≤ fuel := by omega
    have htc := hnormal t hts ht hnt hrt
    have huc := hnormal u hus hu hnu hru
    have lex_case (x y : RelativeTerm Nat)
        (hx : check (q) x = true) (hy : check (q) y = true)
        (hnx : Comparison.Normal (q) x) (hny : Comparison.Normal (q) y)
        (hrx : Restricted q root x) (hry : Restricted q root y)
        (hxw : IsAdditiveNormalForm ((Comparison.atoms x).map
          (fun z => denote (betaCode q root) (transform q root z))))
        (hyw : IsAdditiveNormalForm ((Comparison.atoms y).map
          (fun z => denote (betaCode q root) (transform q root z))))
        (hsmall : ∀ b ∈ Comparison.atoms x, ∀ c ∈ Comparison.atoms y, b.size + c.size < fuel) :
        denote (betaCode q root) (transform q root x) < denote (betaCode q root) (transform q root y) ↔
          denote (q) x < denote (q) y := by
      apply mapped_word_lt_iff q root ha x y hx hy hnx hny hrx hry hxw hyw
      intro b hb c hc
      have hbc := atoms_checked_normal _ x b hx hnx hb
      have hcc := atoms_checked_normal _ y c hy hny hc
      have hbr := restricted_atoms q root x b hrx hb
      have hcr := restricted_atoms q root y c hry hc
      have hi := (ih (b.size + c.size) (hsmall b hb c hc)).2
      exact ⟨hi b c le_rfl hbc.1 hcc.1 hbc.2 hcc.2 hbr hcr,
        hi c b (by omega) hcc.1 hbc.1 hcc.2 hbc.2 hcr hbr⟩
    by_cases hlt : t.outerSort ≤ 1
    · by_cases hlu : u.outerSort ≤ 1
      · exact transform_low_lt_iff q root ha t u ht hu hrt hru hlt hlu
      · have hp := transform_low_high_lt q root ha t u ht hu hrt hru hlt (by omega)
        exact ⟨fun _ => hp.1, fun _ => hp.2⟩
    · by_cases hlu : u.outerSort ≤ 1
      · have hp := transform_low_high_lt q root ha u t hu ht hru hrt hlu (by omega)
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
                · have hp := transform_shifted_level_lt q root k l ha t u ht hu hrt hru hkl
                  exact ⟨fun _ => hp.1, fun _ => hp.2⟩
                · by_cases hlk : l < k
                  · have hp := transform_shifted_level_lt q root l k ha u t hu ht hru hrt hlk
                    exact ⟨fun h => False.elim (h.not_ge hp.2.le),
                      fun h => False.elim (h.not_ge hp.1.le)⟩
                  · have he : l = k := by omega
                    subst l
                    have hta := BaseTransformation.theta_argument_check _ (k + 1) t ht
                    have hua := BaseTransformation.theta_argument_check _ (k + 1) u hu
                    have htr := (restricted_theta_succ q root k t).mp hrt
                    have hur := (restricted_theta_succ q root k u).mp hru
                    have hnt' : Comparison.Normal (q) t := hnt
                    have hnu' : Comparison.Normal (q) u := hnu
                    have hb : t.size + u.size < fuel := by
                      simp only [RelativeTerm.size] at hsize
                      omega
                    have hab := (ih (t.size + u.size) hb).2 t u le_rfl hta hua hnt' hnu' htr hur
                    have htt := transform_checked q root ha (.theta (k + 1) t) ht hrt
                    have hut := transform_checked q root ha (.theta (k + 1) u) hu hru
                    rw [transform_theta_succ q root k ha t ht hrt] at htt htc
                    rw [transform_theta_succ q root k ha u hu hru] at hut huc
                    have htn : Comparison.Normal (betaCode q root) (transform q root t) := htc.1
                    have hun : Comparison.Normal (betaCode q root) (transform q root u) := huc.1
                    have hall :
                        (∀ x ∈ exposedThetaList k (transform q root t),
                          denote (betaCode q root) x < denote (betaCode q root) (.theta k (transform q root u))) ↔
                        ∀ x ∈ exposedThetaList (k + 1) t,
                          denote (q) x < denote (q) (.theta (k + 1) u) := by
                      rw [transform_exposedThetaList q root k ha t hta htr]
                      constructor
                      · intro hh x hx
                        have hxc := exposed_checked_normal _ (k + 1) t x hta hnt' hx
                        have hxr := restricted_exposed q root (k + 1) t x htr hx
                        have hxs := exposedTheta_size_le (k + 1) t x
                          ((mem_exposedThetaList_iff (k + 1) t x).mp hx)
                        have hsmall : x.size + (.theta (k + 1) u : RelativeTerm Nat).size < fuel := by
                          simp only [RelativeTerm.size] at hsize ⊢
                          omega
                        have ho := (ih (x.size + (.theta (k + 1) u : RelativeTerm Nat).size) hsmall).2
                          x (.theta (k + 1) u) le_rfl hxc.1 hu hxc.2 hnu hxr hru
                        apply ho.mp
                        rw [transform_theta_succ q root k ha u hu hru]
                        exact hh _ (List.mem_map.mpr ⟨x, hx, rfl⟩)
                      · intro hh z hz
                        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
                        have hxc := exposed_checked_normal _ (k + 1) t x hta hnt' hx
                        have hxr := restricted_exposed q root (k + 1) t x htr hx
                        have hxs := exposedTheta_size_le (k + 1) t x
                          ((mem_exposedThetaList_iff (k + 1) t x).mp hx)
                        have hsmall : x.size + (.theta (k + 1) u : RelativeTerm Nat).size < fuel := by
                          simp only [RelativeTerm.size] at hsize ⊢
                          omega
                        have ho := (ih (x.size + (.theta (k + 1) u : RelativeTerm Nat).size) hsmall).2
                          x (.theta (k + 1) u) le_rfl hxc.1 hu hxc.2 hnu hxr hru
                        have hv := ho.mpr (hh x hx)
                        simpa only [transform_theta_succ q root k ha u hu hru] using hv
                    have hany :
                        (∃ x ∈ exposedThetaList k (transform q root u),
                          denote (betaCode q root) (.theta k (transform q root t)) ≤ denote (betaCode q root) x) ↔
                        ∃ x ∈ exposedThetaList (k + 1) u,
                          denote (q) (.theta (k + 1) t) ≤ denote (q) x := by
                      rw [transform_exposedThetaList q root k ha u hua hur]
                      constructor
                      · rintro ⟨z, hz, hv⟩
                        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
                        have hxc := exposed_checked_normal _ (k + 1) u x hua hnu' hx
                        have hxr := restricted_exposed q root (k + 1) u x hur hx
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
                        rw [transform_theta_succ q root k ha t ht hrt] at hv'
                        exact hv'.not_ge hv
                      · rintro ⟨x, hx, hv⟩
                        have hxc := exposed_checked_normal _ (k + 1) u x hua hnu' hx
                        have hxr := restricted_exposed q root (k + 1) u x hur hx
                        have hxs := exposedTheta_size_le (k + 1) u x
                          ((mem_exposedThetaList_iff (k + 1) u x).mp hx)
                        have hsmall : x.size + (.theta (k + 1) t : RelativeTerm Nat).size < fuel := by
                          simp only [RelativeTerm.size] at hsize ⊢
                          omega
                        have ho := (ih (x.size + (.theta (k + 1) t : RelativeTerm Nat).size) hsmall).2
                          x (.theta (k + 1) t) le_rfl hxc.1 ht hxc.2 hnt hxr hrt
                        refine ⟨transform q root x, List.mem_map.mpr ⟨x, hx, rfl⟩, le_of_not_gt ?_⟩
                        intro h
                        have hv' : denote (betaCode q root) (transform q root x) <
                            denote (betaCode q root) (transform q root (.theta (k + 1) t)) := by
                          simpa only [transform_theta_succ q root k ha t ht hrt] using h
                        exact (ho.mp hv').not_ge hv
                    rw [transform_theta_succ q root k ha t ht hrt,
                      transform_theta_succ q root k ha u hu hru,
                      checked_theta_lt_iff_exposed _ k _ _ htt hut htn hun,
                      hab, hall, hany,
                      checked_theta_lt_iff_exposed _ (k + 1) t u ht hu hnt' hnu']

/-- Full weak Normal transport on the ORIGINAL checked Normal restricted
source, with no low-argument or target-Normal guard. -/
theorem transform_normal (q root : Nat) (ha : rootCheck q root = true)
    (t : RelativeTerm Nat) (ht : check (q) t = true)
    (hn : Comparison.Normal (q) t) (hr : Restricted q root t) :
    Comparison.Normal (betaCode q root) (transform q root t) :=
  ((simultaneous q root ha t.size).1 t le_rfl ht hn hr).1

/-- Arbitrary high arguments and all exposed recursive comparison queries
are included. The genuine transform preserves AND reflects strict order. -/
theorem transform_lt_iff (q root : Nat) (ha : rootCheck q root = true)
    (t u : RelativeTerm Nat) (ht : check (q) t = true)
    (hu : check (q) u = true)
    (hnt : Comparison.Normal (q) t) (hnu : Comparison.Normal (q) u)
    (hrt : Restricted q root t) (hru : Restricted q root u) :
    denote (betaCode q root) (transform q root t) < denote (betaCode q root) (transform q root u) ↔
      denote (q) t < denote (q) u :=
  (simultaneous q root ha (t.size + u.size)).2 t u le_rfl ht hu hnt hnu hrt hru

theorem transform_le_iff (q root : Nat) (ha : rootCheck q root = true)
    (t u : RelativeTerm Nat) (ht : check (q) t = true)
    (hu : check (q) u = true)
    (hnt : Comparison.Normal (q) t) (hnu : Comparison.Normal (q) u)
    (hrt : Restricted q root t) (hru : Restricted q root u) :
    denote (betaCode q root) (transform q root t) ≤ denote (betaCode q root) (transform q root u) ↔
      denote (q) t ≤ denote (q) u := by
  simpa only [not_lt] using not_congr (transform_lt_iff q root ha u t hu ht hnu hnt hru hrt)

/-- Presentation independence follows from the proved two strict-order
directions; equality is not a semantic hypothesis of the induction. -/
theorem transform_eq_iff (q root : Nat) (ha : rootCheck q root = true)
    (t u : RelativeTerm Nat) (ht : check (q) t = true)
    (hu : check (q) u = true)
    (hnt : Comparison.Normal (q) t) (hnu : Comparison.Normal (q) u)
    (hrt : Restricted q root t) (hru : Restricted q root u) :
    denote (betaCode q root) (transform q root t) = denote (betaCode q root) (transform q root u) ↔
      denote (q) t = denote (q) u := by
  have htu := transform_le_iff q root ha t u ht hu hnt hnu hrt hru
  have hut := transform_le_iff q root ha u t hu ht hnu hnt hru hrt
  constructor
  · intro h
    exact le_antisymm (htu.mp h.le) (hut.mp h.symm.le)
  · intro h
    exact le_antisymm (htu.mpr h.le) (hut.mpr h.symm.le)

/-- The actual transformed source principal word is the actual target's
canonical ANF, even when the transform atomizes a whole low subtree. -/
theorem transform_atoms_anf (q root : Nat) (ha : rootCheck q root = true)
    (t : RelativeTerm Nat) (ht : check (q) t = true)
    (hn : Comparison.Normal (q) t) (hr : Restricted q root t) :
    (Comparison.atoms t).map (fun x => denote (betaCode q root) (transform q root x)) =
      canonicalANF (denote (betaCode q root) (transform q root t)) :=
  (canonicalANF_eq_of_normal ((simultaneous q root ha t.size).1 t le_rfl ht hn hr).2
    (mapped_atoms_value q root ha t ht hn hr)).symm

/-- The real source final-principal binary sum condition transports on all
original normal restricted sums, including sums that become one parameter. -/
theorem transform_source_normal_sum (q root : Nat) (ha : rootCheck q root = true)
    (t u : RelativeTerm Nat) (ht : check (q) t = true)
    (hu : check (q) u = true)
    (hnt : Comparison.Normal (q) t) (hnu : Comparison.Normal (q) u)
    (hrt : Restricted q root t) (hru : Restricted q root u)
    (hs : SourceNormalSum (denote (q) t + denote (q) u)
      (denote (q) t) (denote (q) u)) :
    SourceNormalSum
      (denote (betaCode q root) (transform q root (.sum t u)))
      (denote (betaCode q root) (transform q root t))
      (denote (betaCode q root) (transform q root u)) := by
  rw [transform_add q root ha t u ht hu]
  apply mapped_normalSum q root ha t u ht hu hnt hnu hrt hru hs
  · rw [transform_atoms_anf q root ha t ht hnt hrt]
    exact canonicalANF_normal _
  · rw [transform_atoms_anf q root ha u hu hnu hru]
    exact canonicalANF_normal _
  · intro x hx y hy hle
    have hxc := atoms_checked_normal _ t x ht hnt hx
    have hyc := atoms_checked_normal _ u y hu hnu hy
    exact (transform_le_iff q root ha y x hyc.1 hxc.1 hyc.2 hxc.2
      (restricted_atoms q root u y hru hy) (restricted_atoms q root t x hrt hx)).mpr hle


theorem literalCode_accepted (q root c : Nat) (hc : inputCheck q root c = true) :
    Comparison.acceptedCode (betaCode q root) (literalCode q root c) = true := by
  obtain ⟨ha, t, rfl, ht, hn, hs⟩ := (inputCheck_exact q root c).mp hc
  have hr := (restricted_iff_sourceStar q root ha t ht hn).mpr hs
  rw [literalCode_code q root ha t ht hn hr]
  apply (Comparison.acceptedCode_exact _ _).mpr
  exact ⟨by simpa only [checkCode_code] using transform_checked q root ha t ht hr,
    by simpa only [ThetaCourse.rawTree_code] using transform_normal q root ha t ht hn hr⟩

theorem literalCode_lt_iff (q root c d : Nat) (hc : inputCheck q root c = true)
    (hd : inputCheck q root d = true) :
    interpretation (betaCode q root) (literalCode q root c) <
        interpretation (betaCode q root) (literalCode q root d) ↔
      interpretation (q) c < interpretation (q) d := by
  obtain ⟨ha, t, rfl, ht, hn, hs⟩ := (inputCheck_exact q root c).mp hc
  obtain ⟨_, u, rfl, hu, hnu, hsu⟩ := (inputCheck_exact q root d).mp hd
  have hr := (restricted_iff_sourceStar q root ha t ht hn).mpr hs
  have hru := (restricted_iff_sourceStar q root ha u hu hnu).mpr hsu
  rw [literalCode_code q root ha t ht hn hr, literalCode_code q root ha u hu hnu hru,
    interpretation_code, interpretation_code, interpretation_code, interpretation_code]
  exact transform_lt_iff q root ha t u ht hu hn hnu hr hru

theorem literalCode_eq_iff (q root c d : Nat) (hc : inputCheck q root c = true)
    (hd : inputCheck q root d = true) :
    interpretation (betaCode q root) (literalCode q root c) =
        interpretation (betaCode q root) (literalCode q root d) ↔
      interpretation (q) c = interpretation (q) d := by
  obtain ⟨ha, t, rfl, ht, hn, hs⟩ := (inputCheck_exact q root c).mp hc
  obtain ⟨_, u, rfl, hu, hnu, hsu⟩ := (inputCheck_exact q root d).mp hd
  have hr := (restricted_iff_sourceStar q root ha t ht hn).mpr hs
  have hru := (restricted_iff_sourceStar q root ha u hu hnu).mpr hsu
  rw [literalCode_code q root ha t ht hn hr, literalCode_code q root ha u hu hnu hru,
    interpretation_code, interpretation_code, interpretation_code, interpretation_code]
  exact transform_eq_iff q root ha t u ht hu hn hnu hr hru

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota
