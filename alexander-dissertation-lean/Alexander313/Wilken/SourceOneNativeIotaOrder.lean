import Alexander313.Wilken.SourceOneNativeIotaOrderSupport

/-!
# Full genuine original source-one iota order and Normal transport

One simultaneous finite-size induction constructs target weak Normality,
the real mapped original source theta-atom ANF, and both strict-order
directions. Every same-level high theta comparison uses the actual ORIGINAL
source-one exposed theorem and the separate actual native alpha theorem.
Every hidden high argument and recursive whole-root comparison retains the
original admission, Normality and full printed restriction. No source-base
one epsilon parser, shifted-collapse identity, target Normal or order oracle
is used. This gives the order/Normal part of 2.46(a); inverse/coverage and
source-one mu remain separate. Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota

open OrderSupport
open NativeContext.Iota.OrderInduction (checked_theta_pos_principal checked_theta_lt_iff_exposed)

private theorem simultaneous (a : Nat) (ha : rootCheck a = true) (fuel : Nat) :
    (∀ t : RelativeTerm Nat, t.size ≤ fuel → check 0 t = true →
      Theta.Normal 0 t → Restricted a t →
      NativeContext.Comparison.Normal (alphaCode a) (transform a t) ∧
      IsAdditiveNormalForm ((thetaAtoms t).map
        (fun x => NativeContext.denote (alphaCode a) (transform a x)))) ∧
    (∀ t u : RelativeTerm Nat, t.size + u.size ≤ fuel →
      check 0 t = true → check 0 u = true →
      Theta.Normal 0 t → Theta.Normal 0 u →
      Restricted a t → Restricted a u →
      (NativeContext.denote (alphaCode a) (transform a t) < NativeContext.denote (alphaCode a) (transform a u) ↔
        denote 0 t < denote 0 u)) := by
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    have hnormal : ∀ t : RelativeTerm Nat, t.size ≤ fuel → check 0 t = true →
        Theta.Normal 0 t → Restricted a t →
        NativeContext.Comparison.Normal (alphaCode a) (transform a t) ∧
        IsAdditiveNormalForm ((thetaAtoms t).map
          (fun x => NativeContext.denote (alphaCode a) (transform a x))) := by
      intro t hsize ht hn hr
      by_cases hl : t.outerSort ≤ 1
      · refine ⟨transform_low_normal a ha t ht hr hl, ?_⟩
        rw [mapped_atoms_low a ha t ht hn hr hl]
        exact source_atoms_normal t ht hn
      · cases t with
        | parameter p => exact False.elim (hl (Nat.zero_le _))
        | sum t u =>
          have hc := sum_checks t u ht
          have hrs := (restricted_sum a t u).mp hr
          have hts : t.size < fuel := (RelativeTerm.sum_left_size_lt t u).trans_le hsize
          have hus : u.size < fuel := (RelativeTerm.sum_right_size_lt t u).trans_le hsize
          have htc := (ih t.size hts).1 t le_rfl hc.1 hn.1 hrs.1
          have huc := (ih u.size hus).1 u le_rfl hc.2 hn.2.1 hrs.2
          have hs : SourceNormalSum (denote 0 t + denote 0 u)
              (denote 0 t) (denote 0 u) := hn.2.2
          have hcross : ∀ x ∈ thetaAtoms t, ∀ y ∈ thetaAtoms u,
              denote 0 y ≤ denote 0 x →
              NativeContext.denote (alphaCode a) (transform a y) ≤ NativeContext.denote (alphaCode a) (transform a x) := by
            intro x hx y hy hle
            have hxc := atoms_checked_normal t x hc.1 hn.1 hx
            have hyc := atoms_checked_normal u y hc.2 hn.2.1 hy
            have hxr := restricted_atoms a t x hrs.1 hx
            have hyr := restricted_atoms a u y hrs.2 hy
            have hxs := thetaAtoms_size_le t x hx
            have hys := thetaAtoms_size_le u y hy
            have hb : x.size + y.size < fuel := by
              simp only [RelativeTerm.size] at hsize
              omega
            have ho := (ih (x.size + y.size) hb).2 x y le_rfl hxc.1 hyc.1 hxc.2 hyc.2 hxr hyr
            exact le_of_not_gt (fun h => (ho.mp h).not_ge hle)
          have hsum := mapped_normalSum a ha t u hc.1 hc.2 hn.1 hn.2.1 hrs.1 hrs.2
            hs htc.2 huc.2 hcross
          have hf : small a (.sum t u) = false := by
            cases he : small a (.sum t u) with
            | false => rfl
            | true => exact False.elim (hl ((small_iff_outerSort a ha _ ht hr).mp he))
          have he : transform a (.sum t u) = .sum (transform a t) (transform a u) := by
            simp only [transform, hf, Bool.cond_false]
          refine ⟨?_, ?_⟩
          · rw [he]
            exact ⟨htc.1, huc.1, hsum⟩
          · have hw := sourceNormalSum_canonical_concat hsum
            rw [canonicalANF_eq_of_normal htc.2 (mapped_atoms_value a ha t hc.1 hn.1 hrs.1),
              canonicalANF_eq_of_normal huc.2 (mapped_atoms_value a ha u hc.2 hn.2.1 hrs.2)] at hw
            simpa only [thetaAtoms, List.map_append] using hw
        | theta k t =>
          cases k with
          | zero => exact False.elim (hl le_rfl)
          | succ k =>
            have htc := argument_checked (k + 1) t ht
            have htr := (restricted_theta_succ a k t).mp hr
            have hts : t.size < fuel := (RelativeTerm.theta_arg_size_lt (k + 1) t).trans_le hsize
            have hc := (ih t.size hts).1 t le_rfl htc hn htr
            have htt := transform_checked a ha (.theta (k + 1) t) ht hr
            rw [transform_theta_succ a k ha t ht hr] at htt ⊢
            refine ⟨hc.1, ?_⟩
            have hp := checked_theta_pos_principal _ k (transform a t) htt
            simpa only [thetaAtoms, List.map_cons, List.map_nil,
              transform_theta_succ a k ha t ht hr] using additiveNormalForm_singleton hp.1 hp.2
    refine ⟨hnormal, ?_⟩
    intro t u hsize ht hu hnt hnu hrt hru
    have hts : t.size ≤ fuel := by omega
    have hus : u.size ≤ fuel := by omega
    have htc := hnormal t hts ht hnt hrt
    have huc := hnormal u hus hu hnu hru
    have lex_case (x y : RelativeTerm Nat)
        (hx : check 0 x = true) (hy : check 0 y = true)
        (hnx : Theta.Normal 0 x) (hny : Theta.Normal 0 y)
        (hrx : Restricted a x) (hry : Restricted a y)
        (hxw : IsAdditiveNormalForm ((thetaAtoms x).map
          (fun z => NativeContext.denote (alphaCode a) (transform a z))))
        (hyw : IsAdditiveNormalForm ((thetaAtoms y).map
          (fun z => NativeContext.denote (alphaCode a) (transform a z))))
        (hsmall : ∀ b ∈ thetaAtoms x, ∀ c ∈ thetaAtoms y, b.size + c.size < fuel) :
        NativeContext.denote (alphaCode a) (transform a x) < NativeContext.denote (alphaCode a) (transform a y) ↔
          denote 0 x < denote 0 y := by
      apply mapped_word_lt_iff a ha x y hx hy hnx hny hrx hry hxw hyw
      intro b hb c hc
      have hbc := atoms_checked_normal x b hx hnx hb
      have hcc := atoms_checked_normal y c hy hny hc
      have hbr := restricted_atoms a x b hrx hb
      have hcr := restricted_atoms a y c hry hc
      have hi := (ih (b.size + c.size) (hsmall b hb c hc)).2
      exact ⟨hi b c le_rfl hbc.1 hcc.1 hbc.2 hcc.2 hbr hcr,
        hi c b (by omega) hcc.1 hbc.1 hcc.2 hbc.2 hcr hbr⟩
    by_cases hlt : t.outerSort ≤ 1
    · by_cases hlu : u.outerSort ≤ 1
      · exact transform_low_lt_iff a ha t u ht hu hrt hru hlt hlu
      · have hp := transform_low_high_lt a ha t u ht hu hrt hru hlt (by omega)
        exact ⟨fun _ => hp.1, fun _ => hp.2⟩
    · by_cases hlu : u.outerSort ≤ 1
      · have hp := transform_low_high_lt a ha u t hu ht hru hrt hlu (by omega)
        exact ⟨fun h => False.elim (h.not_ge hp.2.le),
          fun h => False.elim (h.not_ge hp.1.le)⟩
      · cases t with
        | parameter p => exact False.elim (hlt (Nat.zero_le _))
        | sum t v =>
          apply lex_case (.sum t v) u ht hu hnt hnu hrt hru htc.2 huc.2
          intro x hx y hy
          have hxs := thetaAtoms_sum_size_lt t v x hx
          have hys := thetaAtoms_size_le u y hy
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
              have hxs := thetaAtoms_size_le (.theta (k + 1) t) x hx
              have hys := thetaAtoms_sum_size_lt u v y hy
              omega
            | theta l u =>
              cases l with
              | zero => exact False.elim (hlu le_rfl)
              | succ l =>
                by_cases hkl : k < l
                · have hp := transform_shifted_level_lt a k l ha t u ht hu hrt hru hkl
                  exact ⟨fun _ => hp.1, fun _ => hp.2⟩
                · by_cases hlk : l < k
                  · have hp := transform_shifted_level_lt a l k ha u t hu ht hru hrt hlk
                    exact ⟨fun h => False.elim (h.not_ge hp.2.le),
                      fun h => False.elim (h.not_ge hp.1.le)⟩
                  · have he : l = k := by omega
                    subst l
                    have hta := argument_checked (k + 1) t ht
                    have hua := argument_checked (k + 1) u hu
                    have htr := (restricted_theta_succ a k t).mp hrt
                    have hur := (restricted_theta_succ a k u).mp hru
                    have hnt' : Theta.Normal 0 t := hnt
                    have hnu' : Theta.Normal 0 u := hnu
                    have hb : t.size + u.size < fuel := by
                      simp only [RelativeTerm.size] at hsize
                      omega
                    have hab := (ih (t.size + u.size) hb).2 t u le_rfl hta hua hnt' hnu' htr hur
                    have htt := transform_checked a ha (.theta (k + 1) t) ht hrt
                    have hut := transform_checked a ha (.theta (k + 1) u) hu hru
                    rw [transform_theta_succ a k ha t ht hrt] at htt htc
                    rw [transform_theta_succ a k ha u hu hru] at hut huc
                    have htn : NativeContext.Comparison.Normal (alphaCode a) (transform a t) := htc.1
                    have hun : NativeContext.Comparison.Normal (alphaCode a) (transform a u) := huc.1
                    have hall :
                        (∀ x ∈ exposedThetaList k (transform a t),
                          NativeContext.denote (alphaCode a) x < NativeContext.denote (alphaCode a) (.theta k (transform a u))) ↔
                        ∀ x ∈ exposedThetaList (k + 1) t,
                          denote 0 x < denote 0 (.theta (k + 1) u) := by
                      rw [transform_exposedThetaList a k ha t hta htr]
                      constructor
                      · intro hh x hx
                        have hxc := exposed_checked_normal (k + 1) t x hta hnt' hx
                        have hxr := restricted_exposed a (k + 1) t x htr hx
                        have hxs := exposedTheta_size_le (k + 1) t x
                          ((mem_exposedThetaList_iff (k + 1) t x).mp hx)
                        have hsmall : x.size + (.theta (k + 1) u : RelativeTerm Nat).size < fuel := by
                          simp only [RelativeTerm.size] at hsize ⊢
                          omega
                        have ho := (ih (x.size + (.theta (k + 1) u : RelativeTerm Nat).size) hsmall).2
                          x (.theta (k + 1) u) le_rfl hxc.1 hu hxc.2 hnu hxr hru
                        apply ho.mp
                        rw [transform_theta_succ a k ha u hu hru]
                        exact hh _ (List.mem_map.mpr ⟨x, hx, rfl⟩)
                      · intro hh z hz
                        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
                        have hxc := exposed_checked_normal (k + 1) t x hta hnt' hx
                        have hxr := restricted_exposed a (k + 1) t x htr hx
                        have hxs := exposedTheta_size_le (k + 1) t x
                          ((mem_exposedThetaList_iff (k + 1) t x).mp hx)
                        have hsmall : x.size + (.theta (k + 1) u : RelativeTerm Nat).size < fuel := by
                          simp only [RelativeTerm.size] at hsize ⊢
                          omega
                        have ho := (ih (x.size + (.theta (k + 1) u : RelativeTerm Nat).size) hsmall).2
                          x (.theta (k + 1) u) le_rfl hxc.1 hu hxc.2 hnu hxr hru
                        have hv := ho.mpr (hh x hx)
                        simpa only [transform_theta_succ a k ha u hu hru] using hv
                    have hany :
                        (∃ x ∈ exposedThetaList k (transform a u),
                          NativeContext.denote (alphaCode a) (.theta k (transform a t)) ≤ NativeContext.denote (alphaCode a) x) ↔
                        ∃ x ∈ exposedThetaList (k + 1) u,
                          denote 0 (.theta (k + 1) t) ≤ denote 0 x := by
                      rw [transform_exposedThetaList a k ha u hua hur]
                      constructor
                      · rintro ⟨z, hz, hv⟩
                        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
                        have hxc := exposed_checked_normal (k + 1) u x hua hnu' hx
                        have hxr := restricted_exposed a (k + 1) u x hur hx
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
                        rw [transform_theta_succ a k ha t ht hrt] at hv'
                        exact hv'.not_ge hv
                      · rintro ⟨x, hx, hv⟩
                        have hxc := exposed_checked_normal (k + 1) u x hua hnu' hx
                        have hxr := restricted_exposed a (k + 1) u x hur hx
                        have hxs := exposedTheta_size_le (k + 1) u x
                          ((mem_exposedThetaList_iff (k + 1) u x).mp hx)
                        have hsmall : x.size + (.theta (k + 1) t : RelativeTerm Nat).size < fuel := by
                          simp only [RelativeTerm.size] at hsize ⊢
                          omega
                        have ho := (ih (x.size + (.theta (k + 1) t : RelativeTerm Nat).size) hsmall).2
                          x (.theta (k + 1) t) le_rfl hxc.1 ht hxc.2 hnt hxr hrt
                        refine ⟨transform a x, List.mem_map.mpr ⟨x, hx, rfl⟩, le_of_not_gt ?_⟩
                        intro h
                        have hv' : NativeContext.denote (alphaCode a) (transform a x) <
                            NativeContext.denote (alphaCode a) (transform a (.theta (k + 1) t)) := by
                          simpa only [transform_theta_succ a k ha t ht hrt] using h
                        exact (ho.mp hv').not_ge hv
                    rw [transform_theta_succ a k ha t ht hrt,
                      transform_theta_succ a k ha u hu hru,
                      checked_theta_lt_iff_exposed _ k _ _ htt hut htn hun,
                      hab, hall, hany,
                      checked_source_theta_lt_iff_exposed (k + 1) t u ht hu hnt' hnu']

/-- Full weak Normal transport on the ORIGINAL checked Normal restricted
source, with no low-argument or target-Normal guard. -/
theorem transform_normal (a : Nat) (ha : rootCheck a = true)
    (t : RelativeTerm Nat) (ht : check 0 t = true)
    (hn : Theta.Normal 0 t) (hr : Restricted a t) :
    NativeContext.Comparison.Normal (alphaCode a) (transform a t) :=
  ((simultaneous a ha t.size).1 t le_rfl ht hn hr).1

/-- Arbitrary high arguments and all exposed recursive comparison queries
are included. The genuine transform preserves AND reflects strict order. -/
theorem transform_lt_iff (a : Nat) (ha : rootCheck a = true)
    (t u : RelativeTerm Nat) (ht : check 0 t = true)
    (hu : check 0 u = true)
    (hnt : Theta.Normal 0 t) (hnu : Theta.Normal 0 u)
    (hrt : Restricted a t) (hru : Restricted a u) :
    NativeContext.denote (alphaCode a) (transform a t) < NativeContext.denote (alphaCode a) (transform a u) ↔
      denote 0 t < denote 0 u :=
  (simultaneous a ha (t.size + u.size)).2 t u le_rfl ht hu hnt hnu hrt hru

theorem transform_le_iff (a : Nat) (ha : rootCheck a = true)
    (t u : RelativeTerm Nat) (ht : check 0 t = true)
    (hu : check 0 u = true)
    (hnt : Theta.Normal 0 t) (hnu : Theta.Normal 0 u)
    (hrt : Restricted a t) (hru : Restricted a u) :
    NativeContext.denote (alphaCode a) (transform a t) ≤ NativeContext.denote (alphaCode a) (transform a u) ↔
      denote 0 t ≤ denote 0 u := by
  simpa only [not_lt] using not_congr (transform_lt_iff a ha u t hu ht hnu hnt hru hrt)

/-- Presentation independence follows from the proved two strict-order
directions; equality is not a semantic hypothesis of the induction. -/
theorem transform_eq_iff (a : Nat) (ha : rootCheck a = true)
    (t u : RelativeTerm Nat) (ht : check 0 t = true)
    (hu : check 0 u = true)
    (hnt : Theta.Normal 0 t) (hnu : Theta.Normal 0 u)
    (hrt : Restricted a t) (hru : Restricted a u) :
    NativeContext.denote (alphaCode a) (transform a t) = NativeContext.denote (alphaCode a) (transform a u) ↔
      denote 0 t = denote 0 u := by
  have htu := transform_le_iff a ha t u ht hu hnt hnu hrt hru
  have hut := transform_le_iff a ha u t hu ht hnu hnt hru hrt
  constructor
  · intro h
    exact le_antisymm (htu.mp h.le) (hut.mp h.symm.le)
  · intro h
    exact le_antisymm (htu.mpr h.le) (hut.mpr h.symm.le)

/-- The actual transformed source principal word is the actual target's
canonical ANF, even when the transform atomizes a whole low subtree. -/
theorem transform_atoms_anf (a : Nat) (ha : rootCheck a = true)
    (t : RelativeTerm Nat) (ht : check 0 t = true)
    (hn : Theta.Normal 0 t) (hr : Restricted a t) :
    (thetaAtoms t).map (fun x => NativeContext.denote (alphaCode a) (transform a x)) =
      canonicalANF (NativeContext.denote (alphaCode a) (transform a t)) :=
  (canonicalANF_eq_of_normal ((simultaneous a ha t.size).1 t le_rfl ht hn hr).2
    (mapped_atoms_value a ha t ht hn hr)).symm

/-- The real source final-principal binary sum condition transports on all
original normal restricted sums, including sums that become one parameter. -/
theorem transform_source_normal_sum (a : Nat) (ha : rootCheck a = true)
    (t u : RelativeTerm Nat) (ht : check 0 t = true)
    (hu : check 0 u = true)
    (hnt : Theta.Normal 0 t) (hnu : Theta.Normal 0 u)
    (hrt : Restricted a t) (hru : Restricted a u)
    (hs : SourceNormalSum (denote 0 t + denote 0 u)
      (denote 0 t) (denote 0 u)) :
    SourceNormalSum
      (NativeContext.denote (alphaCode a) (transform a (.sum t u)))
      (NativeContext.denote (alphaCode a) (transform a t))
      (NativeContext.denote (alphaCode a) (transform a u)) := by
  rw [transform_add a ha t u ht hu]
  apply mapped_normalSum a ha t u ht hu hnt hnu hrt hru hs
  · rw [transform_atoms_anf a ha t ht hnt hrt]
    exact canonicalANF_normal _
  · rw [transform_atoms_anf a ha u hu hnu hru]
    exact canonicalANF_normal _
  · intro x hx y hy hle
    have hxc := atoms_checked_normal t x ht hnt hx
    have hyc := atoms_checked_normal u y hu hnu hy
    exact (transform_le_iff a ha y x hyc.1 hxc.1 hyc.2 hxc.2
      (restricted_atoms a u y hru hy) (restricted_atoms a t x hrt hx)).mpr hle

/-- The actual guarded literal evaluator supplies a genuine native Normal
caller on the whole ORIGINAL source-one domain. -/
theorem literalCode_accepted (a c : Nat) (hc : inputCheck a c = true) :
    NativeContext.Comparison.acceptedCode (alphaCode a) (literalCode a c) = true := by
  obtain ⟨ha, t, rfl, ht, hn, hs⟩ := (inputCheck_exact a c).mp hc
  have hr := (restricted_iff_sourceStar a ha t ht hn).mpr hs
  rw [literalCode_code a ha t ht hn hr]
  exact (NativeContext.Comparison.acceptedCode_exact _ _).mpr
    ⟨by simpa only [NativeContext.checkCode_code] using transform_checked a ha t ht hr,
      by simpa only [ThetaCourse.rawTree_code] using transform_normal a ha t ht hn hr⟩

theorem literalCode_lt_iff (a c d : Nat) (hc : inputCheck a c = true)
    (hd : inputCheck a d = true) :
    NativeContext.interpretation (alphaCode a) (literalCode a c) <
        NativeContext.interpretation (alphaCode a) (literalCode a d) ↔
      interpretation 0 c < interpretation 0 d := by
  obtain ⟨ha, t, rfl, ht, hn, hs⟩ := (inputCheck_exact a c).mp hc
  obtain ⟨ha', u, rfl, hu, hnu, hsu⟩ := (inputCheck_exact a d).mp hd
  have hrt := (restricted_iff_sourceStar a ha t ht hn).mpr hs
  have hru := (restricted_iff_sourceStar a ha u hu hnu).mpr hsu
  rw [literalCode_code a ha t ht hn hrt, literalCode_code a ha u hu hnu hru,
    NativeContext.interpretation_code, NativeContext.interpretation_code,
    interpretation_code, interpretation_code]
  exact transform_lt_iff a ha t u ht hu hn hnu hrt hru

theorem argument_literalCode_accepted (a : Nat) (ha : rootCheck a = true) :
    NativeContext.Comparison.acceptedCode (alphaCode a) (literalCode a (Localization.argumentCode a)) = true :=
  literalCode_accepted a _ (argument_inputCheck a ha)

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota
