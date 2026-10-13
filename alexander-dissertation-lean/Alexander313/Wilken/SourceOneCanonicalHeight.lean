import Alexander313.Wilken.SourceOneHeightSupport

/-!
# Canonical value height for the original base-one grammar

Canonical ANF words align the actual theta atoms of equal normal values.
Finite-size induction, using actual collapse injection, proves written height
invariance. Genuine normalization therefore computes the least fragment among
all originally admitted presentations, including raw nonnormal trees.
No supplied value-height or coverage hypothesis occurs. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.SourceOne.CanonicalHeight

open Height

private theorem aligned_heights (n : Nat) (as bs : List (RelativeTerm Nat))
    (hv : as.map (denote n) = bs.map (denote n))
    (hr : ∀ a ∈ as, ∀ b ∈ bs, denote n a = denote n b → a.height = b.height) :
    as.map RelativeTerm.height = bs.map RelativeTerm.height := by
  revert bs hv hr
  induction as with
  | nil =>
    intro bs hv _
    have hb : bs = [] := List.map_eq_nil_iff.mp hv.symm
    subst bs
    rfl
  | cons a as ih =>
    intro bs hv hr
    cases bs with
    | nil => simp only [List.map_cons, List.map_nil, List.cons_ne_nil] at hv
    | cons b bs =>
      have he := List.cons.inj hv
      have hh := hr a List.mem_cons_self b List.mem_cons_self he.1
      have ht := ih bs he.2 (fun x hx y hy =>
        hr x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))
      rw [List.map_cons, List.map_cons, hh, ht]

private theorem via_atoms (n : Nat) (t u : RelativeTerm Nat)
    (ht : admissible n t) (hu : admissible n u) (hnt : Normal n t) (hnu : Normal n u)
    (hv : denote n t = denote n u)
    (hr : ∀ x ∈ thetaAtoms t, ∀ y ∈ thetaAtoms u,
      denote n x = denote n y → x.height = y.height) : t.height = u.height := by
  have hw : (thetaAtoms t).map (denote n) = (thetaAtoms u).map (denote n) := by
    rw [thetaAtoms_denote_anf n t ht hnt, thetaAtoms_denote_anf n u hu hnu, hv]
  have hh := aligned_heights n (thetaAtoms t) (thetaAtoms u) hw hr
  apply Nat.le_antisymm
  · apply (height_le_iff_atoms t u.height).mpr
    intro a ha
    have hmem : a.height ∈ (thetaAtoms u).map RelativeTerm.height := by
      rw [← hh]
      exact List.mem_map.mpr ⟨a, ha, rfl⟩
    obtain ⟨b, hb, he⟩ := List.mem_map.mp hmem
    exact he ▸ atoms_height u b hb
  · apply (height_le_iff_atoms u t.height).mpr
    intro b hb
    have hmem : b.height ∈ (thetaAtoms t).map RelativeTerm.height := by
      rw [hh]
      exact List.mem_map.mpr ⟨b, hb, rfl⟩
    obtain ⟨a, ha, he⟩ := List.mem_map.mp hmem
    exact he ▸ atoms_height t a ha

/-- Actual finite normal inputs of equal value have equal written height. -/
theorem finite_height_invariant (n : Nat) (t u : RelativeTerm Nat)
    (ht : admissible n t) (hu : admissible n u)
    (hnt : Normal n t) (hnu : Normal n u) (hv : denote n t = denote n u) :
    t.height = u.height := by
  have H : ∀ z : Nat, ∀ t u : RelativeTerm Nat, t.size + u.size = z →
      admissible n t → admissible n u → Normal n t → Normal n u →
      denote n t = denote n u → t.height = u.height := by
    intro z
    induction z using Nat.strong_induction_on with
    | h z ih =>
      intro t u hs ht hu hnt hnu hv
      have recur (x y : RelativeTerm Nat) (hsize : x.size + y.size < z)
          (hx : admissible n x) (hy : admissible n y)
          (hnx : Normal n x) (hny : Normal n y) (he : denote n x = denote n y) :
          x.height = y.height := ih (x.size + y.size) hsize x y rfl hx hy hnx hny he
      have atoms_recur (hsize : ∀ x ∈ thetaAtoms t, ∀ y ∈ thetaAtoms u,
          x.size + y.size < z) : t.height = u.height := by
        apply via_atoms n t u ht hu hnt hnu hv
        intro x hx y hy he
        exact recur x y (hsize x hx y hy) (ht.thetaAtoms hx) (hu.thetaAtoms hy)
          (NormalSums.thetaAtoms hnt hx) (NormalSums.thetaAtoms hnu hy) he
      cases t with
      | sum a b =>
        apply atoms_recur
        intro x hx y hy
        have hxs := thetaAtoms_sum_size_lt a b x hx
        have hys := thetaAtoms_size_le u y hy
        omega
      | parameter p =>
        cases u with
        | sum a b =>
          apply atoms_recur
          intro x hx y hy
          have hxs := thetaAtoms_size_le (.parameter p) x hx
          have hys := thetaAtoms_sum_size_lt a b y hy
          omega
        | parameter v => rfl
        | theta k a =>
          cases ht with
          | parameter hp =>
            have hp0 := (parameter_lt_base_iff p).mp hp
            subst p
            have hz : denote n (.theta k a) = 0 := by
              simpa only [denote, eval, parameters, Nat.cast_zero] using hv.symm
            cases hu with
            | theta h0k hkn hsort ha =>
              exact False.elim ((sourceFiniteCollapse_pos 1 zero_lt_one n k hkn _).ne' hz)
      | theta k a =>
        cases u with
        | sum b c =>
          apply atoms_recur
          intro x hx y hy
          have hxs := thetaAtoms_size_le (.theta k a) x hx
          have hys := thetaAtoms_sum_size_lt b c y hy
          omega
        | parameter p =>
          cases hu with
          | parameter hp =>
            have hp0 := (parameter_lt_base_iff p).mp hp
            subst p
            have hz : denote n (.theta k a) = 0 := by
              simpa only [denote, eval, parameters, Nat.cast_zero] using hv
            cases ht with
            | theta h0k hkn hsort ha =>
              exact False.elim ((sourceFiniteCollapse_pos 1 zero_lt_one n k hkn _).ne' hz)
        | theta l b =>
          obtain ⟨hkl, he⟩ := theta_value_injective n k l a b ht hu hv
          subst l
          cases ht with
          | theta h0k hkn hsort ha =>
            cases hu with
            | theta h0k' hkn' hsort' hb =>
              have hsize : a.size + b.size < z := by
                have has := RelativeTerm.theta_arg_size_lt k a
                have hbs := RelativeTerm.theta_arg_size_lt k b
                omega
              have hh := recur a b hsize ha hb hnt hnu he
              exact congrArg (max (k + 1)) hh
  exact H (t.size + u.size) t u rfl ht hu hnt hnu hv

theorem height_invariant (n m : Nat) (t u : RelativeTerm Nat)
    (ht : admissible n t) (hu : admissible m u) (hnt : Normal n t) (hnu : Normal m u)
    (hv : PublicCodes.denote t = PublicCodes.denote u) : t.height = u.height := by
  let z := max t.height u.height
  have ht' := checked_admissible z t (admitted_checked n t ht) (le_max_left _ _)
  have hu' := checked_admissible z u (admitted_checked m u hu) (le_max_right _ _)
  exact finite_height_invariant z t u ht' hu'
    (Comparison.normal_transfer n z t ht ht' hnt)
    (Comparison.normal_transfer m z u hu hu' hnu)
    ((PublicCodes.denote_eq_finite z t ht').symm.trans
      (hv.trans (PublicCodes.denote_eq_finite z u hu')))

def canonicalHeightCode (c : Nat) : Nat := heightCode (Normalization.normalizeCode c)

theorem canonicalHeightCode_primrec : Primrec canonicalHeightCode :=
  heightCode_primrec.comp Normalization.Effective.normalizeCode_primrec

theorem normalCode_height_invariant (c d : Nat)
    (hc : Comparison.acceptedCode c = true) (hd : Comparison.acceptedCode d = true)
    (hv : PublicCodes.interpretation c = PublicCodes.interpretation d) :
    heightCode c = heightCode d := by
  obtain ⟨t, rfl, ht, hnt⟩ := (Comparison.acceptedCode_iff c).mp hc
  obtain ⟨u, rfl, hu, hnu⟩ := (Comparison.acceptedCode_iff d).mp hd
  simpa only [heightCode_code] using height_invariant _ _ t u
    ((check_iff _ t).mp ht) ((check_iff _ u).mp hu) hnt hnu
    (by simpa only [PublicCodes.interpretation_code] using hv)

theorem canonicalHeightCode_invariant (c d : Nat)
    (hc : PublicCodes.checkCode c = true) (hd : PublicCodes.checkCode d = true)
    (hv : PublicCodes.interpretation c = PublicCodes.interpretation d) :
    canonicalHeightCode c = canonicalHeightCode d := by
  have hs := Normalization.normalizeCode_checked c hc
  have hr := Normalization.normalizeCode_checked d hd
  exact normalCode_height_invariant _ _ hs.1 hr.1 (hs.2.trans (hv.trans hr.2.symm))

theorem canonicalHeightCode_normal (c : Nat) (hc : Comparison.acceptedCode c = true) :
    canonicalHeightCode c = heightCode c := by
  have hs := Normalization.normalizeCode_checked c (Bool.and_eq_true_iff.mp hc).1
  exact normalCode_height_invariant _ c hs.1 hc hs.2

theorem canonicalHeightCode_le_raw (c : Nat) (hc : PublicCodes.checkCode c = true) :
    canonicalHeightCode c ≤ heightCode c := by
  obtain ⟨t, rfl, ht⟩ := (PublicCodes.checkCode_iff c).mp hc
  simpa only [canonicalHeightCode, Normalization.normalizeCode_code, heightCode_code] using
    normalize_height t

theorem canonicalHeightCode_le_representation (c : Nat) (t : RelativeTerm Nat)
    (hc : PublicCodes.checkCode c = true) (ht : PublicCodes.check t = true)
    (hv : PublicCodes.interpretation c = PublicCodes.denote t) :
    canonicalHeightCode c ≤ t.height := by
  have hd : PublicCodes.checkCode t.code = true := by simpa only [PublicCodes.checkCode_code] using ht
  rw [canonicalHeightCode_invariant c t.code hc hd
    (by simpa only [PublicCodes.interpretation_code] using hv)]
  simpa only [heightCode_code] using canonicalHeightCode_le_raw t.code hd

/-- The least fragment ranges over ALL original admitted presentations. -/
theorem canonicalHeightCode_fragment_iff (n c : Nat) (hc : PublicCodes.checkCode c = true) :
    canonicalHeightCode c ≤ n ↔
      ∃ t : RelativeTerm Nat, admissible n t ∧ PublicCodes.denote t = PublicCodes.interpretation c := by
  constructor
  · intro hh
    obtain ⟨t, rfl, ht⟩ := (PublicCodes.checkCode_iff c).mp hc
    have ha := (check_iff (PublicCodes.fragment t) t).mp ht
    have hn : (Normalization.normalize t).height ≤ n := by
      simpa only [canonicalHeightCode, Normalization.normalizeCode_code, heightCode_code] using hh
    exact ⟨Normalization.normalize t,
      checked_admissible n _ (Normalization.normalize_checked _ t ha) hn,
      by simpa only [PublicCodes.interpretation_code] using Normalization.normalize_global_denote _ t ha⟩
  · rintro ⟨t, ht, hv⟩
    exact (canonicalHeightCode_le_representation c t hc (admitted_checked n t ht) hv.symm).trans
      (admissible_height_le n t ht)

theorem canonicalHeightCode_zero_iff (c : Nat) (hc : PublicCodes.checkCode c = true) :
    canonicalHeightCode c = 0 ↔ PublicCodes.interpretation c = 0 := by
  rw [← Nat.le_zero, canonicalHeightCode_fragment_iff 0 c hc]
  constructor
  · rintro ⟨t, ht, hv⟩
    have hz : denote 0 t = 0 := by
      clear hv
      induction ht with
      | @parameter p hp =>
        have hp0 := (parameter_lt_base_iff p).mp hp
        subst p
        simp [denote, eval, parameters]
      | @sum a b ha hb iha ihb =>
        change denote 0 a + denote 0 b = 0
        rw [iha, ihb, add_zero]
      | theta h0k hkn hsort ha ih => omega
    exact hv.symm.trans ((PublicCodes.denote_eq_finite 0 t ht).trans hz)
  · intro hv
    refine ⟨.parameter 0, .parameter ((parameter_lt_base_iff 0).mpr rfl), ?_⟩
    simpa only [PublicCodes.denote, eval, parameters, Nat.cast_zero] using hv.symm

end Alexander313.Wilken.RelativeTerm.SourceOne.CanonicalHeight
