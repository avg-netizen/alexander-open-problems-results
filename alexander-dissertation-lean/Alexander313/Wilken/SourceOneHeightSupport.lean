import Alexander313.Wilken.SourceOneNormalizationPrimitive

/-!
# Written height at the original base one

The base-one case has only zero parameters, so its genuine theta atom list
records every contribution to written height. Actual atom absorption cannot
increase this height. Genuine finite collapse injection identifies the index
and argument value of equal theta values. These are structural supporting
lemmas for value height, without a supplied height or normality oracle.
All proof candidates remain uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.SourceOne.Height

theorem atoms_height (t s : RelativeTerm Nat) (ha : s ∈ thetaAtoms t) :
    s.height ≤ t.height := by
  revert ha
  induction t with
  | parameter p => intro ha; simp [thetaAtoms] at ha
  | sum a b iha ihb =>
    intro ha
    rcases List.mem_append.mp ha with ha | ha
    · exact (iha ha).trans (le_max_left _ _)
    · exact (ihb ha).trans (le_max_right _ _)
  | theta k a =>
    intro ha
    have he := List.mem_singleton.mp ha
    subst s
    exact le_rfl

theorem height_le_iff_atoms (t : RelativeTerm Nat) (n : Nat) :
    t.height ≤ n ↔ ∀ a ∈ thetaAtoms t, a.height ≤ n := by
  constructor
  · intro ht a ha; exact (atoms_height t a ha).trans ht
  · intro ha
    revert ha
    induction t with
    | parameter p => intro _; exact Nat.zero_le n
    | sum a b iha ihb =>
      intro ha
      exact max_le
        (iha (fun x hx => ha x (List.mem_append.mpr (Or.inl hx))))
        (ihb (fun x hx => ha x (List.mem_append.mpr (Or.inr hx))))
    | theta k a => intro ha; exact ha (.theta k a) List.mem_cons_self

theorem height_eq_zero_of_atoms_nil (t : RelativeTerm Nat) (ht : thetaAtoms t = []) :
    t.height = 0 := by
  apply Nat.le_zero.mp
  apply (height_le_iff_atoms t 0).mpr
  intro a ha
  rw [ht] at ha
  exact False.elim (List.not_mem_nil ha)

theorem buildRev_height (as : List (RelativeTerm Nat)) (n : Nat)
    (ha : ∀ a ∈ as, a.height ≤ n) : (Normalization.buildRev as).height ≤ n := by
  revert ha
  induction as with
  | nil => intro _; exact Nat.zero_le n
  | cons a as ih =>
    intro ha
    exact max_le (ih (fun b hb => ha b (List.mem_cons_of_mem _ hb)))
      (ha a List.mem_cons_self)

theorem buildAtoms_height (as : List (RelativeTerm Nat)) (n : Nat)
    (ha : ∀ a ∈ as, a.height ≤ n) : (Normalization.buildAtoms as).height ≤ n :=
  buildRev_height as.reverse n (fun a h => ha a (List.mem_reverse.mp h))

theorem normalize_height (t : RelativeTerm Nat) : (Normalization.normalize t).height ≤ t.height := by
  induction t with
  | parameter p => exact le_rfl
  | theta k a ih => exact max_le_max le_rfl ih
  | sum a b iha ihb =>
    apply buildAtoms_height
    intro x hx
    have hm := Normalization.normalizeAtoms_mem x _ hx
    rcases List.mem_append.mp hm with hm | hm
    · exact ((atoms_height _ x hm).trans iha).trans (le_max_left _ _)
    · exact ((atoms_height _ x hm).trans ihb).trans (le_max_right _ _)

theorem admissible_height_le (n : Nat) (t : RelativeTerm Nat) (ht : admissible n t) :
    t.height ≤ n := by
  induction ht with
  | parameter hp => exact Nat.zero_le n
  | sum ha hb iha ihb => exact max_le iha ihb
  | theta h0k hkn hsort ha ih => exact max_le (by omega) ih

theorem admitted_checked (n : Nat) (t : RelativeTerm Nat) (ht : admissible n t) :
    PublicCodes.check t = true :=
  (PublicCodes.check_iff_finite_admissible t).mpr ⟨n, ht⟩

theorem checked_admissible (n : Nat) (t : RelativeTerm Nat)
    (ht : PublicCodes.check t = true) (hh : t.height ≤ n) : admissible n t :=
  (check_iff n t).mp (PublicCodes.check_transfer (PublicCodes.fragment t) t ht n hh)

/-- Equal genuine finite theta values force equal levels and argument values. -/
theorem theta_value_injective (n k l : Nat) (a b : RelativeTerm Nat)
    (ha : admissible n (.theta k a)) (hb : admissible n (.theta l b))
    (hv : denote n (.theta k a) = denote n (.theta l b)) :
    k = l ∧ denote n a = denote n b := by
  have hk : k = l := by
    rcases lt_trichotomy k l with hkl | he | hlk
    · exact False.elim ((theta_lt_of_level_lt n k l a b ha hb hkl).ne hv)
    · exact he
    · exact False.elim ((theta_lt_of_level_lt n l k b a hb ha hlk).ne hv.symm)
  subst l
  cases ha with
  | theta h0k hkn hsorta haa =>
    cases hb with
    | theta h0k' hkn' hsortb hbb =>
      have hna : sourceNotation 1 n 0 (denote n a) := by
        rw [sourceNotation, if_pos (by omega : 0 < n)]
        exact haa.denote
      have hnb : sourceNotation 1 n 0 (denote n b) := by
        rw [sourceNotation, if_pos (by omega : 0 < n)]
        exact hbb.denote
      exact ⟨rfl, sourceFiniteCollapse_injective_on 1 n k hkn
        ⟨sourceNotation_upward 1 n 0 (k + 1) (by omega) (by omega) hna, hsorta⟩
        ⟨sourceNotation_upward 1 n 0 (k + 1) (by omega) (by omega) hnb, hsortb⟩ hv⟩

end Alexander313.Wilken.RelativeTerm.SourceOne.Height
