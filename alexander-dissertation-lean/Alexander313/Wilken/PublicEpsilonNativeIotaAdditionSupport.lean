import Alexander313.Wilken.PublicEpsilonNativeIotaOrderInduction

/-!
# Actual absorption and reconstruction for iota addition

Source atoms retain original admission, Normality and full restriction at the literal public epsilon q.
The proved strict-order equivalence controls the real suffix-absorption
algorithm. Genuine target principal values then preserve the value of the
whole absorbed word. No additive-map or normalization oracle is supplied.
Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonIota.Addition

open OrderSupport
open Iota.OrderInduction (atoms_checked_normal source_atoms_value checked_theta_pos_principal)

theorem atoms_shape (t x : RelativeTerm Nat) (hx : x ∈ Comparison.atoms t) :
    (∃ p, x = .parameter p) ∨ ∃ k u, x = .theta k u := by
  revert hx
  induction t with
  | parameter p =>
    intro hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    exact Or.inl ⟨c, rfl⟩
  | sum t u iht ihu =>
    intro hx
    rcases List.mem_append.mp hx with hx | hx
    · exact iht hx
    · exact ihu hx
  | theta k u => intro hx; exact Or.inr ⟨k, u, List.mem_singleton.mp hx⟩

theorem transform_atom_principal (q root : Nat) (ha : rootCheck q root = true)
    (t x : RelativeTerm Nat) (ht : check q t = true)
    (hn : Comparison.Normal q t) (hr : Restricted q root t)
    (hx : x ∈ Comparison.atoms t) :
    0 < denote (betaCode q root) (transform q root x) ∧
      Ordinal.IsPrincipal (· + ·) (denote (betaCode q root) (transform q root x)) := by
  have hc := atoms_checked_normal _ t x ht hn hx
  have hxr := restricted_atoms q root t x hr hx
  have hg := Normalization.GoodAtoms.atoms q _ (source_checked q root ha) t
    (checked_admissible _ _ ht) hn x hx
  rcases atoms_shape t x hx with ⟨p, rfl⟩ | ⟨k, u, rfl⟩
  · rw [transform_low_value q root ha (.parameter p) hc.1 hxr (Nat.zero_le _)]
    exact hg.2.2
  · cases k with
    | zero =>
      rw [transform_low_value q root ha (.theta 0 u) hc.1 hxr le_rfl]
      exact hg.2.2
    | succ k =>
      have htarget := transform_checked q root ha (.theta (k + 1) u) hc.1 hxr
      rw [transform_theta_succ q root k ha u hc.1 hxr] at htarget ⊢
      exact checked_theta_pos_principal _ k _ htarget

theorem buildRev_restricted (q root : Nat) (as : List (RelativeTerm Nat))
    (hr : ∀ x ∈ as, Restricted q root x) : Restricted q root (Normalization.buildRev as) := by
  revert hr
  induction as with
  | nil =>
    intro hr
    simp only [Normalization.buildRev, Normalization.zeroTree, Restricted, fullList,
      RelativeTerm.PrincipalSupport.principalList, List.not_mem_nil, false_implies,
      implies_true, forall_const]
  | cons x xs ih =>
    intro hr
    exact (restricted_sum q root _ _).mpr
      ⟨ih (fun y hy => hr y (List.mem_cons_of_mem _ hy)), hr x List.mem_cons_self⟩

theorem buildAtoms_restricted (q root : Nat) (as : List (RelativeTerm Nat))
    (hr : ∀ x ∈ as, Restricted q root x) : Restricted q root (Normalization.buildAtoms as) :=
  buildRev_restricted q root as.reverse (fun x hx => hr x (List.mem_reverse.mp hx))

theorem transform_buildRev_value (q root n : Nat) (ha : rootCheck q root = true)
    (as : List (RelativeTerm Nat)) (hg : Normalization.GoodAtoms q n as)
    (hr : ∀ x ∈ as, Restricted q root x) :
    denote (betaCode q root) (transform q root (Normalization.buildRev as)) =
      principalSum (as.reverse.map (fun x => denote (betaCode q root) (transform q root x))) := by
  revert hg hr
  induction as with
  | nil =>
    intro hg hr
    have hc := Normalization.zeroTree_checked q (source_checked q root ha)
    have hz := transform_low_value q root ha Normalization.zeroTree hc
      (buildRev_restricted q root [] (by simp)) (Nat.zero_le _)
    simpa only [Normalization.buildRev, Normalization.zeroTree_denote,
      List.reverse_nil, List.map_nil, principalSum] using hz
  | cons x xs ih =>
    intro hg hr
    have htail : Normalization.GoodAtoms q n xs :=
      fun y hy => hg y (List.mem_cons_of_mem _ hy)
    have htailr : ∀ y ∈ xs, Restricted q root y :=
      fun y hy => hr y (List.mem_cons_of_mem _ hy)
    have hc := Comparison.admitted_checked q n (source_checked q root ha) _
      (Normalization.buildRev_admissible _ n (source_checked q root ha) xs htail)
    have hxc := Comparison.admitted_checked q n (source_checked q root ha) x
      (hg x List.mem_cons_self).1
    rw [Normalization.buildRev, transform_add q root ha _ x hc hxc, ih htail htailr,
      List.reverse_cons, List.map_append, principalSum_append]
    simp only [List.map_cons, List.map_nil, principalSum, add_zero]

theorem transform_buildAtoms_value (q root n : Nat) (ha : rootCheck q root = true)
    (as : List (RelativeTerm Nat)) (hg : Normalization.GoodAtoms q n as)
    (hr : ∀ x ∈ as, Restricted q root x) :
    denote (betaCode q root) (transform q root (Normalization.buildAtoms as)) =
      principalSum (as.map (fun x => denote (betaCode q root) (transform q root x))) := by
  simpa only [Normalization.buildAtoms, List.reverse_reverse] using
    transform_buildRev_value q root n ha as.reverse hg.reverse
      (fun x hx => hr x (List.mem_reverse.mp hx))

theorem prependAtom_mapped (q root n : Nat) (ha : rootCheck q root = true)
    (x : RelativeTerm Nat) (xs : List (RelativeTerm Nat))
    (hx : Normalization.GoodAtoms q n [x])
    (hxs : Normalization.GoodAtoms q n xs)
    (hrx : Restricted q root x) (hrxs : ∀ y ∈ xs, Restricted q root y) :
    (Normalization.prependAtom q x xs).map
      (fun z => denote (betaCode q root) (transform q root z)) =
      prependPrincipal (denote (betaCode q root) (transform q root x))
        (xs.map (fun z => denote (betaCode q root) (transform q root z))) := by
  cases xs with
  | nil => rfl
  | cons y ys =>
    have hxc := hx x List.mem_cons_self
    have hyc := hxs y List.mem_cons_self
    have hc := Comparison.less_correct q x y
      (Comparison.admitted_checked _ n (source_checked q root ha) x hxc.1)
      (Comparison.admitted_checked _ n (source_checked q root ha) y hyc.1) hxc.2.1 hyc.2.1
    have ht := transform_lt_iff q root ha x y
      (Comparison.admitted_checked _ n (source_checked q root ha) x hxc.1)
      (Comparison.admitted_checked _ n (source_checked q root ha) y hyc.1) hxc.2.1 hyc.2.1
      hrx (hrxs y List.mem_cons_self)
    cases hcmp : Comparison.less q x y with
    | false =>
      have hnlt : ¬ denote (betaCode q root) (transform q root x) <
          denote (betaCode q root) (transform q root y) := by
        intro h
        have he := hc.mpr (ht.mp h)
        simp only [hcmp, Bool.false_eq_true] at he
      simp [Normalization.prependAtom, prependPrincipal, hcmp, hnlt]
    | true =>
      simp [Normalization.prependAtom, prependPrincipal, hcmp, ht.mpr (hc.mp hcmp)]

theorem normalizeAtoms_mapped (q root n : Nat) (ha : rootCheck q root = true)
    (xs : List (RelativeTerm Nat)) (hg : Normalization.GoodAtoms q n xs)
    (hr : ∀ x ∈ xs, Restricted q root x) :
    (Normalization.normalizeAtoms q xs).map
      (fun x => denote (betaCode q root) (transform q root x)) =
      normalizePrincipal (xs.map (fun x => denote (betaCode q root) (transform q root x))) := by
  revert hg hr
  induction xs with
  | nil => intro hg hr; rfl
  | cons x xs ih =>
    intro hg hr
    have htail : Normalization.GoodAtoms q n xs :=
      fun y hy => hg y (List.mem_cons_of_mem _ hy)
    have htailr : ∀ y ∈ xs, Restricted q root y := fun y hy => hr y (List.mem_cons_of_mem _ hy)
    have hx : Normalization.GoodAtoms q n [x] := by
      intro y hy
      have he : y = x := List.mem_singleton.mp hy
      subst y
      exact hg x List.mem_cons_self
    rw [Normalization.normalizeAtoms,
      prependAtom_mapped q root n ha x _ hx htail.normalizeAtoms (hr x List.mem_cons_self)
        (fun y hy => htailr y (Normalization.normalizeAtoms_mem _ y xs hy)),
      ih htail htailr]
    rfl

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonIota.Addition
