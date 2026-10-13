import Alexander313.Wilken.HereditaryNativeIotaOrderInduction

/-!
# Actual absorption and reconstruction for iota addition

Source atoms retain their original admission, Normality and restriction.
The proved strict-order equivalence controls the real suffix-absorption
algorithm. Genuine target principal values then preserve the value of the
whole absorbed word. No additive-map or normalization oracle is supplied.
Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Iota.Addition

open NativePublicBridge (contextCode contextCode_checked)
open OrderInduction

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

theorem transform_atom_principal (s a : Nat) (ha : rootCheck s a = true)
    (t x : RelativeTerm Nat) (ht : check (contextCode s) t = true)
    (hn : Comparison.Normal (contextCode s) t) (hr : Restricted s a t)
    (hx : x ∈ Comparison.atoms t) :
    0 < denote (alphaCode s a) (transform s a x) ∧
      Ordinal.IsPrincipal (· + ·) (denote (alphaCode s a) (transform s a x)) := by
  have hc := atoms_checked_normal _ t x ht hn hx
  have hxr := restricted_atoms s a t x hr hx
  have hg := Normalization.GoodAtoms.atoms (contextCode s) _ (contextCode_checked s) t
    (checked_admissible _ _ ht) hn x hx
  rcases atoms_shape t x hx with ⟨p, rfl⟩ | ⟨k, u, rfl⟩
  · rw [transform_low_value s a ha (.parameter p) hc.1 hxr (Nat.zero_le _)]
    exact hg.2.2
  · cases k with
    | zero =>
      rw [transform_low_value s a ha (.theta 0 u) hc.1 hxr le_rfl]
      exact hg.2.2
    | succ k =>
      have htarget := transform_checked s a ha (.theta (k + 1) u) hc.1 hxr
      rw [transform_theta_succ s a k ha u hc.1 hxr] at htarget ⊢
      exact checked_theta_pos_principal _ k _ htarget

theorem buildRev_restricted (s a : Nat) (as : List (RelativeTerm Nat))
    (hr : ∀ x ∈ as, Restricted s a x) : Restricted s a (Normalization.buildRev as) := by
  revert hr
  induction as with
  | nil =>
    intro hr
    simp only [Normalization.buildRev, Normalization.zeroTree, Restricted, fullList,
      RelativeTerm.PrincipalSupport.principalList, List.not_mem_nil, false_implies,
      implies_true, forall_const]
  | cons x xs ih =>
    intro hr
    exact (restricted_sum s a _ _).mpr
      ⟨ih (fun y hy => hr y (List.mem_cons_of_mem _ hy)), hr x List.mem_cons_self⟩

theorem buildAtoms_restricted (s a : Nat) (as : List (RelativeTerm Nat))
    (hr : ∀ x ∈ as, Restricted s a x) : Restricted s a (Normalization.buildAtoms as) :=
  buildRev_restricted s a as.reverse (fun x hx => hr x (List.mem_reverse.mp hx))

theorem transform_buildRev_value (s a n : Nat) (ha : rootCheck s a = true)
    (as : List (RelativeTerm Nat)) (hg : Normalization.GoodAtoms (contextCode s) n as)
    (hr : ∀ x ∈ as, Restricted s a x) :
    denote (alphaCode s a) (transform s a (Normalization.buildRev as)) =
      principalSum (as.reverse.map (fun x => denote (alphaCode s a) (transform s a x))) := by
  revert hg hr
  induction as with
  | nil =>
    intro hg hr
    have hc := Normalization.zeroTree_checked (contextCode s) (contextCode_checked s)
    have hz := transform_low_value s a ha Normalization.zeroTree hc
      (buildRev_restricted s a [] (by simp)) (Nat.zero_le _)
    simpa only [Normalization.buildRev, Normalization.zeroTree_denote,
      List.reverse_nil, List.map_nil, principalSum] using hz
  | cons x xs ih =>
    intro hg hr
    have htail : Normalization.GoodAtoms (contextCode s) n xs :=
      fun y hy => hg y (List.mem_cons_of_mem _ hy)
    have htailr : ∀ y ∈ xs, Restricted s a y :=
      fun y hy => hr y (List.mem_cons_of_mem _ hy)
    have hc := Comparison.admitted_checked (contextCode s) n (contextCode_checked s) _
      (Normalization.buildRev_admissible _ n (contextCode_checked s) xs htail)
    have hxc := Comparison.admitted_checked (contextCode s) n (contextCode_checked s) x
      (hg x List.mem_cons_self).1
    rw [Normalization.buildRev, transform_add s a ha _ x hc hxc, ih htail htailr,
      List.reverse_cons, List.map_append, principalSum_append]
    simp only [List.map_cons, List.map_nil, principalSum, add_zero]

theorem transform_buildAtoms_value (s a n : Nat) (ha : rootCheck s a = true)
    (as : List (RelativeTerm Nat)) (hg : Normalization.GoodAtoms (contextCode s) n as)
    (hr : ∀ x ∈ as, Restricted s a x) :
    denote (alphaCode s a) (transform s a (Normalization.buildAtoms as)) =
      principalSum (as.map (fun x => denote (alphaCode s a) (transform s a x))) := by
  simpa only [Normalization.buildAtoms, List.reverse_reverse] using
    transform_buildRev_value s a n ha as.reverse hg.reverse
      (fun x hx => hr x (List.mem_reverse.mp hx))

theorem prependAtom_mapped (s a n : Nat) (ha : rootCheck s a = true)
    (x : RelativeTerm Nat) (xs : List (RelativeTerm Nat))
    (hx : Normalization.GoodAtoms (contextCode s) n [x])
    (hxs : Normalization.GoodAtoms (contextCode s) n xs)
    (hrx : Restricted s a x) (hrxs : ∀ y ∈ xs, Restricted s a y) :
    (Normalization.prependAtom (contextCode s) x xs).map
      (fun z => denote (alphaCode s a) (transform s a z)) =
      prependPrincipal (denote (alphaCode s a) (transform s a x))
        (xs.map (fun z => denote (alphaCode s a) (transform s a z))) := by
  cases xs with
  | nil => rfl
  | cons y ys =>
    have hxc := hx x List.mem_cons_self
    have hyc := hxs y List.mem_cons_self
    have hc := Comparison.less_correct (contextCode s) x y
      (Comparison.admitted_checked _ n (contextCode_checked s) x hxc.1)
      (Comparison.admitted_checked _ n (contextCode_checked s) y hyc.1) hxc.2.1 hyc.2.1
    have ht := transform_lt_iff s a ha x y
      (Comparison.admitted_checked _ n (contextCode_checked s) x hxc.1)
      (Comparison.admitted_checked _ n (contextCode_checked s) y hyc.1) hxc.2.1 hyc.2.1
      hrx (hrxs y List.mem_cons_self)
    cases hcmp : Comparison.less (contextCode s) x y with
    | false =>
      have hnlt : ¬ denote (alphaCode s a) (transform s a x) <
          denote (alphaCode s a) (transform s a y) := by
        intro h
        have he := hc.mpr (ht.mp h)
        simp only [hcmp, Bool.false_eq_true] at he
      simp [Normalization.prependAtom, prependPrincipal, hcmp, hnlt]
    | true =>
      simp [Normalization.prependAtom, prependPrincipal, hcmp, ht.mpr (hc.mp hcmp)]

theorem normalizeAtoms_mapped (s a n : Nat) (ha : rootCheck s a = true)
    (xs : List (RelativeTerm Nat)) (hg : Normalization.GoodAtoms (contextCode s) n xs)
    (hr : ∀ x ∈ xs, Restricted s a x) :
    (Normalization.normalizeAtoms (contextCode s) xs).map
      (fun x => denote (alphaCode s a) (transform s a x)) =
      normalizePrincipal (xs.map (fun x => denote (alphaCode s a) (transform s a x))) := by
  revert hg hr
  induction xs with
  | nil => intro hg hr; rfl
  | cons x xs ih =>
    intro hg hr
    have htail : Normalization.GoodAtoms (contextCode s) n xs :=
      fun y hy => hg y (List.mem_cons_of_mem _ hy)
    have htailr : ∀ y ∈ xs, Restricted s a y := fun y hy => hr y (List.mem_cons_of_mem _ hy)
    have hx : Normalization.GoodAtoms (contextCode s) n [x] := by
      intro y hy
      have he : y = x := List.mem_singleton.mp hy
      subst y
      exact hg x List.mem_cons_self
    rw [Normalization.normalizeAtoms,
      prependAtom_mapped s a n ha x _ hx htail.normalizeAtoms (hr x List.mem_cons_self)
        (fun y hy => htailr y (Normalization.normalizeAtoms_mem _ y xs hy)),
      ih htail htailr]
    rfl

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Iota.Addition
