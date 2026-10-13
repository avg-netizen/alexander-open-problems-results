import Alexander313.Wilken.SourceOneNativeIotaOrder
import Alexander313.Wilken.SourceOneOmegaQuotientSupport

/-!
# Original source-one absorption under actual iota

The ORIGINAL check0, Theta.Normal and zero-omitting thetaAtoms dictionary
controls source suffix absorption. Actual source-one iota order and ANF
identify mapped principal values. Native admission appears only at the
genuine alpha target; no native base-one source parser is used. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.Addition

open OrderSupport

theorem transform_atom_principal (a : Nat) (ha : rootCheck a = true)
    (t x : RelativeTerm Nat) (ht : check 0 t = true)
    (hn : Theta.Normal 0 t) (hr : Restricted a t) (hx : x ∈ thetaAtoms t) :
    0 < NativeContext.denote (alphaCode a) (transform a x) ∧
      Ordinal.IsPrincipal (· + ·) (NativeContext.denote (alphaCode a) (transform a x)) := by
  apply (canonicalANF_normal (NativeContext.denote (alphaCode a) (transform a t))).1
  rw [← transform_atoms_anf a ha t ht hn hr]
  exact List.mem_map.mpr ⟨x, hx, rfl⟩

/-- Genuine original ANF singleton shape derives positive-principal
preservation without a supplied transformed-principal premise. -/
theorem transform_positive_principal (a : Nat) (ha : rootCheck a = true)
    (t : RelativeTerm Nat) (ht : check 0 t = true) (hn : Theta.Normal 0 t)
    (hr : Restricted a t) (hp : 0 < denote 0 t)
    (hprincipal : Ordinal.IsPrincipal (· + ·) (denote 0 t)) :
    0 < NativeContext.denote (alphaCode a) (transform a t) ∧
      Ordinal.IsPrincipal (· + ·) (NativeContext.denote (alphaCode a) (transform a t)) := by
  have hlength : (thetaAtoms t).length = 1 := by
    have h := congrArg List.length ((source_atoms_anf t ht hn).trans
      (canonicalANF_principal hp hprincipal))
    simpa only [List.length_map, List.length_singleton] using h
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hlength
  have hmem : x ∈ thetaAtoms t := by rw [hx]; exact List.mem_singleton_self _
  have hv : NativeContext.denote (alphaCode a) (transform a t) =
      NativeContext.denote (alphaCode a) (transform a x) := by
    have h := mapped_atoms_value a ha t ht hn hr
    simpa only [hx, List.map_cons, List.map_nil, principalSum, add_zero] using h.symm
  rw [hv]
  exact transform_atom_principal a ha t x ht hn hr hmem

theorem transform_buildRev_value (a n : Nat) (ha : rootCheck a = true)
    (as : List (RelativeTerm Nat)) (hg : Theta.Normalization.GoodAtoms 0 n as)
    (hr : ∀ x ∈ as, Restricted a x) :
    NativeContext.denote (alphaCode a) (transform a (Theta.Normalization.buildRev 0 as)) =
      principalSum (as.reverse.map (fun x => NativeContext.denote (alphaCode a) (transform a x))) := by
  revert hg hr
  induction as with
  | nil =>
    intro hg hr
    have hz := transform_low_value a ha (zeroTree 0)
      (Bool.and_eq_true.mp (zeroTree_lowCheck 0)).1
      (OmegaQuotient.zero_restricted a) (Nat.zero_le _)
    simpa only [Theta.Normalization.buildRev, zeroTree_denote,
      List.reverse_nil, List.map_nil, principalSum] using hz
  | cons x xs ih =>
    intro hg hr
    have htail : Theta.Normalization.GoodAtoms 0 n xs :=
      fun y hy => hg y (List.mem_cons_of_mem _ hy)
    have htailr : ∀ y ∈ xs, Restricted a y :=
      fun y hy => hr y (List.mem_cons_of_mem _ hy)
    have hc := Theta.admitted_checked (Theta.Normalization.buildRev_admissible 0 n xs htail)
    have hxc := Theta.admitted_checked (hg x List.mem_cons_self).1
    rw [Theta.Normalization.buildRev, transform_add a ha _ x hc hxc, ih htail htailr,
      List.reverse_cons, List.map_append, principalSum_append]
    simp only [List.map_cons, List.map_nil, principalSum, add_zero]

theorem transform_buildAtoms_value (a n : Nat) (ha : rootCheck a = true)
    (as : List (RelativeTerm Nat)) (hg : Theta.Normalization.GoodAtoms 0 n as)
    (hr : ∀ x ∈ as, Restricted a x) :
    NativeContext.denote (alphaCode a) (transform a (Theta.Normalization.buildAtoms 0 as)) =
      principalSum (as.map (fun x => NativeContext.denote (alphaCode a) (transform a x))) := by
  simpa only [Theta.Normalization.buildAtoms, List.reverse_reverse] using
    transform_buildRev_value a n ha as.reverse hg.reverse
      (fun x hx => hr x (List.mem_reverse.mp hx))

theorem prependAtom_mapped (a n : Nat) (ha : rootCheck a = true)
    (x : RelativeTerm Nat) (xs : List (RelativeTerm Nat))
    (hx : Theta.Normalization.GoodAtoms 0 n [x])
    (hxs : Theta.Normalization.GoodAtoms 0 n xs)
    (hrx : Restricted a x) (hrxs : ∀ y ∈ xs, Restricted a y) :
    (Theta.Normalization.prependAtom 0 x xs).map
      (fun z => NativeContext.denote (alphaCode a) (transform a z)) =
      prependPrincipal (NativeContext.denote (alphaCode a) (transform a x))
        (xs.map (fun z => NativeContext.denote (alphaCode a) (transform a z))) := by
  cases xs with
  | nil => rfl
  | cons y ys =>
    have hxc := hx x List.mem_cons_self
    have hyc := hxs y List.mem_cons_self
    have hc := Theta.less_correct 0 x y (Theta.admitted_checked hxc.1)
      (Theta.admitted_checked hyc.1) hxc.2.1 hyc.2.1
    have ht := transform_lt_iff a ha x y (Theta.admitted_checked hxc.1)
      (Theta.admitted_checked hyc.1) hxc.2.1 hyc.2.1 hrx (hrxs y List.mem_cons_self)
    cases hcmp : Theta.less 0 x y with
    | false =>
      have hnlt : ¬ NativeContext.denote (alphaCode a) (transform a x) <
          NativeContext.denote (alphaCode a) (transform a y) := by
        intro h
        have he := hc.mpr (ht.mp h)
        simp only [hcmp, Bool.false_eq_true] at he
      simp [Theta.Normalization.prependAtom, prependPrincipal, hcmp, hnlt]
    | true =>
      simp [Theta.Normalization.prependAtom, prependPrincipal, hcmp, ht.mpr (hc.mp hcmp)]

theorem normalizeAtoms_mapped (a n : Nat) (ha : rootCheck a = true)
    (xs : List (RelativeTerm Nat)) (hg : Theta.Normalization.GoodAtoms 0 n xs)
    (hr : ∀ x ∈ xs, Restricted a x) :
    (Theta.Normalization.normalizeAtoms 0 xs).map
      (fun x => NativeContext.denote (alphaCode a) (transform a x)) =
      normalizePrincipal (xs.map (fun x => NativeContext.denote (alphaCode a) (transform a x))) := by
  revert hg hr
  induction xs with
  | nil => intro hg hr; rfl
  | cons x xs ih =>
    intro hg hr
    have htail : Theta.Normalization.GoodAtoms 0 n xs :=
      fun y hy => hg y (List.mem_cons_of_mem _ hy)
    have htailr : ∀ y ∈ xs, Restricted a y := fun y hy => hr y (List.mem_cons_of_mem _ hy)
    have hx : Theta.Normalization.GoodAtoms 0 n [x] := by
      intro y hy
      have he : y = x := List.mem_singleton.mp hy
      subst y
      exact hg x List.mem_cons_self
    rw [Theta.Normalization.normalizeAtoms,
      prependAtom_mapped a n ha x _ hx htail.normalizeAtoms (hr x List.mem_cons_self)
        (fun y hy => htailr y (Theta.Normalization.normalizeAtoms_mem 0 y xs hy)),
      ih htail htailr]
    rfl

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.Addition
