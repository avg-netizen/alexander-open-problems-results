import Alexander313.Wilken.HereditaryThetaComparison

/-!
# Actual principal-word normalization at every hereditary level

The executing hereditary comparator performs literal suffix absorption.
Mapping the resulting atoms to their real source values agrees with the
already proved ordinal principal normalization. Reconstruction uses the
actual hereditary zero tree, and its source sums retain the required final
principal convention. The following invariants are proved for constructed
atoms, rather than supplied semantic normalization assumptions. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.Theta.Normalization

def prependAtom (r : Nat) (a : RelativeTerm Nat) : List (RelativeTerm Nat) → List (RelativeTerm Nat)
  | [] => [a]
  | b :: bs => cond (less r a b) (b :: bs) (a :: b :: bs)

def normalizeAtoms (r : Nat) : List (RelativeTerm Nat) → List (RelativeTerm Nat)
  | [] => []
  | a :: as => prependAtom r a (normalizeAtoms r as)

theorem prependAtom_mem (r : Nat) (a p : RelativeTerm Nat) (as : List (RelativeTerm Nat))
    (hp : p ∈ prependAtom r a as) : p = a ∨ p ∈ as := by
  cases as with
  | nil => simpa [prependAtom] using hp
  | cons b bs =>
    cases hcmp : less r a b with
    | false => simpa [prependAtom, hcmp] using hp
    | true => exact Or.inr (by simpa [prependAtom, hcmp] using hp)

theorem normalizeAtoms_mem (r : Nat) (p : RelativeTerm Nat) (as : List (RelativeTerm Nat))
    (hp : p ∈ normalizeAtoms r as) : p ∈ as := by
  revert hp
  induction as with
  | nil => intro hp; simp [normalizeAtoms] at hp
  | cons a as ih =>
    intro hp
    rcases prependAtom_mem r a p _ hp with rfl | hp
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih hp)

def GoodAtoms (r n : Nat) (as : List (RelativeTerm Nat)) : Prop :=
  ∀ a ∈ as, admissible r n a ∧ Normal r a ∧
    0 < denote r a ∧ Ordinal.IsPrincipal (· + ·) (denote r a)

theorem GoodAtoms.atoms (r n : Nat) (t : RelativeTerm Nat)
    (ht : admissible r n t) (hn : Normal r t) : GoodAtoms r n (atoms r t) := by
  intro a ha
  have hprincipal := (atoms_denote_normal r n t ht hn).1 _
    (List.mem_map.mpr ⟨a, ha, rfl⟩)
  exact ⟨atoms_admissible r n t a ht hn ha, atoms_normal r n t a ht hn ha,
    hprincipal.1, hprincipal.2⟩

theorem GoodAtoms.append {r n : Nat} {as bs : List (RelativeTerm Nat)}
    (ha : GoodAtoms r n as) (hb : GoodAtoms r n bs) : GoodAtoms r n (as ++ bs) := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact ha p hp
  · exact hb p hp

theorem GoodAtoms.reverse {r n : Nat} {as : List (RelativeTerm Nat)}
    (ha : GoodAtoms r n as) : GoodAtoms r n as.reverse :=
  fun p hp => ha p (List.mem_reverse.mp hp)

theorem GoodAtoms.normalizeAtoms {r n : Nat} {as : List (RelativeTerm Nat)}
    (ha : GoodAtoms r n as) : GoodAtoms r n (normalizeAtoms r as) :=
  fun p hp => ha p (normalizeAtoms_mem r p as hp)

private theorem prependAtom_map (r n : Nat) (a : RelativeTerm Nat) (as : List (RelativeTerm Nat))
    (ha : admissible r n a) (hna : Normal r a)
    (has : ∀ b ∈ as, admissible r n b ∧ Normal r b) :
    (prependAtom r a as).map (denote r) = prependPrincipal (denote r a) (as.map (denote r)) := by
  classical
  cases as with
  | nil => rfl
  | cons b bs =>
    have hb := has b (List.mem_cons_self)
    have hc := less_correct r a b (admitted_checked ha) (admitted_checked hb.1) hna hb.2
    cases hcmp : less r a b with
    | false =>
      have hnlt : ¬denote r a < denote r b := by
        intro h
        have htrue := hc.mpr h
        simp only [hcmp, Bool.false_eq_true] at htrue
      simp [prependAtom, prependPrincipal, hcmp, hnlt]
    | true => simp [prependAtom, prependPrincipal, hcmp, hc.mp hcmp]

theorem normalizeAtoms_map (r n : Nat) (as : List (RelativeTerm Nat)) (ha : GoodAtoms r n as) :
    (normalizeAtoms r as).map (denote r) = normalizePrincipal (as.map (denote r)) := by
  revert ha
  induction as with
  | nil => intro _; rfl
  | cons a as ih =>
    intro ha
    have hhead := ha a (List.mem_cons_self)
    have htail : GoodAtoms r n as := fun b hb => ha b (List.mem_cons_of_mem _ hb)
    rw [normalizeAtoms, prependAtom_map r n a _ hhead.1 hhead.2.1
      (fun b hb => ⟨(htail.normalizeAtoms b hb).1, (htail.normalizeAtoms b hb).2.1⟩), ih htail]
    rfl

theorem normalizeAtoms_normal (r n : Nat) (as : List (RelativeTerm Nat)) (ha : GoodAtoms r n as) :
    IsAdditiveNormalForm ((normalizeAtoms r as).map (denote r)) := by
  rw [normalizeAtoms_map r n as ha]
  apply normalizePrincipal_normal
  intro p hp
  obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hp
  exact (ha a ha').2.2

theorem normalizeAtoms_denote (r n : Nat) (as : List (RelativeTerm Nat)) (ha : GoodAtoms r n as) :
    principalSum ((normalizeAtoms r as).map (denote r)) = principalSum (as.map (denote r)) := by
  rw [normalizeAtoms_map r n as ha]
  apply principalSum_normalizePrincipal
  intro p hp
  obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hp
  exact (ha a ha').2.2

theorem zeroTree_normal (r : Nat) : Normal r (zeroTree r) := by
  induction r with
  | zero => trivial
  | succ r ih =>
    simpa only [zeroTree, normal_parameter_succ, decode_code, Option.getD_some] using ih

private theorem zeroTree_height (r : Nat) : (zeroTree r).height = 0 := by
  cases r <;> rfl

theorem zeroTree_admissible (r n : Nat) : admissible r n (zeroTree r) :=
  checked_admissible r n (zeroTree r) (Bool.and_eq_true_iff.mp (zeroTree_lowCheck r)).1
    (by rw [zeroTree_height]; exact Nat.zero_le n)

def buildRev (r : Nat) : List (RelativeTerm Nat) → RelativeTerm Nat
  | [] => zeroTree r
  | a :: as => .sum (buildRev r as) a

def buildAtoms (r : Nat) (as : List (RelativeTerm Nat)) : RelativeTerm Nat :=
  buildRev r as.reverse

theorem buildRev_denote (r : Nat) (as : List (RelativeTerm Nat)) :
    denote r (buildRev r as) = principalSum (as.reverse.map (denote r)) := by
  induction as with
  | nil => simp only [buildRev, zeroTree_denote, List.reverse_nil, List.map_nil, principalSum]
  | cons a as ih =>
    change denote r (buildRev r as) + denote r a = _
    rw [ih, List.reverse_cons, List.map_append, principalSum_append]
    simp [principalSum]

theorem buildRev_admissible (r n : Nat) (as : List (RelativeTerm Nat)) (ha : GoodAtoms r n as) :
    admissible r n (buildRev r as) := by
  revert ha
  induction as with
  | nil => intro _; exact zeroTree_admissible r n
  | cons a as ih =>
    intro ha
    have hp := ih (fun b hb => ha b (List.mem_cons_of_mem _ hb))
    have hhead := (ha a (List.mem_cons_self)).1
    exact ⟨⟨hp.1, hhead.1⟩, .sum hp.2 hhead.2⟩

theorem buildRev_normal (r n : Nat) (as : List (RelativeTerm Nat)) (ha : GoodAtoms r n as)
    (hn : IsAdditiveNormalForm (as.reverse.map (denote r))) : Normal r (buildRev r as) := by
  revert ha hn
  induction as with
  | nil => intro _ _; exact zeroTree_normal r
  | cons a as ih =>
    intro ha hn
    have hfull : IsAdditiveNormalForm ((as.reverse.map (denote r)) ++ [denote r a]) := by
      simpa only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil] using hn
    have hprefix : IsAdditiveNormalForm (as.reverse.map (denote r)) :=
      ⟨fun p hp => hfull.1 p (List.mem_append_left _ hp),
        (List.pairwise_append.mp hfull.2).1⟩
    apply Normal.sum (ih (fun b hb => ha b (List.mem_cons_of_mem _ hb)) hprefix)
      (ha a (List.mem_cons_self)).2.1
    refine Or.inr ⟨as.reverse.map (denote r), hfull, ?_, ?_⟩
    · exact (buildRev_denote r as).symm
    · rw [principalSum_append]
      simp only [principalSum, add_zero]
      rw [← buildRev_denote r as]
      rfl

theorem buildAtoms_denote (r : Nat) (as : List (RelativeTerm Nat)) :
    denote r (buildAtoms r as) = principalSum (as.map (denote r)) := by
  simpa only [buildAtoms, List.reverse_reverse] using buildRev_denote r as.reverse

theorem buildAtoms_admissible (r n : Nat) (as : List (RelativeTerm Nat)) (ha : GoodAtoms r n as) :
    admissible r n (buildAtoms r as) := buildRev_admissible r n as.reverse ha.reverse

theorem buildAtoms_normal (r n : Nat) (as : List (RelativeTerm Nat)) (ha : GoodAtoms r n as)
    (hn : IsAdditiveNormalForm (as.map (denote r))) : Normal r (buildAtoms r as) := by
  apply buildRev_normal r n as.reverse ha.reverse
  simpa only [List.reverse_reverse] using hn

end Alexander313.Wilken.RelativeTerm.Hereditary.Theta.Normalization
