import Alexander313.Wilken.SourceOneNormalComparison

/-!
# Executing principal-atom normalization at base one

The already constructed tree comparator determines which earlier principal
atoms are absorbed by a larger suffix. Mapping this literal computation to
actual denotations gives exactly the existing ordinal principal normalization.
Left-associated reconstruction respects the final-principal-summand source
convention, including its permitted zero prefix.

The list hypotheses below are ordinary intermediate induction invariants.
The tree normalization in the companion file constructs them from admission;
no semantic normalization or comparison contract is supplied to its theorem.
-/

namespace Alexander313.Wilken.RelativeTerm.SourceOne.Normalization

def prependAtom (a : RelativeTerm Nat) : List (RelativeTerm Nat) → List (RelativeTerm Nat)
  | [] => [a]
  | b :: bs => cond (Comparison.less a b) (b :: bs) (a :: b :: bs)

def normalizeAtoms : List (RelativeTerm Nat) → List (RelativeTerm Nat)
  | [] => []
  | a :: as => prependAtom a (normalizeAtoms as)

theorem prependAtom_mem (a p : RelativeTerm Nat) (as : List (RelativeTerm Nat))
    (hp : p ∈ prependAtom a as) : p = a ∨ p ∈ as := by
  cases as with
  | nil => simpa [prependAtom] using hp
  | cons b bs =>
    cases hcmp : Comparison.less a b with
    | false => simpa [prependAtom, hcmp] using hp
    | true => exact Or.inr (by simpa [prependAtom, hcmp] using hp)

theorem normalizeAtoms_mem (p : RelativeTerm Nat) (as : List (RelativeTerm Nat))
    (hp : p ∈ normalizeAtoms as) : p ∈ as := by
  revert hp
  induction as with
  | nil => intro hp; simp [normalizeAtoms] at hp
  | cons a as ih =>
    intro hp
    rcases prependAtom_mem a p _ hp with rfl | hp
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih hp)

def GoodAtoms (n : Nat) (as : List (RelativeTerm Nat)) : Prop :=
  ∀ a ∈ as, admissible n a ∧ Normal n a ∧
    0 < denote n a ∧ Ordinal.IsPrincipal (· + ·) (denote n a)

theorem GoodAtoms.thetaAtoms (n : Nat) (t : RelativeTerm Nat)
    (ht : admissible n t) (hn : Normal n t) : GoodAtoms n (thetaAtoms t) := by
  intro a ha
  have hprincipal := (thetaAtoms_denote_normal n t ht hn).1 _
    (List.mem_map.mpr ⟨a, ha, rfl⟩)
  exact ⟨ht.thetaAtoms ha, NormalSums.thetaAtoms hn ha, hprincipal.1, hprincipal.2⟩

theorem GoodAtoms.append {n : Nat} {as bs : List (RelativeTerm Nat)}
    (ha : GoodAtoms n as) (hb : GoodAtoms n bs) : GoodAtoms n (as ++ bs) := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact ha p hp
  · exact hb p hp

theorem GoodAtoms.reverse {n : Nat} {as : List (RelativeTerm Nat)}
    (ha : GoodAtoms n as) : GoodAtoms n as.reverse := by
  intro p hp
  exact ha p (List.mem_reverse.mp hp)

theorem GoodAtoms.normalizeAtoms {n : Nat} {as : List (RelativeTerm Nat)}
    (ha : GoodAtoms n as) : GoodAtoms n (normalizeAtoms as) :=
  fun p hp => ha p (normalizeAtoms_mem p as hp)

private theorem prependAtom_map (n : Nat) (a : RelativeTerm Nat) (as : List (RelativeTerm Nat))
    (ha : admissible n a) (hna : Normal n a)
    (has : ∀ b ∈ as, admissible n b ∧ Normal n b) :
    (prependAtom a as).map (denote n) = prependPrincipal (denote n a) (as.map (denote n)) := by
  classical
  cases as with
  | nil => rfl
  | cons b bs =>
    have hb := has b (List.mem_cons_self)
    have hc := Comparison.less_correct n a b ha hb.1 hna hb.2
    cases hcmp : Comparison.less a b with
    | false =>
      have hnlt : ¬denote n a < denote n b := by
        intro h
        have htrue := hc.mpr h
        simp only [hcmp, Bool.false_eq_true] at htrue
      simp [prependAtom, prependPrincipal, hcmp, hnlt]
    | true => simp [prependAtom, prependPrincipal, hcmp, hc.mp hcmp]

theorem normalizeAtoms_map (n : Nat) (as : List (RelativeTerm Nat)) (ha : GoodAtoms n as) :
    (normalizeAtoms as).map (denote n) = normalizePrincipal (as.map (denote n)) := by
  revert ha
  induction as with
  | nil => intro _; rfl
  | cons a as ih =>
    intro ha
    have hhead := ha a (List.mem_cons_self)
    have htail : GoodAtoms n as := fun b hb => ha b (List.mem_cons_of_mem _ hb)
    rw [normalizeAtoms, prependAtom_map n a _ hhead.1 hhead.2.1
      (fun b hb => ⟨(htail.normalizeAtoms b hb).1, (htail.normalizeAtoms b hb).2.1⟩), ih htail]
    rfl

theorem normalizeAtoms_normal (n : Nat) (as : List (RelativeTerm Nat)) (ha : GoodAtoms n as) :
    IsAdditiveNormalForm ((normalizeAtoms as).map (denote n)) := by
  rw [normalizeAtoms_map n as ha]
  apply normalizePrincipal_normal
  intro p hp
  obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hp
  exact (ha a ha').2.2

theorem normalizeAtoms_denote (n : Nat) (as : List (RelativeTerm Nat)) (ha : GoodAtoms n as) :
    principalSum ((normalizeAtoms as).map (denote n)) = principalSum (as.map (denote n)) := by
  rw [normalizeAtoms_map n as ha]
  apply principalSum_normalizePrincipal
  intro p hp
  obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hp
  exact (ha a ha').2.2

def buildRev : List (RelativeTerm Nat) → RelativeTerm Nat
  | [] => .parameter 0
  | a :: as => .sum (buildRev as) a

def buildAtoms (as : List (RelativeTerm Nat)) : RelativeTerm Nat := buildRev as.reverse

theorem buildRev_denote (n : Nat) (as : List (RelativeTerm Nat)) :
    denote n (buildRev as) = principalSum (as.reverse.map (denote n)) := by
  induction as with
  | nil => simp [buildRev, denote, eval, parameters, principalSum]
  | cons a as ih =>
    change denote n (buildRev as) + denote n a = _
    rw [ih, List.reverse_cons, List.map_append, principalSum_append]
    simp [principalSum]

theorem buildRev_admissible (n : Nat) (as : List (RelativeTerm Nat)) (ha : GoodAtoms n as) :
    admissible n (buildRev as) := by
  revert ha
  induction as with
  | nil => intro _; exact .parameter ((parameter_lt_base_iff 0).mpr rfl)
  | cons a as ih =>
    intro ha
    exact .sum (ih (fun b hb => ha b (List.mem_cons_of_mem _ hb)))
      (ha a (List.mem_cons_self)).1

theorem buildRev_normal (n : Nat) (as : List (RelativeTerm Nat)) (ha : GoodAtoms n as)
    (hn : IsAdditiveNormalForm (as.reverse.map (denote n))) : Normal n (buildRev as) := by
  revert ha hn
  induction as with
  | nil => intro _ _; trivial
  | cons a as ih =>
    intro ha hn
    have hfull : IsAdditiveNormalForm ((as.reverse.map (denote n)) ++ [denote n a]) := by
      simpa only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil] using hn
    have hprefix : IsAdditiveNormalForm (as.reverse.map (denote n)) :=
      ⟨fun p hp => hfull.1 p (List.mem_append_left _ hp),
        (List.pairwise_append.mp hfull.2).1⟩
    refine ⟨ih (fun b hb => ha b (List.mem_cons_of_mem _ hb)) hprefix,
      (ha a (List.mem_cons_self)).2.1, Or.inr ⟨as.reverse.map (denote n), hfull, ?_, ?_⟩⟩
    · exact (buildRev_denote n as).symm
    · rw [principalSum_append]
      simp only [principalSum, add_zero]
      rw [← buildRev_denote n as]
      rfl

theorem buildAtoms_denote (n : Nat) (as : List (RelativeTerm Nat)) :
    denote n (buildAtoms as) = principalSum (as.map (denote n)) := by
  simpa only [buildAtoms, List.reverse_reverse] using buildRev_denote n as.reverse

theorem buildAtoms_admissible (n : Nat) (as : List (RelativeTerm Nat)) (ha : GoodAtoms n as) :
    admissible n (buildAtoms as) := buildRev_admissible n as.reverse ha.reverse

theorem buildAtoms_normal (n : Nat) (as : List (RelativeTerm Nat)) (ha : GoodAtoms n as)
    (hn : IsAdditiveNormalForm (as.map (denote n))) : Normal n (buildAtoms as) := by
  apply buildRev_normal n as.reverse ha.reverse
  simpa only [List.reverse_reverse] using hn

end Alexander313.Wilken.RelativeTerm.SourceOne.Normalization
