import Alexander313.Wilken.HereditaryPrincipalSupport

/-!
# Principal-support values under weak sum normality

The full cutoff-m support in Definition 2.23 has the same actual value set
as the literal theta-m list on admitted `NormalSums` terms. A zero-leading
sum can itself denote a principal ordinal, so its shape need not be theta;
the proof instead finds a literal theta node with the same value in its
right child. Nonzero normal prefixes are excluded by genuine ANF uniqueness.

This removes `SourceNormal` only for principal-support VALUE sets and their
maxima. It does not identify written subterm sets, alternate spellings, or
literal parameter support. Parameters remain atomic, and the stronger Par
syntax convention remains separate. All proofs are uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.PrincipalSupport

variable {Parameter : Type}

/-- Principal nodes of any literal cutoff-m subterm remain principal nodes
of the whole tree. No admission or normality premise is needed. -/
theorem principalList_mem_of_subtermsAt [DecidableEq Parameter]
    (m : Nat) (t s q : RelativeTerm Parameter)
    (hs : s ∈ t.subtermsAt m) (hq : q ∈ principalList m s) :
    q ∈ principalList m t := by
  revert hs hq
  induction t with
  | parameter p =>
    intro hs hq
    have he : s = .parameter p := by
      simpa only [subtermsAt, Finset.mem_singleton] using hs
    subst s
    exact hq
  | sum a b iha ihb =>
    intro hs hq
    rcases Finset.mem_insert.mp hs with he | hs
    · subst s; exact hq
    · rcases Finset.mem_union.mp hs with hs | hs
      · exact List.mem_append.mpr (Or.inl (iha hs hq))
      · exact List.mem_append.mpr (Or.inr (ihb hs hq))
  | theta k a ih =>
    intro hs hq
    by_cases hmk : m ≤ k
    · rw [subtermsAt, if_pos hmk] at hs
      rcases Finset.mem_insert.mp hs with he | hs
      · subst s; exact hq
      · have hqa := ih hs hq
        by_cases hkm : k = m
        · rw [principalList, if_pos hmk, if_pos hkm]
          exact List.mem_cons_of_mem _ hqa
        · simpa only [principalList, if_pos hmk, if_neg hkm] using hqa
    · have he : s = .theta k a := by
        simpa only [subtermsAt, if_neg hmk, Finset.mem_singleton] using hs
      subst s
      exact hq

/-- A weak-normal term with a positive principal value in the m-th range
contains an actual theta-m node with that same value. -/
theorem principal_range_value_witness [DecidableEq Parameter]
    (τ : Ordinal.{0}) (hτ : 0 < τ) (parameters : Parameter → Ordinal.{0})
    (n m : Nat) (t : RelativeTerm Parameter)
    (ht : Admissible parameters (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 t)
    (hn : NormalSums τ parameters n t)
    (hv : 0 < t.eval parameters (sourceFiniteCollapse τ n) ∧
      Ordinal.IsPrincipal (· + ·) (t.eval parameters (sourceFiniteCollapse τ n)) ∧
      omegaSequence τ m ≤ t.eval parameters (sourceFiniteCollapse τ n) ∧
      t.eval parameters (sourceFiniteCollapse τ n) < omegaSequence τ (m + 1)) :
    ∃ q ∈ principalList m t,
      q.eval parameters (sourceFiniteCollapse τ n) = t.eval parameters (sourceFiniteCollapse τ n) := by
  revert hn hv
  induction ht with
  | parameter hp =>
    intro hn hv
    exact False.elim (hp.not_ge
      (((omegaSequence_strictMono τ).monotone (Nat.zero_le m)).trans hv.2.2.1))
  | @sum a b ha hb iha ihb =>
    intro hn hv
    by_cases hz : a.eval parameters (sourceFiniteCollapse τ n) = 0
    · have he : (.sum a b : RelativeTerm Parameter).eval parameters (sourceFiniteCollapse τ n) =
          b.eval parameters (sourceFiniteCollapse τ n) := by
        change a.eval parameters (sourceFiniteCollapse τ n) +
          b.eval parameters (sourceFiniteCollapse τ n) = _
        rw [hz, zero_add]
      obtain ⟨q, hq, hvalue⟩ := ihb hn.2.1 (by rw [← he]; exact hv)
      exact ⟨q, List.mem_append.mpr (Or.inr hq), hvalue.trans he.symm⟩
    · exact False.elim (sourceNormalSum_not_principal hn.2.2
        (pos_iff_ne_zero.mpr hz) hv.2.1)
  | @theta k a h0k hkn hsort ha ih =>
    intro hn hv
    have hr := source_theta_range τ parameters n k a hkn ha hsort
    have hk : k = m := by
      by_contra he
      rcases lt_or_gt_of_ne he with hkm | hmk
      · exact (hr.2.trans_le ((omegaSequence_strictMono τ).monotone
          (Nat.succ_le_of_lt hkm))).not_ge hv.2.2.1
      · exact hv.2.2.2.not_ge (((omegaSequence_strictMono τ).monotone
          (Nat.succ_le_of_lt hmk)).trans hr.1)
    subst k
    exact ⟨.theta m a, principalList_root m a, rfl⟩

/-- The reverse inclusion uses actual theta admission and range, without
any stronger sum-normality premise. -/
theorem principalList_value_class [DecidableEq Parameter]
    (τ : Ordinal.{0}) (hτ : 0 < τ) (parameters : Parameter → Ordinal.{0})
    (n m : Nat) (t q : RelativeTerm Parameter)
    (ht : Admissible parameters (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 t)
    (hq : q ∈ principalList m t) :
    0 < q.eval parameters (sourceFiniteCollapse τ n) ∧
      Ordinal.IsPrincipal (· + ·) (q.eval parameters (sourceFiniteCollapse τ n)) ∧
      omegaSequence τ m ≤ q.eval parameters (sourceFiniteCollapse τ n) ∧
      q.eval parameters (sourceFiniteCollapse τ n) < omegaSequence τ (m + 1) := by
  have ha := principalList_admissible ht m hq
  obtain ⟨a, rfl⟩ := principalList_shape m t q hq
  cases ha with
  | theta h0m hmn hsort ha =>
    exact ⟨sourceFiniteCollapse_pos τ hτ n m hmn _,
      sourceFiniteCollapse_add_closed τ n m hmn _,
      source_theta_range τ parameters n m a hmn ha hsort⟩

/-- Definition 2.23 principal support as an actual VALUE set is already
exact under NormalSums, including admitted zero-leading sums. -/
theorem sourcePrincipalSupport_eq_principalList_weak [DecidableEq Parameter]
    (τ : Ordinal.{0}) (hτ : 0 < τ) (parameters : Parameter → Ordinal.{0})
    (n m : Nat) (t : RelativeTerm Parameter)
    (ht : Admissible parameters (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 t)
    (hn : NormalSums τ parameters n t) :
    sourcePrincipalSupport τ parameters n m t =
      ((principalList m t).map (fun s => s.eval parameters (sourceFiniteCollapse τ n))).toFinset := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨hp, hclass⟩ := Finset.mem_filter.mp hp
    obtain ⟨s, hs, he⟩ := Finset.mem_image.mp hp
    obtain ⟨q, hq, hvalue⟩ := principal_range_value_witness τ hτ parameters n m s
      (subtermsAt_admissible ht m hs) (subtermsAt_normalSums hn m hs)
      (by rw [he]; exact hclass)
    exact List.mem_toFinset.mpr (List.mem_map.mpr
      ⟨q, principalList_mem_of_subtermsAt m t s q hs hq, hvalue.trans he⟩)
  · intro hp
    obtain ⟨q, hq, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr
      ⟨q, ((principalList_mem_iff m t q).mp hq).1, he⟩, ?_⟩
    rw [← he]
    exact principalList_value_class τ hτ parameters n m t q ht hq

/-- The full Definition 2.23 maximum and genuine finite source star agree
under the same weak-normal guard; the support sets themselves are distinct. -/
theorem sourcePrincipalSupport_star_weak [DecidableEq Parameter]
    (τ : Ordinal.{0}) (hτ : 0 < τ) (parameters : Parameter → Ordinal.{0})
    (n m : Nat) (hm : m < n) (t : RelativeTerm Parameter)
    (ht : Admissible parameters (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 t)
    (hn : NormalSums τ parameters n t) :
    (sourcePrincipalSupport τ parameters n m t).sup id =
      sourceStar τ hτ n m hm (sourceAdmittedOrdinal τ parameters n m hm t ht) := by
  rw [sourcePrincipalSupport_eq_principalList_weak τ hτ parameters n m t ht hn]
  exact fullStar_eq_sourceStar τ hτ parameters n m hm t ht hn

end Alexander313.Wilken.RelativeTerm.PrincipalSupport

namespace Alexander313.Wilken.RelativeTerm.Hereditary.PrincipalSupport

open scoped Classical

/-- Actual public denotation of literal Sub_m intersect P and the m-th
cardinal interval, for every original checked weak-normal hereditary level. -/
theorem sourcePrincipalValueSupport_eq_principalList
    (r m : Nat) (t : RelativeTerm Nat) (ht : check r t = true) (hn : Theta.Normal r t) :
    ((t.subtermsAt m).image (denote r)).filter (fun p =>
      0 < p ∧ Ordinal.IsPrincipal (· + ·) p ∧
      omegaSequence (finiteBase r) m ≤ p ∧ p < omegaSequence (finiteBase r) (m + 1)) =
      ((principalList m t).map (denote r)).toFinset := by
  classical
  obtain ⟨n, ha⟩ := (check_iff_finite_admissible r t).mp ht
  have hsub : (t.subtermsAt m).image (denote r) =
      (t.subtermsAt m).image (fun s => s.eval (parameters r) (sourceFiniteCollapse (finiteBase r) n)) := by
    apply Finset.image_congr
    intro s hs
    exact denote_eq_finite r n s (RelativeTerm.PrincipalSupport.subtermsAt_admissible ha.2 m hs)
  have hlist : (principalList m t).map (denote r) =
      (principalList m t).map (fun s => s.eval (parameters r) (sourceFiniteCollapse (finiteBase r) n)) := by
    apply List.map_congr_left
    intro s hs
    exact denote_eq_finite r n s (RelativeTerm.PrincipalSupport.principalList_admissible ha.2 m hs)
  rw [hsub, hlist]
  exact RelativeTerm.PrincipalSupport.sourcePrincipalSupport_eq_principalList_weak
    (finiteBase r) (finiteBase_pos r) (parameters r) n m t ha.2 (hn.finite ha)

/-- The executing full-depth support list denotes precisely the literal
principal-support value set; code admission and weak normality are explicit. -/
theorem listCode_sourcePrincipalValueSupport
    (r m : Nat) (t : RelativeTerm Nat) (ht : check r t = true) (hn : Theta.Normal r t) :
    ((t.subtermsAt m).image (denote r)).filter (fun p =>
      0 < p ∧ Ordinal.IsPrincipal (· + ·) p ∧
      omegaSequence (finiteBase r) m ≤ p ∧ p < omegaSequence (finiteBase r) (m + 1)) =
      ((listCode m t.code).map (interpretation r)).toFinset := by
  rw [sourcePrincipalValueSupport_eq_principalList r m t ht hn, listCode_code, List.map_map]
  congr 1
  apply List.map_congr_left
  intro s hs
  exact (interpretation_code r s).symm

end Alexander313.Wilken.RelativeTerm.Hereditary.PrincipalSupport
