import Alexander313.Wilken.SourceSupport

/-!
# Actual presentations for canonical support components

A Pⁿₘ component extracted from a term over a lower base has an actual
admissible presentation over that same base, of no greater size. Higher
arguments and proper canonical atoms have strictly smaller presentations.
The proof includes base level zero and follows the constructed support
recursion; it does not collect raw leaves that ordinal addition absorbs.

These semantic witness bounds are used to prove finite coverage by real
finite-tree descent. They are not effective parameter conversions or a
public ordinal code. All terms await external compilation.
-/

namespace Alexander313.Wilken

theorem source_admissible_denote_proper (τ : Ordinal.{0}) (n q : Nat) (hq : q < n)
    (t : SourceRelativeTerm τ q)
    (ht : RelativeTerm.Admissible (sourceParameters τ q) (omegaSequence τ)
      (sourceFiniteCollapse τ n) n q t) :
    sourceNotation τ n q (t.eval (sourceParameters τ q) (sourceFiniteCollapse τ n)) := by
  rw [sourceNotation, if_pos hq]
  exact ht.denote

/-- A higher support constructor in an actual lower-base tree has a
strictly smaller argument tree. Cardinal ranges and actual injectivity
identify the argument even when the original base is level zero. -/
theorem sourceRelativeTerm_support_argument_witness (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n q m : Nat) (hqm : q ≤ m) (hm : m < n) (t : SourceRelativeTerm τ q)
    (ht : RelativeTerm.Admissible (sourceParameters τ q) (omegaSequence τ)
      (sourceFiniteCollapse τ n) n q t) :
    ∀ k γ, m < k → k < n → sourceNotation τ n (m + 1) γ →
      γ < omegaSequence τ (k + 2) →
      sourceFiniteCollapse τ n k γ ∈
        canonicalANF (t.eval (sourceParameters τ q) (sourceFiniteCollapse τ n)) →
      ∃ s : SourceRelativeTerm τ q,
        RelativeTerm.Admissible (sourceParameters τ q) (omegaSequence τ)
          (sourceFiniteCollapse τ n) n q s ∧
        s.eval (sourceParameters τ q) (sourceFiniteCollapse τ n) = γ ∧ s.size < t.size := by
  have hq : q < n := hqm.trans_lt hm
  induction ht with
  | @parameter p hp =>
    intro k γ hmk hkn hγ hsort hc
    have hsmall := (canonicalANF_mem_le hc).trans_lt hp
    have hlarge : omegaSequence τ q ≤ sourceFiniteCollapse τ n k γ :=
      ((omegaSequence_strictMono τ).monotone (hqm.trans hmk.le)).trans
        (sourceFiniteCollapse_bounds τ n k hkn γ).1
    exact False.elim (hsmall.not_ge hlarge)
  | @sum a b ha hb iha ihb =>
    intro k γ hmk hkn hγ hsort hc
    rcases canonicalANF_add_mem hc with hc | hc
    · obtain ⟨s, hs, hval, hsize⟩ := iha k γ hmk hkn hγ hsort hc
      exact ⟨s, hs, hval, hsize.trans (RelativeTerm.sum_left_size_lt a b)⟩
    · obtain ⟨s, hs, hval, hsize⟩ := ihb k γ hmk hkn hγ hsort hc
      exact ⟨s, hs, hval, hsize.trans (RelativeTerm.sum_right_size_lt a b)⟩
  | @theta l a hql hln hsorta ha ih =>
    intro k γ hmk hkn hγ hsortγ hc
    have hanf := canonicalANF_principal
      (sourceFiniteCollapse_pos τ hτ n l hln
        (a.eval (sourceParameters τ q) (sourceFiniteCollapse τ n)))
      (sourceFiniteCollapse_add_closed τ n l hln
        (a.eval (sourceParameters τ q) (sourceFiniteCollapse τ n)))
    simp only [RelativeTerm.eval] at hc
    rw [hanf, List.mem_singleton] at hc
    have haNotation := source_admissible_denote_proper τ n q hq a ha
    have hγDomain : γ ∈ sourceCollapseDomain τ n k :=
      ⟨sourceNotation_upward τ n (m + 1) (k + 1) (by omega)
        (Nat.succ_le_of_lt hkn) hγ, hsortγ⟩
    have haDomain : a.eval (sourceParameters τ q) (sourceFiniteCollapse τ n) ∈
        sourceCollapseDomain τ n l :=
      ⟨sourceNotation_upward τ n q (l + 1) (hql.trans (Nat.le_succ l))
        (Nat.succ_le_of_lt hln) haNotation, hsorta⟩
    have hlevel := sourceFiniteCollapse_level_eq τ n k l hkn hln hγDomain haDomain hc
    subst l
    have harg := sourceFiniteCollapse_injective_on τ n k hkn hγDomain haDomain hc
    exact ⟨a, ha, harg.symm, RelativeTerm.theta_arg_size_lt k a⟩

/-- Every actual support component retains a denoting tree over the
original lower base. The size bound is proved by finite descent through
the canonical support recursion, not by a syntactic leaf approximation. -/
theorem sourceRelativeTerm_support_component_witness (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n q m : Nat) (hqm : q ≤ m) (hm : m < n) (t : SourceRelativeTerm τ q)
    (ht : RelativeTerm.Admissible (sourceParameters τ q) (omegaSequence τ)
      (sourceFiniteCollapse τ n) n q t)
    (ξ : SourceNotationOrdinal τ n (m + 1))
    (hval : t.eval (sourceParameters τ q) (sourceFiniteCollapse τ n) = ξ.val) :
    ∀ p ∈ sourceP τ hτ n m hm ξ, ∃ s : SourceRelativeTerm τ q,
      RelativeTerm.Admissible (sourceParameters τ q) (omegaSequence τ)
        (sourceFiniteCollapse τ n) n q s ∧
      s.eval (sourceParameters τ q) (sourceFiniteCollapse τ n) = p ∧ s.size ≤ t.size := by
  classical
  revert ht ξ hval
  refine (InvImage.wf (fun t : SourceRelativeTerm τ q => t.size) Nat.lt_wfRel.wf).induction t
    (C := fun t =>
      RelativeTerm.Admissible (sourceParameters τ q) (omegaSequence τ)
        (sourceFiniteCollapse τ n) n q t →
      ∀ ξ : SourceNotationOrdinal τ n (m + 1),
      t.eval (sourceParameters τ q) (sourceFiniteCollapse τ n) = ξ.val →
      ∀ p ∈ sourceP τ hτ n m hm ξ, ∃ s : SourceRelativeTerm τ q,
        RelativeTerm.Admissible (sourceParameters τ q) (omegaSequence τ)
          (sourceFiniteCollapse τ n) n q s ∧
        s.eval (sourceParameters τ q) (sourceFiniteCollapse τ n) = p ∧ s.size ≤ t.size) ?_
  intro t ih ht ξ hval p hp
  by_cases hlow : ξ.val < omegaSequence τ (m + 1)
  · rw [sourceP_low τ hτ n m hm ξ hlow, List.mem_toFinset] at hp
    exact sourceRelativeTerm_component_witness τ hτ n q t ht p
      (by simpa only [hval] using hp)
  · by_cases hprincipal : Ordinal.IsPrincipal (· + ·) ξ.val
    · let a := sourceHigherPresentation τ hτ n m hm ξ (le_of_not_gt hlow) hprincipal
      have hcomponent : sourceFiniteCollapse τ n a.level a.argument.val ∈
          canonicalANF (t.eval (sourceParameters τ q) (sourceFiniteCollapse τ n)) := by
        rw [hval, a.denote,
          canonicalANF_principal (sourceFiniteCollapse_pos τ hτ n a.level a.upper _)
            (sourceFiniteCollapse_add_closed τ n a.level a.upper _)]
        exact List.mem_singleton_self _
      obtain ⟨s, hs, hsval, hsize⟩ := sourceRelativeTerm_support_argument_witness
        τ hτ n q m hqm hm t ht a.level a.argument.val (by have h := a.lower; omega)
        a.upper a.argument.property a.sort hcomponent
      rw [sourceP_principal τ hτ n m hm ξ (le_of_not_gt hlow) hprincipal] at hp
      obtain ⟨u, hu, huval, husize⟩ := ih s hsize hs a.argument hsval p hp
      exact ⟨u, hu, huval, husize.trans hsize.le⟩
    · rw [sourceP_nonprincipal τ hτ n m hm ξ (le_of_not_gt hlow) hprincipal,
        Finset.mem_biUnion] at hp
      obtain ⟨a, ha, hp⟩ := hp
      have haList := List.mem_toFinset.1 a.property
      have hne : a.val ≠ ξ.val := by
        intro heq
        exact hprincipal (by rw [← heq]; exact ((canonicalANF_normal ξ.val).1 a.val haList).2)
      have hhigh : omegaSequence τ q ≤
          t.eval (sourceParameters τ q) (sourceFiniteCollapse τ n) := by
        rw [hval]
        exact ((omegaSequence_strictMono τ).monotone (hqm.trans (Nat.le_succ m))).trans
          (le_of_not_gt hlow)
      obtain ⟨s, hs, hsval, hsize⟩ := sourceRelativeTerm_proper_component_witness
        τ hτ n q t ht hhigh (by simpa only [hval] using haList)
        (by simpa only [hval] using hne)
      obtain ⟨u, hu, huval, husize⟩ := ih s hsize hs
        (sourceComponent τ hτ n m hm ξ a.val haList) hsval p hp
      exact ⟨u, hu, huval, husize.trans hsize.le⟩

end Alexander313.Wilken
