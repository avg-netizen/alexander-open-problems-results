import Alexander313.Wilken.FiniteTowers
import Alexander313.Wilken.SupportPresentationWitness

/-!
# Actual general finite coverage

Wilken Theorem 2.13 is proved for the constructed descending sequences.
Finite-tree induction bounds every low denotation of an actual admissible
term. At a nonterminal collapsing node, its argument is bounded at the
next level, and actual smaller support presentations bound its star at
the current level. Cofinal approximants and the proved star comparison
then bound the collapsing output. The reverse inclusion uses the actual
initial-hull theorem and genuine notation presentations of the sequence.

No coverage, end-extension or reflection field is assumed. The theorem
uses Ordinal universe zero and τ>0. Semantic suprema and support remain
noncomputable; effective hereditary notation is not asserted. All terms
are uncompiled candidates.
-/

namespace Alexander313.Wilken

/-- The argument and star bounds together imply a genuine output bound.
Both bounds are discharged by finite-tree induction in the theorem below. -/
theorem finiteBoundary_collapse_bound (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m + 1 < n) (α : SourceNotationOrdinal τ n (m + 1))
    (hα : α.val < finiteBoundary τ n (m + 1))
    (hstar : sourceStar τ hτ n m (by omega) α < finiteBoundary τ n m) :
    sourceFiniteCollapse τ n m α.val < finiteBoundary τ n m := by
  obtain ⟨i, hi⟩ := (finiteBoundary_cofinal τ n m (by omega) _).1 hstar
  obtain ⟨j, hj⟩ := (finiteBoundary_cofinal τ n (m + 1) hm α.val).1 hα
  let k := max i j
  let γ : SourceNotationOrdinal τ n (m + 1) :=
    ⟨finiteApproximant τ n (m + 1) k,
      finiteApproximant_lower_notation τ hτ n (m + 1) hm (m + 1) le_rfl k⟩
  have hαγ : α.val < γ.val :=
    hj.trans_le ((finiteApproximant_strictMono τ hτ n (m + 1) hm).monotone (le_max_right i j))
  have hstarγ : sourceStar τ hτ n m (by omega) α < sourceFiniteCollapse τ n m γ.val := by
    have hk := hi.trans_le ((finiteApproximant_strictMono τ hτ n m (by omega)).monotone
      (le_max_left i j))
    change sourceStar τ hτ n m (by omega) α < finiteApproximant τ n m k at hk
    simpa only [γ, finiteApproximant_next τ n m k hm] using hk
  have hc := (sourceFiniteCollapse_lt_iff_sourceStar τ hτ n m (by omega) α γ
    (hα.trans (finiteBoundary_lt_cardinal τ hτ n (m + 1) hm))
    (finiteApproximant_lt_cardinal τ hτ n (m + 1) hm k)).2 (Or.inl ⟨hαγ, hstarγ⟩)
  have hγbound : sourceFiniteCollapse τ n m γ.val < finiteBoundary τ n m := by
    simpa only [γ, finiteApproximant_next τ n m k hm] using
      finiteApproximant_lt_boundary τ hτ n m (by omega) k
  exact hc.trans hγbound

/-- Every low value of an actual lower-base term lies below the actual
source boundary at that level. This includes the support witnesses used
inside its collapsing arguments, with strictly smaller finite sizes. -/
theorem sourceRelativeTerm_finite_boundary_bound (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n q : Nat) (hq : q < n) (t : SourceRelativeTerm τ q)
    (ht : RelativeTerm.Admissible (sourceParameters τ q) (omegaSequence τ)
      (sourceFiniteCollapse τ n) n q t) :
    ∀ m, q ≤ m → m < n →
      t.eval (sourceParameters τ q) (sourceFiniteCollapse τ n) < omegaSequence τ (m + 1) →
      t.eval (sourceParameters τ q) (sourceFiniteCollapse τ n) < finiteBoundary τ n m := by
  classical
  revert ht
  refine (InvImage.wf (fun t : SourceRelativeTerm τ q => t.size) Nat.lt_wfRel.wf).induction t
    (C := fun t => RelativeTerm.Admissible (sourceParameters τ q) (omegaSequence τ)
      (sourceFiniteCollapse τ n) n q t → ∀ m, q ≤ m → m < n →
      t.eval (sourceParameters τ q) (sourceFiniteCollapse τ n) < omegaSequence τ (m + 1) →
      t.eval (sourceParameters τ q) (sourceFiniteCollapse τ n) < finiteBoundary τ n m) ?_
  intro t ih ht m hqm hmn hsmall
  cases ht with
  | @parameter p hp =>
    exact (hp.trans_le ((omegaSequence_strictMono τ).monotone hqm)).trans
      (finiteBoundary_base_lt τ hτ n m hmn)
  | @sum a b ha hb =>
    exact finiteBoundary_add_closed τ hτ n m hmn
      (ih a (RelativeTerm.sum_left_size_lt a b) ha m hqm hmn
        (le_self_add.trans_lt hsmall))
      (ih b (RelativeTerm.sum_right_size_lt a b) hb m hqm hmn
        (le_add_self.trans_lt hsmall))
  | @theta l a hql hln hsort ha =>
    have haNotation := source_admissible_denote_proper τ n q hq a ha
    have hrange := sourceFiniteCollapse_typed_range τ n q l hql hln _ haNotation hsort
    have hlm : l ≤ m := by
      by_contra hnot
      have hml : m + 1 ≤ l := by omega
      exact hsmall.not_ge (((omegaSequence_strictMono τ).monotone hml).trans hrange.1)
    rcases hlm.eq_or_lt with heq | hlt
    · subst l
      by_cases hnext : m + 1 < n
      · let α : SourceNotationOrdinal τ n (m + 1) :=
          ⟨a.eval (sourceParameters τ q) (sourceFiniteCollapse τ n),
            sourceNotation_upward τ n q (m + 1) (hqm.trans (Nat.le_succ m))
              (Nat.succ_le_of_lt hmn) haNotation⟩
        have hαbound : α.val < finiteBoundary τ n (m + 1) :=
          ih a (RelativeTerm.theta_arg_size_lt m a) ha (m + 1)
            (hqm.trans (Nat.le_succ m)) hnext hsort
        have hsupport : ∀ p ∈ sourceP τ hτ n m hmn α, p < finiteBoundary τ n m := by
          intro p hp
          obtain ⟨s, hs, hsval, hsize⟩ := sourceRelativeTerm_support_component_witness
            τ hτ n q m hqm hmn a ha α rfl p hp
          have hpSmall := sourceP_below τ hτ n m hmn α p hp
          have hsbound := ih s (hsize.trans_lt (RelativeTerm.theta_arg_size_lt m a))
            hs m hqm hmn (by simpa only [hsval] using hpSmall)
          simpa only [hsval] using hsbound
        have hbase := finiteBoundary_base_lt τ hτ n m hmn
        have hstarbound : sourceStar τ hτ n m hmn α < finiteBoundary τ n m :=
          (sourceStar_lt_iff τ hτ n m hmn α (finiteBoundary τ n m)
            ((hτ.trans_le ((omegaSequence_strictMono τ).monotone (Nat.zero_le m))).trans hbase)
            hbase.le).2 hsupport
        exact finiteBoundary_collapse_bound τ hτ n m hnext α hαbound hstarbound
      · have htop : n = m + 1 := by omega
        subst n
        have hargTerminal := sourceNotation_upward τ (m + 1) q (m + 1)
          (by omega) le_rfl haNotation
        have hargSmall : a.eval (sourceParameters τ q) (sourceFiniteCollapse τ (m + 1)) <
            omegaSequence τ (m + 1) := by
          simpa only [sourceNotation, if_neg (lt_irrefl (m + 1))] using hargTerminal
        have hargBound := ih a (RelativeTerm.theta_arg_size_lt m a) ha m hqm
          (Nat.lt_succ_self m) hargSmall
        rw [finiteBoundary_top] at hargBound ⊢
        exact terminalBoundary_collapse_closed τ m hargBound
    · exact (hrange.2.trans_le ((omegaSequence_strictMono τ).monotone
        (Nat.succ_le_of_lt hlt))).trans (finiteBoundary_base_lt τ hτ n m hmn)

theorem source_finite_notation_sorted_lt_boundary (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n q m : Nat) (hqm : q ≤ m) (hm : m < n) {ξ : Ordinal.{0}}
    (hξ : sourceNotation τ n q ξ) (hsmall : ξ < omegaSequence τ (m + 1)) :
    ξ < finiteBoundary τ n m := by
  obtain ⟨t, ht, hval⟩ := (sourceNotation_iff_relativeTerm τ n q (hqm.trans_lt hm) ξ).1 hξ
  have hbound := sourceRelativeTerm_finite_boundary_bound τ hτ n q (hqm.trans_lt hm) t ht
    m hqm hm (by simpa only [hval] using hsmall)
  simpa only [hval] using hbound

/-- Full finite source coverage, Theorem 2.13, for the actual θⁿₘ of
Definition 2.12 and the previously constructed notation domain. -/
theorem source_finite_notation_low_iff_lt_boundary (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (ξ : Ordinal.{0}) :
    (sourceNotation τ n m ξ ∧ ξ < omegaSequence τ (m + 1)) ↔ ξ < finiteBoundary τ n m := by
  constructor
  · rintro ⟨hξ, hsmall⟩
    exact source_finite_notation_sorted_lt_boundary τ hτ n m m le_rfl hm hξ hsmall
  · intro hξ
    obtain ⟨k, hk⟩ := (finiteBoundary_cofinal τ n m hm ξ).1 hξ
    have hnotation := finiteApproximant_lower_notation τ hτ n m hm m le_rfl k
    have hin := (sourceNotation_iff_hull τ n m hm _).1 hnotation
    have hξNotation := (sourceNotation_iff_hull τ n m hm ξ).2
      (source_hull_initial_segment τ hτ n m hm (omegaSequence τ (m + 2)) 0
        le_rfl (omegaSequence_isSuccLimit τ m).bot_lt hin
        (finiteApproximant_lt_cardinal τ hτ n m hm k) hk)
    exact ⟨hξNotation, hξ.trans (finiteBoundary_lt_cardinal τ hτ n m hm)⟩

theorem source_finite_boundary_absent (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) : ¬ sourceNotation τ n m (finiteBoundary τ n m) := by
  intro h
  exact lt_irrefl _ ((source_finite_notation_low_iff_lt_boundary τ hτ n m hm _).1
    ⟨h, finiteBoundary_lt_cardinal τ hτ n m hm⟩)

/-- Every actual constructor argument in the finite source grammar is
below the next source boundary, including its duplicated terminal case.
Arbitrary parameter seeds of a larger bounded hull are not silently
treated as finite source constructor arguments. -/
theorem source_finite_collapse_argument_lt_boundary (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n q k : Nat) (hqk : q ≤ k) (hk : k < n) {η : Ordinal.{0}}
    (hη : sourceNotation τ n q η) (hsort : η < omegaSequence τ (k + 2)) :
    η < finiteBoundary τ n (k + 1) := by
  by_cases hnext : k + 1 < n
  · exact source_finite_notation_sorted_lt_boundary τ hτ n q (k + 1)
      (hqk.trans (Nat.le_succ k)) hnext hη hsort
  · have htop : n = k + 1 := by omega
    subst n
    have hterminal := sourceNotation_upward τ (k + 1) q (k + 1) (by omega) le_rfl hη
    have hsmall : η < omegaSequence τ (k + 1) := by
      simpa only [sourceNotation, if_neg (lt_irrefl (k + 1))] using hterminal
    have hbound := source_finite_notation_sorted_lt_boundary τ hτ (k + 1) q k
      hqk (Nat.lt_succ_self k) hη hsmall
    simpa only [finiteBoundary_terminal τ (k + 1) (Nat.succ_pos k),
      Nat.add_sub_cancel] using hbound

end Alexander313.Wilken
