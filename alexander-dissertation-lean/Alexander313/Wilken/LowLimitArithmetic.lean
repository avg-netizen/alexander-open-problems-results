import Alexander313.Wilken.GlobalBaseArithmetic

/-!
# Actual countable low-limit arithmetic

For a genuine strictly increasing countable low argument sequence, regularity
bounds both its argument supremum and its collapse-image supremum. The latter
is a real additive principal. The actual source minimum at the argument limit
is that image supremum if the argument is strictly below it, and the next
additive principal if the two suprema coincide.

This derives the source's fixed-point jump at these countable limits. It does
not prove the full non-epsilon enumeration, identify epsilon bases or the υ
sequence, or compute ordinal codes. Every proof awaits external compilation.
-/

namespace Alexander313.Wilken

noncomputable def lowArgumentSup (s : Nat → Ordinal.{0}) : Ordinal.{0} := ⨆ j, s j

noncomputable def lowCollapseSup (τ : Ordinal.{0}) (n m : Nat)
    (s : Nat → Ordinal.{0}) : Ordinal.{0} :=
  ⨆ j, sourceFiniteCollapse τ n m (s j)

theorem lowArgumentSup_lt_cardinal (τ : Ordinal.{0}) (m : Nat)
    (s : Nat → Ordinal.{0}) (hs : ∀ j, s j < omegaSequence τ (m + 1)) :
    lowArgumentSup s < omegaSequence τ (m + 1) := by
  apply Ordinal.lift_iSup_lt_of_lt_cof
  · simpa only [Cardinal.mk_nat, Cardinal.lift_aleph0, Ordinal.lift_id, omegaSequence,
      (omegaSequence_regular τ m).cof_ord] using
        (levelCardinal_infinite τ m).trans_lt (levelCardinal_step τ m)
  · exact hs

theorem lowCollapseSequence_strictMono (τ : Ordinal.{0}) (n m : Nat)
    (hm : m < n) (s : Nat → Ordinal.{0}) (hmono : StrictMono s)
    (hs : ∀ j, s j < omegaSequence τ (m + 1)) :
    StrictMono (fun j => sourceFiniteCollapse τ n m (s j)) := by
  intro i j hij
  exact sourceFiniteCollapse_strictMono_low τ n m hm (hmono hij) (hs j)

theorem lowCollapseSup_lt_cardinal (τ : Ordinal.{0}) (n m : Nat)
    (hm : m < n) (s : Nat → Ordinal.{0})
    (hs : ∀ j, s j < omegaSequence τ (m + 1)) :
    lowCollapseSup τ n m s < omegaSequence τ (m + 1) := by
  apply lowArgumentSup_lt_cardinal τ m
  intro j
  exact sourceFiniteCollapse_proper_notation τ n m hm (s j)
    ((hs j).trans (omegaSequence_step τ (m + 1)))
    (sourceNotation_next_of_low τ n m hm (hs j))

theorem lowArgumentSup_entry_lt (s : Nat → Ordinal.{0}) (hmono : StrictMono s)
    (j : Nat) : s j < lowArgumentSup s :=
  (hmono (Nat.lt_succ_self j)).trans_le (Ordinal.le_iSup s (j + 1))

theorem lowCollapseSup_entry_lt (τ : Ordinal.{0}) (n m : Nat) (hm : m < n)
    (s : Nat → Ordinal.{0}) (hmono : StrictMono s)
    (hs : ∀ j, s j < omegaSequence τ (m + 1)) (j : Nat) :
    sourceFiniteCollapse τ n m (s j) < lowCollapseSup τ n m s :=
  lowArgumentSup_entry_lt _ (lowCollapseSequence_strictMono τ n m hm s hmono hs) j

theorem lowArgumentSup_le_lowCollapseSup (τ : Ordinal.{0}) (n m : Nat)
    (hm : m < n) (s : Nat → Ordinal.{0})
    (hs : ∀ j, s j < omegaSequence τ (m + 1)) :
    lowArgumentSup s ≤ lowCollapseSup τ n m s := by
  apply Ordinal.iSup_le
  intro j
  exact (sourceFiniteCollapse_low_argument_lt τ n m hm (hs j)).le.trans
    (Ordinal.le_iSup (fun i => sourceFiniteCollapse τ n m (s i)) j)

theorem lowCollapseSup_add_closed (τ : Ordinal.{0}) (n m : Nat) (hm : m < n)
    (s : Nat → Ordinal.{0}) :
    Ordinal.IsPrincipal (· + ·) (lowCollapseSup τ n m s) := by
  intro α β hα hβ
  obtain ⟨i, hi⟩ := Ordinal.lt_iSup_iff.mp hα
  obtain ⟨j, hj⟩ := Ordinal.lt_iSup_iff.mp hβ
  by_cases h : sourceFiniteCollapse τ n m (s i) ≤ sourceFiniteCollapse τ n m (s j)
  · exact ((sourceFiniteCollapse_add_closed τ n m hm (s j))
      (hi.trans_le h) hj).trans_le
      (Ordinal.le_iSup (fun q => sourceFiniteCollapse τ n m (s q)) j)
  · exact ((sourceFiniteCollapse_add_closed τ n m hm (s i)) hi
      (hj.trans_le (le_of_not_ge h))).trans_le
      (Ordinal.le_iSup (fun q => sourceFiniteCollapse τ n m (s q)) i)

theorem lowCollapseSup_base_le (τ : Ordinal.{0}) (n m : Nat) (hm : m < n)
    (s : Nat → Ordinal.{0}) : omegaSequence τ m ≤ lowCollapseSup τ n m s :=
  (sourceFiniteCollapse_bounds τ n m hm (s 0)).1.trans
    (Ordinal.le_iSup (fun j => sourceFiniteCollapse τ n m (s j)) 0)

theorem sourceFiniteCollapse_below_lowArgumentSup (τ : Ordinal.{0}) (n m : Nat)
    (hm : m < n) (s : Nat → Ordinal.{0}) (hmono : StrictMono s)
    (hs : ∀ j, s j < omegaSequence τ (m + 1)) (γ : Ordinal.{0})
    (hγ : γ < lowArgumentSup s) :
    sourceFiniteCollapse τ n m γ < lowCollapseSup τ n m s := by
  obtain ⟨j, hj⟩ := Ordinal.lt_iSup_iff.mp hγ
  exact (sourceFiniteCollapse_strictMono_low τ n m hm hj (hs j)).trans
    (lowCollapseSup_entry_lt τ n m hm s hmono hs j)

theorem lowCollapseSup_le_limit_value (τ : Ordinal.{0}) (n m : Nat)
    (hm : m < n) (s : Nat → Ordinal.{0}) (hmono : StrictMono s)
    (hs : ∀ j, s j < omegaSequence τ (m + 1)) :
    lowCollapseSup τ n m s ≤ sourceFiniteCollapse τ n m (lowArgumentSup s) := by
  apply Ordinal.iSup_le
  intro j
  exact (sourceFiniteCollapse_strictMono_low τ n m hm
    (lowArgumentSup_entry_lt s hmono j) (lowArgumentSup_lt_cardinal τ m s hs)).le

/-- The actual minimum is continuous at a countable limit that lies below
the supremum of the earlier values. -/
theorem sourceFiniteCollapse_limit_eq_sup_of_lt (τ : Ordinal.{0}) (n m : Nat)
    (hm : m < n) (s : Nat → Ordinal.{0}) (hmono : StrictMono s)
    (hs : ∀ j, s j < omegaSequence τ (m + 1))
    (hgap : lowArgumentSup s < lowCollapseSup τ n m s) :
    sourceFiniteCollapse τ n m (lowArgumentSup s) = lowCollapseSup τ n m s := by
  apply le_antisymm
  · apply (sourceFiniteCollapse_low_le_iff_principal τ n m hm _ _
      (lowArgumentSup_lt_cardinal τ m s hs) (lowCollapseSup_lt_cardinal τ n m hm s hs)
      (lowCollapseSup_add_closed τ n m hm s)).mpr
    exact ⟨lowCollapseSup_base_le τ n m hm s, hgap,
      sourceFiniteCollapse_below_lowArgumentSup τ n m hm s hmono hs⟩
  · exact lowCollapseSup_le_limit_value τ n m hm s hmono hs

/-- When argument and image suprema coincide, the real minimum skips the
fixed point and takes the independently defined next additive principal. -/
theorem sourceFiniteCollapse_limit_eq_next_of_eq (τ : Ordinal.{0}) (n m : Nat)
    (hm : m < n) (s : Nat → Ordinal.{0}) (hmono : StrictMono s)
    (hs : ∀ j, s j < omegaSequence τ (m + 1))
    (heq : lowArgumentSup s = lowCollapseSup τ n m s) :
    sourceFiniteCollapse τ n m (lowArgumentSup s) =
      nextAdditivePrincipal (lowCollapseSup τ n m s) := by
  let α := lowArgumentSup s
  let δ := lowCollapseSup τ n m s
  have hα : α < omegaSequence τ (m + 1) := lowArgumentSup_lt_cardinal τ m s hs
  have hnextle : nextAdditivePrincipal δ ≤ sourceFiniteCollapse τ n m α :=
    nextAdditivePrincipal_le δ _ (by
      change lowCollapseSup τ n m s < sourceFiniteCollapse τ n m (lowArgumentSup s)
      rw [← heq]
      exact sourceFiniteCollapse_low_argument_lt τ n m hm hα)
      (sourceFiniteCollapse_add_closed τ n m hm α)
  have hproper := sourceFiniteCollapse_proper_notation τ n m hm α
    (hα.trans (omegaSequence_step τ (m + 1)))
    (sourceNotation_next_of_low τ n m hm hα)
  apply le_antisymm
  · apply (sourceFiniteCollapse_low_le_iff_principal τ n m hm α _ hα
      (hnextle.trans_lt hproper) (nextAdditivePrincipal_spec δ).2).mpr
    refine ⟨(lowCollapseSup_base_le τ n m hm s).trans
      (nextAdditivePrincipal_spec δ).1.le, ?_, ?_⟩
    · change lowArgumentSup s < nextAdditivePrincipal (lowCollapseSup τ n m s)
      rw [heq]
      exact (nextAdditivePrincipal_spec δ).1
    · intro γ hγ
      exact (sourceFiniteCollapse_below_lowArgumentSup τ n m hm s hmono hs γ hγ).trans
        (nextAdditivePrincipal_spec δ).1
  · exact hnextle

theorem sourceFiniteCollapse_limit_dichotomy (τ : Ordinal.{0}) (n m : Nat)
    (hm : m < n) (s : Nat → Ordinal.{0}) (hmono : StrictMono s)
    (hs : ∀ j, s j < omegaSequence τ (m + 1)) :
    (lowArgumentSup s < lowCollapseSup τ n m s ∧
      sourceFiniteCollapse τ n m (lowArgumentSup s) = lowCollapseSup τ n m s) ∨
    (lowArgumentSup s = lowCollapseSup τ n m s ∧
      sourceFiniteCollapse τ n m (lowArgumentSup s) =
        nextAdditivePrincipal (lowCollapseSup τ n m s)) := by
  rcases (lowArgumentSup_le_lowCollapseSup τ n m hm s hs).lt_or_eq with h | h
  · exact Or.inl ⟨h, sourceFiniteCollapse_limit_eq_sup_of_lt τ n m hm s hmono hs h⟩
  · exact Or.inr ⟨h, sourceFiniteCollapse_limit_eq_next_of_eq τ n m hm s hmono hs h⟩

end Alexander313.Wilken
