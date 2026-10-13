import Alexander313.Wilken.FiniteCoverage

/-!
# Exact argument-bound domains for finite hull calls

Actual higher calls, and local calls at a nonterminal level, have argument
bounds from the proved finite coverage. The source Corollary 2.14 speaks
of "terms" in a hull. Its interpretation cannot be silently strengthened
to every call in the unrestricted Hull grammar: a terminal local call
seeded above the terminal boundary gives the explicit exception below.

No claim is made that this exception refutes the source's intended
notation-term interpretation. That correspondence requires clarification.
The exact proved call domains and the exception are recorded as actual
proof terms, all uncompiled and specialized to Ordinal universe zero.
-/

namespace Alexander313.Wilken

theorem source_hull_higher_argument_lt_boundary (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (α β : Ordinal.{0})
    (hα : α ≤ omegaSequence τ (m + 2)) (hβ : β ≤ omegaSequence τ (m + 1))
    (k : Nat) (hmk : m < k) (hk : k < n) {η : Ordinal.{0}}
    (hη : Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α β η)
    (hsort : η < omegaSequence τ (k + 2)) : η < finiteBoundary τ n (k + 1) := by
  have hnext := (source_nextNotation_iff_hull τ n m hm η).2
    (source_hull_to_admissible τ n m hm hα hβ hη)
  exact source_finite_collapse_argument_lt_boundary τ hτ n (m + 1) k
    (Nat.succ_le_of_lt hmk) hk hnext hsort

theorem source_hull_nonterminal_local_argument_lt_boundary (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m + 1 < n) (α β : Ordinal.{0})
    (hα : α ≤ omegaSequence τ (m + 2)) (hβ : β ≤ omegaSequence τ (m + 1))
    {η : Ordinal.{0}} (hη : Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α β η)
    (hlocal : η < α) : η < finiteBoundary τ n (m + 1) := by
  have hmn : m < n := by omega
  have hnext := (source_nextNotation_iff_hull τ n m hmn η).2
    (source_hull_to_admissible τ n m hmn hα hβ hη)
  exact source_finite_notation_sorted_lt_boundary τ hτ n (m + 1) (m + 1)
    le_rfl hm hnext (hlocal.trans_le hα)

/-- The unrestricted grammar really admits a terminal local argument at
the terminal boundary when both seeds are its successor. This prevents
using an unqualified all-hull-call bound as a source theorem. -/
theorem terminal_hull_unrestricted_argument_counterexample (τ : Ordinal.{0}) (m : Nat) :
    ∃ α β η : Ordinal.{0}, α < omegaSequence τ (m + 2) ∧
      β < omegaSequence τ (m + 1) ∧ η < α ∧
      Hull (omegaSequence τ) (sourceFiniteCollapse τ (m + 1)) (m + 1) m α β η ∧
      Hull (omegaSequence τ) (sourceFiniteCollapse τ (m + 1)) (m + 1) m α β
        (sourceFiniteCollapse τ (m + 1) m η) ∧
      ¬ η < finiteBoundary τ (m + 1) (m + 1) := by
  let cut := terminalBoundary τ m
  have hcard : cut + 1 < omegaSequence τ (m + 1) :=
    (omegaSequence_isSuccLimit τ m).add_one_lt (terminalBoundary_lt_cardinal τ m)
  have hseed : cut < cut + 1 := lt_add_one cut
  refine ⟨cut + 1, cut + 1, cut, hcard.trans (omegaSequence_step τ (m + 1)),
    hcard, hseed, .below_parameter hseed, .«local» hseed (.below_parameter hseed), ?_⟩
  rw [finiteBoundary_terminal τ (m + 1) (Nat.succ_pos m), Nat.add_sub_cancel, finiteBoundary_top]
  exact lt_irrefl cut

end Alexander313.Wilken
