import Alexander313.Wilken.EndpointGrowth

/-!
# Actual finite-fragment coherence over arbitrary heights

Adjacent source results are iterated over Nat, with the actual endpoint
bounds propagated at every step. These are proofs about the constructed
finite families, not supplied direct-limit coherence fields. Candidate
proof terms await external compilation.
-/

namespace Alexander313.Wilken

theorem sourceNotation_fragment_mono (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m n' : Nat) (hm : m ≤ n) (hnn' : n ≤ n') {ξ : Ordinal.{0}}
    (hξ : sourceNotation τ n m ξ) : sourceNotation τ n' m ξ := by
  have steps : ∀ d, sourceNotation τ (n + d) m ξ := by
    intro d
    induction d with
    | zero => simpa only [Nat.add_zero] using hξ
    | succ d ih =>
      simpa only [Nat.add_succ] using
        sourceNotation_finite_end_extension τ hτ (n + d) m (by omega) ih
  simpa only [Nat.add_sub_of_le hnn'] using steps (n' - n)

theorem finiteBoundary_fragment_le (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n : Nat) (hn : 0 < n) (m n' : Nat) (hm : m ≤ n) (hnn' : n ≤ n') :
    finiteBoundary τ n m ≤ finiteBoundary τ n' m := by
  have steps : ∀ d, finiteBoundary τ n m ≤ finiteBoundary τ (n + d) m := by
    intro d
    induction d with
    | zero => simp only [Nat.add_zero, le_refl]
    | succ d ih =>
      exact ih.trans (by
        simpa only [Nat.add_succ] using
          (finiteBoundary_strict_end_extension τ hτ (n + d) (by omega) m (by omega)).le)
  simpa only [Nat.add_sub_of_le hnn'] using steps (n' - n)

theorem sourceFiniteCollapse_fragment_agreement (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m n' : Nat) (hm : m < n) (hnn' : n ≤ n') (α : Ordinal.{0})
    (hα : α < finiteBoundary τ n (m + 1)) :
    sourceFiniteCollapse τ n m α = sourceFiniteCollapse τ n' m α := by
  have steps : ∀ d, sourceFiniteCollapse τ n m α = sourceFiniteCollapse τ (n + d) m α := by
    intro d
    induction d with
    | zero => simp only [Nat.add_zero]
    | succ d ih =>
      have hbound : α < finiteBoundary τ (n + d) (m + 1) :=
        hα.trans_le (finiteBoundary_fragment_le τ hτ n (by omega) (m + 1) (n + d)
          (by omega) (by omega))
      exact ih.trans (by
        simpa only [Nat.add_succ] using
          sourceFiniteCollapse_finite_end_extension τ hτ (n + d) m (by omega) α hbound)
  simpa only [Nat.add_sub_of_le hnn'] using steps (n' - n)

end Alexander313.Wilken
