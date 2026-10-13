import Alexander313.Wilken.PrincipalDecomposition

/-!
# Inverting higher collapsing calls in actual source hulls

The higher-θ clause of the support equivalence in Wilken Lemma 2.10(b)
requires more than hull closure under addition. A higher collapsing value
can belong to a hull only if its actual argument belongs to that hull.

This is derived from canonical ANF, cardinal range separation, and actual
collapse injectivity. The base and parameter cases are excluded by the
next-cardinal bound; local outputs are excluded by proper collapse. No
inverse-closure contract or star-support package is assumed.
All proof terms are candidates awaiting external compilation.
-/

namespace Alexander313.Wilken

/-- A higher collapsing value occurring as a canonical principal
component has its unique admissible argument in the hull. -/
theorem source_hull_higher_argument_of_component (τ : Ordinal) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (α β : Ordinal)
    (hα : α ≤ omegaSequence τ (m + 2)) (hβ : β ≤ omegaSequence τ (m + 1))
    {ξ : Ordinal}
    (hξ : Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α β ξ) :
    ∀ k γ, m < k → k < n → sourceNotation τ n (m + 1) γ →
      γ < omegaSequence τ (k + 2) →
      sourceFiniteCollapse τ n k γ ∈ canonicalANF ξ →
      Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α β γ := by
  induction hξ with
  | below_base hξ =>
    intro k γ hmk hkn hγ hsort hc
    have hsmall := (canonicalANF_mem_le hc).trans_lt hξ
    have hlarge : omegaSequence τ m ≤ sourceFiniteCollapse τ n k γ :=
      ((omegaSequence_strictMono τ).monotone hmk.le).trans
        (sourceFiniteCollapse_bounds τ n k hkn γ).1
    exact False.elim (hsmall.not_ge hlarge)
  | below_parameter hξ =>
    intro k γ hmk hkn hγ hsort hc
    have hsmall := ((canonicalANF_mem_le hc).trans_lt hξ).trans_le hβ
    have hlarge : omegaSequence τ (m + 1) ≤ sourceFiniteCollapse τ n k γ :=
      ((omegaSequence_strictMono τ).monotone (Nat.succ_le_of_lt hmk)).trans
        (sourceFiniteCollapse_bounds τ n k hkn γ).1
    exact False.elim (hsmall.not_ge hlarge)
  | add hξ hη ihξ ihη =>
    intro k γ hmk hkn hγ hsort hc
    exact (canonicalANF_add_mem hc).elim
      (ihξ k γ hmk hkn hγ hsort) (ihη k γ hmk hkn hγ hsort)
  | @higher l δ hml hln hsortδ hδ ih =>
    intro k γ hmk hkn hγ hsortγ hc
    have hanf := canonicalANF_principal
      (sourceFiniteCollapse_pos τ hτ n l hln δ)
      (sourceFiniteCollapse_add_closed τ n l hln δ)
    rw [hanf, List.mem_singleton] at hc
    have hδnotation : sourceNotation τ n (m + 1) δ :=
      (source_nextNotation_iff_hull τ n m hm δ).mpr
        (source_hull_to_admissible τ n m hm hα hβ hδ)
    have hsame := sourceFiniteCollapse_presentation_unique τ n (m + 1) k l
      (Nat.succ_le_of_lt hmk) (Nat.succ_le_of_lt hml) hkn hln
      hγ hδnotation hsortγ hsortδ hc
    simpa only [hsame.2] using hδ
  | @«local» δ hδα hδ ih =>
    intro k γ hmk hkn hγ hsortγ hc
    have hanf := canonicalANF_principal
      (sourceFiniteCollapse_pos τ hτ n m hm δ)
      (sourceFiniteCollapse_add_closed τ n m hm δ)
    rw [hanf, List.mem_singleton] at hc
    have hδnotation : sourceNotation τ n (m + 1) δ :=
      (source_nextNotation_iff_hull τ n m hm δ).mpr
        (source_hull_to_admissible τ n m hm hα hβ hδ)
    have hlocal := sourceFiniteCollapse_proper_notation τ n m hm δ
      (hδα.trans_le hα) hδnotation
    have hlarge : omegaSequence τ (m + 1) ≤ sourceFiniteCollapse τ n k γ :=
      ((omegaSequence_strictMono τ).monotone (Nat.succ_le_of_lt hmk)).trans
        (sourceFiniteCollapse_bounds τ n k hkn γ).1
    exact False.elim ((ne_of_lt (hlocal.trans_le hlarge)) hc.symm)

/-- The literal higher-collapse branch required by Definition 2.9 and
Lemma 2.10(b), with source-admissible arguments and actual hulls. -/
theorem source_hull_higher_iff_argument (τ : Ordinal) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (α β : Ordinal)
    (hα : α ≤ omegaSequence τ (m + 2)) (hβ : β ≤ omegaSequence τ (m + 1))
    (k : Nat) (hmk : m < k) (hkn : k < n) (γ : Ordinal)
    (hγ : sourceNotation τ n (m + 1) γ) (hsort : γ < omegaSequence τ (k + 2)) :
    Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α β
        (sourceFiniteCollapse τ n k γ) ↔
      Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α β γ := by
  constructor
  · intro h
    apply source_hull_higher_argument_of_component τ hτ n m hm α β hα hβ h
      k γ hmk hkn hγ hsort
    rw [canonicalANF_principal (sourceFiniteCollapse_pos τ hτ n k hkn γ)
      (sourceFiniteCollapse_add_closed τ n k hkn γ)]
    exact List.mem_singleton_self _
  · exact Hull.higher hmk hkn hsort

end Alexander313.Wilken
