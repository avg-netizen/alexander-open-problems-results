import Alexander313.Wilken.FiniteNotations

/-!
# Actual fragment independence on low collapsing arguments

Every higher collapsing constructor has value at least Ωₘ₊₁. Hence the
small part of a hull with local argument at most Ωₘ₊₁ sees only parameter
seeds, addition and already defined local values. Restricted hull
induction and ordinal induction prove that the actual functions ϑⁿₘ
agree on arguments below Ωₘ₊₁ for every n>m.

This does not establish the full end-extension interval θ^{n}_{m+1},
which can extend above Ωₘ₊₁. It is a proved prerequisite and includes the
terminal case. No comparison, coverage or end-extension package is an
input. Proof terms are candidates awaiting external compilation.
-/

namespace Alexander313.Wilken

theorem source_low_hull_congr_of_local (τ : Ordinal) (n n' m : Nat)
    (α β : Ordinal) (hα : α ≤ omegaSequence τ (m + 1))
    («local» : ∀ γ < α, sourceFiniteCollapse τ n m γ = sourceFiniteCollapse τ n' m γ)
    (ξ : Ordinal) (hξ : ξ < omegaSequence τ (m + 1)) :
    Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α β ξ ↔
      Hull (omegaSequence τ) (sourceFiniteCollapse τ n') n' m α β ξ := by
  have forward : ∀ (a b : Nat),
      (∀ γ < α, sourceFiniteCollapse τ a m γ = sourceFiniteCollapse τ b m γ) →
      ∀ ξ, Hull (omegaSequence τ) (sourceFiniteCollapse τ a) a m α β ξ →
        ξ < omegaSequence τ (m + 1) →
        Hull (omegaSequence τ) (sourceFiniteCollapse τ b) b m α β ξ := by
    intro a b heq ξ h
    induction h with
    | below_base h => intro _; exact .below_base h
    | below_parameter h => intro _; exact .below_parameter h
    | @add x y hx hy ihx ihy =>
      intro hsmall
      exact .add (ihx (le_self_add.trans_lt hsmall)) (ihy (le_add_self.trans_lt hsmall))
    | @higher k γ hmk hka hsort harg ih =>
      intro hsmall
      have hlevel : omegaSequence τ (m + 1) ≤ omegaSequence τ k :=
        (omegaSequence_strictMono τ).monotone (Nat.succ_le_of_lt hmk)
      exact False.elim (hsmall.not_ge
        (hlevel.trans (sourceFiniteCollapse_bounds τ a k hka γ).1))
    | @«local» γ hγα harg ih =>
      intro _
      rw [heq γ hγα]
      exact .«local» hγα (ih (hγα.trans_le hα))
  exact ⟨fun h => forward n n' «local» ξ h hξ,
    fun h => forward n' n (fun γ hγ => («local» γ hγ).symm) ξ h hξ⟩

theorem source_low_candidate_congr_of_local (τ : Ordinal) (n n' m : Nat)
    (α β : Ordinal) (hα : α < omegaSequence τ (m + 1))
    («local» : ∀ γ < α, sourceFiniteCollapse τ n m γ = sourceFiniteCollapse τ n' m γ) :
    CollapseCandidate (omegaSequence τ) (sourceFiniteCollapse τ n) n m α β ↔
      CollapseCandidate (omegaSequence τ) (sourceFiniteCollapse τ n') n' m α β := by
  have hh := source_low_hull_congr_of_local τ n n' m α β hα.le «local»
  constructor
  · rintro ⟨hβ, hclosed, harg⟩
    refine ⟨hβ, ?_, (hh α hα).1 harg⟩
    intro ξ hin hsmall
    exact hclosed ξ ((hh ξ hsmall).2 hin) hsmall
  · rintro ⟨hβ, hclosed, harg⟩
    refine ⟨hβ, ?_, (hh α hα).2 harg⟩
    intro ξ hin hsmall
    exact hclosed ξ ((hh ξ hsmall).1 hin) hsmall

/-- Every actual finite fragment has the same collapsing function on
low arguments. Neither τ>0 nor source notation membership is needed. -/
theorem sourceFiniteCollapse_low_fragment_agreement (τ : Ordinal) (n n' m : Nat)
    (hm : m < n) (hm' : m < n') (α : Ordinal)
    (hα : α < omegaSequence τ (m + 1)) :
    sourceFiniteCollapse τ n m α = sourceFiniteCollapse τ n' m α := by
  revert hα
  refine WellFoundedLT.induction α (motive := fun ξ =>
    ξ < omegaSequence τ (m + 1) →
    sourceFiniteCollapse τ n m ξ = sourceFiniteCollapse τ n' m ξ) ?_
  intro α ih hα
  have hlocal : ∀ γ < α, sourceFiniteCollapse τ n m γ = sourceFiniteCollapse τ n' m γ := by
    intro γ hγ
    exact ih γ hγ (hγ.trans hα)
  have hc : collapseCandidates (omegaSequence τ) (sourceFiniteCollapse τ n) n m α =
      collapseCandidates (omegaSequence τ) (sourceFiniteCollapse τ n') n' m α := by
    ext β
    change (CollapseCandidate _ _ _ _ _ β ∨ β = omegaSequence τ (m + 1)) ↔
      (CollapseCandidate _ _ _ _ _ β ∨ β = omegaSequence τ (m + 1))
    rw [source_low_candidate_congr_of_local τ n n' m α β hα hlocal]
  change finiteCollapse (omegaSequence τ) n m α = finiteCollapse (omegaSequence τ) n' m α
  rw [finiteCollapse_eq _ _ _ hm, finiteCollapse_eq _ _ _ hm']
  exact congrArg sInf hc

theorem source_low_hull_fragment_agreement (τ : Ordinal) (n n' m : Nat)
    (hm : m < n) (hm' : m < n') (α β ξ : Ordinal)
    (hα : α ≤ omegaSequence τ (m + 1)) (hξ : ξ < omegaSequence τ (m + 1)) :
    Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α β ξ ↔
      Hull (omegaSequence τ) (sourceFiniteCollapse τ n') n' m α β ξ :=
  source_low_hull_congr_of_local τ n n' m α β hα
    (fun γ hγ => sourceFiniteCollapse_low_fragment_agreement τ n n' m hm hm' γ
      (hγ.trans_le hα)) ξ hξ

end Alexander313.Wilken
