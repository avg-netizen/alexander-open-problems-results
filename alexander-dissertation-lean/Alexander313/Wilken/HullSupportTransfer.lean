import Alexander313.Wilken.FiniteCoverage

/-!
# Support transfer along actual hull derivations

Higher collapsing arguments need not be smaller than their outputs or
than a fragment cutoff. This proof transfers their canonical P support
instead. Arbitrary addition can absorb atoms, so its proved support law
is an inclusion; no raw-leaf union or normal-sum premise is substituted.
All terms are candidates awaiting external compilation.
-/

namespace Alexander313.Wilken

/-- Absorption may remove support, but addition introduces none. -/
theorem sourceP_add_subset (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (ξ a b : SourceNotationOrdinal τ n (m + 1))
    (heq : ξ.val = a.val + b.val) :
    sourceP τ hτ n m hm ξ ⊆ sourceP τ hτ n m hm a ∪ sourceP τ hτ n m hm b := by
  classical
  intro p hp
  obtain ⟨c, hc, hp⟩ := (sourceP_mem_anf τ hτ n m hm ξ p).1 hp
  have hc' : c ∈ canonicalANF (a.val + b.val) := by simpa only [heq] using hc
  rcases canonicalANF_add_mem hc' with ha | hb
  · exact Finset.mem_union.2 (Or.inl ((sourceP_mem_anf τ hτ n m hm a p).2 ⟨c, ha, hp⟩))
  · exact Finset.mem_union.2 (Or.inr ((sourceP_mem_anf τ hτ n m hm b p).2 ⟨c, hb, hp⟩))

/-- Bounded hull membership supplies the actual next-level domain. -/
theorem source_hull_next_notation (τ : Ordinal.{0}) (n m : Nat) (hm : m < n)
    {α β ξ : Ordinal.{0}} (hα : α ≤ omegaSequence τ (m + 2))
    (hβ : β ≤ omegaSequence τ (m + 1))
    (hξ : Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α β ξ) :
    sourceNotation τ n (m + 1) ξ :=
  (source_nextNotation_iff_hull τ n m hm ξ).2
    (source_hull_to_admissible τ n m hm hα hβ hξ)

/-- Transfer actual support through the hull rules. The predicate Q is
used as an induction invariant; later fragment theorems instantiate it
with an actual hull and prove every closure premise. -/
theorem source_hull_support_transfer (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (α β : Ordinal.{0})
    (hα : α ≤ omegaSequence τ (m + 2)) (hβ : β ≤ omegaSequence τ (m + 1))
    (Q : Ordinal.{0} → Prop)
    (base : ∀ p < omegaSequence τ m, Q p)
    (parameter : ∀ p < β, Q p)
    («local» : ∀ γ : SourceNotationOrdinal τ n (m + 1), γ.val < α →
      (∀ p ∈ sourceP τ hτ n m hm γ, Q p) → Q (sourceFiniteCollapse τ n m γ.val))
    {ξ : Ordinal.{0}}
    (hξ : Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α β ξ)
    (x : SourceNotationOrdinal τ n (m + 1)) (hx : x.val = ξ) :
    ∀ p ∈ sourceP τ hτ n m hm x, Q p := by
  classical
  revert x
  induction hξ with
  | @below_base ξ h =>
    intro x hx p hp
    have hsmall : x.val < omegaSequence τ (m + 1) := by
      rw [hx]; exact h.trans (omegaSequence_step τ m)
    rw [sourceP_low τ hτ n m hm x hsmall, List.mem_toFinset] at hp
    exact base p ((canonicalANF_mem_le hp).trans_lt (by simpa only [hx] using h))
  | @below_parameter ξ h =>
    intro x hx p hp
    have hsmall : x.val < omegaSequence τ (m + 1) := by rw [hx]; exact h.trans_le hβ
    rw [sourceP_low τ hτ n m hm x hsmall, List.mem_toFinset] at hp
    exact parameter p ((canonicalANF_mem_le hp).trans_lt (by simpa only [hx] using h))
  | @add a b ha hb iha ihb =>
    intro x hx p hp
    let a' : SourceNotationOrdinal τ n (m + 1) :=
      ⟨a, source_hull_next_notation τ n m hm hα hβ ha⟩
    let b' : SourceNotationOrdinal τ n (m + 1) :=
      ⟨b, source_hull_next_notation τ n m hm hα hβ hb⟩
    rcases Finset.mem_union.1 (sourceP_add_subset τ hτ n m hm x a' b' hx hp) with hp | hp
    · exact iha a' rfl p hp
    · exact ihb b' rfl p hp
  | @higher k γ hmk hkn hsort hγ ih =>
    intro x hx p hp
    let γ' : SourceNotationOrdinal τ n (m + 1) :=
      ⟨γ, source_hull_next_notation τ n m hm hα hβ hγ⟩
    rw [sourceP_theta τ hτ n m hm x γ' k hmk hkn hsort hx] at hp
    exact ih γ' rfl p hp
  | @«local» γ hγα hγ ih =>
    intro x hx p hp
    let γ' : SourceNotationOrdinal τ n (m + 1) :=
      ⟨γ, source_hull_next_notation τ n m hm hα hβ hγ⟩
    have hsmall : x.val < omegaSequence τ (m + 1) := by
      rw [hx]
      exact sourceFiniteCollapse_proper_notation τ n m hm γ (hγα.trans_le hα) γ'.property
    have hanf := canonicalANF_principal (sourceFiniteCollapse_pos τ hτ n m hm γ)
      (sourceFiniteCollapse_add_closed τ n m hm γ)
    rw [sourceP_low τ hτ n m hm x hsmall, hx, hanf, List.mem_toFinset,
      List.mem_singleton] at hp
    subst p
    exact «local» γ' hγα (ih γ' rfl)

end Alexander313.Wilken
