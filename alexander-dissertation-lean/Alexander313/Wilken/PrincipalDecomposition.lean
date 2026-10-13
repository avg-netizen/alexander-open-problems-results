import Alexander313.Wilken.CanonicalHullSupport
import Alexander313.Wilken.CollapseComparison

/-!
# Actual principal representations in the finite source domain

Every canonical principal summand of a finite source notation is either a
parameter or an actual source collapsing value. The proof follows the
finite grammar and the canonical absorption law, so a surviving summand
is not an arbitrarily chosen leaf of a raw sum expression.

The argument sort and notation domain give the proper range of each
collapsing call. Disjoint cardinal ranges determine its level, and the
already constructed source injectivity determines its argument. These
are prerequisites for Definition 2.9; this module does not assert the
full P/star recursion or an effective comparison algorithm.
All proof terms await external compilation.
-/

namespace Alexander313.Wilken

/-- Iterate the proved source inclusion through any bounded number of
levels. The terminal case is exactly Tⁿₙ=Ωₙ. -/
theorem sourceNotation_add_steps (τ : Ordinal) (n r d : Nat)
    {ξ : Ordinal} (hξ : sourceNotation τ n r ξ) (hbound : r + d ≤ n) :
    sourceNotation τ n (r + d) ξ := by
  revert hbound
  induction d with
  | zero => intro _; simpa using hξ
  | succ d ih =>
    intro hbound
    have hs : r + d < n := by omega
    have hprev := ih hs.le
    simpa only [Nat.add_succ] using sourceNotation_embeds_next τ n (r + d) hs hprev

theorem sourceNotation_upward (τ : Ordinal) (n r s : Nat)
    (hrs : r ≤ s) (hs : s ≤ n) {ξ : Ordinal} (hξ : sourceNotation τ n r ξ) :
    sourceNotation τ n s ξ := by
  have heq : r + (s - r) = s := by omega
  have hbound : r + (s - r) ≤ n := by omega
  simpa only [heq] using sourceNotation_add_steps τ n r (s - r) hξ hbound

/-- An actual collapsing constructor in a lower source grammar lies in
its proper cardinal range. No range premise is supplied by a caller. -/
theorem sourceFiniteCollapse_typed_range (τ : Ordinal) (n r k : Nat)
    (hrk : r ≤ k) (hk : k < n) (α : Ordinal)
    (hα : sourceNotation τ n r α) (hsort : α < omegaSequence τ (k + 2)) :
    omegaSequence τ k ≤ sourceFiniteCollapse τ n k α ∧
      sourceFiniteCollapse τ n k α < omegaSequence τ (k + 1) := by
  refine ⟨(sourceFiniteCollapse_bounds τ n k hk α).1, ?_⟩
  exact sourceFiniteCollapse_proper_notation τ n k hk α hsort
    (sourceNotation_upward τ n r (k + 1) (hrk.trans (Nat.le_succ k))
      (Nat.succ_le_of_lt hk) hα)

/-- Each surviving canonical atom has a genuine constructor from the
finite source grammar, with its original admissible argument retained. -/
theorem sourceNotation_canonical_atom_cases (τ : Ordinal) (hτ : 0 < τ)
    (n r : Nat) (hr : r < n) {ξ : Ordinal}
    (hξ : sourceNotation τ n r ξ) :
    ∀ a ∈ canonicalANF ξ, a < omegaSequence τ r ∨
      ∃ k α, r ≤ k ∧ k < n ∧ sourceNotation τ n r α ∧
        α < omegaSequence τ (k + 2) ∧ a = sourceFiniteCollapse τ n k α := by
  rw [sourceNotation, if_pos hr] at hξ
  induction hξ with
  | parameter hξ =>
    intro a ha
    exact Or.inl ((canonicalANF_mem_le ha).trans_lt hξ)
  | add hξ hη ihξ ihη =>
    intro a ha
    exact (canonicalANF_add_mem ha).elim (ihξ a) (ihη a)
  | @collapse k α hrk hkn hsort hα ih =>
    intro a ha
    have hanf := canonicalANF_principal
      (sourceFiniteCollapse_pos τ hτ n k hkn α)
      (sourceFiniteCollapse_add_closed τ n k hkn α)
    rw [hanf, List.mem_singleton] at ha
    subst a
    refine Or.inr ⟨k, α, hrk, hkn, ?_, hsort, rfl⟩
    rw [sourceNotation, if_pos hr]
    exact hα

/-- Principal notations have the literal parameter/θ alternatives. -/
theorem sourceNotation_principal_cases (τ : Ordinal) (hτ : 0 < τ)
    (n r : Nat) (hr : r < n) {ξ : Ordinal}
    (hξ : sourceNotation τ n r ξ) (hpos : 0 < ξ)
    (hprincipal : Ordinal.IsPrincipal (· + ·) ξ) :
    ξ < omegaSequence τ r ∨
      ∃ k α, r ≤ k ∧ k < n ∧ sourceNotation τ n r α ∧
        α < omegaSequence τ (k + 2) ∧ ξ = sourceFiniteCollapse τ n k α := by
  apply sourceNotation_canonical_atom_cases τ hτ n r hr hξ ξ
  rw [canonicalANF_principal hpos hprincipal]
  exact List.mem_singleton_self _

/-- Disjoint proper cardinal ranges make the written collapsing level
unique. This includes the top, non-collapsing finite level. -/
theorem sourceFiniteCollapse_level_eq (τ : Ordinal) (n k l : Nat)
    (hk : k < n) (hl : l < n) {α γ : Ordinal}
    (hα : α ∈ sourceCollapseDomain τ n k)
    (hγ : γ ∈ sourceCollapseDomain τ n l)
    (heq : sourceFiniteCollapse τ n k α = sourceFiniteCollapse τ n l γ) : k = l := by
  have hkrange := sourceFiniteCollapse_bounds τ n k hk α
  have hlrange := sourceFiniteCollapse_bounds τ n l hl γ
  have hkproper := sourceFiniteCollapse_proper_notation τ n k hk α hα.2 hα.1
  have hlproper := sourceFiniteCollapse_proper_notation τ n l hl γ hγ.2 hγ.1
  rcases lt_trichotomy k l with hkl | hkl | hlk
  · have hlevels : omegaSequence τ (k + 1) ≤ omegaSequence τ l :=
      (omegaSequence_strictMono τ).monotone (Nat.succ_le_of_lt hkl)
    have hvalues := (hkproper.trans_le hlevels).trans_le hlrange.1
    exact False.elim ((ne_of_lt hvalues) heq)
  · exact hkl
  · have hlevels : omegaSequence τ (l + 1) ≤ omegaSequence τ k :=
      (omegaSequence_strictMono τ).monotone (Nat.succ_le_of_lt hlk)
    have hvalues := (hlproper.trans_le hlevels).trans_le hkrange.1
    exact False.elim ((ne_of_lt hvalues) heq.symm)

/-- Uniqueness of the actual level and argument of a principal θ value,
using the same common finite grammar for both arguments. -/
theorem sourceFiniteCollapse_presentation_unique (τ : Ordinal) (n r k l : Nat)
    (hrk : r ≤ k) (hrl : r ≤ l) (hk : k < n) (hl : l < n)
    {α γ : Ordinal} (hα : sourceNotation τ n r α) (hγ : sourceNotation τ n r γ)
    (hsortα : α < omegaSequence τ (k + 2))
    (hsortγ : γ < omegaSequence τ (l + 2))
    (heq : sourceFiniteCollapse τ n k α = sourceFiniteCollapse τ n l γ) :
    k = l ∧ α = γ := by
  have hdomα : α ∈ sourceCollapseDomain τ n k :=
    ⟨sourceNotation_upward τ n r (k + 1) (hrk.trans (Nat.le_succ k))
      (Nat.succ_le_of_lt hk) hα, hsortα⟩
  have hdomγ : γ ∈ sourceCollapseDomain τ n l :=
    ⟨sourceNotation_upward τ n r (l + 1) (hrl.trans (Nat.le_succ l))
      (Nat.succ_le_of_lt hl) hγ, hsortγ⟩
  have hkl := sourceFiniteCollapse_level_eq τ n k l hk hl hdomα hdomγ heq
  subst l
  exact ⟨rfl, sourceFiniteCollapse_injective_on τ n k hk hdomα hdomγ heq⟩

/-- A parameter leaf and an actual admissible collapsing constructor
cannot denote the same principal atom at a fixed finite source base. -/
theorem sourceFiniteCollapse_not_parameter (τ : Ordinal) (n r k : Nat)
    (hrk : r ≤ k) (hk : k < n) (α : Ordinal) {ξ : Ordinal}
    (hξ : ξ < omegaSequence τ r) : ξ ≠ sourceFiniteCollapse τ n k α := by
  have hlevels : omegaSequence τ r ≤ omegaSequence τ k :=
    (omegaSequence_strictMono τ).monotone hrk
  exact ne_of_lt (hξ.trans_le
    (hlevels.trans (sourceFiniteCollapse_bounds τ n k hk α).1))

end Alexander313.Wilken
