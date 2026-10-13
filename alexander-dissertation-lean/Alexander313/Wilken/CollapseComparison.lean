import Alexander313.Wilken.FiniteNotations

/-!
# Injectivity and comparison of the constructed collapsing functions

The injectivity part of Wilken Lemma 2.10(d) follows directly from the
minimum and hull equations on the now constructed Tⁿₘ₊₁ domain. This module
also proves exact comparisons in terms of membership in the defining hull.
No comparison law is an assumed field or package.

Replacing those hull tests by the finite star-support inequalities of the
displayed Lemma 2.10(d) still requires the source normal-form/support theorem.
The hull characterization here is semantic, not an effective decision rule.
All proof terms are uncompiled candidates.
-/

namespace Alexander313.Wilken

/-- The domain of ϑⁿₘ used by Wilken Lemma 2.10(c,d). -/
def sourceCollapseDomain (τ : Ordinal) (n m : Nat) : Set Ordinal :=
  {α | sourceNotation τ n (m + 1) α ∧ α < omegaSequence τ (m + 2)}

/-- If the arguments increase and the values do not decrease, the values
strictly increase: the earlier collapsing call belongs to the later hull. -/
theorem finiteCollapse_strict_of_argument_lt {omega : Nat → Ordinal} {n m : Nat}
    (hm : m < n) {α γ : Ordinal} (hα : finiteCollapse omega n m α < omega (m + 1))
    (hαγ : α < γ) (hvalues : finiteCollapse omega n m α ≤ finiteCollapse omega n m γ) :
    finiteCollapse omega n m α < finiteCollapse omega n m γ := by
  have hinα := finiteCollapse_arg_mem_of_lt hm α hα
  have hinγ := hull_mono hαγ.le hvalues hinα
  have hcall := Hull.«local» hαγ hinγ
  exact (finiteCollapse_hull_initial hm γ _).mp ⟨hcall, hα⟩

/-- The actual source restriction is one-to-one. No ANF/support or
comparison contract is used to prove this part of Lemma 2.10(d). -/
theorem sourceFiniteCollapse_injective_on (τ : Ordinal) (n m : Nat) (hm : m < n) :
    Set.InjOn (sourceFiniteCollapse τ n m) (sourceCollapseDomain τ n m) := by
  intro α hα γ hγ heq
  rcases lt_trichotomy α γ with hαγ | hαγ | hγα
  · have hproper := sourceFiniteCollapse_proper_notation τ n m hm α hα.2 hα.1
    have hstrict := finiteCollapse_strict_of_argument_lt hm hproper hαγ heq.le
    exact False.elim (heq.not_lt hstrict)
  · exact hαγ
  · have hproper := sourceFiniteCollapse_proper_notation τ n m hm γ hγ.2 hγ.1
    have hstrict := finiteCollapse_strict_of_argument_lt hm hproper hγα heq.symm.le
    exact False.elim (heq.symm.not_lt hstrict)

theorem sourceFiniteCollapse_eq_iff (τ : Ordinal) (n m : Nat) (hm : m < n)
    {α γ : Ordinal} (hα : α ∈ sourceCollapseDomain τ n m)
    (hγ : γ ∈ sourceCollapseDomain τ n m) :
    sourceFiniteCollapse τ n m α = sourceFiniteCollapse τ n m γ ↔ α = γ :=
  ⟨sourceFiniteCollapse_injective_on τ n m hm hα hγ, fun h => congrArg _ h⟩

/-- The actual comparison law before finite normal-form support extraction. -/
theorem sourceFiniteCollapse_lt_iff_hulls (τ : Ordinal) (n m : Nat) (hm : m < n)
    {α γ : Ordinal} (hα : α ∈ sourceCollapseDomain τ n m)
    (hγ : γ ∈ sourceCollapseDomain τ n m) :
    sourceFiniteCollapse τ n m α < sourceFiniteCollapse τ n m γ ↔
      (α < γ ∧ Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m γ
        (sourceFiniteCollapse τ n m γ) α) ∨
      (γ < α ∧ ¬ Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α
        (sourceFiniteCollapse τ n m α) γ) := by
  have hproperα := sourceFiniteCollapse_proper_notation τ n m hm α hα.2 hα.1
  have hproperγ := sourceFiniteCollapse_proper_notation τ n m hm γ hγ.2 hγ.1
  have hargα := sourceFiniteCollapse_argument_notation τ n m hm α hα.2 hα.1
  have hargγ := sourceFiniteCollapse_argument_notation τ n m hm γ hγ.2 hγ.1
  constructor
  · intro hvalues
    rcases lt_trichotomy α γ with hαγ | hαγ | hγα
    · exact Or.inl ⟨hαγ, hull_mono hαγ.le hvalues.le hargα⟩
    · subst γ
      exact False.elim (lt_irrefl _ hvalues)
    · refine Or.inr ⟨hγα, ?_⟩
      intro hinγ
      have hcall := Hull.«local» hγα hinγ
      have hreverse := (finiteCollapse_hull_initial hm α _).mp ⟨hcall, hproperγ⟩
      exact (lt_asymm hvalues hreverse)
  · rintro (⟨hαγ, hinα⟩ | ⟨hγα, hnot⟩)
    · have hcall := Hull.«local» hαγ hinα
      exact (finiteCollapse_hull_initial hm γ _).mp ⟨hcall, hproperα⟩
    · by_contra! hvalues
      exact hnot (hull_mono hγα.le hvalues hargγ)

/-- For increasing arguments, only the positive later-hull test is needed. -/
theorem sourceFiniteCollapse_lt_iff_later_hull (τ : Ordinal) (n m : Nat) (hm : m < n)
    {α γ : Ordinal} (hα : α ∈ sourceCollapseDomain τ n m)
    (hγ : γ ∈ sourceCollapseDomain τ n m) (hαγ : α < γ) :
    sourceFiniteCollapse τ n m α < sourceFiniteCollapse τ n m γ ↔
      Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m γ
        (sourceFiniteCollapse τ n m γ) α := by
  rw [sourceFiniteCollapse_lt_iff_hulls τ n m hm hα hγ]
  simp only [hαγ, true_and, hαγ.not_gt, false_and, or_false]

/-- For decreasing arguments, the negative earlier-hull test is exact. -/
theorem sourceFiniteCollapse_lt_iff_not_earlier_hull (τ : Ordinal) (n m : Nat) (hm : m < n)
    {α γ : Ordinal} (hα : α ∈ sourceCollapseDomain τ n m)
    (hγ : γ ∈ sourceCollapseDomain τ n m) (hγα : γ < α) :
    sourceFiniteCollapse τ n m α < sourceFiniteCollapse τ n m γ ↔
      ¬ Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α
        (sourceFiniteCollapse τ n m α) γ := by
  rw [sourceFiniteCollapse_lt_iff_hulls τ n m hm hα hγ]
  simp only [hγα, true_and, hγα.not_gt, false_and, false_or]

end Alexander313.Wilken
