import Alexander313.Wilken.LowNonEpsilonEnumeration
import Alexander313.Wilken.TerminalPrincipalArithmetic

/-!
# Actual global low principal enumeration

Licensed global/finite agreement on the whole low interval transfers the
constructed growth bound and exact non-epsilon principal range. These are
genuine calls of globalCollapse, not its outside-domain zero value. Full
high-argument source arithmetic and public-code tracking remain separate.
Uncompiled candidates.
-/

namespace Alexander313.Wilken

theorem globalCollapse_low_power_upper (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) (α : Ordinal.{0}) (hα : α < omegaSequence τ (m + 1)) :
    globalCollapse τ m α ≤ Ordinal.omega0 ^ (omegaSequence τ m + α + 1) := by
  rw [globalCollapse_low_finite_agreement τ hτ (m + 1) m (Nat.lt_succ_self m) α hα]
  exact sourceFiniteCollapse_low_power_upper τ (m + 1) m (Nat.lt_succ_self m) α hα

theorem globalCollapse_low_epsilon_eq_base (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) (α : Ordinal.{0}) (hα : α < omegaSequence τ (m + 1))
    (hepsilon : Ordinal.omega0 ^ globalCollapse τ m α = globalCollapse τ m α) :
    globalCollapse τ m α = omegaSequence τ m := by
  have hagree := globalCollapse_low_finite_agreement τ hτ (m + 1) m (Nat.lt_succ_self m) α hα
  rw [hagree] at hepsilon ⊢
  exact sourceFiniteCollapse_low_epsilon_eq_base τ (m + 1) m (Nat.lt_succ_self m) α hα hepsilon

theorem globalCollapse_low_non_epsilon_of_pos (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) (α : Ordinal.{0}) (hpositive : 0 < α)
    (hα : α < omegaSequence τ (m + 1)) :
    Ordinal.omega0 ^ globalCollapse τ m α ≠ globalCollapse τ m α := by
  rw [globalCollapse_low_finite_agreement τ hτ (m + 1) m (Nat.lt_succ_self m) α hα]
  exact sourceFiniteCollapse_low_non_epsilon_of_pos τ (m + 1) m (Nat.lt_succ_self m)
    α hpositive hα

theorem globalCollapse_low_range_iff (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) (β : Ordinal.{0}) :
    (∃ α : Ordinal.{0}, α < omegaSequence τ (m + 1) ∧ globalCollapse τ m α = β) ↔
      0 < β ∧ Ordinal.IsPrincipal (· + ·) β ∧ omegaSequence τ m ≤ β ∧
      β < omegaSequence τ (m + 1) ∧
      (β = omegaSequence τ m ∨ Ordinal.omega0 ^ β ≠ β) := by
  have hagree : (∃ α : Ordinal.{0}, α < omegaSequence τ (m + 1) ∧
      globalCollapse τ m α = β) ↔
      ∃ α : Ordinal.{0}, α < omegaSequence τ (m + 1) ∧
        sourceFiniteCollapse τ (m + 1) m α = β := by
    constructor <;> rintro ⟨α, hα, he⟩
    · refine ⟨α, hα, ?_⟩
      rw [← globalCollapse_low_finite_agreement τ hτ (m + 1) m (Nat.lt_succ_self m) α hα]
      exact he
    · refine ⟨α, hα, ?_⟩
      rw [globalCollapse_low_finite_agreement τ hτ (m + 1) m (Nat.lt_succ_self m) α hα]
      exact he
  exact hagree.trans (sourceFiniteCollapse_low_range_iff τ (m + 1) m (Nat.lt_succ_self m) β)

/-- The range statement applies to the actual hereditary finite bases because
their positivity and principal class were constructed earlier. -/
theorem RelativeTerm.Hereditary.finiteBase_collapse_low_range_iff
    (r m : Nat) (β : Ordinal.{0}) :
    (∃ α : Ordinal.{0}, α < omegaSequence (RelativeTerm.Hereditary.finiteBase r) (m + 1) ∧
      globalCollapse (RelativeTerm.Hereditary.finiteBase r) m α = β) ↔
      0 < β ∧ Ordinal.IsPrincipal (· + ·) β ∧
      omegaSequence (RelativeTerm.Hereditary.finiteBase r) m ≤ β ∧
      β < omegaSequence (RelativeTerm.Hereditary.finiteBase r) (m + 1) ∧
      (β = omegaSequence (RelativeTerm.Hereditary.finiteBase r) m ∨ Ordinal.omega0 ^ β ≠ β) :=
  globalCollapse_low_range_iff (RelativeTerm.Hereditary.finiteBase r)
    (RelativeTerm.Hereditary.finiteBase_pos r) m β

end Alexander313.Wilken
