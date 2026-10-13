import Alexander313.Wilken.AdditiveNormalForm
import Alexander313.Wilken.TerminalPrincipalArithmetic

/-!
# Ordinary omega powers below actual low collapsing values

Positive additive principals are ordinary omega powers. The representation
below is extracted from the already constructed canonical ANF and its actual
CNF expansion, rather than assumed as a source arithmetic interface.

Ordinal induction then proves that each actual low collapsing value dominates
omega raised to its argument. A purported smaller value has an earlier
exponent, where the induction hypothesis contradicts the genuine strict
increase of the collapsing function. No epsilon-base or enumeration premise
is used. All proof terms await external compilation.
-/

namespace Alexander313.Wilken

universe u

/-- The ordinary omega-exponentiation map is strictly increasing. -/
theorem omegaPower_strictMono :
    StrictMono (fun α : Ordinal.{u} => Ordinal.omega0 ^ α) := by
  intro α β hαβ
  exact (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr hαβ

/-- Self-domination follows directly from strict increase and ordinal
induction; this does not assume a fixed-point enumeration. -/
theorem omegaPower_self_le (α : Ordinal.{u}) : α ≤ Ordinal.omega0 ^ α := by
  refine WellFoundedLT.induction α (motive := fun α => α ≤ Ordinal.omega0 ^ α) ?_
  intro α ih
  apply le_of_not_gt
  intro hsmall
  have hpower := omegaPower_strictMono hsmall
  have hprevious := ih (Ordinal.omega0 ^ α) hsmall
  exact (not_lt_of_ge hprevious) hpower

private theorem expandPrincipalCNF_mem_power
    (xs : List (Ordinal.{u} × Ordinal.{u})) {a : Ordinal.{u}}
    (ha : a ∈ expandPrincipalCNF xs) :
    ∃ δ : Ordinal.{u}, a = Ordinal.omega0 ^ δ := by
  revert ha
  induction xs with
  | nil => simp [expandPrincipalCNF]
  | cons p xs ih =>
    intro ha
    rcases List.mem_append.mp ha with ha | ha
    · exact ⟨p.1, List.eq_of_mem_replicate ha⟩
    · exact ih ha

/-- Every positive additive principal has a genuine ordinary omega-power
representation, obtained from the finite canonical CNF construction. -/
theorem positive_additivePrincipal_eq_omegaPower {α : Ordinal.{u}}
    (hα : 0 < α) (hprincipal : Ordinal.IsPrincipal (· + ·) α) :
    ∃ δ : Ordinal.{u}, α = Ordinal.omega0 ^ δ := by
  have hmem : α ∈ canonicalANF α := by
    rw [canonicalANF_principal hα hprincipal]
    exact List.mem_singleton_self α
  exact expandPrincipalCNF_mem_power _ (normalizePrincipal_mem hmem)

/-- The actual low source function dominates ordinary omega-exponentiation.
Its source minimum and principal/strict-order laws supply every hypothesis. -/
theorem sourceFiniteCollapse_low_omegaPower_le (τ : Ordinal.{0})
    (n m : Nat) (hm : m < n) (α : Ordinal.{0})
    (hα : α < omegaSequence τ (m + 1)) :
    Ordinal.omega0 ^ α ≤ sourceFiniteCollapse τ n m α := by
  revert hα
  refine WellFoundedLT.induction α
    (motive := fun α => α < omegaSequence τ (m + 1) →
      Ordinal.omega0 ^ α ≤ sourceFiniteCollapse τ n m α) ?_
  intro α ih hα
  have hpositive : 0 < sourceFiniteCollapse τ n m α :=
    ((zero_le : 0 ≤ α)).trans_lt (sourceFiniteCollapse_low_argument_lt τ n m hm hα)
  obtain ⟨δ, hδ⟩ := positive_additivePrincipal_eq_omegaPower hpositive
    (sourceFiniteCollapse_add_closed τ n m hm α)
  by_contra! hsmall
  have hδα : δ < α := by
    by_contra! hαδ
    have hpower := omegaPower_strictMono.monotone hαδ
    rw [← hδ] at hpower
    exact (not_le_of_gt hsmall) hpower
  have hprevious := ih δ hδα (hδα.trans hα)
  have hstrict := sourceFiniteCollapse_strictMono_low τ n m hm hδα hα
  rw [hδ] at hstrict
  exact (not_lt_of_ge hprevious) hstrict

/-- Finite/global low coherence transfers the actual exponentiation bound;
the auxiliary outside-domain global value is never invoked. -/
theorem globalCollapse_low_omegaPower_le (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) (α : Ordinal.{0}) (hα : α < omegaSequence τ (m + 1)) :
    Ordinal.omega0 ^ α ≤ globalCollapse τ m α := by
  rw [globalCollapse_low_finite_agreement τ hτ (m + 1) m (Nat.lt_succ_self m) α hα]
  exact sourceFiniteCollapse_low_omegaPower_le τ (m + 1) m (Nat.lt_succ_self m) α hα

/-- For a positive additive principal, closure of its actual initial segment
under ordinary omega powers forces a literal omega fixed point. -/
theorem omegaPower_eq_self_of_principal_closed {β : Ordinal.{u}}
    (hβ : 0 < β) (hprincipal : Ordinal.IsPrincipal (· + ·) β)
    (hclosed : ∀ α < β, Ordinal.omega0 ^ α < β) :
    Ordinal.omega0 ^ β = β := by
  obtain ⟨δ, hδ⟩ := positive_additivePrincipal_eq_omegaPower hβ hprincipal
  have hδle : δ ≤ β := by
    rw [hδ]
    exact omegaPower_self_le δ
  have hδeq : δ = β := by
    apply le_antisymm hδle
    by_contra! hsmall
    have h := hclosed δ hsmall
    rw [← hδ] at h
    exact (lt_irrefl β) h
  simpa only [hδeq] using hδ.symm

end Alexander313.Wilken
