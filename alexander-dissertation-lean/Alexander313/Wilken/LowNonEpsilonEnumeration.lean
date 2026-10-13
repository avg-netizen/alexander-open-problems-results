import Alexander313.Wilken.LowPowerBounds

/-!
# The complete positive-principal range of the actual low collapse

A least-index argument constructs a preimage of every positive non-epsilon
additive principal above the starting base and below the next cardinal. The
only possible epsilon output is the base itself, which is hit at zero whenever
it is a positive additive principal. This is about genuine low ordinal inputs;
full high-argument arithmetic, tracking, reflection and public-code algorithms
are separate. No enumeration theorem is an input. Uncompiled.
-/

namespace Alexander313.Wilken

/-- The real zero minimum is the base whenever that base is itself a positive
additive principal. This also states precisely the exceptional range endpoint. -/
theorem sourceFiniteCollapse_zero_of_base_principal (τ : Ordinal.{0})
    (n m : Nat) (hm : m < n)
    (hpositive : 0 < omegaSequence τ m)
    (hprincipal : Ordinal.IsPrincipal (· + ·) (omegaSequence τ m)) :
    sourceFiniteCollapse τ n m 0 = omegaSequence τ m := by
  apply le_antisymm
  · apply (sourceFiniteCollapse_low_le_iff_principal τ n m hm 0 (omegaSequence τ m)
      (hpositive.trans (omegaSequence_step τ m)) (omegaSequence_step τ m) hprincipal).mpr
    refine ⟨le_rfl, hpositive, ?_⟩
    intro γ hγ
    exact False.elim ((not_lt_of_ge ((zero_le : 0 ≤ γ))) hγ)
  · exact (sourceFiniteCollapse_bounds τ n m hm 0).1

/-- Actual preimage construction for the full low non-epsilon principal range.
The least crossing index is at most beta. Equality would force omega-power
closure below beta, contrary to the supplied literal non-epsilon condition. -/
theorem sourceFiniteCollapse_low_covers_non_epsilon (τ : Ordinal.{0})
    (n m : Nat) (hm : m < n) (β : Ordinal.{0}) (hpositive : 0 < β)
    (hprincipal : Ordinal.IsPrincipal (· + ·) β)
    (hbase : omegaSequence τ m ≤ β) (hβ : β < omegaSequence τ (m + 1))
    (hnon : Ordinal.omega0 ^ β ≠ β) :
    ∃ α : Ordinal.{0}, α < omegaSequence τ (m + 1) ∧
      sourceFiniteCollapse τ n m α = β := by
  let S : Set Ordinal.{0} := {α | β ≤ sourceFiniteCollapse τ n m α}
  have hβmem : β ∈ S := (sourceFiniteCollapse_low_argument_lt τ n m hm hβ).le
  let α := sInf S
  have hcross : β ≤ sourceFiniteCollapse τ n m α := csInf_mem ⟨β, hβmem⟩
  have hαβ : α ≤ β := csInf_le' hβmem
  have hα : α < omegaSequence τ (m + 1) := hαβ.trans_lt hβ
  have hprevious : ∀ γ < α, sourceFiniteCollapse τ n m γ < β := by
    intro γ hγα
    by_contra! hγ
    have hmin : α ≤ γ := csInf_le' hγ
    exact (not_lt_of_ge hmin) hγα
  have hstrict : α < β := by
    apply lt_of_le_of_ne hαβ
    intro he
    apply hnon
    apply omegaPower_eq_self_of_principal_closed hpositive hprincipal
    intro γ hγ
    have hγα : γ < α := by simpa only [he] using hγ
    exact (sourceFiniteCollapse_low_omegaPower_le τ n m hm γ (hγ.trans hβ)).trans_lt
      (hprevious γ hγα)
  refine ⟨α, hα, le_antisymm ?_ hcross⟩
  exact (sourceFiniteCollapse_low_le_iff_principal τ n m hm α β hα hβ hprincipal).mpr
    ⟨hbase, hstrict, hprevious⟩

/-- Exact range classification on the actual low interval. This includes the
base endpoint precisely when it is positive and principal, without changing
the original total function or using its outside-domain values. -/
theorem sourceFiniteCollapse_low_range_iff (τ : Ordinal.{0})
    (n m : Nat) (hm : m < n) (β : Ordinal.{0}) :
    (∃ α : Ordinal.{0}, α < omegaSequence τ (m + 1) ∧
      sourceFiniteCollapse τ n m α = β) ↔
      0 < β ∧ Ordinal.IsPrincipal (· + ·) β ∧ omegaSequence τ m ≤ β ∧
      β < omegaSequence τ (m + 1) ∧
      (β = omegaSequence τ m ∨ Ordinal.omega0 ^ β ≠ β) := by
  constructor
  · rintro ⟨α, hα, rfl⟩
    refine ⟨((zero_le : 0 ≤ α)).trans_lt (sourceFiniteCollapse_low_argument_lt τ n m hm hα),
      sourceFiniteCollapse_add_closed τ n m hm α,
      (sourceFiniteCollapse_bounds τ n m hm α).1,
      sourceFiniteCollapse_proper_notation τ n m hm α
        (hα.trans (omegaSequence_step τ (m + 1)))
        (sourceNotation_next_of_low τ n m hm hα), ?_⟩
    by_cases h : Ordinal.omega0 ^ sourceFiniteCollapse τ n m α =
        sourceFiniteCollapse τ n m α
    · exact Or.inl (sourceFiniteCollapse_low_epsilon_eq_base τ n m hm α hα h)
    · exact Or.inr h
  · rintro ⟨hpositive, hprincipal, hbase, hβ, hendpoint | hnon⟩
    · subst β
      exact ⟨0, hpositive.trans (omegaSequence_step τ m),
        sourceFiniteCollapse_zero_of_base_principal τ n m hm hpositive hprincipal⟩
    · exact sourceFiniteCollapse_low_covers_non_epsilon τ n m hm β hpositive
        hprincipal hbase hβ hnon

/-- Strict monotonicity gives the unique real low index of every value in this
range; syntactic public-code uniqueness is not asserted. -/
theorem sourceFiniteCollapse_low_preimage_unique (τ : Ordinal.{0})
    (n m : Nat) (hm : m < n) (α β : Ordinal.{0})
    (hα : α < omegaSequence τ (m + 1)) (hβ : β < omegaSequence τ (m + 1))
    (he : sourceFiniteCollapse τ n m α = sourceFiniteCollapse τ n m β) : α = β := by
  rcases lt_trichotomy α β with h | h | h
  · have hs := sourceFiniteCollapse_strictMono_low τ n m hm h hβ
    rw [he] at hs
    exact False.elim ((lt_irrefl _) hs)
  · exact h
  · have hs := sourceFiniteCollapse_strictMono_low τ n m hm h hα
    rw [he] at hs
    exact False.elim ((lt_irrefl _) hs)

end Alexander313.Wilken
