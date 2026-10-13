import Alexander313.Wilken.CollapseExponentiation
import Alexander313.Wilken.LowCollapseArithmetic

/-!
# A genuine omega-power upper bound for the low source collapse

The actual low minimum is bounded above by omega^(Omega_m + alpha + 1).
The proof uses ordinal induction, the real low principal-minimum criterion,
and the previously proved lower power bound to license powers below the next
cardinal. No epsilon enumeration or supplied arithmetic bound is assumed.
All terms are uncompiled candidates.
-/

namespace Alexander313.Wilken

private theorem lowPower_add_left_strict (a : Ordinal.{0}) {b c : Ordinal.{0}}
    (h : b < c) : a + b < a + c := by
  have hle : a + b ≤ a + c := add_le_add_right h.le a
  have hne : a + b ≠ a + c := fun he => h.ne (add_left_cancel he)
  exact lt_of_le_of_ne hle hne

/-- Ordinary omega powers of low arguments remain genuinely below the next
cardinal. This is derived from the actual source collapse, not a cardinal-power
formula or an outside-domain fallback. -/
theorem omegaPower_lt_next_cardinal (τ : Ordinal.{0}) (n m : Nat) (hm : m < n)
    (α : Ordinal.{0}) (hα : α < omegaSequence τ (m + 1)) :
    Ordinal.omega0 ^ α < omegaSequence τ (m + 1) :=
  (sourceFiniteCollapse_low_omegaPower_le τ n m hm α hα).trans_lt
    (sourceFiniteCollapse_proper_notation τ n m hm α
      (hα.trans (omegaSequence_step τ (m + 1)))
      (sourceNotation_next_of_low τ n m hm hα))

/-- A concrete growth bound for the actual low collapse at every ordinal
argument in its true low domain. In particular, the induction covers arbitrary
limits, rather than only displayed countable sequences. -/
theorem sourceFiniteCollapse_low_power_upper (τ : Ordinal.{0})
    (n m : Nat) (hm : m < n) (α : Ordinal.{0})
    (hα : α < omegaSequence τ (m + 1)) :
    sourceFiniteCollapse τ n m α ≤
      Ordinal.omega0 ^ (omegaSequence τ m + α + 1) := by
  revert hα
  refine WellFoundedLT.induction α
    (motive := fun α => α < omegaSequence τ (m + 1) →
      sourceFiniteCollapse τ n m α ≤ Ordinal.omega0 ^ (omegaSequence τ m + α + 1)) ?_
  intro α ih hα
  let δ := omegaSequence τ m + α + 1
  let β := Ordinal.omega0 ^ δ
  have hsum : omegaSequence τ m + α < omegaSequence τ (m + 1) :=
    omegaSequence_add_closed τ m (omegaSequence_step τ m) hα
  have hδ : δ < omegaSequence τ (m + 1) :=
    (omegaSequence_isSuccLimit τ m).add_one_lt hsum
  have hβ : β < omegaSequence τ (m + 1) :=
    omegaPower_lt_next_cardinal τ n m hm δ hδ
  have hprincipal : Ordinal.IsPrincipal (· + ·) β :=
    Ordinal.isPrincipal_add_omega0_opow δ
  have hbaseδ : omegaSequence τ m < δ :=
    le_self_add.trans_lt (lt_add_one (omegaSequence τ m + α))
  have hαδ : α < δ :=
    le_add_self.trans_lt (lt_add_one (omegaSequence τ m + α))
  have hδβ : δ ≤ β := omegaPower_self_le δ
  apply (sourceFiniteCollapse_low_le_iff_principal τ n m hm α β hα hβ hprincipal).mpr
  refine ⟨hbaseδ.le.trans hδβ, hαδ.trans_le hδβ, ?_⟩
  intro γ hγα
  have hγ : γ < omegaSequence τ (m + 1) := hγα.trans hα
  have hstep : γ + 1 < α + 1 := (Order.add_one_le_of_lt hγα).trans_lt (lt_add_one α)
  have hexp : omegaSequence τ m + γ + 1 < δ := by
    simpa only [δ, add_assoc] using lowPower_add_left_strict (omegaSequence τ m) hstep
  exact (ih γ hγα hγ).trans_lt (omegaPower_strictMono hexp)

/-- A low value which is an omega fixed point can only be the starting base.
The actual principal output and strict argument bound are essential. -/
theorem sourceFiniteCollapse_low_epsilon_eq_base (τ : Ordinal.{0})
    (n m : Nat) (hm : m < n) (α : Ordinal.{0})
    (hα : α < omegaSequence τ (m + 1))
    (hepsilon : Ordinal.omega0 ^ sourceFiniteCollapse τ n m α =
      sourceFiniteCollapse τ n m α) :
    sourceFiniteCollapse τ n m α = omegaSequence τ m := by
  let β := sourceFiniteCollapse τ n m α
  have hbase : omegaSequence τ m ≤ β := (sourceFiniteCollapse_bounds τ n m hm α).1
  by_contra hne
  have hbaseβ : omegaSequence τ m < β := lt_of_le_of_ne hbase (Ne.symm hne)
  have hαβ : α < β := sourceFiniteCollapse_low_argument_lt τ n m hm hα
  have hpositive : 0 < β := ((zero_le : 0 ≤ α)).trans_lt hαβ
  have hprincipal : Ordinal.IsPrincipal (· + ·) β :=
    sourceFiniteCollapse_add_closed τ n m hm α
  have hone : 1 < β := by
    have h := omegaPower_strictMono hpositive
    dsimp only [β] at h
    rw [hepsilon] at h
    simpa only [Ordinal.opow_zero] using h
  have hexp : omegaSequence τ m + α + 1 < β :=
    hprincipal (hprincipal hbaseβ hαβ) hone
  have hpower : Ordinal.omega0 ^ (omegaSequence τ m + α + 1) < β := by
    have h := omegaPower_strictMono hexp
    dsimp only [β] at h
    rw [hepsilon] at h
    exact h
  exact (not_lt_of_ge (sourceFiniteCollapse_low_power_upper τ n m hm α hα)) hpower

/-- Every positive low input has a genuinely non-epsilon principal value. -/
theorem sourceFiniteCollapse_low_non_epsilon_of_pos (τ : Ordinal.{0})
    (n m : Nat) (hm : m < n) (α : Ordinal.{0})
    (hpositive : 0 < α) (hα : α < omegaSequence τ (m + 1)) :
    Ordinal.omega0 ^ sourceFiniteCollapse τ n m α ≠ sourceFiniteCollapse τ n m α := by
  intro hepsilon
  have hbase := sourceFiniteCollapse_low_epsilon_eq_base τ n m hm α hα hepsilon
  have hstrict := sourceFiniteCollapse_strictMono_low τ n m hm hpositive hα
  rw [hbase] at hstrict
  exact (not_lt_of_ge (sourceFiniteCollapse_bounds τ n m hm 0).1) hstrict

end Alexander313.Wilken
