import Alexander313.Wilken.HighCollapseEpsilon

/-!
# Exact ordinary omega powers of genuine low source collapses

The actual low principal minimum determines its exponent. At base one the
ordinary exponent is the input. At an epsilon base it is base + input.
An input epsilon + n whose epsilon is strictly above the base instead has
exponent input + 1. The proof uses ordinal induction and the real minimum,
not a supplied logarithm or arithmetic interface. It covers arbitrary low
limits, as well as finite successors. All proof terms remain uncompiled.
-/

namespace Alexander313.Wilken

open Order

private theorem lowOmega_add_right_strict (a : Ordinal.{0}) {b c : Ordinal.{0}}
    (h : b < c) : a + b < a + c :=
  lt_of_le_of_ne (add_le_add_right h.le a) (fun he => h.ne (add_left_cancel he))

private theorem lowOmega_power_lt_iff (a b : Ordinal.{0}) :
    Ordinal.omega0 ^ a < Ordinal.omega0 ^ b ↔ a < b := by
  constructor
  · intro h
    by_contra! hn
    exact h.not_ge (omegaPower_strictMono.monotone hn)
  · exact fun h => omegaPower_strictMono h

private theorem lowOmega_power_le_iff (a b : Ordinal.{0}) :
    Ordinal.omega0 ^ a ≤ Ordinal.omega0 ^ b ↔ a ≤ b := by
  constructor
  · intro h
    by_contra! hn
    exact (not_lt_of_ge h) (omegaPower_strictMono hn)
  · exact fun h => omegaPower_strictMono.monotone h

/-- The source correction is strictly above the base at its epsilon prefix. -/
def EpsilonFiniteAbove (τ α : Ordinal.{0}) : Prop :=
  ∃ ε : Ordinal.{0}, ∃ n : Nat,
    τ < ε ∧ Ordinal.omega0 ^ ε = ε ∧ α = ε + (n : Ordinal.{0})

theorem epsilonFiniteAbove_successor (τ α : Ordinal.{0})
    (h : EpsilonFiniteAbove τ α) : EpsilonFiniteAbove τ (α + 1) := by
  obtain ⟨ε, n, hτε, hε, hα⟩ := h
  exact ⟨ε, n + 1, hτε, hε, by rw [hα, Nat.cast_succ, add_assoc]⟩

/-- This is the semantic starting exponent, with the literal base-one case. -/
noncomputable def lowOmegaBase (τ : Ordinal.{0}) : Ordinal.{0} := by
  classical
  exact if τ = 1 then 0 else τ

theorem lowOmegaBase_one : lowOmegaBase 1 = 0 := by simp [lowOmegaBase]

theorem lowOmegaBase_of_epsilon (τ : Ordinal.{0})
    (hτ : Ordinal.omega0 ^ τ = τ) : lowOmegaBase τ = τ := by
  have hne : τ ≠ 1 := by
    intro h
    rw [h, Ordinal.opow_one] at hτ
    exact Ordinal.one_lt_omega0.ne' hτ
  simp only [lowOmegaBase, if_neg hne]

theorem lowOmegaBase_le (τ : Ordinal.{0}) : lowOmegaBase τ ≤ τ := by
  classical
  by_cases hτ : τ = 1
  · simp only [lowOmegaBase, if_pos hτ, zero_le]
  · simp only [lowOmegaBase, if_neg hτ, le_refl]

theorem lowOmegaBase_power (τ : Ordinal.{0})
    (hτ : τ = 1 ∨ Ordinal.omega0 ^ τ = τ) : Ordinal.omega0 ^ lowOmegaBase τ = τ := by
  rcases hτ with rfl | hτ
  · rw [lowOmegaBase_one, Ordinal.opow_zero]
  · rw [lowOmegaBase_of_epsilon τ hτ, hτ]

theorem lowOmegaBase_absorbed (τ α : Ordinal.{0}) (h : EpsilonFiniteAbove τ α) :
    lowOmegaBase τ + α = α := by
  obtain ⟨ε, n, hτε, hε, rfl⟩ := h
  rw [← add_assoc,
    (epsilon_or_one_add_closed (Or.inr hε)).add_eq_right ((lowOmegaBase_le τ).trans_lt hτε)]

/-- The exact low source exponent, defined as a mathematical value for the
proof. Executing code decisions are constructed separately. -/
noncomputable def lowOmegaExponent (τ α : Ordinal.{0}) : Ordinal.{0} := by
  classical
  exact if EpsilonFiniteAbove τ α then α + 1 else lowOmegaBase τ + α

theorem lowOmegaExponent_of_offset (τ α : Ordinal.{0}) (h : EpsilonFiniteAbove τ α) :
    lowOmegaExponent τ α = α + 1 := by simp only [lowOmegaExponent, if_pos h]

theorem lowOmegaExponent_of_not_offset (τ α : Ordinal.{0}) (h : ¬ EpsilonFiniteAbove τ α) :
    lowOmegaExponent τ α = lowOmegaBase τ + α := by simp only [lowOmegaExponent, if_neg h]

theorem lowOmegaExponent_shift_le (τ α : Ordinal.{0}) :
    lowOmegaBase τ + α ≤ lowOmegaExponent τ α := by
  classical
  by_cases h : EpsilonFiniteAbove τ α
  · rw [lowOmegaExponent_of_offset τ α h, lowOmegaBase_absorbed τ α h]
    exact (lt_add_one α).le
  · rw [lowOmegaExponent_of_not_offset τ α h]

theorem lowOmegaExponent_le_shift_succ (τ α : Ordinal.{0}) :
    lowOmegaExponent τ α ≤ lowOmegaBase τ + α + 1 := by
  classical
  by_cases h : EpsilonFiniteAbove τ α
  · rw [lowOmegaExponent_of_offset τ α h]
    exact add_le_add_left le_add_self 1
  · rw [lowOmegaExponent_of_not_offset τ α h]
    exact (lt_add_one _).le

/-- The independently constructed next principal is the next ordinary power. -/
theorem nextAdditivePrincipal_omegaPower (α : Ordinal.{0}) :
    nextAdditivePrincipal (Ordinal.omega0 ^ α) = Ordinal.omega0 ^ (α + 1) := by
  apply le_antisymm
  · exact nextAdditivePrincipal_le _ _ (omegaPower_strictMono (lt_add_one α))
      (Ordinal.isPrincipal_add_omega0_opow _)
  · obtain ⟨δ, hδ⟩ := positive_additivePrincipal_eq_omegaPower
      ((Ordinal.opow_pos _ Ordinal.omega0_pos).trans
        (nextAdditivePrincipal_spec (Ordinal.omega0 ^ α)).1)
      (nextAdditivePrincipal_spec (Ordinal.omega0 ^ α)).2
    have hαδ : α < δ := (lowOmega_power_lt_iff α δ).mp (by
      rw [← hδ]
      exact (nextAdditivePrincipal_spec (Ordinal.omega0 ^ α)).1)
    rw [hδ]
    exact omegaPower_strictMono.monotone (Order.add_one_le_of_lt hαδ)

/-- Full genuine low arithmetic at the zero sort. Every local-call estimate
comes from the induction hypothesis on the actual source function. -/
theorem sourceFiniteCollapse_low_eq_omegaPower (τ : Ordinal.{0})
    (hτ : τ = 1 ∨ Ordinal.omega0 ^ τ = τ) (n : Nat) (hn : 0 < n)
    (α : Ordinal.{0}) (hα : α < omegaSequence τ 1) :
    sourceFiniteCollapse τ n 0 α = Ordinal.omega0 ^ lowOmegaExponent τ α := by
  classical
  revert hα
  refine WellFoundedLT.induction α
    (motive := fun α => α < omegaSequence τ 1 →
      sourceFiniteCollapse τ n 0 α = Ordinal.omega0 ^ lowOmegaExponent τ α) ?_
  intro α ih hα
  have hpositive := sourceFiniteCollapse_pos τ (epsilon_or_one_pos hτ) n 0 hn α
  obtain ⟨γ, hγ⟩ := positive_additivePrincipal_eq_omegaPower hpositive
    (sourceFiniteCollapse_add_closed τ n 0 hn α)
  have hbase : τ ≤ sourceFiniteCollapse τ n 0 α := by
    simpa only [omegaSequence_zero] using (sourceFiniteCollapse_bounds τ n 0 hn α).1
  have hbγ : lowOmegaBase τ ≤ γ := (lowOmega_power_le_iff _ _).mp (by
    rw [lowOmegaBase_power τ hτ, ← hγ]
    exact hbase)
  have hlowerShift : Ordinal.omega0 ^ (lowOmegaBase τ + α) ≤ sourceFiniteCollapse τ n 0 α := by
    by_contra! hsmall
    rw [hγ] at hsmall
    have hγsmall := (lowOmega_power_lt_iff _ _).mp hsmall
    let δ := γ - lowOmegaBase τ
    have hadd : lowOmegaBase τ + δ = γ := Ordinal.add_sub_cancel_of_le hbγ
    have hδα : δ < α := by
      by_contra! hnδα
      exact hγsmall.not_ge (by rw [← hadd]; exact add_le_add_right hnδα _)
    have hδpower : Ordinal.omega0 ^ γ ≤ sourceFiniteCollapse τ n 0 δ := by
      calc
        Ordinal.omega0 ^ γ = Ordinal.omega0 ^ (lowOmegaBase τ + δ) := by rw [hadd]
        _ ≤ Ordinal.omega0 ^ lowOmegaExponent τ δ :=
          omegaPower_strictMono.monotone (lowOmegaExponent_shift_le τ δ)
        _ = sourceFiniteCollapse τ n 0 δ := (ih δ hδα (hδα.trans hα)).symm
    have hstrict := sourceFiniteCollapse_strictMono_low τ n 0 hn hδα hα
    rw [hγ] at hstrict
    exact (not_lt_of_ge hδpower) hstrict
  have hexponent : lowOmegaExponent τ α < omegaSequence τ 1 := by
    by_cases hoff : EpsilonFiniteAbove τ α
    · rw [lowOmegaExponent_of_offset τ α hoff]
      exact (omegaSequence_isSuccLimit τ 0).add_one_lt hα
    · rw [lowOmegaExponent_of_not_offset τ α hoff]
      exact (omegaSequence_add_closed τ 0)
        ((lowOmegaBase_le τ).trans_lt (omegaSequence_base_lt τ)) hα
  have hpowerSmall := omegaPower_lt_next_cardinal τ n 0 hn _ hexponent
  have hargument : α < Ordinal.omega0 ^ lowOmegaExponent τ α := by
    by_cases hoff : EpsilonFiniteAbove τ α
    · rw [lowOmegaExponent_of_offset τ α hoff]
      exact (lt_add_one α).trans_le (omegaPower_self_le _)
    · have hαexponent : α ≤ lowOmegaExponent τ α :=
        le_add_self.trans (lowOmegaExponent_shift_le τ α)
      apply lt_of_le_of_ne (hαexponent.trans (omegaPower_self_le _))
      intro he
      have hexponentEq : lowOmegaExponent τ α = α :=
        le_antisymm ((omegaPower_self_le _).trans_eq he.symm) hαexponent
      have hepsilon : Ordinal.omega0 ^ α = α := by
        rw [hexponentEq] at he
        exact he.symm
      have hαpos := epsilon_or_one_pos (Or.inr hepsilon)
      have hτα : τ < α := by
        rcases hτ with rfl | hτ
        · simpa only [Ordinal.opow_zero, hepsilon] using omegaPower_strictMono hαpos
        · rw [lowOmegaExponent_of_not_offset τ α hoff, lowOmegaBase_of_epsilon τ hτ] at hexponentEq
          have hstrict := lowOmega_add_right_strict τ hαpos
          simpa only [add_zero, hexponentEq] using hstrict
      exact hoff ⟨α, 0, hτα, hepsilon, by simp only [Nat.cast_zero, add_zero]⟩
  have hupper : sourceFiniteCollapse τ n 0 α ≤ Ordinal.omega0 ^ lowOmegaExponent τ α := by
    apply (sourceFiniteCollapse_low_le_iff_principal τ n 0 hn _ _ hα hpowerSmall
      (Ordinal.isPrincipal_add_omega0_opow _)).mpr
    refine ⟨?_, hargument, ?_⟩
    · calc
        τ = Ordinal.omega0 ^ lowOmegaBase τ := (lowOmegaBase_power τ hτ).symm
        _ ≤ Ordinal.omega0 ^ lowOmegaExponent τ α :=
          omegaPower_strictMono.monotone (le_self_add.trans (lowOmegaExponent_shift_le τ α))
    · intro δ hδα
      rw [ih δ hδα (hδα.trans hα)]
      apply omegaPower_strictMono
      by_cases hαoff : EpsilonFiniteAbove τ α
      · rw [lowOmegaExponent_of_offset τ α hαoff]
        have hshift : lowOmegaBase τ + δ < α := by
          simpa only [lowOmegaBase_absorbed τ α hαoff] using lowOmega_add_right_strict (lowOmegaBase τ) hδα
        exact ((lowOmegaExponent_le_shift_succ τ δ).trans (add_one_le_of_lt hshift)).trans_lt (lt_add_one α)
      · rw [lowOmegaExponent_of_not_offset τ α hαoff]
        by_cases hδoff : EpsilonFiniteAbove τ δ
        · rw [lowOmegaExponent_of_offset τ δ hδoff]
          have hsucc : δ + 1 < α := lt_of_le_of_ne (add_one_le_of_lt hδα) (fun he =>
            hαoff (by rw [← he]; exact epsilonFiniteAbove_successor τ δ hδoff))
          exact hsucc.trans_le le_add_self
        · rw [lowOmegaExponent_of_not_offset τ δ hδoff]
          exact lowOmega_add_right_strict _ hδα
  apply le_antisymm hupper
  by_cases hoff : EpsilonFiniteAbove τ α
  · rw [lowOmegaExponent_of_offset τ α hoff]
    obtain ⟨ε, k, hτε, hε, hαε⟩ := hoff
    have hprevious : Ordinal.omega0 ^ α < sourceFiniteCollapse τ n 0 α := by
      cases k with
      | zero =>
        have he : α = ε := by simpa only [Nat.cast_zero, add_zero] using hαε
        simpa only [he, hε] using sourceFiniteCollapse_low_argument_lt τ n 0 hn hα
      | succ k =>
        let δ := ε + (k : Ordinal.{0})
        have hδα : δ + 1 = α := by
          simpa only [δ, Nat.cast_succ, add_assoc] using hαε.symm
        have hδlt : δ < α := (lt_add_one δ).trans_eq hδα
        have hδoff : EpsilonFiniteAbove τ δ := ⟨ε, k, hτε, hε, rfl⟩
        have hvalue : sourceFiniteCollapse τ n 0 δ = Ordinal.omega0 ^ α := by
          rw [ih δ hδlt (hδlt.trans hα), lowOmegaExponent_of_offset τ δ hδoff, hδα]
        rw [← hvalue]
        exact sourceFiniteCollapse_strictMono_low τ n 0 hn hδlt hα
    rw [hγ] at hprevious
    have hαγ := (lowOmega_power_lt_iff _ _).mp hprevious
    rw [hγ]
    exact omegaPower_strictMono.monotone (add_one_le_of_lt hαγ)
  · simpa only [lowOmegaExponent_of_not_offset τ α hoff] using hlowerShift

theorem globalCollapse_low_eq_omegaPower (τ : Ordinal.{0})
    (hτ : τ = 1 ∨ Ordinal.omega0 ^ τ = τ) (α : Ordinal.{0})
    (hα : α < omegaSequence τ 1) :
    globalCollapse τ 0 α = Ordinal.omega0 ^ lowOmegaExponent τ α := by
  rw [globalCollapse_low_finite_agreement τ (epsilon_or_one_pos hτ) 1 0 (Nat.zero_lt_succ 0) α hα]
  exact sourceFiniteCollapse_low_eq_omegaPower τ hτ 1 (Nat.zero_lt_succ 0) α hα

theorem epsilon_omega_lt {ε : Ordinal.{0}} (hε : Ordinal.omega0 ^ ε = ε) :
    Ordinal.omega0 < ε := by
  have hpositive := epsilon_or_one_pos (Or.inr hε)
  have hone : 1 < ε := by
    simpa only [Ordinal.opow_zero, hε] using omegaPower_strictMono hpositive
  simpa only [Ordinal.opow_one, hε] using omegaPower_strictMono hone

theorem not_epsilonFiniteAbove_nat (τ : Ordinal.{0}) (n : Nat) :
    ¬ EpsilonFiniteAbove τ (n : Ordinal.{0}) := by
  rintro ⟨ε, k, _, hε, he⟩
  have hn : (n : Ordinal.{0}) < Ordinal.omega0 := Ordinal.lt_omega0.mpr ⟨n, rfl⟩
  have hεn : ε ≤ (n : Ordinal.{0}) := by rw [he]; exact le_self_add
  exact (not_lt_of_ge hεn) (hn.trans (epsilon_omega_lt hε))

theorem lowOmegaExponent_nat (τ : Ordinal.{0}) (n : Nat) :
    lowOmegaExponent τ (n : Ordinal.{0}) = lowOmegaBase τ + (n : Ordinal.{0}) :=
  lowOmegaExponent_of_not_offset τ _ (not_epsilonFiniteAbove_nat τ n)

theorem lowOmegaExponent_sub_base (τ ζ : Ordinal.{0})
    (hbase : lowOmegaBase τ ≤ ζ) (hoff : ¬ EpsilonFiniteAbove τ ζ) :
    lowOmegaExponent τ (ζ - lowOmegaBase τ) = ζ := by
  have hadd := Ordinal.add_sub_cancel_of_le hbase
  have hnot : ¬ EpsilonFiniteAbove τ (ζ - lowOmegaBase τ) := by
    intro h
    have he : ζ - lowOmegaBase τ = ζ :=
      (lowOmegaBase_absorbed τ _ h).symm.trans hadd
    exact hoff (he ▸ h)
  rw [lowOmegaExponent_of_not_offset τ _ hnot]
  exact hadd

theorem lowOmegaExponent_offset_predecessor (τ ε : Ordinal.{0}) (n : Nat)
    (hτε : τ < ε) (hε : Ordinal.omega0 ^ ε = ε) (hn : 0 < n) :
    lowOmegaExponent τ (ε + ((n - 1 : Nat) : Ordinal.{0})) = ε + (n : Ordinal.{0}) := by
  rw [lowOmegaExponent_of_offset τ _ ⟨ε, n - 1, hτε, hε, rfl⟩, add_assoc]
  apply congrArg (fun x : Ordinal.{0} => ε + x)
  have h := congrArg (fun k : Nat => (k : Ordinal.{0}))
    (Nat.sub_add_cancel (Nat.succ_le_of_lt hn))
  simpa only [Nat.cast_add, Nat.cast_one] using h

theorem nat_lt_next_cardinal (τ : Ordinal.{0}) (n : Nat) :
    (n : Ordinal.{0}) < omegaSequence τ 1 := by
  induction n with
  | zero =>
    simpa only [Nat.cast_zero] using (omegaSequence_isSuccLimit τ 0).pos
  | succ n ih =>
    simpa only [Nat.cast_succ] using (omegaSequence_isSuccLimit τ 0).add_one_lt ih

theorem globalCollapse_one_nat (n : Nat) :
    globalCollapse 1 0 (n : Ordinal.{0}) = Ordinal.omega0 ^ (n : Ordinal.{0}) := by
  rw [globalCollapse_low_eq_omegaPower 1 (Or.inl rfl) _ (nat_lt_next_cardinal 1 n),
    lowOmegaExponent_nat, lowOmegaBase_one, zero_add]

end Alexander313.Wilken
