import Alexander313.Wilken.HereditaryNativeIotaInverse
import Alexander313.Wilken.HereditaryNativeLowArithmetic

/-!
# Genuine all-level low collapse arithmetic for an Omega-one quotient

The actual source minimum proof is repeated at an arbitrary cardinal level.
Its starting exponent is the actual level base, and its epsilon-plus-finite
correction is retained in full. This is a mathematical kernel for the full
native high-part quotient construction; it assumes no quotient, inverse,
admission transport, or collapse formula oracle. Source-only, uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.OmegaQuotient

private theorem add_right_strict (a : Ordinal.{0}) {b c : Ordinal.{0}}
    (h : b < c) : a + b < a + c :=
  lt_of_le_of_ne (add_le_add_right h.le a) (fun he => h.ne (add_left_cancel he))

private theorem power_lt_iff (a b : Ordinal.{0}) :
    Ordinal.omega0 ^ a < Ordinal.omega0 ^ b ↔ a < b := by
  constructor
  · intro h
    by_contra! hn
    exact h.not_ge (omegaPower_strictMono.monotone hn)
  · exact omegaPower_strictMono

private theorem power_le_iff (a b : Ordinal.{0}) :
    Ordinal.omega0 ^ a ≤ Ordinal.omega0 ^ b ↔ a ≤ b := by
  constructor
  · intro h
    by_contra! hn
    exact (not_lt_of_ge h) (omegaPower_strictMono hn)
  · exact omegaPower_strictMono.monotone

theorem finiteCollapse_low_eq_power (τ : Ordinal.{0})
    (hτ : τ = 1 ∨ Ordinal.omega0 ^ τ = τ) (n m : Nat) (hm : m < n)
    (α : Ordinal.{0}) (hα : α < omegaSequence τ (m + 1)) :
    sourceFiniteCollapse τ n m α =
      Ordinal.omega0 ^ lowOmegaExponent (omegaSequence τ m) α := by
  classical
  have hΩ : omegaSequence τ m = 1 ∨
      Ordinal.omega0 ^ omegaSequence τ m = omegaSequence τ m := by
    cases m with
    | zero => simpa only [omegaSequence_zero] using hτ
    | succ m => exact Or.inr (omegaSequence_succ_omegaPower_eq_self τ m)
  revert hα
  refine Ordinal.induction α ?_
  intro α ih hα
  have hpositive := sourceFiniteCollapse_pos τ (epsilon_or_one_pos hτ) n m hm α
  obtain ⟨γ, hγ⟩ := positive_additivePrincipal_eq_omegaPower hpositive
    (sourceFiniteCollapse_add_closed τ n m hm α)
  have hbase : omegaSequence τ m ≤ sourceFiniteCollapse τ n m α := by
    exact (sourceFiniteCollapse_bounds τ n m hm α).1
  have hbγ : lowOmegaBase (omegaSequence τ m) ≤ γ := (power_le_iff _ _).mp (by
    rw [lowOmegaBase_power (omegaSequence τ m) hΩ, ← hγ]
    exact hbase)
  have hlowerShift : Ordinal.omega0 ^ (lowOmegaBase (omegaSequence τ m) + α) ≤ sourceFiniteCollapse τ n m α := by
    by_contra! hsmall
    rw [hγ] at hsmall
    have hγsmall := (power_lt_iff _ _).mp hsmall
    let δ := γ - lowOmegaBase (omegaSequence τ m)
    have hadd : lowOmegaBase (omegaSequence τ m) + δ = γ := Ordinal.add_sub_cancel_of_le hbγ
    have hδα : δ < α := by
      by_contra! hnδα
      exact hγsmall.not_ge (by rw [← hadd]; exact add_le_add_right hnδα _)
    have hδpower : Ordinal.omega0 ^ γ ≤ sourceFiniteCollapse τ n m δ := by
      calc
        Ordinal.omega0 ^ γ = Ordinal.omega0 ^ (lowOmegaBase (omegaSequence τ m) + δ) := by rw [hadd]
        _ ≤ Ordinal.omega0 ^ lowOmegaExponent (omegaSequence τ m) δ :=
          omegaPower_strictMono.monotone (lowOmegaExponent_shift_le (omegaSequence τ m) δ)
        _ = sourceFiniteCollapse τ n m δ := (ih δ hδα (hδα.trans hα)).symm
    have hstrict := sourceFiniteCollapse_strictMono_low τ n m hm hδα hα
    rw [hγ] at hstrict
    exact (not_lt_of_ge hδpower) hstrict
  have hexponent : lowOmegaExponent (omegaSequence τ m) α < omegaSequence τ (m + 1) := by
    by_cases hoff : EpsilonFiniteAbove (omegaSequence τ m) α
    · rw [lowOmegaExponent_of_offset (omegaSequence τ m) α hoff]
      exact (omegaSequence_isSuccLimit τ m).add_one_lt hα
    · rw [lowOmegaExponent_of_not_offset (omegaSequence τ m) α hoff]
      exact (omegaSequence_add_closed τ m)
        ((lowOmegaBase_le (omegaSequence τ m)).trans_lt (omegaSequence_step τ m)) hα
  have hpowerSmall := omegaPower_lt_next_cardinal τ n m hm _ hexponent
  have hargument : α < Ordinal.omega0 ^ lowOmegaExponent (omegaSequence τ m) α := by
    by_cases hoff : EpsilonFiniteAbove (omegaSequence τ m) α
    · rw [lowOmegaExponent_of_offset (omegaSequence τ m) α hoff]
      exact (lt_add_one α).trans_le (omegaPower_self_le _)
    · have hαexponent : α ≤ lowOmegaExponent (omegaSequence τ m) α :=
        le_add_self.trans (lowOmegaExponent_shift_le (omegaSequence τ m) α)
      apply lt_of_le_of_ne (hαexponent.trans (omegaPower_self_le _))
      intro he
      have hexponentEq : lowOmegaExponent (omegaSequence τ m) α = α :=
        le_antisymm ((omegaPower_self_le _).trans_eq he.symm) hαexponent
      have hepsilon : Ordinal.omega0 ^ α = α := by
        rw [hexponentEq] at he
        exact he.symm
      have hαpos := epsilon_or_one_pos (Or.inr hepsilon)
      have hτα : omegaSequence τ m < α := by
        rcases hΩ with hΩ | hΩ
        · simpa only [hΩ, Ordinal.opow_zero, hepsilon] using omegaPower_strictMono hαpos
        · rw [lowOmegaExponent_of_not_offset (omegaSequence τ m) α hoff, lowOmegaBase_of_epsilon (omegaSequence τ m) hΩ] at hexponentEq
          have hstrict := add_right_strict (omegaSequence τ m) hαpos
          simpa only [add_zero, hexponentEq] using hstrict
      exact hoff ⟨α, 0, hτα, hepsilon, by simp only [Nat.cast_zero, add_zero]⟩
  have hupper : sourceFiniteCollapse τ n m α ≤ Ordinal.omega0 ^ lowOmegaExponent (omegaSequence τ m) α := by
    apply (sourceFiniteCollapse_low_le_iff_principal τ n m hm _ _ hα hpowerSmall
      (Ordinal.isPrincipal_add_omega0_opow _)).mpr
    refine ⟨?_, hargument, ?_⟩
    · calc
        omegaSequence τ m = Ordinal.omega0 ^ lowOmegaBase (omegaSequence τ m) := (lowOmegaBase_power (omegaSequence τ m) hΩ).symm
        _ ≤ Ordinal.omega0 ^ lowOmegaExponent (omegaSequence τ m) α :=
          omegaPower_strictMono.monotone (le_self_add.trans (lowOmegaExponent_shift_le (omegaSequence τ m) α))
    · intro δ hδα
      rw [ih δ hδα (hδα.trans hα)]
      apply omegaPower_strictMono
      by_cases hαoff : EpsilonFiniteAbove (omegaSequence τ m) α
      · rw [lowOmegaExponent_of_offset (omegaSequence τ m) α hαoff]
        have hshift : lowOmegaBase (omegaSequence τ m) + δ < α := by
          simpa only [lowOmegaBase_absorbed (omegaSequence τ m) α hαoff] using add_right_strict (lowOmegaBase (omegaSequence τ m)) hδα
        exact ((lowOmegaExponent_le_shift_succ (omegaSequence τ m) δ).trans (add_one_le_of_lt hshift)).trans_lt (lt_add_one α)
      · rw [lowOmegaExponent_of_not_offset (omegaSequence τ m) α hαoff]
        by_cases hδoff : EpsilonFiniteAbove (omegaSequence τ m) δ
        · rw [lowOmegaExponent_of_offset (omegaSequence τ m) δ hδoff]
          have hsucc : δ + 1 < α := lt_of_le_of_ne (add_one_le_of_lt hδα) (fun he =>
            hαoff (by rw [← he]; exact epsilonFiniteAbove_successor (omegaSequence τ m) δ hδoff))
          exact hsucc.trans_le le_add_self
        · rw [lowOmegaExponent_of_not_offset (omegaSequence τ m) δ hδoff]
          exact add_right_strict _ hδα
  apply le_antisymm hupper
  by_cases hoff : EpsilonFiniteAbove (omegaSequence τ m) α
  · rw [lowOmegaExponent_of_offset (omegaSequence τ m) α hoff]
    obtain ⟨ε, k, hτε, hε, hαε⟩ := hoff
    have hprevious : Ordinal.omega0 ^ α < sourceFiniteCollapse τ n m α := by
      cases k with
      | zero =>
        have he : α = ε := by simpa only [Nat.cast_zero, add_zero] using hαε
        simpa only [he, hε] using sourceFiniteCollapse_low_argument_lt τ n m hm hα
      | succ k =>
        let δ := ε + (k : Ordinal.{0})
        have hδα : δ + 1 = α := by
          simpa only [δ, Nat.cast_succ, add_assoc] using hαε.symm
        have hδlt : δ < α := (lt_add_one δ).trans_eq hδα
        have hδoff : EpsilonFiniteAbove (omegaSequence τ m) δ := ⟨ε, k, hτε, hε, rfl⟩
        have hvalue : sourceFiniteCollapse τ n m δ = Ordinal.omega0 ^ α := by
          rw [ih δ hδlt (hδlt.trans hα), lowOmegaExponent_of_offset (omegaSequence τ m) δ hδoff, hδα]
        rw [← hvalue]
        exact sourceFiniteCollapse_strictMono_low τ n m hm hδlt hα
    rw [hγ] at hprevious
    have hαγ := (power_lt_iff _ _).mp hprevious
    rw [hγ]
    exact omegaPower_strictMono.monotone (add_one_le_of_lt hαγ)
  · simpa only [lowOmegaExponent_of_not_offset (omegaSequence τ m) α hoff] using hlowerShift


/-- Actual finite/global coherence carries the all-level minimum equation. -/
theorem globalCollapse_low_eq_power (τ : Ordinal.{0})
    (hτ : τ = 1 ∨ Ordinal.omega0 ^ τ = τ) (m : Nat)
    (α : Ordinal.{0}) (hα : α < omegaSequence τ (m + 1)) :
    globalCollapse τ m α =
      Ordinal.omega0 ^ lowOmegaExponent (omegaSequence τ m) α := by
  rw [globalCollapse_low_finite_agreement τ (epsilon_or_one_pos hτ)
    (m + 1) m (Nat.lt_succ_self m) α hα]
  exact finiteCollapse_low_eq_power τ hτ (m + 1) m (Nat.lt_succ_self m) α hα

/-- The executable threshold is the actual first positive low theta-one
value, rather than an assumed multiplication operation. -/
theorem theta_one_unit (τ : Ordinal.{0})
    (hτ : τ = 1 ∨ Ordinal.omega0 ^ τ = τ) :
    globalCollapse τ 1 1 = omegaSequence τ 1 * Ordinal.omega0 := by
  rw [globalCollapse_low_eq_power τ hτ 1 1 (nat_lt_next_cardinal τ 1 |>.trans
    (omegaSequence_step τ 1)), lowOmegaExponent_nat,
    lowOmegaBase_of_epsilon _ (omegaSequence_succ_omegaPower_eq_self τ 0),
    Ordinal.opow_add_one, omegaSequence_succ_omegaPower_eq_self τ 0]

/-- No epsilon-plus-finite correction can lie below the genuine threshold.
An epsilon strictly above Omega has exponent above Omega+1. -/
theorem not_offset_below_threshold (Ω β : Ordinal.{0})
    (hΩ : Ordinal.omega0 ^ Ω = Ω) (hb : β < Ω * Ordinal.omega0) :
    ¬ EpsilonFiniteAbove Ω β := by
  rintro ⟨ε, k, hΩε, hε, he⟩
  have hεlim := Ordinal.isSuccLimit_of_isPrincipal_add
    (Ordinal.one_lt_omega0.trans (epsilon_omega_lt hε))
    (epsilon_or_one_add_closed (Or.inr hε))
  have hthreshold : Ω * Ordinal.omega0 < ε := by
    calc
      Ω * Ordinal.omega0 = Ordinal.omega0 ^ (Ω + 1) := by
        rw [Ordinal.opow_add_one, hΩ]
      _ < Ordinal.omega0 ^ ε := omegaPower_strictMono (hεlim.add_one_lt hΩε)
      _ = ε := hε
  exact (hb.trans hthreshold).not_ge (by rw [he]; exact le_self_add)

/-- Below the threshold the exact correction-free exponent is Omega+beta. -/
theorem theta_one_below_threshold (τ : Ordinal.{0})
    (hτ : τ = 1 ∨ Ordinal.omega0 ^ τ = τ) (β : Ordinal.{0})
    (hβ : β < omegaSequence τ 1 * Ordinal.omega0) :
    globalCollapse τ 1 β = omegaSequence τ 1 * Ordinal.omega0 ^ β := by
  have hΩ := omegaSequence_succ_omegaPower_eq_self τ 0
  have hthreshold : omegaSequence τ 1 * Ordinal.omega0 < omegaSequence τ 2 := by
    rw [← theta_one_unit τ hτ]
    exact (globalCollapse_bounds τ (epsilon_or_one_pos hτ) 1 1
      ((nat_lt_next_cardinal τ 1).trans ((omegaSequence_step τ 1).trans
        (globalBoundary_base_lt τ (epsilon_or_one_pos hτ) 2)))).2
  rw [globalCollapse_low_eq_power τ hτ 1 β (hβ.trans hthreshold),
    lowOmegaExponent_of_not_offset _ _ (not_offset_below_threshold _ _ hΩ hβ),
    lowOmegaBase_of_epsilon _ hΩ, Ordinal.opow_add, hΩ]

/-- The upper threshold case retains the actual epsilon-finite correction.
Its exponent is at least beta and therefore absorbs Omega on the left. -/
theorem theta_one_above_threshold (τ : Ordinal.{0})
    (hτ : τ = 1 ∨ Ordinal.omega0 ^ τ = τ) (β : Ordinal.{0})
    (hβ : omegaSequence τ 1 * Ordinal.omega0 ≤ β)
    (hβlow : β < omegaSequence τ 2) :
    omegaSequence τ 1 * globalCollapse τ 1 β = globalCollapse τ 1 β := by
  let Ω := omegaSequence τ 1
  have hΩ : Ordinal.omega0 ^ Ω = Ω := omegaSequence_succ_omegaPower_eq_self τ 0
  have hthreshold : Ordinal.IsPrincipal (· + ·) (Ω * Ordinal.omega0) := by
    rw [← hΩ, ← Ordinal.opow_add_one]
    exact Ordinal.isPrincipal_add_omega0_opow _
  have hΩt : Ω < Ω * Ordinal.omega0 := by
    calc
      Ω = Ω * 1 := (mul_one _).symm
      _ < Ω * Ordinal.omega0 := mul_lt_mul_of_pos_left Ordinal.one_lt_omega0
        (omegaSequence_isSuccLimit τ 0).bot_lt
  have he : Ω + lowOmegaExponent Ω β = lowOmegaExponent Ω β :=
    hthreshold.add_eq_right_of_le hΩt
      (hβ.trans (le_add_self.trans (lowOmegaExponent_shift_le Ω β)))
  rw [globalCollapse_low_eq_power τ hτ 1 β hβlow]
  change Ω * Ordinal.omega0 ^ lowOmegaExponent Ω β = _
  rw [← hΩ, ← Ordinal.opow_add, he]

/-- Every principal value at or above the second cardinal absorbs Omega-one.
The actual principal exponent, not epsilon status of the value, is used. -/
theorem principal_above_second_absorbs (τ p : Ordinal.{0})
    (hp : Ordinal.IsPrincipal (· + ·) p) (hlarge : omegaSequence τ 2 ≤ p) :
    omegaSequence τ 1 * p = p := by
  obtain ⟨γ, hγ⟩ := positive_additivePrincipal_eq_omegaPower
    ((omegaSequence_isSuccLimit τ 1).bot_lt.trans_le hlarge) hp
  have hΩ₂γ : omegaSequence τ 2 ≤ γ := (power_le_iff _ _).mp (by
    rw [omegaSequence_succ_omegaPower_eq_self τ 1, ← hγ]
    exact hlarge)
  have he : omegaSequence τ 1 + γ = γ :=
    (omegaSequence_add_closed τ 1).add_eq_right_of_le (omegaSequence_step τ 1) hΩ₂γ
  rw [hγ, ← omegaSequence_succ_omegaPower_eq_self τ 0, ← Ordinal.opow_add, he]


/-- The middle case uses the real left-removing ordinal subtraction. In
particular beta=Omega returns theta-one zero, whose value is Omega. -/
theorem theta_one_shifted_quotient (τ : Ordinal.{0})
    (hτ : τ = 1 ∨ Ordinal.omega0 ^ τ = τ) (β : Ordinal.{0})
    (hbase : omegaSequence τ 1 ≤ β)
    (hβ : β < omegaSequence τ 1 * Ordinal.omega0) :
    omegaSequence τ 1 * globalCollapse τ 1 (β - omegaSequence τ 1) =
      globalCollapse τ 1 β := by
  let Ω := omegaSequence τ 1
  have hΩ : Ordinal.omega0 ^ Ω = Ω := omegaSequence_succ_omegaPower_eq_self τ 0
  have hn : ¬ EpsilonFiniteAbove Ω β := not_offset_below_threshold Ω β hΩ hβ
  have hbase' : lowOmegaBase Ω ≤ β := by
    simpa only [lowOmegaBase_of_epsilon Ω hΩ] using hbase
  have he : lowOmegaExponent Ω (β - Ω) = β := by
    simpa only [lowOmegaBase_of_epsilon Ω hΩ] using lowOmegaExponent_sub_base Ω β hbase' hn
  have hthreshold : Ω * Ordinal.omega0 < omegaSequence τ 2 := by
    rw [← theta_one_unit τ hτ]
    exact (globalCollapse_bounds τ (epsilon_or_one_pos hτ) 1 1
      ((nat_lt_next_cardinal τ 1).trans ((omegaSequence_step τ 1).trans
        (globalBoundary_base_lt τ (epsilon_or_one_pos hτ) 2)))).2
  rw [globalCollapse_low_eq_power τ hτ 1 (β - Ω)
    ((Ordinal.sub_le_self β Ω).trans_lt (hβ.trans hthreshold)), he,
    theta_one_below_threshold τ hτ β hβ]

/-- A genuine epsilon strictly above Omega absorbs its left product. -/
theorem epsilon_above_absorbs (Ω p : Ordinal.{0})
    (hΩ : Ordinal.omega0 ^ Ω = Ω) (hp : Ordinal.omega0 ^ p = p)
    (hlt : Ω < p) : Ω * p = p := by
  calc
    Ω * p = Ordinal.omega0 ^ Ω * Ordinal.omega0 ^ p := by rw [hΩ, hp]
    _ = Ordinal.omega0 ^ (Ω + p) := (Ordinal.opow_add _ _ _).symm
    _ = Ordinal.omega0 ^ p := by
      rw [(epsilon_or_one_add_closed (Or.inr hp)).add_eq_right hlt]
    _ = p := hp

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.OmegaQuotient
