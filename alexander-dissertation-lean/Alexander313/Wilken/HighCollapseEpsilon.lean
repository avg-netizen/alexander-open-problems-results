import Alexander313.Wilken.GlobalLowEnumeration
import Alexander313.Wilken.SuccessorEpsilonBases

/-!
# Actual high-input collapse values are epsilons

The source hull closes the initial segment of a proper high collapse under
every low call. The proved low omega-power lower bound therefore gives
omega-power closure of that initial segment. Its actual principal output is
an omega fixed point. No high-collapse arithmetic or epsilon-class oracle is
assumed. All proof terms remain uncompiled.
-/

namespace Alexander313.Wilken

theorem sourceFiniteCollapse_high_omegaPower_closed (τ : Ordinal.{0})
    (n m : Nat) (hm : m < n) (α : Ordinal.{0})
    (hhigh : omegaSequence τ (m + 1) ≤ α)
    (hproper : sourceFiniteCollapse τ n m α < omegaSequence τ (m + 1))
    {γ : Ordinal.{0}} (hγ : γ < sourceFiniteCollapse τ n m α) :
    Ordinal.omega0 ^ γ < sourceFiniteCollapse τ n m α := by
  have hlow : γ < omegaSequence τ (m + 1) := hγ.trans hproper
  have hγα : γ < α := hlow.trans_le hhigh
  have hlocal : Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α
      (sourceFiniteCollapse τ n m α) (sourceFiniteCollapse τ n m γ) :=
    .«local» hγα (.below_parameter hγ)
  have hlocalproper := sourceFiniteCollapse_proper_notation τ n m hm γ
    (hlow.trans (omegaSequence_step τ (m + 1)))
    (sourceNotation_next_of_low τ n m hm hlow)
  have hlocalbelow : sourceFiniteCollapse τ n m γ < sourceFiniteCollapse τ n m α :=
    (finiteCollapse_hull_initial hm α _).mp ⟨hlocal, hlocalproper⟩
  exact (sourceFiniteCollapse_low_omegaPower_le τ n m hm γ hlow).trans_lt hlocalbelow

theorem sourceFiniteCollapse_high_base_lt (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (α : Ordinal.{0})
    (hhigh : omegaSequence τ (m + 1) ≤ α) :
    omegaSequence τ m < sourceFiniteCollapse τ n m α := by
  have hpositive := sourceFiniteCollapse_pos τ hτ n m hm α
  have hαpositive : 0 < α :=
    (hτ.trans_le ((omegaSequence_strictMono τ).monotone (Nat.zero_le (m + 1)))).trans_le hhigh
  have hzero : Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α
      (sourceFiniteCollapse τ n m α) (sourceFiniteCollapse τ n m 0) :=
    .«local» hαpositive (.below_parameter hpositive)
  have hzeroproper := sourceFiniteCollapse_proper_notation τ n m hm 0
    ((hτ.trans_le ((omegaSequence_strictMono τ).monotone (Nat.zero_le (m + 2)))))
    (sourceNotation_next_of_low τ n m hm
      (hτ.trans_le ((omegaSequence_strictMono τ).monotone (Nat.zero_le (m + 1)))))
  exact (sourceFiniteCollapse_bounds τ n m hm 0).1.trans_lt
    ((finiteCollapse_hull_initial hm α _).mp ⟨hzero, hzeroproper⟩)

theorem sourceFiniteCollapse_high_omegaPower_eq_self (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (α : Ordinal.{0})
    (hhigh : omegaSequence τ (m + 1) ≤ α)
    (hproper : sourceFiniteCollapse τ n m α < omegaSequence τ (m + 1)) :
    Ordinal.omega0 ^ sourceFiniteCollapse τ n m α = sourceFiniteCollapse τ n m α :=
  omegaPower_eq_self_of_principal_closed (sourceFiniteCollapse_pos τ hτ n m hm α)
    (sourceFiniteCollapse_add_closed τ n m hm α)
    (fun _ h => sourceFiniteCollapse_high_omegaPower_closed τ n m hm α hhigh hproper h)

/-- The source's strict epsilon-above-base condition, on its genuine sorted
argument domain. The zero low input cannot satisfy the strict base bound. -/
theorem sourceFiniteCollapse_epsilon_above_base_iff (τ : Ordinal.{0})
    (hτ : τ = 1 ∨ Ordinal.omega0 ^ τ = τ) (n m : Nat) (hm : m < n)
    (α : Ordinal.{0}) (hsort : α < omegaSequence τ (m + 2))
    (hα : sourceNotation τ n (m + 1) α) :
    (Ordinal.omega0 ^ sourceFiniteCollapse τ n m α = sourceFiniteCollapse τ n m α ∧
      omegaSequence τ m < sourceFiniteCollapse τ n m α) ↔
      omegaSequence τ (m + 1) ≤ α := by
  constructor
  · rintro ⟨hepsilon, habove⟩
    by_contra! hlow
    exact habove.ne' (sourceFiniteCollapse_low_epsilon_eq_base τ n m hm α hlow hepsilon)
  · intro hhigh
    exact ⟨sourceFiniteCollapse_high_omegaPower_eq_self τ (epsilon_or_one_pos hτ)
      n m hm α hhigh (sourceFiniteCollapse_proper_notation τ n m hm α hsort hα),
      sourceFiniteCollapse_high_base_lt τ (epsilon_or_one_pos hτ) n m hm α hhigh⟩

/-- Every positive cardinal-sort base is itself an actual omega fixed point.
This uses low collapse bounds below that cardinal, rather than a cardinal
exponentiation formula. -/
theorem omegaSequence_succ_omegaPower_eq_self (τ : Ordinal.{0}) (m : Nat) :
    Ordinal.omega0 ^ omegaSequence τ (m + 1) = omegaSequence τ (m + 1) := by
  apply omegaPower_eq_self_of_principal_closed
    (omegaSequence_isSuccLimit τ m).bot_lt (omegaSequence_add_closed τ m)
  intro γ hγ
  exact omegaPower_lt_next_cardinal τ (m + 1) m (Nat.lt_succ_self m) γ hγ

end Alexander313.Wilken
