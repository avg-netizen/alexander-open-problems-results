import Alexander313.Wilken.HereditaryNativeSourceChiPowers
import Alexander313.Wilken.SourceCollapseSuccessors
import Alexander313.Wilken.GlobalLowEnumeration

/-!
# Actual lower-context successor bounds below an epsilon ceiling

For a genuine non-epsilon theta value, its original argument is LOW. The
literal next argument at that SAME source context remains below every
larger epsilon. An epsilon value also has the genuine self-context
theta_mu(0) presentation, whose actual theta_mu(1) successor stays below a
larger epsilon. These are explicit source-context statements. They do not
define Convention 2.28 on an arbitrary parameter of another context or
identify these contexts with the printed mu-parameter convention.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.ParameterSuccessorBounds

theorem epsilon_isSuccLimit {ε : Ordinal.{0}}
    (hε : Ordinal.omega0 ^ ε = ε) : IsSuccLimit ε := by
  rw [← hε]
  exact Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0
    (ne_of_gt (epsilon_or_one_pos (Or.inr hε)))

/-- The genuine high-collapse epsilon theorem derives the low argument;
no LOW classification is supplied as an additional premise. -/
theorem non_epsilon_argument_low (τ : Ordinal.{0})
    (hτ : τ = 1 ∨ Ordinal.omega0 ^ τ = τ)
    (a : GlobalNotationOrdinal τ 1) (ha : a.val < omegaSequence τ 2)
    (hne : Ordinal.omega0 ^ globalCollapse τ 0 a.val ≠ globalCollapse τ 0 a.val) :
    a.val < omegaSequence τ 1 := by
  apply lt_of_not_ge
  intro hh
  exact hne (RelativeTerm.Hereditary.NativeContext.SourceChi.Powers.global_high_epsilon
    τ hτ a ha hh)

theorem low_argument_le_collapse (τ : Ordinal.{0})
    (hτ : τ = 1 ∨ Ordinal.omega0 ^ τ = τ) (a : Ordinal.{0})
    (ha : a < omegaSequence τ 1) : a ≤ globalCollapse τ 0 a := by
  rw [globalCollapse_low_eq_omegaPower τ hτ a ha]
  exact (show a ≤ lowOmegaBase τ + a from le_add_self).trans
    ((lowOmegaExponent_shift_le τ a).trans (omegaPower_self_le _))

theorem low_base_le_collapse (τ : Ordinal.{0})
    (hτ : τ = 1 ∨ Ordinal.omega0 ^ τ = τ) (a : Ordinal.{0})
    (ha : a < omegaSequence τ 1) : τ ≤ globalCollapse τ 0 a := by
  calc
    τ = Ordinal.omega0 ^ lowOmegaBase τ := (lowOmegaBase_power τ hτ).symm
    _ ≤ Ordinal.omega0 ^ lowOmegaExponent τ a := omegaPower_strictMono.monotone
      ((show lowOmegaBase τ ≤ lowOmegaBase τ + a from le_self_add).trans
        (lowOmegaExponent_shift_le τ a))
    _ = globalCollapse τ 0 a := (globalCollapse_low_eq_omegaPower τ hτ a ha).symm

/-- The literal source successor bound follows from genuine low source
arithmetic and the epsilon ceiling's actual additive and power closure. -/
theorem low_successor_lt_epsilon (τ : Ordinal.{0})
    (hτ : τ = 1 ∨ Ordinal.omega0 ^ τ = τ) (a : Ordinal.{0})
    (ha : a < omegaSequence τ 1) (ε : Ordinal.{0})
    (hε : Ordinal.omega0 ^ ε = ε) (hv : globalCollapse τ 0 a < ε) :
    globalCollapse τ 0 (a + 1) < ε := by
  have hτlt := (low_base_le_collapse τ hτ a ha).trans_lt hv
  have halt := (low_argument_le_collapse τ hτ a ha).trans_lt hv
  have hsucc := (epsilon_isSuccLimit hε).add_one_lt halt
  have hsmall := (omegaSequence_isSuccLimit τ 0).add_one_lt ha
  have hone : (1 : Ordinal.{0}) < ε :=
    RelativeTerm.Hereditary.EpsilonOffsets.epsilon_one_lt hε
  have hprincipal := epsilon_or_one_add_closed (Or.inr hε)
  have hsum : τ + (a + 1) + 1 < ε := hprincipal (hprincipal hτlt hsucc) hone
  have hupper : globalCollapse τ 0 (a + 1) ≤ Ordinal.omega0 ^ (τ + (a + 1) + 1) := by
    simpa only [omegaSequence_zero] using
      globalCollapse_low_power_upper τ (epsilon_or_one_pos hτ) 0 (a + 1) hsmall
  exact hupper.trans_lt ((omegaPower_strictMono hsum).trans_eq hε)

/-- At the explicitly retained lower context, the real argument-plus-one
operation is strictly larger and still below the greater epsilon. -/
theorem non_epsilon_successor_interval (τ : Ordinal.{0})
    (hτ : τ = 1 ∨ Ordinal.omega0 ^ τ = τ)
    (a : GlobalNotationOrdinal τ 1) (ha : a.val < omegaSequence τ 2)
    (hne : Ordinal.omega0 ^ globalCollapse τ 0 a.val ≠ globalCollapse τ 0 a.val)
    (ε : Ordinal.{0}) (hε : Ordinal.omega0 ^ ε = ε)
    (hv : globalCollapse τ 0 a.val < ε) :
    globalCollapse τ 0 a.val < globalCollapse τ 0 (a.val + 1) ∧
      globalCollapse τ 0 (a.val + 1) < ε :=
  ⟨SourceCollapseSuccessors.global_collapse_lt_successor τ (epsilon_or_one_pos hτ) 0 a ha,
    low_successor_lt_epsilon τ hτ a.val (non_epsilon_argument_low τ hτ a ha hne) ε hε hv⟩

/-- The actual epsilon self-context zero presentation and its literal
argument-one successor, with no substituted successor operation. -/
theorem epsilon_self_successor_interval (μ ε : Ordinal.{0})
    (hμ : Ordinal.omega0 ^ μ = μ) (hε : Ordinal.omega0 ^ ε = ε) (hμε : μ < ε) :
    globalCollapse μ 0 0 = μ ∧ μ < globalCollapse μ 0 1 ∧ globalCollapse μ 0 1 < ε := by
  have hp := epsilon_or_one_pos (Or.inr hμ)
  have hzero := globalCollapse_zero μ hp (epsilon_or_one_add_closed (Or.inr hμ)) 0
  have hv : globalCollapse μ 0 0 = μ := by simpa only [omegaSequence_zero] using hzero
  let a : GlobalNotationOrdinal μ 1 :=
    ⟨0, .parameter (hp.trans (omegaSequence_base_lt μ))⟩
  have hs : a.val < omegaSequence μ 2 :=
    hp.trans_le ((omegaSequence_strictMono μ).monotone (Nat.zero_le 2))
  have hlt := SourceCollapseSuccessors.global_collapse_lt_successor μ hp 0 a hs
  refine ⟨hv, ?_, ?_⟩
  · simpa only [a, zero_add, hv] using hlt
  · simpa only [zero_add] using low_successor_lt_epsilon μ (Or.inr hμ) 0
      (hp.trans (omegaSequence_base_lt μ)) ε hε (hv.trans_lt hμε)

end Alexander313.Wilken.ParameterSuccessorBounds
