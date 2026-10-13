import Alexander313.Wilken.HereditaryParameterSuccessorBounds

/-!
# Value fidelity of genuine LOW context successors

The actual epsilon-plus-finite correction is preserved by argument plus
one in both directions. Therefore a real LOW theta successor is the existing
independently defined next additive principal of its value. Every genuine
non-epsilon theta representation has a LOW argument, so this identifies its
successor across all genuine lower E1 contexts. The explicit epsilon
self-context also has this property. No new parameter-plus operation is
defined, and no HIGH epsilon presentation is identified with that operation.
Uncompiled candidates.
-/

namespace Alexander313.Wilken.ParameterSuccessorBounds.LowContext

/-- The strict-above-base epsilon offset correction cannot start at the
successor of a non-offset argument: a pure epsilon is a proper limit. -/
theorem epsilonFiniteAbove_add_one_iff (tau a : Ordinal.{0}) :
    EpsilonFiniteAbove tau (a + 1) ↔ EpsilonFiniteAbove tau a := by
  constructor
  · rintro ⟨epsilon, n, hbase, hepsilon, he⟩
    cases n with
    | zero =>
      have he' : a + 1 = epsilon := by simpa only [Nat.cast_zero, add_zero] using he
      have ha : a < epsilon := (lt_add_one a).trans_eq he'
      exact False.elim (((epsilon_isSuccLimit hepsilon).add_one_lt ha).ne he')
    | succ n =>
      have he' : a + 1 = (epsilon + (n : Ordinal.{0})) + 1 := by
        simpa only [Nat.cast_succ, ← add_assoc] using he
      exact ⟨epsilon, n, hbase, hepsilon, (Ordinal.add_right_cancel 1).mp he'⟩
  · exact epsilonFiniteAbove_successor tau a

/-- The genuine corrected exponent commutes with a literal argument
successor, including the full strict epsilon-plus-finite correction. -/
theorem lowOmegaExponent_add_one (tau a : Ordinal.{0}) :
    lowOmegaExponent tau (a + 1) = lowOmegaExponent tau a + 1 := by
  classical
  by_cases h : EpsilonFiniteAbove tau a
  · rw [lowOmegaExponent_of_offset tau (a + 1) (epsilonFiniteAbove_successor tau a h),
      lowOmegaExponent_of_offset tau a h]
  · have hs : ¬ EpsilonFiniteAbove tau (a + 1) :=
      fun hs => h ((epsilonFiniteAbove_add_one_iff tau a).mp hs)
    rw [lowOmegaExponent_of_not_offset tau (a + 1) hs,
      lowOmegaExponent_of_not_offset tau a h, add_assoc]

/-- This is an equality about the actual theta argument-plus-one operation,
not a definition replacing a context-dependent successor. -/
theorem low_collapse_successor_eq_next (tau : Ordinal.{0})
    (htau : tau = 1 ∨ Ordinal.omega0 ^ tau = tau) (a : Ordinal.{0})
    (ha : a < omegaSequence tau 1) :
    globalCollapse tau 0 (a + 1) = nextAdditivePrincipal (globalCollapse tau 0 a) := by
  have hs := (omegaSequence_isSuccLimit tau 0).add_one_lt ha
  rw [globalCollapse_low_eq_omegaPower tau htau (a + 1) hs,
    globalCollapse_low_eq_omegaPower tau htau a ha,
    nextAdditivePrincipal_omegaPower, lowOmegaExponent_add_one]

/-- Every genuine non-epsilon theta representation, at any actual E1
context, has the same literal successor value when its root value agrees. -/
theorem non_epsilon_successor_value_invariant
    (tau sigma : Ordinal.{0})
    (htau : tau = 1 ∨ Ordinal.omega0 ^ tau = tau)
    (hsigma : sigma = 1 ∨ Ordinal.omega0 ^ sigma = sigma)
    (a : GlobalNotationOrdinal tau 1) (b : GlobalNotationOrdinal sigma 1)
    (ha : a.val < omegaSequence tau 2) (hb : b.val < omegaSequence sigma 2)
    (hne : Ordinal.omega0 ^ globalCollapse tau 0 a.val ≠ globalCollapse tau 0 a.val)
    (hv : globalCollapse tau 0 a.val = globalCollapse sigma 0 b.val) :
    globalCollapse tau 0 (a.val + 1) = globalCollapse sigma 0 (b.val + 1) := by
  have hne' : Ordinal.omega0 ^ globalCollapse sigma 0 b.val ≠ globalCollapse sigma 0 b.val := by
    rw [← hv]
    exact hne
  rw [low_collapse_successor_eq_next tau htau a.val
      (non_epsilon_argument_low tau htau a ha hne),
    low_collapse_successor_eq_next sigma hsigma b.val
      (non_epsilon_argument_low sigma hsigma b hb hne'), hv]

/-- The explicitly constructed epsilon self-context is a genuine LOW
theta context, so its literal theta_mu(1) has the same independent value. -/
theorem epsilon_self_successor_eq_next (mu : Ordinal.{0})
    (hmu : Ordinal.omega0 ^ mu = mu) :
    globalCollapse mu 0 1 = nextAdditivePrincipal mu := by
  have hp := epsilon_or_one_pos (Or.inr hmu)
  have hz : globalCollapse mu 0 0 = mu := by
    simpa only [omegaSequence_zero] using
      globalCollapse_zero mu hp (epsilon_or_one_add_closed (Or.inr hmu)) 0
  simpa only [zero_add, hz] using low_collapse_successor_eq_next mu (Or.inr hmu) 0
    (hp.trans (omegaSequence_base_lt mu))

end Alexander313.Wilken.ParameterSuccessorBounds.LowContext
