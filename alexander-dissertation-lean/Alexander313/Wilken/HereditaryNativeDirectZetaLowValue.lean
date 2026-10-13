import Alexander313.Wilken.HereditaryNativeDirectZeta
import Alexander313.Wilken.HereditaryNativeLambdaPrincipalLimitsSupport
import Alexander313.Wilken.HereditaryLastExponentAddition

/-!
# Actual low zeta depends only on its non-epsilon root value

The literal corrected LOW collapse exponent gives the exact zeta value,
not just its zero test. A genuine epsilon-plus-finite offset has successor
corrected exponent: the pure epsilon input is actually fixed, and a positive
finite tail already has last exponent zero. Outside that offset case, true
fixed-point epsilon recognition derives STRICT, and positive right addition
preserves the last exponent. Actual low collapse and logarithm injectivity
then make non-epsilon zeta independent of its coded epsilon base.
No fixedness, strictness, logarithm or cross-base transport oracle is given.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.DirectZeta.LowValue

open NativeContext.Lambda.PrincipalLimits

theorem low_zeta_exact (q : Nat) (t : RelativeTerm Nat)
    (ht : check q (.theta 0 t) = true) (hn : Comparison.Normal q t)
    (hl : denote q t < omegaSequence (base q) 1) (hp : 0 < denote q t) :
    (if FixedPoint.SourceStrict q 0 t.code then Hereditary.SourceZeta.lastExponent (denote q t) else 0) =
      Hereditary.SourceZeta.lastExponent (lowOmegaExponent (base q) (denote q t)) := by
  classical
  have hq := (Bool.and_eq_true.mp ht).1
  have hepsilon := SourceChi.epsilon_base q hq
  by_cases hoff : EpsilonFiniteAbove (base q) (denote q t)
  · have he : Hereditary.SourceZeta.lastExponent (lowOmegaExponent (base q) (denote q t)) = 0 := by
      rw [lowOmegaExponent_of_offset _ _ hoff, Hereditary.SourceZeta.lastExponent,
        SourceChi.Powers.endValue_successor, Ordinal.log_one_right]
    rw [he]
    obtain ⟨ε, k, hτε, hε, hη⟩ := hoff
    cases k with
    | zero =>
      have hηε : denote q t = ε := by simpa only [Nat.cast_zero, add_zero] using hη
      have hf : FixedPoint.SourceFixed q 0 t.code := by
        simp only [FixedPoint.SourceFixed, FixedPoint.delta, FixedPoint.residual,
          interpretation_code, Ordinal.div_eq_zero_of_lt hl, mul_zero,
          Ordinal.mod_eq_of_lt hl, hηε]
        exact SourceChi.Powers.epsilon_low_sup_fixed (base q) ε hepsilon hτε hε
          (by simpa only [hηε] using hl)
      have hs : ¬ FixedPoint.SourceStrict q 0 t.code := fun hs =>
        (strict_iff_not_fixed q t ht hn).mp hs hf
      simp only [if_neg hs]
    | succ k =>
      have hz : Hereditary.SourceZeta.lastExponent (denote q t) = 0 := by
        rw [hη, Nat.cast_succ, ← add_assoc, Hereditary.SourceZeta.lastExponent,
          SourceChi.Powers.endValue_successor, Ordinal.log_one_right]
      split_ifs <;> simp only [hz]
  · have hnf : ¬ FixedPoint.SourceFixed q 0 t.code := by
      intro hf
      have hε := SourceChi.Powers.fixed_low_epsilon q t ht hn hl hp hf
      exact hoff ⟨denote q t, 0, hε.2, hε.1, by simp only [Nat.cast_zero, add_zero]⟩
    have hs := (strict_iff_not_fixed q t ht hn).mpr hnf
    rw [if_pos hs, lowOmegaExponent_of_not_offset _ _ hoff, lowOmegaBase_of_epsilon _ hepsilon]
    exact (Hereditary.LastExponentAddition.lastExponent_add _ _ hp).symm

theorem sourceValue_low_root (q : Nat) (t : RelativeTerm Nat)
    (ht : check q (.theta 0 t) = true) (hn : Comparison.Normal q t)
    (hl : denote q t < omegaSequence (base q) 1) (hp : 0 < denote q t) :
    sourceValue q (.theta 0 t : RelativeTerm Nat).code =
      Hereditary.SourceZeta.lastExponent (Ordinal.log Ordinal.omega0 (denote q (.theta 0 t))) := by
  have hcollapse : denote q (.theta 0 t) = Ordinal.omega0 ^ lowOmegaExponent (base q) (denote q t) :=
    globalCollapse_low_eq_omegaPower (base q)
      (Or.inr (SourceChi.epsilon_base q (Bool.and_eq_true.mp ht).1)) _ hl
  rw [hcollapse, Ordinal.log_opow Ordinal.one_lt_omega0]
  simpa only [sourceValue, argumentCode, Localization.argumentCode_theta,
    FixedPoint.residual, interpretation_code, Ordinal.mod_eq_of_lt hl] using
    low_zeta_exact q t ht hn hl hp

/-- Every ORIGINAL non-epsilon Normal theta-zero root derives its LOW
positive argument; no additional branch or argument guard is supplied. -/
theorem sourceValue_non_epsilon (q c : Nat) (hc : inputCheck q c = true)
    (hε : Ordinal.omega0 ^ interpretation q c ≠ interpretation q c) :
    sourceValue q c = Hereditary.SourceZeta.lastExponent (Ordinal.log Ordinal.omega0 (interpretation q c)) := by
  obtain ⟨t, he, ht, hn⟩ := (inputCheck_exact q c).mp hc
  have hq := (Bool.and_eq_true.mp ht).1
  have hne : Ordinal.omega0 ^ denote q (.theta 0 t) ≠ denote q (.theta 0 t) := by
    simpa only [he, interpretation_code] using hε
  have hl : denote q t < omegaSequence (base q) 1 := by
    apply lt_of_not_ge
    intro hh
    exact hne ((OmegaPowers.theta_epsilon_iff q t ht).mpr (Or.inr hh))
  have hnz : denote q t ≠ 0 := by
    intro hz
    have hb : denote q (.theta 0 t) = base q := by
      change globalCollapse (base q) 0 (denote q t) = base q
      rw [hz, globalCollapse_zero (base q) (base_pos q hq) (base_add_closed q hq) 0,
        omegaSequence_zero]
    exact hne ((OmegaPowers.theta_epsilon_iff q t ht).mpr (Or.inl hb))
  simpa only [he, interpretation_code] using sourceValue_low_root q t ht hn hl
    (pos_iff_ne_zero.mpr hnz)

/-- The mathematical zeta values at ANY genuine coded epsilon contexts
agree for equal ORIGINAL admitted non-epsilon root values. -/
theorem sourceValue_invariant_non_epsilon (q c p d : Nat)
    (hc : inputCheck q c = true) (hd : inputCheck p d = true)
    (hv : interpretation q c = interpretation p d)
    (hε : Ordinal.omega0 ^ interpretation q c ≠ interpretation q c) :
    sourceValue q c = sourceValue p d := by
  have hεd : Ordinal.omega0 ^ interpretation p d ≠ interpretation p d := by
    simpa only [hv] using hε
  rw [sourceValue_non_epsilon q c hc hε, sourceValue_non_epsilon p d hd hεd, hv]

theorem execute_value_invariant_non_epsilon (q c out p d other : Nat)
    (ho : out ∈ execute q c) (he : other ∈ execute p d)
    (hv : interpretation q c = interpretation p d)
    (hε : Ordinal.omega0 ^ interpretation q c ≠ interpretation q c) :
    interpretation q out = interpretation p other := by
  have hs := execute_spec q c out ho
  have ht := execute_spec p d other he
  exact hs.2.2.2.trans ((sourceValue_invariant_non_epsilon q c p d hs.1 ht.1 hv hε).trans ht.2.2.2.symm)

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.DirectZeta.LowValue
