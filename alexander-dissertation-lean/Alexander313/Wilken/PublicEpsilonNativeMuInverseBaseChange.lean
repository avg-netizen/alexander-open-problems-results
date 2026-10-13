import Alexander313.Wilken.PublicEpsilonNativeMuInverseBaseChangeSupport

/-!
# Actual inverse-pi mu comparison from genuine high-part order

The lower mu code itself is a genuine upper-base preimage for pi. Its
literal omega-power producer and corrected chi/finite exponent agree at
both admitted epsilon contexts. Actual iota order, zero-or-limit
coefficients and finite-tail uniqueness prove the comparison from the
original source high-part order. A separate original fine-predecessor
adapter supplies that order on the printed 3.10 interval; the displayed
head-order premise here is a supporting arithmetic hypothesis, not a
replacement for the source's fine-predecessor premise. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.MuInverseBaseChange

open ThetaCourse Support

/-- The genuine lower coefficient also has the upper-root iota caller,
and its actual tree code is independent of these two roots. -/
theorem lower_coefficient_common (q lower upper : Nat)
    (hl : Mu.inputCheck q lower = true) (hu : Mu.inputCheck q upper = true)
    (hlt : interpretation q lower < interpretation q upper) :
    inputCheck q upper (OmegaQuotient.coefficientCode q lower) = true ∧
      Mu.mappedCoefficient q lower =
        literalCode q upper (OmegaQuotient.coefficientCode q lower) :=
  ⟨input_root_mono q lower upper _ hu hlt.le (OmegaQuotient.coefficient_iota_input q lower hl),
    literal_root_eq q lower upper _ hu hlt.le (OmegaQuotient.coefficient_iota_input q lower hl)⟩

theorem lower_mapped_accepted (q lower upper : Nat)
    (hl : Mu.inputCheck q lower = true) (hu : Mu.inputCheck q upper = true)
    (hlt : interpretation q lower < interpretation q upper) :
    lowCheckCode (betaCode q upper) (Mu.mappedCoefficient q lower) = true ∧
      Comparison.acceptedCode (betaCode q upper) (Mu.mappedCoefficient q lower) = true := by
  have hs := Mu.mappedCoefficient_spec q lower hl
  have hb : base (betaCode q lower) ≤ base (betaCode q upper) := by
    rw [beta_base q lower hl, beta_base q upper hu]
    exact hlt.le
  exact ⟨low_larger _ _ _ hs.1 (betaCode_baseCheck q upper hu) hb,
    accepted_larger _ _ _ hs.2 (betaCode_baseCheck q upper hu) hb⟩

/-- The chi correction in the ORIGINAL lower mu spelling equals the
actual upper-base chi of its genuinely admitted raised coefficient. -/
theorem lower_chi_raised (q lower upper : Nat)
    (hl : Mu.inputCheck q lower = true) (hu : Mu.inputCheck q upper = true)
    (hlt : interpretation q lower < interpretation q upper) :
    Mu.chi q lower = SourceChi.chiCode (betaCode q upper) (Mu.mappedCoefficient q lower) :=
  SourceChi.BaseChange.chiCode_context _ _ _ (Mu.mappedCoefficient_spec q lower hl).2
    (lower_mapped_accepted q lower upper hl hu hlt).2

/-- The actual inverse-pi preimage has the literal corrected omega-power
value at the UPPER root base, with every power/finite-tail caller derived. -/
theorem inverse_mu_value (q lower upper : Nat)
    (hl : Mu.inputCheck q lower = true) (hu : Mu.inputCheck q upper = true)
    (hlt : interpretation q lower < interpretation q upper) :
    interpretation (betaCode q upper) (Mu.muCode q lower) = Ordinal.omega0 ^
      (interpretation (betaCode q upper) (Mu.mappedCoefficient q lower) +
        cond (Mu.chi q lower) (1 : Ordinal.{0}) 0 +
          (OmegaQuotient.coefficientOffset q lower : Ordinal.{0})) := by
  have hc := lower_mapped_accepted q lower upper hl hu hlt
  have hγ := Mu.exponentCode_spec q lower hl
  have he := OmegaPowerHeight.finiteTailCode_spec (betaCode q upper)
    (Mu.mappedCoefficient q lower) (Mu.tail q lower) hc.1
  have hcode : Mu.exponentCode q lower = OmegaPowerHeight.finiteTailCode (betaCode q upper)
      (Mu.mappedCoefficient q lower) (Mu.tail q lower) :=
    OmegaPowers.BaseChange.finiteTailCode_context _ _ _ _
      (betaCode_baseCheck q lower hl) (betaCode_baseCheck q upper hu)
      ((Comparison.acceptedCode_exact _ _).mp (Mu.mappedCoefficient_spec q lower hl).2).1
      ((Comparison.acceptedCode_exact _ _).mp hc.2).1
  have he' : lowCheckCode (betaCode q upper) (Mu.exponentCode q lower) = true := by
    rw [hcode]
    exact he.1
  rw [Mu.muCode_literal q lower hl,
    OmegaPowers.BaseChange.powerCode_context _ _ _ hγ.1 he',
    (OmegaPowers.powerCode_spec _ _ he').2.2, hcode, he.2.2.1,
    Mu.tail, Nat.cast_add, add_assoc]
  cases hc : Mu.chi q lower <;>
    simp only [hc, Bool.cond_true, Bool.cond_false, Nat.cast_zero, Nat.cast_one]

theorem source_coefficient_order (q lower upper : Nat)
    (hl : Mu.inputCheck q lower = true) (hu : Mu.inputCheck q upper = true)
    (hh : interpretation q (OmegaQuotient.deltaCode lower) ≤
      interpretation q (OmegaQuotient.deltaCode upper)) :
    interpretation q (OmegaQuotient.coefficientCode q lower) <
        interpretation q (OmegaQuotient.coefficientCode q upper) ∨
      interpretation q (OmegaQuotient.coefficientCode q lower) =
          interpretation q (OmegaQuotient.coefficientCode q upper) ∧
        OmegaQuotient.coefficientOffset q lower ≤ OmegaQuotient.coefficientOffset q upper := by
  have hls := OmegaQuotient.coefficientCode_spec q lower hl
  have hus := OmegaQuotient.coefficientCode_spec q upper hu
  have hc : interpretation q (OmegaQuotient.coefficientCode q lower) +
      (OmegaQuotient.coefficientOffset q lower : Ordinal.{0}) ≤
        interpretation q (OmegaQuotient.coefficientCode q upper) +
          (OmegaQuotient.coefficientOffset q upper : Ordinal.{0}) := by
    apply le_of_not_gt
    intro hc
    have hm := mul_lt_mul_of_pos_left hc (omegaSequence_isSuccLimit (base q) 0).bot_lt
    rw [hls.2.2.2, hus.2.2.2] at hm
    exact hm.not_ge hh
  exact coefficient_order _ _ _ _ hls.2.2.1 hus.2.2.1 hc

/-- This supporting inequality has the explicit original high-part
order hypothesis. The real fine-predecessor interval supplies it in the
printed source adapter; no coefficient/order oracle is introduced. -/
theorem inverse_mu_le_of_delta_le (q lower upper : Nat)
    (hl : Mu.inputCheck q lower = true) (hu : Mu.inputCheck q upper = true)
    (hlt : interpretation q lower < interpretation q upper)
    (hh : interpretation q (OmegaQuotient.deltaCode lower) ≤
      interpretation q (OmegaQuotient.deltaCode upper)) :
    interpretation (betaCode q upper) (Mu.muCode q lower) ≤ Mu.sourceValue q upper := by
  have hcl := lower_coefficient_common q lower upper hl hu hlt
  have hcu := OmegaQuotient.coefficient_iota_input q upper hu
  have hal := lower_mapped_accepted q lower upper hl hu hlt
  have hau := Mu.mappedCoefficient_spec q upper hu
  have hchi := lower_chi_raised q lower upper hl hu hlt
  rw [inverse_mu_value q lower upper hl hu hlt, Mu.sourceValue, ← Mu.chi_correct q upper hu]
  apply (omegaPower_strictMono.monotone)
  rcases source_coefficient_order q lower upper hl hu hh with hs | ⟨hs, hk⟩
  · have hm : interpretation (betaCode q upper) (Mu.mappedCoefficient q lower) <
        interpretation (betaCode q upper) (Mu.mappedCoefficient q upper) := by
      rw [hcl.2, Mu.mappedCoefficient]
      exact (literalCode_lt_iff q upper _ _ hcl.1 hcu).mpr hs
    have hlim := RhoMuSupport.mappedCoefficient_zero_or_limit q upper hu
    rcases hlim with hz | hlim
    · rw [hz] at hm
      exact False.elim (hm.not_ge (bot_le))
    · have hf := hlim.add_natCast_lt hm
        (cond (Mu.chi q lower) (1 : Nat) 0 + OmegaQuotient.coefficientOffset q lower)
      have hf' : interpretation (betaCode q upper) (Mu.mappedCoefficient q lower) +
          cond (Mu.chi q lower) (1 : Ordinal.{0}) 0 +
            (OmegaQuotient.coefficientOffset q lower : Ordinal.{0}) <
          interpretation (betaCode q upper) (Mu.mappedCoefficient q upper) := by
        cases hc : Mu.chi q lower <;>
          simpa only [hc, Bool.cond_true, Bool.cond_false, Nat.cast_add,
            Nat.cast_zero, Nat.cast_one, add_assoc] using hf
      calc
        _ ≤ interpretation (betaCode q upper) (Mu.mappedCoefficient q upper) := hf'.le
        _ ≤ interpretation (betaCode q upper) (Mu.mappedCoefficient q upper) +
            cond (Mu.chi q upper) 1 0 := le_self_add
        _ ≤ interpretation (betaCode q upper) (Mu.mappedCoefficient q upper) +
            cond (Mu.chi q upper) 1 0 +
              (OmegaQuotient.coefficientOffset q upper : Ordinal.{0}) := le_self_add
  · have hm : interpretation (betaCode q upper) (Mu.mappedCoefficient q lower) =
        interpretation (betaCode q upper) (Mu.mappedCoefficient q upper) := by
      rw [hcl.2, Mu.mappedCoefficient]
      exact (literalCode_eq_iff q upper _ _ hcl.1 hcu).mpr hs
    have hc : Mu.chi q lower = Mu.chi q upper := hchi.trans
      (SourceChi.Invariance.chiCode_invariant _ _ _ hal.2 hau.2 hm)
    rw [hm, hc]
    exact add_le_add_left (Nat.cast_le.mpr hk) _

/-- The original lower mu output is the genuine Normal, fully
lower-parameter-bounded inverse-pi spelling and satisfies the comparison. -/
theorem inverse_pi_mu_spec_of_delta_le (q lower upper : Nat)
    (hl : Mu.inputCheck q lower = true) (hu : Mu.inputCheck q upper = true)
    (hlt : interpretation q lower < interpretation q upper)
    (hh : interpretation q (OmegaQuotient.deltaCode lower) ≤
      interpretation q (OmegaQuotient.deltaCode upper)) :
    Comparison.acceptedCode (betaCode q upper) (Mu.muCode q lower) = true ∧
      BaseTransformation.ParBounded (betaCode q upper) (betaCode q lower)
        (rawTree (Mu.muCode q lower)) ∧
      BaseTransformation.piCode (betaCode q upper) (betaCode q lower)
        (Mu.muCode q lower) = Mu.muCode q lower ∧
      interpretation (betaCode q upper) (Mu.muCode q lower) ≤ Mu.sourceValue q upper := by
  have hi := inverse_pi_literal q lower upper hl hu hlt
  exact ⟨hi.1, hi.2.1, hi.2.2, inverse_mu_le_of_delta_le q lower upper hl hu hlt hh⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.MuInverseBaseChange
