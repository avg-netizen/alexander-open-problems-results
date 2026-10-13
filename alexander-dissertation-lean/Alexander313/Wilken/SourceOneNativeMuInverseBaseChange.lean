import Alexander313.Wilken.SourceOneNativeMuInverseBaseChangeSupport

/-!
# Actual inverse-pi mu comparison at the original source base one

All source syntax uses original check0 and Theta.Normal0. The lower mu
code itself is a genuine upper-base preimage for pi. Its
literal omega-power producer and corrected chi/finite exponent agree at
both admitted epsilon contexts. Actual iota order, zero-or-limit
coefficients and finite-tail uniqueness prove the comparison from the
original source high-part order. The actual original0 fine predecessor derives that order on the printed
3.10 interval below. No Native base-one parser is used. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.MuInverseBaseChange

open ThetaCourse Support
open NativeContext.PublicEpsilonUnboundedIota.MuInverseBaseChange.Support
  (low_larger accepted_larger coefficient_order)

/-- The genuine lower coefficient also has the upper-root iota caller,
and its actual tree code is independent of these two roots. -/
theorem lower_coefficient_common (lower upper : Nat)
    (hl : Mu.inputCheck lower = true) (hu : Mu.inputCheck upper = true)
    (hlt : interpretation 0 lower < interpretation 0 upper) :
    inputCheck upper (OmegaQuotient.coefficientCode lower) = true ∧
      Mu.mappedCoefficient lower =
        literalCode upper (OmegaQuotient.coefficientCode lower) :=
  ⟨input_root_mono lower upper _ hu hlt.le (OmegaQuotient.coefficient_iota_input lower hl),
    literal_root_eq lower upper _ hu hlt.le (OmegaQuotient.coefficient_iota_input lower hl)⟩

theorem lower_mapped_accepted (lower upper : Nat)
    (hl : Mu.inputCheck lower = true) (hu : Mu.inputCheck upper = true)
    (hlt : interpretation 0 lower < interpretation 0 upper) :
    NativeContext.lowCheckCode (alphaCode upper) (Mu.mappedCoefficient lower) = true ∧
      NativeContext.Comparison.acceptedCode (alphaCode upper) (Mu.mappedCoefficient lower) = true := by
  have hs := Mu.mappedCoefficient_spec lower hl
  have hb : NativeContext.base (alphaCode lower) ≤ NativeContext.base (alphaCode upper) := by
    rw [OrderSupport.alpha_base lower hl, OrderSupport.alpha_base upper hu]
    exact hlt.le
  exact ⟨low_larger _ _ _ hs.1 (alphaCode_baseCheck upper hu) hb,
    accepted_larger _ _ _ hs.2 (alphaCode_baseCheck upper hu) hb⟩

/-- The chi correction in the ORIGINAL lower mu spelling equals the
actual upper-base chi of its genuinely admitted raised coefficient. -/
theorem lower_chi_raised (lower upper : Nat)
    (hl : Mu.inputCheck lower = true) (hu : Mu.inputCheck upper = true)
    (hlt : interpretation 0 lower < interpretation 0 upper) :
    Mu.chi lower = NativeContext.SourceChi.chiCode (alphaCode upper) (Mu.mappedCoefficient lower) :=
  NativeContext.SourceChi.BaseChange.chiCode_context _ _ _ (Mu.mappedCoefficient_spec lower hl).2
    (lower_mapped_accepted lower upper hl hu hlt).2

/-- The actual inverse-pi preimage has the literal corrected omega-power
value at the UPPER root base, with every power/finite-tail caller derived. -/
theorem inverse_mu_value (lower upper : Nat)
    (hl : Mu.inputCheck lower = true) (hu : Mu.inputCheck upper = true)
    (hlt : interpretation 0 lower < interpretation 0 upper) :
    NativeContext.interpretation (alphaCode upper) (Mu.muCode lower) = Ordinal.omega0 ^
      (NativeContext.interpretation (alphaCode upper) (Mu.mappedCoefficient lower) +
        cond (Mu.chi lower) (1 : Ordinal.{0}) 0 +
          (OmegaQuotient.coefficientOffset lower : Ordinal.{0})) := by
  have hc := lower_mapped_accepted lower upper hl hu hlt
  have hγ := Mu.exponentCode_spec lower hl
  have he := NativeContext.OmegaPowerHeight.finiteTailCode_spec (alphaCode upper)
    (Mu.mappedCoefficient lower) (Mu.tail lower) hc.1
  have hcode : Mu.exponentCode lower = NativeContext.OmegaPowerHeight.finiteTailCode (alphaCode upper)
      (Mu.mappedCoefficient lower) (Mu.tail lower) :=
    NativeContext.OmegaPowers.BaseChange.finiteTailCode_context _ _ _ _
      (alphaCode_baseCheck lower hl) (alphaCode_baseCheck upper hu)
      ((NativeContext.Comparison.acceptedCode_exact _ _).mp (Mu.mappedCoefficient_spec lower hl).2).1
      ((NativeContext.Comparison.acceptedCode_exact _ _).mp hc.2).1
  have he' : NativeContext.lowCheckCode (alphaCode upper) (Mu.exponentCode lower) = true := by
    rw [hcode]
    exact he.1
  rw [Mu.muCode_literal lower hl,
    NativeContext.OmegaPowers.BaseChange.powerCode_context _ _ _ hγ.1 he',
    (NativeContext.OmegaPowers.powerCode_spec _ _ he').2.2, hcode, he.2.2.1,
    Mu.tail, Nat.cast_add, add_assoc]
  cases hc : Mu.chi lower <;>
    simp only [hc, Bool.cond_true, Bool.cond_false, Nat.cast_zero, Nat.cast_one]

theorem source_coefficient_order (lower upper : Nat)
    (hl : Mu.inputCheck lower = true) (hu : Mu.inputCheck upper = true)
    (hh : interpretation 0 (OmegaQuotient.deltaCode lower) ≤
      interpretation 0 (OmegaQuotient.deltaCode upper)) :
    interpretation 0 (OmegaQuotient.coefficientCode lower) <
        interpretation 0 (OmegaQuotient.coefficientCode upper) ∨
      interpretation 0 (OmegaQuotient.coefficientCode lower) =
          interpretation 0 (OmegaQuotient.coefficientCode upper) ∧
        OmegaQuotient.coefficientOffset lower ≤ OmegaQuotient.coefficientOffset upper := by
  have hls := OmegaQuotient.coefficientCode_spec lower hl
  have hus := OmegaQuotient.coefficientCode_spec upper hu
  have hc : interpretation 0 (OmegaQuotient.coefficientCode lower) +
      (OmegaQuotient.coefficientOffset lower : Ordinal.{0}) ≤
        interpretation 0 (OmegaQuotient.coefficientCode upper) +
          (OmegaQuotient.coefficientOffset upper : Ordinal.{0}) := by
    apply le_of_not_gt
    intro hc
    have hm := mul_lt_mul_of_pos_left hc (omegaSequence_isSuccLimit (finiteBase 0) 0).bot_lt
    rw [hls.2.2.2, hus.2.2.2] at hm
    exact hm.not_ge hh
  exact coefficient_order _ _ _ _ hls.2.2.1 hus.2.2.1 hc

/-- This supporting inequality has the explicit original high-part
order hypothesis. The real fine-predecessor interval supplies it in the
printed source adapter; no coefficient/order oracle is introduced. -/
theorem inverse_mu_le_of_delta_le (lower upper : Nat)
    (hl : Mu.inputCheck lower = true) (hu : Mu.inputCheck upper = true)
    (hlt : interpretation 0 lower < interpretation 0 upper)
    (hh : interpretation 0 (OmegaQuotient.deltaCode lower) ≤
      interpretation 0 (OmegaQuotient.deltaCode upper)) :
    NativeContext.interpretation (alphaCode upper) (Mu.muCode lower) ≤ Mu.sourceValue upper := by
  have hcl := lower_coefficient_common lower upper hl hu hlt
  have hcu := OmegaQuotient.coefficient_iota_input upper hu
  have hal := lower_mapped_accepted lower upper hl hu hlt
  have hau := Mu.mappedCoefficient_spec upper hu
  have hchi := lower_chi_raised lower upper hl hu hlt
  rw [inverse_mu_value lower upper hl hu hlt, Mu.sourceValue, ← Mu.chi_correct upper hu]
  apply (omegaPower_strictMono.monotone)
  rcases source_coefficient_order lower upper hl hu hh with hs | ⟨hs, hk⟩
  · have hm : NativeContext.interpretation (alphaCode upper) (Mu.mappedCoefficient lower) <
        NativeContext.interpretation (alphaCode upper) (Mu.mappedCoefficient upper) := by
      rw [hcl.2, Mu.mappedCoefficient]
      exact (literalCode_lt_iff upper _ _ hcl.1 hcu).mpr hs
    have hlim := RhoMuSupport.mappedCoefficient_zero_or_limit upper hu
    rcases hlim with hz | hlim
    · rw [hz] at hm
      exact False.elim (hm.not_ge (bot_le))
    · have hf := hlim.add_natCast_lt hm
        (cond (Mu.chi lower) (1 : Nat) 0 + OmegaQuotient.coefficientOffset lower)
      have hf' : NativeContext.interpretation (alphaCode upper) (Mu.mappedCoefficient lower) +
          cond (Mu.chi lower) (1 : Ordinal.{0}) 0 +
            (OmegaQuotient.coefficientOffset lower : Ordinal.{0}) <
          NativeContext.interpretation (alphaCode upper) (Mu.mappedCoefficient upper) := by
        cases hc : Mu.chi lower <;>
          simpa only [hc, Bool.cond_true, Bool.cond_false, Nat.cast_add,
            Nat.cast_zero, Nat.cast_one, add_assoc] using hf
      calc
        _ ≤ NativeContext.interpretation (alphaCode upper) (Mu.mappedCoefficient upper) := hf'.le
        _ ≤ NativeContext.interpretation (alphaCode upper) (Mu.mappedCoefficient upper) +
            cond (Mu.chi upper) 1 0 := le_self_add
        _ ≤ NativeContext.interpretation (alphaCode upper) (Mu.mappedCoefficient upper) +
            cond (Mu.chi upper) 1 0 +
              (OmegaQuotient.coefficientOffset upper : Ordinal.{0}) := le_self_add
  · have hm : NativeContext.interpretation (alphaCode upper) (Mu.mappedCoefficient lower) =
        NativeContext.interpretation (alphaCode upper) (Mu.mappedCoefficient upper) := by
      rw [hcl.2, Mu.mappedCoefficient]
      exact literal_value_eq upper _ _ hcl.1 hcu hs
    have hc : Mu.chi lower = Mu.chi upper := hchi.trans
      (NativeContext.SourceChi.Invariance.chiCode_invariant _ _ _ hal.2 hau.2 hm)
    rw [hm, hc]
    exact add_le_add_left (Nat.cast_le.mpr hk) _

/-- The original lower mu output is the genuine Normal, fully
lower-parameter-bounded inverse-pi spelling and satisfies the comparison. -/
theorem inverse_pi_mu_spec_of_delta_le (lower upper : Nat)
    (hl : Mu.inputCheck lower = true) (hu : Mu.inputCheck upper = true)
    (hlt : interpretation 0 lower < interpretation 0 upper)
    (hh : interpretation 0 (OmegaQuotient.deltaCode lower) ≤
      interpretation 0 (OmegaQuotient.deltaCode upper)) :
    NativeContext.Comparison.acceptedCode (alphaCode upper) (Mu.muCode lower) = true ∧
      NativeContext.BaseTransformation.ParBounded (alphaCode upper) (alphaCode lower)
        (rawTree (Mu.muCode lower)) ∧
      NativeContext.BaseTransformation.piCode (alphaCode upper) (alphaCode lower)
        (Mu.muCode lower) = Mu.muCode lower ∧
      NativeContext.interpretation (alphaCode upper) (Mu.muCode lower) ≤ Mu.sourceValue upper := by
  have hi := inverse_pi_literal lower upper hl hu hlt
  exact ⟨hi.1, hi.2.1, hi.2.2, inverse_mu_le_of_delta_le lower upper hl hu hlt hh⟩


/-- Actual original-source-one fine predecessor, with the printed original
Definition2.34 algorithm rather than any native-base-one parser. -/
noncomputable def fineBar (root : Nat) : Ordinal.{0} :=
  Localization.value 0 (FinePredecessor.predecessorCode 0 root)

theorem root_node (root : Nat) (ha : Mu.inputCheck root = true) : Localization.Node 0 root := by
  obtain ⟨t, he, ht, hn, hh⟩ := (Mu.inputCheck_exact root).mp ha
  exact ⟨t, he, ht, hn⟩

theorem predecessor_caller (root : Nat) (ha : Mu.inputCheck root = true) :
    FinePredecessor.inputCheck 0 root = true :=
  (FinePredecessor.inputCheck_exact 0 root).mpr ⟨root_node root ha,
    by simpa only [finiteBase_zero, Localization.value] using
      EpsilonOffsets.epsilon_one_lt (root_epsilon root ha)⟩

/-- The actual original fine interval derives strict argument order. -/
theorem fine_gap_argument_lt (lower upper : Nat)
    (hl : Mu.inputCheck lower = true) (hu : Mu.inputCheck upper = true)
    (hlo : fineBar upper < interpretation 0 lower)
    (hhi : interpretation 0 lower < interpretation 0 upper) :
    interpretation 0 (Localization.argumentCode lower) <
      interpretation 0 (Localization.argumentCode upper) := by
  exact FineLocalization.OrderSupport.predecessor_gap_argument_lt 0 upper lower
    (predecessor_caller upper hu) (root_node lower hl) hlo hhi

/-- Real original0 ANF decomposition is the divided high part, with its
actual argument admission derived from the original high root. -/
theorem delta_value (root : Nat) (ha : Mu.inputCheck root = true) :
    interpretation 0 (OmegaQuotient.deltaCode root) =
      SourceHighPartComparison.highPart (omegaSequence (finiteBase 0) 1)
        (interpretation 0 (Localization.argumentCode root)) := by
  simpa only [OmegaQuotient.deltaCode, OmegaQuotient.argumentCode,
    SourceHighPartComparison.highPart, Nat.zero_add] using
    (SourceDecomposition.parts_code_value 0 0 (OmegaQuotient.argumentCode root)
      (OmegaQuotient.argument_accepted root ha)).1

theorem fine_gap_delta_le (lower upper : Nat)
    (hl : Mu.inputCheck lower = true) (hu : Mu.inputCheck upper = true)
    (hlo : fineBar upper < interpretation 0 lower)
    (hhi : interpretation 0 lower < interpretation 0 upper) :
    interpretation 0 (OmegaQuotient.deltaCode lower) ≤
      interpretation 0 (OmegaQuotient.deltaCode upper) := by
  rw [delta_value lower hl, delta_value upper hu]
  exact SourceHighPartComparison.highPart_mono _
    (fine_gap_argument_lt lower upper hl hu hlo hhi).le

/-- Printed Lemma3.10 at the genuine ORIGINAL tau=1 domain. Only the
original epsilon high roots and actual alphaBar < gamma < alpha are
premises; every inverse-pi, argument and coefficient caller is derived. -/
theorem inverse_pi_mu_spec (lower upper : Nat)
    (hl : Mu.inputCheck lower = true) (hu : Mu.inputCheck upper = true)
    (hlo : fineBar upper < interpretation 0 lower)
    (hhi : interpretation 0 lower < interpretation 0 upper) :
    NativeContext.Comparison.acceptedCode (alphaCode upper) (Mu.muCode lower) = true ∧
      NativeContext.BaseTransformation.ParBounded (alphaCode upper) (alphaCode lower)
        (rawTree (Mu.muCode lower)) ∧
      NativeContext.BaseTransformation.piCode (alphaCode upper) (alphaCode lower)
        (Mu.muCode lower) = Mu.muCode lower ∧
      NativeContext.interpretation (alphaCode upper) (Mu.muCode lower) ≤ Mu.sourceValue upper :=
  inverse_pi_mu_spec_of_delta_le lower upper hl hu hhi (fine_gap_delta_le lower upper hl hu hlo hhi)

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.MuInverseBaseChange
