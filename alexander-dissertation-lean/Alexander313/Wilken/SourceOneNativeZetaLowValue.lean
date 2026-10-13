import Alexander313.Wilken.SourceOneNativeLambdaPublicBranches
import Alexander313.Wilken.HereditaryNativeDirectZetaLowValue

/-!
# The genuine original source-one low zeta value

The actual ordinary residual supremum has its source-one fixed boundary at
one, in addition to zero and genuine higher epsilon presentations. Every
case is derived from the original source-zero checker and fixed-point test.
The corrected low-collapse exponent has starting exponent zero at source
one. Its last exponent agrees with the literal STRICT-or-zero zeta; this
gives the same root-logarithm formula as the genuine native epsilon case.
No native base-one parser or fixedness/STRICT/equality oracle is supplied.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.ZetaLowValue

open SourceFixedPointLimits

/-- Genuine low epsilon fixedness also includes the original base one. -/
theorem low_epsilon_sup_fixed (τ ε : Ordinal.{0})
    (hτ : τ = 1 ∨ Ordinal.omega0 ^ τ = τ) (hτε : τ < ε)
    (hε : Ordinal.omega0 ^ ε = ε) (hl : ε < omegaSequence τ 1) :
    globalResidualImageSup τ 0 0 ε = ε := by
  have hτpos := epsilon_or_one_pos hτ
  have hεp := epsilon_or_one_add_closed (Or.inr hε)
  have hεone : 1 < ε := Ordinal.one_lt_omega0.trans (epsilon_omega_lt hε)
  have hlim := Ordinal.isSuccLimit_of_isPrincipal_add hεone hεp
  apply le_antisymm
  · apply Ordinal.bsup_le
    intro σ hσ
    change globalCollapse τ 0 (0 + σ) ≤ ε
    rw [zero_add, globalCollapse_low_eq_omegaPower τ hτ σ (hσ.trans hl)]
    have hshift : lowOmegaBase τ + σ < ε := hεp ((lowOmegaBase_le τ).trans_lt hτε) hσ
    have hexp : lowOmegaExponent τ σ < ε :=
      (lowOmegaExponent_le_shift_succ τ σ).trans_lt (hlim.add_one_lt hshift)
    exact (omegaPower_strictMono hexp).le.trans_eq hε
  · by_contra! hs
    have hp := globalCollapse_low_argument_lt τ hτpos 0
      (globalResidualImageSup τ 0 0 ε) (hs.trans hl)
    have hb := Ordinal.le_bsup (fun σ _ => globalCollapse τ 0 (0 + σ))
      (globalResidualImageSup τ 0 0 ε) hs
    have hb' : globalCollapse τ 0 (globalResidualImageSup τ 0 0 ε) ≤
        globalResidualImageSup τ 0 0 ε := by simpa only [zero_add] using hb
    exact hp.not_ge hb'

theorem strict_iff_not_fixed (t : RelativeTerm Nat)
    (ht : check 0 (.theta 0 t) = true) (hn : Theta.Normal 0 (.theta 0 t)) :
    SourceFixedPoint.SourceStrict 0 0 t.code ↔ ¬ SourceFixedPoint.SourceFixed 0 0 t.code := by
  have hc := (SourceZeta.inputCheck_exact 0 _).mpr ⟨t, rfl, ht, hn⟩
  have hi : SourceFixedPoint.inputCheck 0 0 t.code = true := by
    simpa only [SourceZeta.argumentCode, Localization.argumentCode_theta] using
      SourceZeta.argument_fixedPoint_input 0 (.theta 0 t : RelativeTerm Nat).code hc
  rw [← SourceFixedPoint.strictCode_correct 0 0 t.code hi,
    ← SourceFixedPoint.fixedCode_correct 0 0 t.code hi]
  simp only [SourceFixedPoint.strictCode, hi, Bool.true_and, Bool.not_eq_true',
    Bool.eq_false_eq_not_eq_true]

/-- The actual original one-boundary clause is retained. Outside it, a
positive LOW fixed residual is a genuine epsilon higher presentation. -/
theorem fixed_low_epsilon_or_one (t : RelativeTerm Nat)
    (ht : check 0 (.theta 0 t) = true) (hn : Theta.Normal 0 (.theta 0 t))
    (hl : denote 0 t < omegaSequence 1 1) (hp : 0 < denote 0 t)
    (hf : SourceFixedPoint.SourceFixed 0 0 t.code) :
    denote 0 t = 1 ∨ (Ordinal.omega0 ^ denote 0 t = denote 0 t ∧ 1 < denote 0 t) := by
  have hc := (SourceZeta.inputCheck_exact 0 _).mpr ⟨t, rfl, ht, hn⟩
  have hi : SourceFixedPoint.inputCheck 0 0 t.code = true := by
    simpa only [SourceZeta.argumentCode, Localization.argumentCode_theta] using
      SourceZeta.argument_fixedPoint_input 0 (.theta 0 t : RelativeTerm Nat).code hc
  have ha : SourceDecomposition.inputCheck 0 t.code = true := by
    simpa only [SourceZeta.argumentCode, Localization.argumentCode_theta] using
      SourceZeta.argument_input 0 (.theta 0 t : RelativeTerm Nat).code hc
  have hv := SourceDecomposition.parts_code_value 0 0 t.code ha
  have hd : interpretation 0 (SourceDecomposition.highCode 0 0 t.code) = 0 := by
    rw [hv.1, interpretation_code, finiteBase_zero, Ordinal.div_eq_zero_of_lt hl, mul_zero]
  have he : interpretation 0 (SourceDecomposition.lowCode 0 0 t.code) = denote 0 t := by
    rw [hv.2, interpretation_code, finiteBase_zero, Ordinal.mod_eq_of_lt hl]
  rcases (SourceFixedPoint.fixed_parts_iff 0 0 t.code hi).mp hf with hz | hb | hh
  · exact False.elim ((ne_of_gt hp) (he.symm.trans hz))
  · exact Or.inl (he.symm.trans hb.1)
  · obtain ⟨b, Γ, ρ, hbm, hbs, hΓ, hρ, hbe, hdΓ, hη, hstar⟩ := hh
    have hΓpos : 0 < Γ := by simpa only [SourceFixedPoint.checkedOrdinal_val, hd] using hdΓ
    obtain ⟨δ, hδ⟩ := hΓ
    have hδpos : 0 < δ := by
      apply pos_iff_ne_zero.mpr
      intro hz
      rw [hδ, hz, mul_zero] at hΓpos
      exact (lt_irrefl 0) hΓpos
    have hΩΓ : omegaSequence (finiteBase 0) 1 ≤ Γ := by
      rw [hδ]
      simpa only [mul_one] using mul_le_mul' (le_rfl : omegaSequence (finiteBase 0) 1 ≤ _)
        (Order.one_le_iff_pos.mpr hδpos)
    have hbhigh : omegaSequence (finiteBase 0) 1 ≤ b.val := hΩΓ.trans (by rw [hbe]; exact le_self_add)
    have hvalue : denote 0 t = globalCollapse (finiteBase 0) 0 b.val := he.symm.trans hη
    apply Or.inr
    rw [hvalue]
    exact ⟨global_high_epsilon (finiteBase 0) (Or.inl finiteBase_zero) b hbs hbhigh,
      by simpa only [finiteBase_zero] using NativeContext.SourceChi.Powers.global_high_base_lt
        (finiteBase 0) (finiteBase_pos 0) b hbs hbhigh⟩

theorem low_zeta_exact (t : RelativeTerm Nat)
    (ht : check 0 (.theta 0 t) = true) (hn : Theta.Normal 0 (.theta 0 t))
    (hl : denote 0 t < omegaSequence 1 1) (hp : 0 < denote 0 t) :
    (if SourceFixedPoint.SourceStrict 0 0 t.code then SourceZeta.lastExponent (denote 0 t) else 0) =
      SourceZeta.lastExponent (lowOmegaExponent 1 (denote 0 t)) := by
  classical
  by_cases hoff : EpsilonFiniteAbove 1 (denote 0 t)
  · have he : SourceZeta.lastExponent (lowOmegaExponent 1 (denote 0 t)) = 0 := by
      rw [lowOmegaExponent_of_offset _ _ hoff, SourceZeta.lastExponent,
        NativeContext.SourceChi.Powers.endValue_successor, Ordinal.log_one_right]
    rw [he]
    obtain ⟨ε, k, hτε, hε, hη⟩ := hoff
    cases k with
    | zero =>
      have hηε : denote 0 t = ε := by simpa only [Nat.cast_zero, add_zero] using hη
      have hf : SourceFixedPoint.SourceFixed 0 0 t.code := by
        simp only [SourceFixedPoint.SourceFixed, SourceFixedPoint.delta, SourceFixedPoint.residual,
          interpretation_code, finiteBase_zero, Ordinal.div_eq_zero_of_lt hl, mul_zero,
          Ordinal.mod_eq_of_lt hl, hηε]
        exact low_epsilon_sup_fixed 1 ε (Or.inl rfl) hτε hε (by simpa only [hηε] using hl)
      have hs : ¬ SourceFixedPoint.SourceStrict 0 0 t.code := fun hs =>
        (strict_iff_not_fixed t ht hn).mp hs hf
      simp only [if_neg hs]
    | succ k =>
      have hz : SourceZeta.lastExponent (denote 0 t) = 0 := by
        rw [hη, Nat.cast_succ, ← add_assoc, SourceZeta.lastExponent,
          NativeContext.SourceChi.Powers.endValue_successor, Ordinal.log_one_right]
      split_ifs <;> simp only [hz]
  · rw [lowOmegaExponent_of_not_offset _ _ hoff, lowOmegaBase_one, zero_add]
    by_cases hone : denote 0 t = 1
    · have hz : SourceZeta.lastExponent (denote 0 t) = 0 := by
        rw [hone, SourceZeta.lastExponent, Hereditary.LogEnd.endValue_principal zero_lt_one
          (epsilon_or_one_add_closed (Or.inl rfl)), Ordinal.log_one_right]
      split_ifs <;> simp only [hz]
    · have hnf : ¬ SourceFixedPoint.SourceFixed 0 0 t.code := by
        intro hf
        rcases fixed_low_epsilon_or_one t ht hn hl hp hf with he | ⟨hε, hεone⟩
        · exact hone he
        · exact hoff ⟨denote 0 t, 0, hεone, hε, by simp only [Nat.cast_zero, add_zero]⟩
      rw [if_pos ((strict_iff_not_fixed t ht hn).mpr hnf)]

theorem sourceValue_low_root (t : RelativeTerm Nat)
    (ht : check 0 (.theta 0 t) = true) (hn : Theta.Normal 0 (.theta 0 t))
    (hl : denote 0 t < omegaSequence 1 1) (hp : 0 < denote 0 t) :
    SourceZeta.sourceValue 0 (.theta 0 t : RelativeTerm Nat).code =
      SourceZeta.lastExponent (Ordinal.log Ordinal.omega0 (denote 0 (.theta 0 t))) := by
  have hcollapse : denote 0 (.theta 0 t) = Ordinal.omega0 ^ lowOmegaExponent 1 (denote 0 t) :=
    globalCollapse_low_eq_omegaPower 1 (Or.inl rfl) _ hl
  rw [hcollapse, Ordinal.log_opow Ordinal.one_lt_omega0]
  simpa only [SourceZeta.sourceValue, SourceZeta.argumentCode, Localization.argumentCode_theta,
    SourceFixedPoint.residual, interpretation_code, finiteBase_zero, Ordinal.mod_eq_of_lt hl] using
      low_zeta_exact t ht hn hl hp

theorem sourceValue_non_epsilon (c : Nat) (hc : Lambda.PublicBranches.inputCheck c = true)
    (hε : Ordinal.omega0 ^ interpretation 0 c ≠ interpretation 0 c) :
    SourceZeta.sourceValue 0 c = SourceZeta.lastExponent (Ordinal.log Ordinal.omega0 (interpretation 0 c)) := by
  obtain ⟨t, he, ht, hn, hp⟩ := (Lambda.PublicBranches.inputCheck_exact c).mp hc
  have hl : denote 0 t < omegaSequence 1 1 := by
    apply lt_of_not_ge
    intro hh
    have hsort : 1 < t.outerSort := by
      apply lt_of_not_ge
      intro hs
      have ha := SourceFixedPoint.checked_theta_argument 0 0 t ht
      exact hh.not_gt ((denote_lt_iff_outerSort_le 0 t ha 1 (by omega)).mpr (by simpa using hs))
    have hroot := (rootCheck_exact c).mpr ⟨t, he, ht, hn, hsort⟩
    exact hε (root_epsilon c hroot)
  have hnz : denote 0 t ≠ 0 := by
    intro hz
    have hv : denote 0 (.theta 0 t) = 1 := by
      change globalCollapse (finiteBase 0) 0 (denote 0 t) = 1
      rw [hz, globalCollapse_zero (finiteBase 0) (finiteBase_pos 0)
        (epsilon_or_one_add_closed (finiteBase_epsilon_or_one 0)) 0, omegaSequence_zero, finiteBase_zero]
    exact hp.ne' hv
  simpa only [he, interpretation_code] using sourceValue_low_root t ht hn hl (pos_iff_ne_zero.mpr hnz)

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.ZetaLowValue
