import Alexander313.Wilken.PublicEpsilonNativeUnboundedMuEpsilonCoefficient

/-!
# The original quotient of a genuine below-base epsilon mu

An epsilon mu has its mapped coefficient equal to mu, false indicator and
zero finite offset. When that actual mu lies below the root, genuine iota
order reflects the strict base cut. The original coefficient therefore
lies below the root too and is stopped atomically, with unchanged value.
Consequently the ORIGINAL coefficient equals mu and Delta=Omega-one*mu.
This is a structural classification of the existing small-epsilon case,
not an exclusion of that case or a choice of printed parameter-plus.
Every caller follows from the original ANY-q high-root guard. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.Mu.SmallEpsilon

theorem coefficient_below_root (q root : Nat) (ha : Mu.inputCheck q root = true)
    (he : Ordinal.omega0 ^ interpretation (betaCode q root) (muCode q root) =
      interpretation (betaCode q root) (muCode q root))
    (hsmall : interpretation (betaCode q root) (muCode q root) < interpretation q root) :
    interpretation q (OmegaQuotient.coefficientCode q root) < interpretation q root := by
  have hi := OmegaQuotient.coefficient_iota_input q root ha
  obtain ⟨_, t, hc, ht, hn, hs⟩ := (PublicEpsilonUnboundedIota.inputCheck_exact q root _).mp hi
  have hr := (restricted_iff_sourceStar q root ha t ht hn).mpr hs
  have hm : interpretation (betaCode q root) (mappedCoefficient q root) =
      denote (betaCode q root) (transform q root t) := by
    rw [mappedCoefficient, hc, literalCode_code q root ha t ht hn hr, interpretation_code]
  have hmt : denote (betaCode q root) (transform q root t) < base (betaCode q root) := by
    rw [← hm, (epsilon_coefficient q root ha he).1, beta_base q root ha]
    exact hsmall
  simpa only [hc, interpretation_code] using
    (transform_below_base_iff q root ha t ht hr).mp hmt

theorem coefficient_value (q root : Nat) (ha : Mu.inputCheck q root = true)
    (he : Ordinal.omega0 ^ interpretation (betaCode q root) (muCode q root) =
      interpretation (betaCode q root) (muCode q root))
    (hsmall : interpretation (betaCode q root) (muCode q root) < interpretation q root) :
    interpretation q (OmegaQuotient.coefficientCode q root) =
      interpretation (betaCode q root) (muCode q root) := by
  have hi := OmegaQuotient.coefficient_iota_input q root ha
  obtain ⟨_, t, hc, ht, hn, hs⟩ := (PublicEpsilonUnboundedIota.inputCheck_exact q root _).mp hi
  have hr := (restricted_iff_sourceStar q root ha t ht hn).mpr hs
  have hb : denote q t < interpretation q root := by
    simpa only [hc, interpretation_code] using coefficient_below_root q root ha he hsmall
  have hm : interpretation (betaCode q root) (mappedCoefficient q root) = denote q t := by
    rw [mappedCoefficient, hc, literalCode_code q root ha t ht hn hr, interpretation_code]
    exact (transform_parameter_value q root ha t ht hb).2
  calc
    interpretation q (OmegaQuotient.coefficientCode q root) = denote q t := by
      rw [hc, interpretation_code]
    _ = interpretation (betaCode q root) (mappedCoefficient q root) := hm.symm
    _ = interpretation (betaCode q root) (muCode q root) := (epsilon_coefficient q root ha he).1

/-- A small epsilon mu is a genuine original coefficient with zero tail;
the case is not ruled out by the actual operator definition. -/
theorem original_delta_value (q root : Nat) (ha : Mu.inputCheck q root = true)
    (he : Ordinal.omega0 ^ interpretation (betaCode q root) (muCode q root) =
      interpretation (betaCode q root) (muCode q root))
    (hsmall : interpretation (betaCode q root) (muCode q root) < interpretation q root) :
    chi q root = false ∧ OmegaQuotient.coefficientOffset q root = 0 ∧
      interpretation q (OmegaQuotient.deltaCode root) = omegaSequence (base q) 1 *
        interpretation (betaCode q root) (muCode q root) := by
  have hs := epsilon_coefficient q root ha he
  refine ⟨hs.2.1, hs.2.2, ?_⟩
  rw [← (OmegaQuotient.coefficientCode_spec q root ha).2.2.2,
    coefficient_value q root ha he hsmall, hs.2.2, Nat.cast_zero, add_zero]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.Mu.SmallEpsilon
