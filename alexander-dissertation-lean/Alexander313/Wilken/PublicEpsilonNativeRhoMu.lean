import Alexander313.Wilken.PublicEpsilonNativeRhoMuSupport

/-!
# Actual generic rho(mu) equals the literal iota divided head

Real logarithm, finite-tail and chi cancellation give the target-base
product. The separately constructed four-case quotient-atom factorization
identifies that product with the actual literal iota(Delta) output. The
unchanged original root guard derives both executing operators and every
coefficient/limit/log caller. No product, indicator or cancellation oracle.
Original selected endpoint scope is retained; source-one base1 is separate.
These source-only proof candidates are uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonIota.RhoMu

/-- Actual rho terminates on the actual literal generic mu output from
the unchanged original root guard alone. -/
theorem rho_mu_domain (q root : Nat) (ha : Mu.inputCheck q root = true) :
    (SourceRho.Uniform.execute (betaCode q root) (Mu.muCode q root)).Dom :=
  (SourceRho.Uniform.execute_domain _ _).mpr (Mu.muCode_spec q root ha).1

/-- Genuine source chi correction cancellation computes the mapped
coefficient product, with no supplied target coefficient limit predicate. -/
theorem rho_mu_product (q root out : Nat) (ha : Mu.inputCheck q root = true)
    (ho : out ∈ SourceRho.Uniform.execute (betaCode q root) (Mu.muCode q root)) :
    interpretation (betaCode q root) out = base (betaCode q root) *
      (interpretation (betaCode q root) (Mu.mappedCoefficient q root) +
        (OmegaQuotient.coefficientOffset q root : Ordinal.{0})) := by
  have hs := Mu.mappedCoefficient_spec q root ha
  have hp := SourceRho.Uniform.MuIdentity.rho_power_finite_correction
    (betaCode q root) (Mu.mappedCoefficient q root)
    (OmegaQuotient.coefficientOffset q root) out hs.1 hs.2
    (RhoMuSupport.mappedCoefficient_zero_or_limit q root ha)
  apply hp
  simpa only [Mu.muCode_literal q root ha, Mu.exponentCode, Mu.tail, Mu.chi] using ho

/-- The genuine source3.14(a) equation holds for the REAL executing rho
and actual literal mu and iota(Delta), under only the original root guard. -/
theorem source_lemma_3_14_a (q root out : Nat) (ha : Mu.inputCheck q root = true)
    (ho : out ∈ SourceRho.Uniform.execute (betaCode q root) (Mu.muCode q root)) :
    interpretation (betaCode q root) out =
      interpretation (betaCode q root) (literalCode q root (OmegaQuotient.deltaCode root)) := by
  exact (rho_mu_product q root out ha ho).trans
    (by simpa only [Mu.mappedCoefficient] using
      (MappedOmegaQuotient.literal_delta_coefficient_product q root ha).symm)

/-- Both actual operator executions yield the same actual iota divided
head; no numerical spelling equality is inferred from ordinal equality. -/
theorem execute_rho_mu (q root muOut out : Nat) (hm : muOut ∈ Mu.execute q root)
    (ho : out ∈ SourceRho.Uniform.execute (betaCode q root) muOut) :
    Mu.inputCheck q root = true ∧ lowCheckCode (betaCode q root) out = true ∧
      Comparison.acceptedCode (betaCode q root) out = true ∧
      interpretation (betaCode q root) out =
        interpretation (betaCode q root) (literalCode q root (OmegaQuotient.deltaCode root)) := by
  obtain ⟨ha, rfl⟩ := (Mu.execute_graph q root muOut).mp hm
  have hs := SourceRho.Uniform.source_definition_3_11 (betaCode q root) _ out ho
  exact ⟨ha, hs.2.1, hs.2.2.1, source_lemma_3_14_a q root out ha ho⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonIota.RhoMu
