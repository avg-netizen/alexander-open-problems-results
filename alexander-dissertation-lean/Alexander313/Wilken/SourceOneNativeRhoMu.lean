import Alexander313.Wilken.SourceOneNativeRhoMuSupport

/-!
# Source3.14(a) on the genuine original source-one domain

The actual original source-one mu output enters native rho only at its
true alpha epsilon. Genuine unit-filter limit, chi/right-subtraction
cancellation and the four-case mapped quotient product identify its value
with literal iota(Delta). The ORIGINAL root alone derives every caller;
no native base-one rho is claimed. Source-only and uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.RhoMu

theorem rho_mu_domain (a : Nat) (ha : Mu.inputCheck a = true) :
    (NativeContext.SourceRho.Uniform.execute (alphaCode a) (Mu.muCode a)).Dom :=
  (NativeContext.SourceRho.Uniform.execute_domain _ _).mpr (Mu.muCode_spec a ha).1

theorem rho_mu_product (a out : Nat) (ha : Mu.inputCheck a = true)
    (ho : out ∈ NativeContext.SourceRho.Uniform.execute (alphaCode a) (Mu.muCode a)) :
    NativeContext.interpretation (alphaCode a) out = NativeContext.base (alphaCode a) *
      (NativeContext.interpretation (alphaCode a) (Mu.mappedCoefficient a) +
        (OmegaQuotient.coefficientOffset a : Ordinal.{0})) := by
  have hs := Mu.mappedCoefficient_spec a ha
  have hp := NativeContext.SourceRho.Uniform.MuIdentity.rho_power_finite_correction
    (alphaCode a) (Mu.mappedCoefficient a) (OmegaQuotient.coefficientOffset a) out hs.1 hs.2
    (RhoMuSupport.mappedCoefficient_zero_or_limit a ha)
  apply hp
  simpa only [Mu.muCode_literal a ha, Mu.exponentCode, Mu.tail, Mu.chi] using ho

theorem source_lemma_3_14_a (a out : Nat) (ha : Mu.inputCheck a = true)
    (ho : out ∈ NativeContext.SourceRho.Uniform.execute (alphaCode a) (Mu.muCode a)) :
    NativeContext.interpretation (alphaCode a) out =
      NativeContext.interpretation (alphaCode a) (literalCode a (OmegaQuotient.deltaCode a)) := by
  exact (rho_mu_product a out ha ho).trans (by
    simpa only [Mu.mappedCoefficient] using (MappedOmegaQuotient.literal_delta_coefficient_product a ha).symm)

theorem execute_rho_mu (a muOut out : Nat) (hm : muOut ∈ Mu.execute a)
    (ho : out ∈ NativeContext.SourceRho.Uniform.execute (alphaCode a) muOut) :
    Mu.inputCheck a = true ∧ NativeContext.lowCheckCode (alphaCode a) out = true ∧
      NativeContext.Comparison.acceptedCode (alphaCode a) out = true ∧
      NativeContext.interpretation (alphaCode a) out =
        NativeContext.interpretation (alphaCode a) (literalCode a (OmegaQuotient.deltaCode a)) := by
  obtain ⟨ha, rfl⟩ := (Mu.execute_graph a muOut).mp hm
  have hs := NativeContext.SourceRho.Uniform.source_definition_3_11 (alphaCode a) _ out ho
  exact ⟨ha, hs.2.1, hs.2.2.1, source_lemma_3_14_a a out ha ho⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.RhoMu
