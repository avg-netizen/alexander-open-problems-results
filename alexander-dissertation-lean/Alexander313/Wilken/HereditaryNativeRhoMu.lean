import Alexander313.Wilken.HereditaryNativeRhoMuSupport

/-!
# Actual rho cancellation on the genuine mu exponent

The actual restricted iota coefficient is zero or proper limit, derived
from its original admitted ANF and genuine unit-order transport. The actual
last logarithm of the literal mu output identifies its computed lambda
with that coefficient. Actual chi invariance and dotted RIGHT subtraction
cancel precisely the correction inserted by mu. This proves the actual
rho output equals alpha*(mapped coefficient+k), without a coefficient,
logarithm, finite-decomposition or chi oracle. The final identification
with iota(Delta) requires the genuine mapped quotient-word multiplication
identity; no such identity is assumed by these statements. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceRho.Uniform.MuIdentity

open ThetaCourse
open NativePublicBridge (contextCode)

/-- Actual source chi, actual finite tail, omega power and rho compute
the corrected product at EVERY original admitted Normal LOW zero-or-limit
input. All logarithm and decomposition callers are constructed. -/
theorem rho_power_finite_correction (q c k out : Nat)
    (hc : lowCheckCode q c = true) (hn : Comparison.acceptedCode q c = true)
    (hlim : interpretation q c = 0 ∨ IsSuccLimit (interpretation q c))
    (ho : out ∈ execute q (OmegaPowers.powerCode q
      (OmegaPowerHeight.finiteTailCode q c (cond (SourceChi.chiCode q c) 1 0 + k)))) :
    interpretation q out = base q * (interpretation q c + (k : Ordinal.{0})) := by
  let n : Nat := cond (SourceChi.chiCode q c) 1 0 + k
  let e : Nat := OmegaPowerHeight.finiteTailCode q c n
  have he := OmegaPowerHeight.finiteTailCode_spec q c n hc
  obtain ⟨ell, hl, _⟩ := Part.mem_bind_iff.mp ho
  have hlog : interpretation q ell = interpretation q e :=
    MuSupport.log_powerCode_value q e ell he.1 hl
  have hell := (LogEnd.execute_spec q _ ell hl).2.1
  have ht := FiniteTailDecomposition.lambdaCode_spec q ell (Bool.and_eq_true.mp hell).1
  have hu := LimitFiniteDecomposition.coefficient_unique _ _ _ n ht.2.1 hlim
    (ht.2.2.symm.trans (hlog.trans he.2.2.1))
  have hchi := SourceChi.Invariance.chiCode_invariant q
    (FiniteTailDecomposition.lambdaCode q ell) c
    ((SourceChi.inputCheck_exact q _).mpr ((Comparison.acceptedCode_exact q _).mp ht.1))
    ((SourceChi.inputCheck_exact q c).mpr ((Comparison.acceptedCode_exact q c).mp hn)) hu.1
  have hchiNat : chiNat q ell = cond (SourceChi.chiCode q c) 1 0 := by
    simp only [chiNat, hchi]
  have hnum : ((cond (SourceChi.chiCode q c) (1 : Nat) 0 : Nat) : Ordinal.{0}) =
      cond (SourceChi.chiCode q c) (1 : Ordinal.{0}) 0 := by
    cases SourceChi.chiCode q c <;> rfl
  rw [execute_formula q _ out ell ho hl, hlog, he.2.2.1, hchiNat]
  change base q * OrdinalRightSubtraction.rightSubtract
    (interpretation q c + ((cond (SourceChi.chiCode q c) 1 0 + k : Nat) : Ordinal.{0}))
    ((cond (SourceChi.chiCode q c) 1 0 : Nat) : Ordinal.{0}) = _
  rw [Nat.cast_add, hnum, ← add_assoc, MuSupport.rightSubtract_finite_correction]

/-- The original root alone supplies a genuine mapped zero-or-limit
coefficient; no target limit predicate is assumed. -/
theorem mappedCoefficient_zero_or_limit (s a : Nat) (ha : Mu.inputCheck s a = true) :
    interpretation (Iota.alphaCode s a) (Mu.mappedCoefficient s a) = 0 ∨
      IsSuccLimit (interpretation (Iota.alphaCode s a) (Mu.mappedCoefficient s a)) := by
  have hs := OmegaQuotient.coefficientCode_spec s a ha
  obtain ⟨_, t, hcode, ht, hn, hstar⟩ := (Iota.inputCheck_exact s a _).mp hs.2.1
  have hr := (Iota.restricted_iff_sourceStar s a ha t ht hn).mpr hstar
  have hl : denote (contextCode s) t = 0 ∨ IsSuccLimit (denote (contextCode s) t) := by
    simpa only [hcode, interpretation_code] using hs.2.2.1
  have hv := MuSupport.transform_zero_or_limit s a ha t ht hn hr hl
  have hout : Iota.literalCode s a (OmegaQuotient.coefficientCode s a) =
      (Iota.transform s a t).code := by
    simp only [Iota.literalCode, hs.2.1, Bool.cond_true, hcode, Iota.stateCode_code]
  simpa only [Mu.mappedCoefficient, hout, interpretation_code] using hv

/-- The genuine actual rho at the original target alpha executes on the
literal actual mu output, with no additional domain premise. -/
theorem rho_mu_domain (s a : Nat) (ha : Mu.inputCheck s a = true) :
    (execute (Iota.alphaCode s a) (Mu.muCode s a)).Dom :=
  (execute_domain _ _).mpr (Mu.muCode_spec s a ha).1

/-- The original high-root guard alone yields the actual algebraic
cancellation in source3.14(a): rho_alpha(mu) is alpha times mapped lambda+k.
The remaining iota(Delta) equality is a separate arithmetic construction. -/
theorem rho_mu_product (s a out : Nat) (ha : Mu.inputCheck s a = true)
    (ho : out ∈ execute (Iota.alphaCode s a) (Mu.muCode s a)) :
    interpretation (Iota.alphaCode s a) out =
      base (Iota.alphaCode s a) *
        (interpretation (Iota.alphaCode s a) (Mu.mappedCoefficient s a) +
          (OmegaQuotient.coefficientOffset s a : Ordinal.{0})) := by
  have hs := Mu.mappedCoefficient_spec s a ha
  have hp := rho_power_finite_correction (Iota.alphaCode s a) (Mu.mappedCoefficient s a)
    (OmegaQuotient.coefficientOffset s a) out hs.1 hs.2
      (mappedCoefficient_zero_or_limit s a ha)
  apply hp
  simpa only [Mu.muCode_literal s a ha, Mu.exponentCode, Mu.tail, Mu.chi] using ho

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceRho.Uniform.MuIdentity
