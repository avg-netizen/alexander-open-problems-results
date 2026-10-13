import Alexander313.Wilken.HereditaryNativeSourceChiLogEndUniform
import Alexander313.Wilken.HereditaryNativeRhoMu

/-!
# Actual finite correction bounds below the genuine mu exponent

Real zero-or-limit finite decomposition identifies the actual rho chi
when a log reaches the corrected exponent boundary. The strict bound
uses the genuine last-log indicator law in its caller. Supporting lemmas
state their arithmetic/log hypotheses explicitly. Uncompiled drafts.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceRho.Uniform.PowerBoundSupport

theorem finite_one_swap (a : Ordinal.{0}) (k : Nat) :
    a + 1 + (k : Ordinal.{0}) = (a + (k : Ordinal.{0})) + 1 := by
  rw [add_assoc, ← Nat.cast_one, ← Nat.cast_add, Nat.add_comm 1 k,
    Nat.cast_add, Nat.cast_one, ← add_assoc]

/-- Actual finite-tail uniqueness and SAME-context chi invariance
identify the computed rho correction, including zero coefficients. -/
theorem chiNat_eq_of_value (q c ell : Nat) (n : Nat)
    (hc : Comparison.acceptedCode q c = true) (he : lowCheckCode q ell = true)
    (hlim : interpretation q c = 0 ∨ IsSuccLimit (interpretation q c))
    (hv : interpretation q ell = interpretation q c + (n : Ordinal.{0})) :
    chiNat q ell = cond (SourceChi.chiCode q c) 1 0 := by
  have ht := FiniteTailDecomposition.lambdaCode_spec q ell (Bool.and_eq_true.mp he).1
  have hu := LimitFiniteDecomposition.coefficient_unique _ _ _ n ht.2.1 hlim
    (ht.2.2.symm.trans hv)
  have hchi := SourceChi.Invariance.chiCode_invariant q
    (FiniteTailDecomposition.lambdaCode q ell) c ht.1 hc hu.1
  simp only [chiNat, hchi]

theorem corrected_index_le (q c k ell : Nat)
    (hc : Comparison.acceptedCode q c = true) (he : lowCheckCode q ell = true)
    (hlim : interpretation q c = 0 ∨ IsSuccLimit (interpretation q c))
    (hle : interpretation q ell ≤ interpretation q c +
      cond (SourceChi.chiCode q c) (1 : Ordinal.{0}) 0 + (k : Ordinal.{0})) :
    OrdinalRightSubtraction.rightSubtract (interpretation q ell) (chiNat q ell : Ordinal.{0}) ≤
      interpretation q c + (k : Ordinal.{0}) := by
  cases hχ : SourceChi.chiCode q c with
  | false =>
    simp only [hχ, Bool.cond_false, add_zero] at hle
    exact (OrdinalRightSubtraction.rightSubtract_le _ _).trans hle
  | true =>
    simp only [hχ, Bool.cond_true, finite_one_swap] at hle
    by_cases ht : interpretation q ell ≤ interpretation q c + (k : Ordinal.{0})
    · exact (OrdinalRightSubtraction.rightSubtract_le _ _).trans ht
    · have heq : interpretation q ell = (interpretation q c + (k : Ordinal.{0})) + 1 :=
        le_antisymm hle (Order.add_one_le_iff.mpr (lt_of_not_ge ht))
      have hv : interpretation q ell = interpretation q c + ((k + 1 : Nat) : Ordinal.{0}) := by
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using heq
      have hcor := chiNat_eq_of_value q c ell (k + 1) hc he hlim hv
      simp only [hχ, Bool.cond_true] at hcor
      simpa only [heq, hcor, Nat.cast_one, MuSupport.rightSubtract_add_one] using
        (le_refl (interpretation q c + (k : Ordinal.{0})))

/-- The endpoint case at a zero finite offset is excluded by the
ACTUAL false log indicator; positive offsets cancel one successor. -/
theorem corrected_index_succ_le (q c k ell : Nat)
    (hc : Comparison.acceptedCode q c = true) (he : lowCheckCode q ell = true)
    (hne : Comparison.acceptedCode q ell = true)
    (hlim : interpretation q c = 0 ∨ IsSuccLimit (interpretation q c))
    (hχell : SourceChi.chiCode q ell = false)
    (hlt : interpretation q ell < interpretation q c +
      cond (SourceChi.chiCode q c) (1 : Ordinal.{0}) 0 + (k : Ordinal.{0})) :
    OrdinalRightSubtraction.rightSubtract (interpretation q ell) (chiNat q ell : Ordinal.{0}) + 1 ≤
      interpretation q c + (k : Ordinal.{0}) := by
  cases hχ : SourceChi.chiCode q c with
  | false =>
    simp only [hχ, Bool.cond_false, add_zero] at hlt
    exact (add_le_add_right (OrdinalRightSubtraction.rightSubtract_le _ _) 1).trans
      (Order.add_one_le_iff.mpr hlt)
  | true =>
    simp only [hχ, Bool.cond_true, finite_one_swap] at hlt
    have hle := Order.lt_add_one_iff.mp hlt
    rcases lt_or_eq_of_le hle with ht | ht
    · exact (add_le_add_right (OrdinalRightSubtraction.rightSubtract_le _ _) 1).trans
        (Order.add_one_le_iff.mpr ht)
    · cases k with
      | zero =>
        simp only [Nat.cast_zero, add_zero] at ht
        have hsame := SourceChi.Invariance.chiCode_invariant q ell c hne hc ht
        have hf : (false : Bool) = true := hχell.symm.trans (hsame.trans hχ)
        cases hf
      | succ k =>
        have hv : interpretation q ell = interpretation q c + ((k + 1 : Nat) : Ordinal.{0}) := ht
        have hcor := chiNat_eq_of_value q c ell (k + 1) hc he hlim hv
        simp only [hχ, Bool.cond_true] at hcor
        simpa only [ht, hcor, Nat.cast_one, Nat.cast_add, ← add_assoc,
          MuSupport.rightSubtract_add_one] using
            (le_refl ((interpretation q c + (k : Ordinal.{0})) + 1))

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceRho.Uniform.PowerBoundSupport
