import Alexander313.Wilken.MultiplicativePrincipalIntervalFactors

/-!
# Actual prefix removal for a one-factor interval quotient

The genuine quotient is computed ordinal division. When it belongs to
the real multiplicative principal class, its canonical reduced MNF is a
singleton. The actual intervening input's prefix therefore has exactly
the value of the original greater prefix. No factor code or source
spelling equality is assumed. Source-only uncompiled.
-/

namespace Alexander313.Wilken.MultiplicativePrincipalInterval.Factors

universe u

open MultiplicativeNormalForm MultiplicativePrincipalArithmetic

theorem interval_prefix_eq_of_multiplicative_quotient {eta alpha factor : Ordinal.{u}}
    (heta : 0 < eta) (he : Ordinal.IsPrincipal (· + ·) eta)
    (ha : Ordinal.IsPrincipal (· + ·) alpha) (hf : 1 < factor)
    (hfinal : factor ≤ lf eta) (hl : eta < alpha) (hr : alpha < eta * factor)
    (hq : IsMultiplicativePrincipal (alpha / eta)) :
    factorProduct (factorPrefix (canonicalMNF alpha)) = eta := by
  have hs := interval_factor_stack heta he ha hf hfinal hl hr
  have ht := interval_prefix_step heta he ha hf hfinal hl hr
  have heq := canonicalMNF_multiplicative hq hs.2.1
  simpa only [heq, factorPrefix, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.tail_cons, factorProduct, mul_one] using ht.2

end Alexander313.Wilken.MultiplicativePrincipalInterval.Factors
