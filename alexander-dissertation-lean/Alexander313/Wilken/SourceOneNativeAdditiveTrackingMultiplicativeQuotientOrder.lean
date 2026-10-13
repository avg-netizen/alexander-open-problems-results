import Alexander313.Wilken.SourceOneNativeAdditiveTrackingIntervalFactors

/-!
# The genuine one-quotient-factor case of original tracking order

For an original source-zero principal strictly between the executed
greater prefix and greater input, the genuine quotient is computed by
ordinal division. If that actual quotient is multiplicative principal,
its reduced factor prefix has product one. The real smaller factor
execution therefore returns a child with the greater prefix's value.
Canonical public prefix fidelity identifies the actual original child
codes before the full same-child assignment comparison. No next output,
factorization, spelling equality or subsidiary lexical comparison is
supplied. Nonmultiplicative quotients and accumulating updates remain
separate. Source-only uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.MultiplicativeQuotientOrder

open Alexander313.Wilken.MultiplicativeNormalForm MultiplicativePrincipalArithmetic

theorem execute_interval_multiplicative_quotient_lex
    (greater prefix factor current : Nat) (xs ys : List Nat)
    (hf : (prefix, factor) ∈ Factor.execute greater)
    (hx : xs ∈ Assignment.execute current)
    (hy : ys ∈ Assignment.execute greater)
    (hl : interpretation 0 prefix < interpretation 0 current)
    (hr : interpretation 0 current < interpretation 0 greater)
    (hm : IsMultiplicativePrincipal (interpretation 0 current / interpretation 0 prefix)) :
    List.Lex (· < ·) (xs.map (interpretation 0)) (ys.map (interpretation 0)) := by
  have hc := (Assignment.execute_spec current xs hx).1
  obtain ⟨child, last, hstep, hstack, hremaining, hchild, hlast⟩ :=
    IntervalFactors.interval_factor_returns greater prefix factor current hf hc hl hr
  have hprefix : interpretation 0 child = interpretation 0 prefix := by
    simpa only [(source_prefix_last_multiplicative hm).1, mul_one] using hchild
  exact FactorPrefixSupport.execute_equal_prefix_values_lex current greater
    (child, last) (prefix, factor) xs ys hstep hf hx hy hprefix hr

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.MultiplicativeQuotientOrder
