import Alexander313.Wilken.MultiplicativePrincipalIntervalOneFactor
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingFactorPrefixOrder

/-!
# Genuine native order for a one-factor intervening quotient

The original full smaller assignment and the actual greater factor output
derive a terminating smaller factor call. Its real canonical stack has
the greater prefix followed by the computed quotient. A multiplicative
quotient has one actual factor, so removing it leaves an equal semantic
prefix. The independently executing children and dispatchers then yield
strict whole-word order without source syntax injection. Multiple quotient
factors and general different-prefix order remain separate. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.IntervalOrder

open PublicEpsilonUnboundedIota
open Alexander313.Wilken.MultiplicativeNormalForm MultiplicativePrincipalArithmetic

theorem execute_multiplicative_quotient_lex (q current greater prefix factor : Nat)
    (xs ys : List Nat)
    (hf : (prefix, factor) ∈ Factor.execute q greater)
    (hx : xs ∈ Assignment.execute q current)
    (hy : ys ∈ Assignment.execute q greater)
    (hl : interpretation q prefix < interpretation q current)
    (hr : interpretation q current < interpretation q greater)
    (hq : IsMultiplicativePrincipal (interpretation q current / interpretation q prefix)) :
    List.Lex (· < ·) (xs.map (interpretation q)) (ys.map (interpretation q)) := by
  have hc := (Assignment.execute_spec q current xs hx).1
  obtain ⟨child, last, hstep, hstack⟩ :=
    IntervalFactors.interval_factor_returns q greater prefix factor current hf hc hl hr
  obtain ⟨_, hlp, _, _, _, hp, hbase, _, _, hone, hprod, _, _⟩ :=
    Factor.execute_spec q greater (prefix, factor) hf
  have he := (Assignment.inputCheck_exact q prefix).mp hp
  have hi := (Assignment.inputCheck_exact q current).mp hc
  have hpos := (base_pos q (HeightBoundary.input_spec q prefix hlp).2.1).trans_le hbase
  have hu : interpretation q current < interpretation q prefix * interpretation q factor :=
    hr.trans_eq hprod
  have hcut := Factor.Bounds.execute_last_le_prefix_last q greater (prefix, factor) hf
  have hv := MultiplicativePrincipalInterval.Factors.interval_prefix_eq_of_multiplicative_quotient
    hpos he.2.2 hi.2.2 hone hcut hl hu hq
  have hprefix : interpretation q child = interpretation q prefix :=
    (Factor.Bounds.execute_prefix_value q current (child, last) hstep).trans hv
  exact FactorPrefixOrder.execute_equal_prefix_values_lex q current greater
    (child, last) (prefix, factor) xs ys hstep hf hx hy hprefix hr

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.IntervalOrder
