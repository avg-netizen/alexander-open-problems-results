import Alexander313.Wilken.MultiplicativePrincipalIntervalFactors
import Alexander313.Wilken.SourceOneNativeAdditiveTrackingFactorPrefixSupport

/-!
# Actual source-zero factor callers in the intervening interval

The original checked source-zero input between an executed prefix and its
greater input is genuinely nonmultiplicative, by the actual descending
factor bound. Thus the original factor program terminates at that input;
no Native base-one parser or numerical singleton caller is introduced.
Actual canonical MNF uniqueness identifies its factor stack and next
prefix as the unchanged greater prefix followed by the remaining genuine
quotient factors. Different-child tracking order remains separate.
Source-only uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.IntervalFactors

open Alexander313.Wilken.MultiplicativeNormalForm MultiplicativePrincipalArithmetic

/-- The genuine interval derives the actual original factor guard. -/
theorem interval_factor_caller (greater prefix factor current : Nat)
    (hf : (prefix, factor) ∈ Factor.execute greater)
    (hc : Assignment.inputCheck current = true)
    (hl : interpretation 0 prefix < interpretation 0 current)
    (hr : interpretation 0 current < interpretation 0 greater) :
    Factor.inputCheck current = true := by
  have hi := (Assignment.inputCheck_exact current).mp hc
  obtain ⟨_, _, _, _, _, _, _, _, hproduct, _, _⟩ :=
    Factor.execute_spec greater (prefix, factor) hf
  have hlast := Factor.Bounds.execute_last_le_prefix greater (prefix, factor) hf
  have hu : interpretation 0 current < interpretation 0 prefix * interpretation 0 factor :=
    hr.trans_eq hproduct
  have hnon := MultiplicativePrincipalInterval.intervening_not_multiplicative hlast hl hu
  exact (Factor.inputCheck_exact current).mpr ⟨hi.1, hi.2.1, hi.2.2, hnon⟩

/-- Actual factor outputs identify the complete smaller quotient stack,
its genuinely removed factor and the remaining original prefix value. -/
theorem interval_factor_step (greater prefix factor current child last : Nat)
    (hf : (prefix, factor) ∈ Factor.execute greater)
    (hc : Assignment.inputCheck current = true)
    (hl : interpretation 0 prefix < interpretation 0 current)
    (hr : interpretation 0 current < interpretation 0 greater)
    (hstep : (child, last) ∈ Factor.execute current) :
    canonicalMNF (interpretation 0 current) = canonicalMNF (interpretation 0 prefix) ++
      canonicalMNF (interpretation 0 current / interpretation 0 prefix) ∧
    canonicalMNF (interpretation 0 child) = canonicalMNF (interpretation 0 prefix) ++
      factorPrefix (canonicalMNF (interpretation 0 current / interpretation 0 prefix)) ∧
    interpretation 0 child = interpretation 0 prefix *
      factorProduct (factorPrefix (canonicalMNF (interpretation 0 current / interpretation 0 prefix))) ∧
    interpretation 0 last < interpretation 0 factor := by
  obtain ⟨_, _, _, hp, hfloor, _, _, hone, hproduct, _, _⟩ :=
    Factor.execute_spec greater (prefix, factor) hf
  have he := (Assignment.inputCheck_exact prefix).mp hp
  have hi := (Assignment.inputCheck_exact current).mp hc
  have hpos := Order.one_le_iff_pos.mp hfloor
  have hu : interpretation 0 current < interpretation 0 prefix * interpretation 0 factor :=
    hr.trans_eq hproduct
  have hcut := Factor.Bounds.execute_last_le_prefix_last greater (prefix, factor) hf
  have hs := MultiplicativePrincipalInterval.Factors.interval_factor_stack hpos he.2.2 hi.2.2
    hone hcut hl hu
  have ht := MultiplicativePrincipalInterval.Factors.interval_prefix_step hpos he.2.2 hi.2.2
    hone hcut hl hu
  have hchild := Factor.Bounds.execute_prefix_value current (child, last) hstep
  obtain ⟨_, _, _, _, _, _, _, _, _, hlast, _⟩ := Factor.execute_spec current (child, last) hstep
  exact ⟨hs.2.2.2.1, by rw [hchild]; exact ht.1,
    hchild.trans ht.2, hlast.trans_lt hs.2.2.2.2.2.2⟩

/-- Original admission and the interval derive actual termination and
every stack identity. No next factor output or factorization is supplied. -/
theorem interval_factor_returns (greater prefix factor current : Nat)
    (hf : (prefix, factor) ∈ Factor.execute greater)
    (hc : Assignment.inputCheck current = true)
    (hl : interpretation 0 prefix < interpretation 0 current)
    (hr : interpretation 0 current < interpretation 0 greater) :
    ∃ child last, (child, last) ∈ Factor.execute current ∧
      canonicalMNF (interpretation 0 current) = canonicalMNF (interpretation 0 prefix) ++
        canonicalMNF (interpretation 0 current / interpretation 0 prefix) ∧
      canonicalMNF (interpretation 0 child) = canonicalMNF (interpretation 0 prefix) ++
        factorPrefix (canonicalMNF (interpretation 0 current / interpretation 0 prefix)) ∧
      interpretation 0 child = interpretation 0 prefix *
        factorProduct (factorPrefix (canonicalMNF (interpretation 0 current / interpretation 0 prefix))) ∧
      interpretation 0 last < interpretation 0 factor := by
  have hs := interval_factor_caller greater prefix factor current hf hc hl hr
  obtain ⟨out, ho⟩ := Part.dom_iff_mem.mp ((Factor.execute_domain current).mpr hs)
  rcases out with ⟨child, last⟩
  exact ⟨child, last, ho, interval_factor_step greater prefix factor current child last
    hf hc hl hr ho⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.IntervalFactors
