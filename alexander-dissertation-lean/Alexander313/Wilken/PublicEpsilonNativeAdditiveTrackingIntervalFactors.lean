import Alexander313.Wilken.MultiplicativePrincipalIntervalFactors
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingFrameFactorOrder

/-!
# Genuine native callers in the intervening factor interval

Two actual full executions at a common written recursive prefix derive
their SAME child word and dispatcher calls. For the critical intervening
input, the actual greater factor output derives the descending final cut.
The original raw principal checker and genuine interval then derive the
real factor-removal guard, including the numerical singleton cutoff. Its
actual next prefix is the original greater prefix followed by the genuine
remaining quotient factors. No written parser identity or different-child
tracking comparison is asserted. Source-only uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.IntervalFactors

open PublicEpsilonUnboundedIota
open Alexander313.Wilken.MultiplicativeNormalForm MultiplicativePrincipalArithmetic

theorem actual_factor_child (q current prefix factor : Nat) (out : List Nat)
    (hf : (prefix, factor) ∈ Factor.execute q current)
    (ho : out ∈ Assignment.execute q current) :
    ∃ heads, heads ∈ Assignment.execute q prefix ∧
      out ∈ Branches.execute ((q, factor), heads) := by
  have hcheck := (Factor.execute_spec q current (prefix, factor) hf).1
  have hcut := (Factor.splitCheck_exact q current).mp hcheck
  rcases Assignment.execute_clauses q current out ho with ⟨hm, he⟩ |
    ⟨hm, hs, he⟩ | ⟨hm, hs, child, last, heads, hc, hh, hb⟩
  · exact False.elim (hcut.2.2.2.1
      ((SourceMultiplicativePrincipal.inputCheck_exact q current).mp hm).2.2)
  · exact False.elim (hcut.2.2.2.2.not_ge
      ((Factor.singletonCheck_exact q current).mp hs).2.2.2.2)
  · have he : (prefix, factor) = (child, last) := Part.mem_unique hf hc
    have hp : prefix = child := congrArg Prod.fst he
    have hl : factor = last := congrArg Prod.snd he
    subst child
    subst last
    exact ⟨heads, hh, hb⟩

theorem execute_same_prefix_lex (q leftInput rightInput prefix left right : Nat)
    (xs ys : List Nat)
    (hl : (prefix, left) ∈ Factor.execute q leftInput)
    (hr : (prefix, right) ∈ Factor.execute q rightInput)
    (hx : xs ∈ Assignment.execute q leftInput)
    (hy : ys ∈ Assignment.execute q rightInput)
    (hlt : interpretation q leftInput < interpretation q rightInput) :
    List.Lex (· < ·) (xs.map (interpretation q)) (ys.map (interpretation q)) := by
  obtain ⟨heads, hh, hbx⟩ := actual_factor_child q leftInput prefix left xs hl hx
  obtain ⟨other, ht, hby⟩ := actual_factor_child q rightInput prefix right ys hr hy
  have he : heads = other := Part.mem_unique hh ht
  subst other
  exact FrameFactorOrder.execute_same_prefix_lex q leftInput rightInput prefix left right
    heads xs ys hl hr hh hlt hbx hby

theorem cutoff_multiplicative (q : Nat) (hq : baseCheck q = true) :
    IsMultiplicativePrincipal (base q ^ Ordinal.omega0) := by
  have hpos : 0 < base q * Ordinal.omega0 := mul_pos (base_pos q hq) Ordinal.omega0_pos
  have hadd : Ordinal.IsPrincipal (· + ·) (base q * Ordinal.omega0) :=
    Ordinal.isPrincipal_add_mul_of_isPrincipal_add (base q)
      (ne_of_gt Ordinal.one_lt_omega0) Ordinal.isPrincipal_add_omega0
  have he : base q ^ Ordinal.omega0 = Ordinal.omega0 ^ (base q * Ordinal.omega0) := by
    rw [Ordinal.opow_mul, SourceChi.epsilon_base q hq]
  rw [he]
  exact ⟨Ordinal.opow_pos _ Ordinal.omega0_pos, Ordinal.isPrincipal_add_omega0_opow _,
    (omegaPower_multiplicative_iff _).mpr (Or.inr ⟨hpos, hadd⟩)⟩

/-- Actual greater factor removal and the original raw smaller checker
derive the real smaller split, rather than supplying a factorization flag. -/
theorem interval_split_caller (q greater prefix factor current : Nat)
    (hf : (prefix, factor) ∈ Factor.execute q greater)
    (hc : Assignment.inputCheck q current = true)
    (hl : interpretation q prefix < interpretation q current)
    (hr : interpretation q current < interpretation q greater) :
    Factor.splitCheck q current = true := by
  obtain ⟨hcheck, _, _, _, _, hprefix, _, _, _, _, hproduct, _, _⟩ :=
    Factor.execute_spec q greater (prefix, factor) hf
  have hg := (Factor.splitCheck_exact q greater).mp hcheck
  have hp := (Assignment.inputCheck_exact q prefix).mp hprefix
  have hi := (Assignment.inputCheck_exact q current).mp hc
  have hq := (HeightBoundary.input_spec q prefix hp.1).2.1
  have hpos := (base_pos q hq).trans_le hp.2.1
  have hlast := Factor.Bounds.execute_last_le_prefix q greater (prefix, factor) hf
  have hu : interpretation q current < interpretation q prefix * interpretation q factor :=
    hr.trans_eq hproduct
  have hnon := MultiplicativePrincipalInterval.intervening_not_multiplicative hlast hl hu
  have hfloor : base q ^ Ordinal.omega0 ≤ interpretation q prefix := by
    apply le_of_not_gt
    intro hsmall
    have hm := cutoff_multiplicative q hq
    have hlt := hm.2.2 hsmall (hlast.trans_lt hsmall)
    exact hg.2.2.2.2.not_ge (hproduct.trans_lt hlt).le
  exact (Factor.splitCheck_exact q current).mpr
    ⟨hi.1, hi.2.1, hi.2.2, hnon, hfloor.trans_lt hl⟩

/-- The actual next smaller prefix and final factor are supplied by the
real factor program, and their quotient-stack identities are conclusions. -/
theorem interval_factor_step (q greater prefix factor current child last : Nat)
    (hf : (prefix, factor) ∈ Factor.execute q greater)
    (hc : Assignment.inputCheck q current = true)
    (hl : interpretation q prefix < interpretation q current)
    (hr : interpretation q current < interpretation q greater)
    (hstep : (child, last) ∈ Factor.execute q current) :
    canonicalMNF (interpretation q current) = canonicalMNF (interpretation q prefix) ++
      canonicalMNF (interpretation q current / interpretation q prefix) ∧
    canonicalMNF (interpretation q child) = canonicalMNF (interpretation q prefix) ++
      factorPrefix (canonicalMNF (interpretation q current / interpretation q prefix)) ∧
    interpretation q child = interpretation q prefix *
      factorProduct (factorPrefix (canonicalMNF (interpretation q current / interpretation q prefix))) ∧
    interpretation q last < interpretation q factor := by
  obtain ⟨_, hlp, _, _, _, hp, hbase, _, _, hone, hprod, _, _⟩ :=
    Factor.execute_spec q greater (prefix, factor) hf
  have he := (Assignment.inputCheck_exact q prefix).mp hp
  have hi := (Assignment.inputCheck_exact q current).mp hc
  have hpos := (base_pos q (HeightBoundary.input_spec q prefix hlp).2.1).trans_le hbase
  have hu : interpretation q current < interpretation q prefix * interpretation q factor :=
    hr.trans_eq hprod
  have hcut := Factor.Bounds.execute_last_le_prefix_last q greater (prefix, factor) hf
  have hs := MultiplicativePrincipalInterval.Factors.interval_factor_stack hpos he.2.2 hi.2.2
    hone hcut hl hu
  have ht := MultiplicativePrincipalInterval.Factors.interval_prefix_step hpos he.2.2 hi.2.2
    hone hcut hl hu
  have hchild := Factor.Bounds.execute_prefix_value q current (child, last) hstep
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hlast, _⟩ :=
    Factor.execute_spec q current (child, last) hstep
  exact ⟨hs.2.2.2.1, by rw [hchild]; exact ht.1,
    hchild.trans ht.2, hlast.trans_lt hs.2.2.2.2.2.2⟩

/-- The genuine interval derives termination of the actual next factor
program and the entire remaining canonical stack; no next output is input. -/
theorem interval_factor_returns (q greater prefix factor current : Nat)
    (hf : (prefix, factor) ∈ Factor.execute q greater)
    (hc : Assignment.inputCheck q current = true)
    (hl : interpretation q prefix < interpretation q current)
    (hr : interpretation q current < interpretation q greater) :
    ∃ child last, (child, last) ∈ Factor.execute q current ∧
      canonicalMNF (interpretation q current) = canonicalMNF (interpretation q prefix) ++
        canonicalMNF (interpretation q current / interpretation q prefix) ∧
      canonicalMNF (interpretation q child) = canonicalMNF (interpretation q prefix) ++
        factorPrefix (canonicalMNF (interpretation q current / interpretation q prefix)) ∧
      interpretation q child = interpretation q prefix *
        factorProduct (factorPrefix (canonicalMNF (interpretation q current / interpretation q prefix))) ∧
      interpretation q last < interpretation q factor := by
  have hs := interval_split_caller q greater prefix factor current hf hc hl hr
  obtain ⟨out, ho⟩ := Part.dom_iff_mem.mp ((Factor.execute_domain q current).mpr hs)
  rcases out with ⟨child, last⟩
  exact ⟨child, last, ho, interval_factor_step q greater prefix factor current child last
    hf hc hl hr ho⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.IntervalFactors
