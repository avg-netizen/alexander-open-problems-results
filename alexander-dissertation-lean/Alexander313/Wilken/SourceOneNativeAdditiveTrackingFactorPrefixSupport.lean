import Alexander313.Wilken.SourceOneNativeAdditiveTrackingFrameFactorOrder

/-!
# Genuine canonical public fidelity of an executed source-one prefix

The actual principal logarithm and prefix producer give a canonical
public prefix witness whose original return is literally the executed
factor prefix. Equal prefix VALUES therefore identify canonical public
witnesses and then literal returnCode0 outputs. No equality of original
normal spellings is asserted. The resulting actual common prefix permits
comparison of two complete source assignments. Source-only uncompiled;
strictly different-prefix input comparison remains separate.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.FactorPrefixSupport

open FactorSupport
open Alexander313.Wilken.MultiplicativeNormalForm

/-- The canonical witness comes from the actually executed logarithm;
its genuine original return is the literal factor-program prefix. -/
theorem execute_public_prefix (c : Nat) (pair : Factor.Output)
    (hp : pair ∈ Factor.execute c) :
    ∃ code, Canonical.check code = true ∧
      interpretation 0 pair.1 = unionInterpretation code ∧
        pair.1 = SourceZeta.Transport.returnCode 0 code := by
  have hv := Factor.Bounds.execute_prefix_value c pair hp
  have hc := (Factor.execute_domain c).mp (Part.dom_iff_mem.mpr ⟨pair, hp⟩)
  rw [Factor.execute, hc, Bool.cond_true] at hp
  obtain ⟨d, hd, rfl⟩ := (Part.mem_map_iff _).mp hp
  have hlog := PrincipalLogarithm.logarithm_value (Factor.publicCode c) d hd
  have hpow : Ordinal.omega0 ^ unionInterpretation d = interpretation 0 c := by
    simpa only [Factor.publicCode, unionInterpretation_pair] using hlog.2.2.2.2
  have hword : omegaFactors (unionInterpretation d) = canonicalMNF (interpretation 0 c) := by
    rw [← hpow, canonicalMNF_omegaPower]
  have hs := prefixPublicCode_spec d (Canonical.check_original hlog.2.2.2.1)
  rw [hword] at hs
  exact ⟨prefixPublicCode d, hs.1, hv.trans hs.2.symm, rfl⟩

/-- Equal computed prefix values identify their canonical public inputs
and hence the literal original returns, without original syntax injection. -/
theorem execute_prefix_eq (c d : Nat) (pair other : Factor.Output)
    (hp : pair ∈ Factor.execute c) (ht : other ∈ Factor.execute d)
    (hv : interpretation 0 pair.1 = interpretation 0 other.1) : pair.1 = other.1 := by
  obtain ⟨a, ha, hval, he⟩ := execute_public_prefix c pair hp
  obtain ⟨b, hb, hval', he'⟩ := execute_public_prefix d other ht
  have hcode : a = b := Canonical.check_value_injective a b ha hb
    (hval.symm.trans (hv.trans hval'))
  exact he.trans ((congrArg (SourceZeta.Transport.returnCode 0) hcode).trans he'.symm)

/-- Two independently executing original assignments with equal actual
semantic NF prefixes have genuinely common literal children and strict
VALUE-word order. Actual factor outputs and prefix VALUE equality derive
the shared code; no common spelling or child word is an input oracle. -/
theorem execute_equal_prefix_values_lex (leftInput rightInput : Nat)
    (leftPair rightPair : Factor.Output) (xs ys : List Nat)
    (hl : leftPair ∈ Factor.execute leftInput)
    (hr : rightPair ∈ Factor.execute rightInput)
    (hx : xs ∈ Assignment.execute leftInput)
    (hy : ys ∈ Assignment.execute rightInput)
    (hprefix : interpretation 0 leftPair.1 = interpretation 0 rightPair.1)
    (hlt : interpretation 0 leftInput < interpretation 0 rightInput) :
    List.Lex (· < ·) (xs.map (interpretation 0)) (ys.map (interpretation 0)) := by
  have he := execute_prefix_eq leftInput rightInput leftPair rightPair hl hr hprefix
  have hright : (leftPair.1, rightPair.2) ∈ Factor.execute rightInput := by
    simpa only [he] using hr
  exact FrameFactorOrder.execute_same_prefix_lex leftInput rightInput leftPair.1
    leftPair.2 rightPair.2 xs ys hl hright hx hy hlt

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.FactorPrefixSupport
