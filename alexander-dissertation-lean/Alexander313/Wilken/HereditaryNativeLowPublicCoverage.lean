import Alexander313.Wilken.HereditaryNativeLowPublicCoverageSupport
import Alexander313.Wilken.FiniteUpsilonDomain

/-!
# Public SAME-value coverage of every original native LOW input

The original raw LOW checker derives its actual coded epsilon base and
canonical value height. A sufficiently large real finite public base is
selected from the constructed cofinal sequence; positive towers and the
actual zero-family minima bound the input by its next public base.
Consequently its value is below the actual source upsilon-omega, and the
existing genuine public interval theorem supplies a canonical SAME-value
code. This is existence and uniqueness, not an executing converter.
There is no Normal, selected endpoint, recoder or height premise. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.LowPublicCoverage

/-- Every original RAW LOW input lies below a next genuine finite public
base, selected from its actual coded base rather than fixed at source one. -/
theorem value_lt_next_finiteBase (q c : Nat) (hc : lowCheckCode q c = true) :
    ∃ r : Nat, base q < finiteBase r ∧
      interpretation q c < finiteBase (r + 1) := by
  have hq := (HeightBoundary.input_spec q c hc).2.1
  have hqpos := base_pos q hq
  obtain ⟨r, hr⟩ := (finiteBaseLimit_cofinal (base q)).mp (base_public_bound q hq)
  have hqcount : base q < omegaSequence 1 1 :=
    hr.trans (Support.finiteBase_lt_first_cardinal r)
  have hω := Iota.AlphaPlus.omega_succ 1 (base q)
    (one_le_iff_pos.mpr hqpos) hqcount 0
  have hrq : finiteBase r < omegaSequence (base q) 1 := by
    simpa only [hω] using Support.finiteBase_lt_first_cardinal r
  let n := CanonicalHeight.canonicalHeightCode q c + 1
  have hn : 0 < n := by omega
  have hinput : interpretation q c < finiteBoundary (base q) n 0 :=
    (HeightBoundary.canonicalHeightCode_le_iff_finiteBoundary q n c hc hn).mp
      (Nat.le_succ _)
  have hb := Support.finiteBoundary_mono_base (base q) (finiteBase r)
    hqpos hr.le hrq n hn
  have hnext := finiteBoundary_lt_globalBoundary (finiteBase r) (finiteBase_pos r)
    n hn 0 (Nat.zero_le n)
  refine ⟨r, hr, ?_⟩
  simpa only [finiteBase_succ] using (hinput.trans_le hb).trans hnext

theorem value_lt_finiteBaseLimit (q c : Nat) (hc : lowCheckCode q c = true) :
    interpretation q c < finiteBaseLimit := by
  obtain ⟨r, _, hr⟩ := value_lt_next_finiteBase q c hc
  exact hr.trans (finiteBase_lt_limit (r + 1))

theorem value_lt_sourceUpsilonOmega (q c : Nat) (hc : lowCheckCode q c = true) :
    interpretation q c < Wilken.sourceUpsilonOmega := by
  rw [Wilken.sourceUpsilonOmega_eq_finiteBaseLimit]
  exact value_lt_finiteBaseLimit q c hc

/-- The code is obtained from the actual public interval coverage theorem,
after the native value bound is proved. No public return is assumed. -/
theorem canonical_public_code_exists (q c : Nat) (hc : lowCheckCode q c = true) :
    ∃ p : Nat, Canonical.check p = true ∧ unionInterpretation p = interpretation q c :=
  (Canonical.lt_finiteBaseLimit_iff_code (interpretation q c)).mp
    (value_lt_finiteBaseLimit q c hc)

theorem canonical_public_code_unique (q c : Nat) (hc : lowCheckCode q c = true) :
    ∃! p : Nat, Canonical.check p = true ∧ unionInterpretation p = interpretation q c :=
  (Canonical.lt_finiteBaseLimit_iff_unique_code (interpretation q c)).mp
    (value_lt_finiteBaseLimit q c hc)

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.LowPublicCoverage
