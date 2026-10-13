import Alexander313.Wilken.HereditaryNativeSourceChiPowers
import Alexander313.Wilken.HereditaryOmegaPowers
import Alexander313.Wilken.HereditaryCanonicalArithmetic

/-!
# Actual public values of native low-argument collapse calls

The actual public epsilon-plus-finite parser and actual public comparison
recognize exactly the correction strictly above the coded native base. Public
successor/addition then produce the genuine corrected exponent, and public
omega power produces the SAME native low-collapse value. The source cardinal
bound is required only at this local collapse lemma; the elementary grammar
caller derives it. No cross-context comparison or translation oracle is used.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.ElementaryPublicReturn

/-- The source correction uses an epsilon prefix STRICTLY above the base. -/
def offsetAbove (q w : Nat) : Bool := EpsilonOffsets.check w &&
  Alexander313.HereditaryOrdinalFormation.unionLess q (EpsilonOffsets.head w)

theorem offsetAbove_primrec : Primrec₂ offsetAbove :=
  (Primrec.and.comp (EpsilonOffsets.check_primrec.comp Primrec.snd)
    (Alexander313.HereditaryOrdinalFormation.unionLess_primrec.comp Primrec.fst
      (EpsilonOffsets.head_primrec.comp Primrec.snd))).to₂

theorem offsetAbove_exact (q w : Nat) (hq : baseCheck q = true)
    (hw : unionCheck w = true) :
    offsetAbove q w = true ↔ EpsilonFiniteAbove (base q) (unionInterpretation w) := by
  constructor
  · intro h
    obtain ⟨hc, hl⟩ := Bool.and_eq_true.mp h
    have hs := EpsilonOffsets.decomposition_spec w hc
    have hb := (Alexander313.HereditaryOrdinalFormation.unionLess_exact q _).mp hl
    exact ⟨unionInterpretation (EpsilonOffsets.head w), EpsilonOffsets.offset w,
      hb.2.2, hs.2.2.1, hs.2.2.2⟩
  · rintro ⟨ε, n, hb, hε, hv⟩
    have hc := (EpsilonOffsets.check_exact w).mpr ⟨hw, ε, n, hε, hv⟩
    have hs := EpsilonOffsets.decomposition_spec w hc
    have he := (EpsilonOffsets.decomposition_unique w hc ε n hε hv).1
    refine Bool.and_eq_true.mpr ⟨hc, ?_⟩
    apply (Alexander313.HereditaryOrdinalFormation.unionLess_exact q _).mpr
    exact ⟨((baseCheck_exact q).mp hq).1, Canonical.check_original hs.2.1,
      by simpa only [base, he] using hb⟩

/-- A literal public exponent producer, including the full source correction. -/
def exponentCode (q w : Nat) : Nat := cond (offsetAbove q w)
  (CanonicalArithmetic.successorCode w) (CanonicalArithmetic.canonicalSum q w)

theorem exponentCode_primrec : Primrec₂ exponentCode :=
  (offsetAbove_primrec.cond (CanonicalArithmetic.successorCode_primrec.comp Primrec.snd)
    CanonicalArithmetic.canonicalSum_primrec).to₂

theorem exponentCode_spec (q w : Nat) (hq : baseCheck q = true)
    (hw : unionCheck w = true) :
    Canonical.check (exponentCode q w) = true ∧
      unionInterpretation (exponentCode q w) = lowOmegaExponent (base q) (unionInterpretation w) := by
  have hbase := (baseCheck_exact q).mp hq
  cases h : offsetAbove q w with
  | true =>
    have hoff := (offsetAbove_exact q w hq hw).mp h
    simp only [exponentCode, h, Bool.cond_true]
    exact ⟨CanonicalArithmetic.successorCode_checked w hw,
      (CanonicalArithmetic.successorCode_value w hw).trans
        (lowOmegaExponent_of_offset _ _ hoff).symm⟩
  | false =>
    have hoff : ¬ EpsilonFiniteAbove (base q) (unionInterpretation w) := by
      intro he
      have ht := (offsetAbove_exact q w hq hw).mpr he
      simp only [h, Bool.false_eq_true] at ht
    simp only [exponentCode, h, Bool.cond_false]
    refine ⟨CanonicalArithmetic.canonicalSum_checked q w hbase.1 hw, ?_⟩
    rw [CanonicalArithmetic.canonicalSum_value q w hbase.1 hw,
      lowOmegaExponent_of_not_offset _ _ hoff, lowOmegaBase_of_epsilon _ hbase.2]
    rfl

/-- Public omega power of the genuinely constructed native collapse exponent. -/
def collapseCode (q w : Nat) : Nat := Hereditary.OmegaPowers.powerCode (exponentCode q w)

theorem collapseCode_primrec : Primrec₂ collapseCode :=
  (Hereditary.OmegaPowers.powerCode_primrec.comp exponentCode_primrec).to₂

theorem collapseCode_spec (q w : Nat) (hq : baseCheck q = true)
    (hw : unionCheck w = true)
    (hb : unionInterpretation w < omegaSequence (base q) 1) :
    Canonical.check (collapseCode q w) = true ∧
      unionInterpretation (collapseCode q w) = globalCollapse (base q) 0 (unionInterpretation w) := by
  have hs := exponentCode_spec q w hq hw
  refine ⟨Hereditary.OmegaPowers.powerCode_checked _ (Canonical.check_original hs.1), ?_⟩
  rw [collapseCode, Hereditary.OmegaPowers.powerCode_value _ (Canonical.check_original hs.1), hs.2,
    globalCollapse_low_eq_omegaPower (base q) (Or.inr ((baseCheck_exact q).mp hq).2) _ hb]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.ElementaryPublicReturn
