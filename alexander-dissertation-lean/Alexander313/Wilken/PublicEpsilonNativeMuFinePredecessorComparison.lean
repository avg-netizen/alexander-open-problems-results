import Alexander313.Wilken.PublicEpsilonNativeMuInverseBaseChange
import Alexander313.Wilken.HereditaryNativeFineLocalization
import Alexander313.Wilken.HereditaryNativeDirectZeta

/-!
# Actual fine-predecessor interval supplies the inverse-pi mu comparison

At the original positive public epsilon context, the genuine source return
preserves the original root AND argument values. The actual Definition 2.34
fine predecessor therefore gives the real argument gap and divided high-part
order. The inverse-pi spelling and mu inequality are then constructed from
those derived callers, with no supplied head-order premise in the final theorem.
The original tau-one grammar and arbitrary temporary-base fine predecessors
remain separate constructions. No Native base-one parser is used. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.MuInverseBaseChange.FinePredecessor

open NativePublicBridge (contextCode contextCode_value)
open ThetaCourse

/-- The original positive-context high-root guard derives the original
normal theta-zero source return caller. -/
theorem source_input (s root : Nat) (ha : Mu.inputCheck (contextCode s) root = true) :
    SourceZeta.inputCheck s root = true := by
  obtain ⟨t, he, ht, hn, hh⟩ := (Mu.inputCheck_exact _ _).mp ha
  exact (SourceZeta.inputCheck_exact s root).mpr ⟨t, he, ht, hn⟩

/-- The actual returned public argument retains the SAME original
argument value, rather than merely the root's value. -/
theorem public_argument (s root : Nat) (ha : Mu.inputCheck (contextCode s) root = true) :
    Hereditary.Localization.argumentValue (s + 1) (FineLocalization.publicCode s root) =
      interpretation (contextCode s) (Localization.argumentCode root) := by
  simpa only [Hereditary.Localization.argumentValue, Hereditary.SourceZeta.argumentCode,
    SourceZeta.argumentCode, FineLocalization.publicCode, SourceZeta.publicCode] using
    SourceZeta.public_argument_value s root (SourceZeta.normal_raw_input s root (source_input s root ha))

/-- The actual original Definition 2.34 fine-predecessor value, computed
at the real returned public source root. -/
noncomputable def fineBar (s root : Nat) : Ordinal.{0} :=
  Hereditary.Localization.value (s + 1)
    (Hereditary.FinePredecessor.predecessorCode (s + 1) (FineLocalization.publicCode s root))

theorem predecessor_caller (s root : Nat) (ha : Mu.inputCheck (contextCode s) root = true) :
    Hereditary.FinePredecessor.inputCheck (s + 1) (FineLocalization.publicCode s root) = true := by
  apply (Hereditary.FinePredecessor.inputCheck_exact _ _).mpr
  refine ⟨FineLocalization.publicCode_node s root (source_input s root ha), ?_⟩
  simpa only [FineLocalization.publicCode_value s root (source_input s root ha),
    contextCode_value] using Mu.root_base_lt (contextCode s) root ha

/-- Both actual fine-predecessor branches derive the original argument
comparison throughout the printed open interval. -/
theorem fine_gap_argument_lt (s lower upper : Nat)
    (hl : Mu.inputCheck (contextCode s) lower = true)
    (hu : Mu.inputCheck (contextCode s) upper = true)
    (hlo : fineBar s upper < interpretation (contextCode s) lower)
    (hhi : interpretation (contextCode s) lower < interpretation (contextCode s) upper) :
    interpretation (contextCode s) (Localization.argumentCode lower) <
      interpretation (contextCode s) (Localization.argumentCode upper) := by
  have he := Hereditary.FineLocalization.OrderSupport.predecessor_gap_argument_lt
    (s + 1) (FineLocalization.publicCode s upper) (FineLocalization.publicCode s lower)
    (predecessor_caller s upper hu)
    (FineLocalization.publicCode_node s lower (source_input s lower hl))
    (by simpa only [fineBar, FineLocalization.publicCode_value s lower (source_input s lower hl)] using hlo)
    (by simpa only [FineLocalization.publicCode_value s lower (source_input s lower hl),
      FineLocalization.publicCode_value s upper (source_input s upper hu)] using hhi)
  simpa only [public_argument s lower hl, public_argument s upper hu] using he

/-- Genuine native ANF decomposition is exactly the original divided high
part. Both admission and Normality of the original argument are derived. -/
theorem delta_value (q root : Nat) (ha : Mu.inputCheck q root = true) :
    interpretation q (OmegaQuotient.deltaCode root) =
      SourceHighPartComparison.highPart (omegaSequence (base q) 1)
        (interpretation q (Localization.argumentCode root)) := by
  obtain ⟨t, he, ht, hn, hh⟩ := (Mu.inputCheck_exact q root).mp ha
  have hz : DirectZeta.inputCheck q root = true :=
    (DirectZeta.inputCheck_exact q root).mpr ⟨t, he, ht, hn⟩
  simpa only [OmegaQuotient.deltaCode, OmegaQuotient.argumentCode, DirectZeta.argumentCode,
    SourceHighPartComparison.highPart, Nat.zero_add] using
    (Decomposition.parts_code_value q 0 (DirectZeta.argumentCode root)
      (DirectZeta.argument_input q root hz)).1

/-- The actual fine-predecessor interval supplies high-part order; no
high-part, coefficient or localization comparison is an input premise. -/
theorem fine_gap_delta_le (s lower upper : Nat)
    (hl : Mu.inputCheck (contextCode s) lower = true)
    (hu : Mu.inputCheck (contextCode s) upper = true)
    (hlo : fineBar s upper < interpretation (contextCode s) lower)
    (hhi : interpretation (contextCode s) lower < interpretation (contextCode s) upper) :
    interpretation (contextCode s) (OmegaQuotient.deltaCode lower) ≤
      interpretation (contextCode s) (OmegaQuotient.deltaCode upper) := by
  rw [delta_value _ lower hl, delta_value _ upper hu]
  exact SourceHighPartComparison.highPart_mono _
    (fine_gap_argument_lt s lower upper hl hu hlo hhi).le

/-- Printed Lemma 3.10 at the actual original positive public epsilon.
The original lower mu code is a genuinely admitted Normal inverse-pi
preimage at alpha, fully gamma-parameter-bounded, and lies below mu_alpha.
Only the original epsilon-root domains and alphaBar < gamma < alpha are
premises. No inverse-iota or supplied source-head comparison is used. -/
theorem inverse_pi_mu_spec (s lower upper : Nat)
    (hl : Mu.inputCheck (contextCode s) lower = true)
    (hu : Mu.inputCheck (contextCode s) upper = true)
    (hlo : fineBar s upper < interpretation (contextCode s) lower)
    (hhi : interpretation (contextCode s) lower < interpretation (contextCode s) upper) :
    Comparison.acceptedCode (betaCode (contextCode s) upper) (Mu.muCode (contextCode s) lower) = true ∧
      BaseTransformation.ParBounded (betaCode (contextCode s) upper) (betaCode (contextCode s) lower)
        (rawTree (Mu.muCode (contextCode s) lower)) ∧
      BaseTransformation.piCode (betaCode (contextCode s) upper) (betaCode (contextCode s) lower)
        (Mu.muCode (contextCode s) lower) = Mu.muCode (contextCode s) lower ∧
      interpretation (betaCode (contextCode s) upper) (Mu.muCode (contextCode s) lower) ≤
        Mu.sourceValue (contextCode s) upper :=
  inverse_pi_mu_spec_of_delta_le _ lower upper hl hu hhi
    (fine_gap_delta_le s lower upper hl hu hlo hhi)

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.MuInverseBaseChange.FinePredecessor
