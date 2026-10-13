import Alexander313.Wilken.PublicEpsilonNativeFinePredecessor
import Alexander313.Wilken.PublicEpsilonNativeMuInverseBaseChange

/-!
# Printed inverse-pi mu comparison at every original coded epsilon

The fine predecessor is computed at the literal original native-q base
by its true ANF unit/STRICT first branch or genuine ordinary-localization
fallback. Both branches derive the actual interval argument gap. The real
Omega1 decomposition then supplies the head order required by inverse-pi
mu comparison. No predecessor, head order, inverse representative, chosen
public dictionary or cross-base gap is supplied. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.MuInverseBaseChange.FineUniform

open ThetaCourse

noncomputable def fineBar (q root : Nat) : Ordinal.{0} :=
  SourceLocalization.value q (SourceFinePredecessor.predecessorCode q root)

theorem root_node (q root : Nat) (ha : Mu.inputCheck q root = true) :
    SourceLocalization.Node q root := by
  obtain ⟨t, he, ht, hn, hh⟩ := (rootCheck_exact q root).mp ha
  exact ⟨t, he, ht, hn⟩

theorem predecessor_caller (q root : Nat) (ha : Mu.inputCheck q root = true) :
    SourceFinePredecessor.inputCheck q root = true :=
  (SourceFinePredecessor.inputCheck_exact q root).mpr
    ⟨root_node q root ha, root_base_lt q root ha⟩

theorem fine_gap_argument_lt (q lower upper : Nat)
    (hl : Mu.inputCheck q lower = true) (hu : Mu.inputCheck q upper = true)
    (hlo : fineBar q upper < interpretation q lower)
    (hhi : interpretation q lower < interpretation q upper) :
    interpretation q (SourceLocalization.argumentCode lower) <
      interpretation q (SourceLocalization.argumentCode upper) :=
  SourceFinePredecessor.predecessor_gap_argument_lt q upper lower
    (predecessor_caller q upper hu) (root_node q lower hl) hlo hhi

theorem delta_value (q root : Nat) (ha : Mu.inputCheck q root = true) :
    interpretation q (OmegaQuotient.deltaCode root) =
      SourceHighPartComparison.highPart (omegaSequence (base q) 1)
        (interpretation q (SourceLocalization.argumentCode root)) := by
  simpa only [OmegaQuotient.deltaCode, OmegaQuotient.argumentCode,
    SourceHighPartComparison.highPart, Nat.zero_add] using
    (Decomposition.parts_code_value q 0 (OmegaQuotient.argumentCode root)
      (OmegaQuotient.argument_accepted q root ha)).1

theorem fine_gap_delta_le (q lower upper : Nat)
    (hl : Mu.inputCheck q lower = true) (hu : Mu.inputCheck q upper = true)
    (hlo : fineBar q upper < interpretation q lower)
    (hhi : interpretation q lower < interpretation q upper) :
    interpretation q (OmegaQuotient.deltaCode lower) ≤
      interpretation q (OmegaQuotient.deltaCode upper) := by
  rw [delta_value q lower hl, delta_value q upper hu]
  exact SourceHighPartComparison.highPart_mono _
    (fine_gap_argument_lt q lower upper hl hu hlo hhi).le

/-- Full printed Lemma3.10 on the original ANY-coded-epsilon source.
The literal lower mu spelling is a genuine Normal fully lower-parameter
bounded upper-base inverse-pi preimage, and satisfies the source bound.
Only the original high roots and actual alphaBar < gamma < alpha occur. -/
theorem inverse_pi_mu_spec (q lower upper : Nat)
    (hl : Mu.inputCheck q lower = true) (hu : Mu.inputCheck q upper = true)
    (hlo : fineBar q upper < interpretation q lower)
    (hhi : interpretation q lower < interpretation q upper) :
    Comparison.acceptedCode (betaCode q upper) (Mu.muCode q lower) = true ∧
      BaseTransformation.ParBounded (betaCode q upper) (betaCode q lower)
        (rawTree (Mu.muCode q lower)) ∧
      BaseTransformation.piCode (betaCode q upper) (betaCode q lower)
        (Mu.muCode q lower) = Mu.muCode q lower ∧
      interpretation (betaCode q upper) (Mu.muCode q lower) ≤ Mu.sourceValue q upper :=
  inverse_pi_mu_spec_of_delta_le q lower upper hl hu hhi
    (fine_gap_delta_le q lower upper hl hu hlo hhi)

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.MuInverseBaseChange.FineUniform
