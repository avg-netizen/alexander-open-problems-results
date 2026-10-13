import Alexander313.Carlson.ComputableFairCarrier
import Alexander313.Carlson.ComputableFairSequenceExamples

/-!
# Checks of the canonical carrier presentation

The examples exercise actual first-appearance codes, duplicate and malformed
codes, rational ordering, and both finite-stage relation queries. The
nontrivial seed is the result of the previously checked downward lifting.
Every numeric check uses ordinary kernel reduction.
-/

namespace Alexander313.Carlson.Finite.ComputableFairCarrierExamples

open ComputableFairCarrier
open ComputableFairSequenceExamples (first rawBase empty empty_pattern empty_stage_carrier)

set_option maxRecDepth 8192

/-- These points already occur in the lifted initial presentation. Their
canonical birth stage is zero; a later stage cannot supply a second code. -/
theorem first_appearance_regression :
    valid first (encode 0 (1 / 5)) = true ∧
    valid first (encode 0 1) = true ∧
    valid first (encode 0 3) = true ∧
    valid first (encode 1 (1 / 5)) = false ∧
    valid first (encode 1 1) = false ∧
    valid first (encode 0 0) = false := by
  decide +kernel

/-- This finite presentation makes the rational order differ from the
numerical order of the codes. Both relations have only reflexive edges. -/
def signed : RationalPresentation :=
  ⟨{-1, 0}, {(-1, -1), (0, 0)}, {(-1, -1), (0, 0)}⟩

theorem rational_order_regression :
    encode 0 0 < encode 0 (-1) ∧
    less signed (encode 0 (-1)) (encode 0 0) = true ∧
    less signed (encode 0 0) (encode 0 (-1)) = false ∧
    less signed (encode 0 (-1)) (encode 0 (-1)) = false := by
  decide +kernel

/-- The new lifted point is first-related, but not second-related, to the
old point at `1`. The old second-level edge from `1` to `3` is retained,
and the reversed first-level edge is rejected. -/
theorem relation_regression :
    relates first .one (encode 0 (1 / 5)) (encode 0 1) = true ∧
    relates first .two (encode 0 (1 / 5)) (encode 0 1) = false ∧
    relates first .two (encode 0 1) (encode 0 3) = true ∧
    relates first .one (encode 0 3) (encode 0 1) = false ∧
    relates first .two (encode 0 (1 / 5)) (encode 0 (1 / 5)) = true := by
  decide +kernel

/-- Malformed codes, duplicate birth claims, and stored off-carrier edges
cannot enter either the order or the relation queries. The malformed code
decodes to the same fallback value as a valid point of `signed`. -/
theorem invalid_code_regression :
    value 0 = 0 ∧
    valid signed 0 = false ∧
    less signed (encode 0 (-1)) 0 = false ∧
    relates signed .one 0 (encode 0 0) = false ∧
    relates signed .two (encode 0 0) 0 = false ∧
    relates first .one (encode 1 1) (encode 0 3) = false ∧
    relates rawBase .one (encode 0 99) (encode 0 98) = false ∧
    relates rawBase .two (encode 0 98) (encode 0 99) = false := by
  decide +kernel

/-- Every code is rejected for the empty seed, including arbitrarily
large claimed birth stages. This conclusion has no finite search cutoff. -/
theorem empty_rejects_all (code : ℕ) : valid empty code = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have hmem := mem_birthStage h
  rw [empty_stage_carrier] at hmem
  exact Finset.notMem_empty _ hmem

/-- The canonical carrier faithfully retains the empty limit case. -/
theorem empty_no_label : IsEmpty (Label empty) :=
  ⟨fun a => by
    have h := a.isValid
    rw [empty_rejects_all] at h
    exact Bool.false_ne_true h⟩

/-- The positive initial-code checks define genuine labels with the
rational order supplied by the presentation. -/
def lowerLabel : Label first := ⟨encode 0 (1 / 5), first_appearance_regression.1⟩

def upperLabel : Label first := ⟨encode 0 1, first_appearance_regression.2.1⟩

theorem label_order_regression : lowerLabel < upperLabel := by
  apply (less_labels first lowerLabel upperLabel).mp
  decide +kernel

/-- The computed lifting is a pattern by its already checked generating
rule, so the code queries apply to its actual fair union. -/
theorem first_pattern : first.toStr.IsPattern :=
  ComputableFairSequenceExamples.two_transition_rules.1.target_pattern

/-- The positive first-level and negative second-level answers describe
the whole fair limit, beyond the finite initial presentation. -/
theorem limit_answers_regression :
    (ComputableFairSequence.toGeneratingSequence first first_pattern).rel .one (1 / 5) 1 ∧
    ¬ (ComputableFairSequence.toGeneratingSequence first first_pattern).rel .two (1 / 5) 1 := by
  have h₁ := (relates_eq_true first first_pattern .one
    (encode 0 (1 / 5)) (encode 0 1)).mp relation_regression.1
  refine ⟨?_, ?_⟩
  · simpa only [value_encode] using h₁.2.2
  · intro h₂
    have h := (relates_eq_true first first_pattern .two
      (encode 0 (1 / 5)) (encode 0 1)).mpr
        ⟨first_appearance_regression.1, first_appearance_regression.2.1,
          by simpa only [value_encode] using h₂⟩
    rw [relation_regression.2.1] at h
    exact Bool.false_ne_true h

end Alexander313.Carlson.Finite.ComputableFairCarrierExamples
