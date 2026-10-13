import Alexander313.Source311Programs
import Alexander313.Effective.ValidityPrograms
import Alexander313.ComparatorChallenge

/-!
# Unconditional candidate proof of thesis 3-1-1

The actual exact Valid program discharges the last construction input of the
existing source-family fixed point. Its well-founded soundness theorem already
provides every Solution311 field. This declaration has exactly the frozen
independent comparator type, with no presentation or soundness parameter.

The proof is not yet Lean-compiled or comparator-certified. Thesis 3-1-2 and
3-1-3 still have separate genericity and ordinal construction obligations.
-/

namespace Alexander313

theorem thesis311 : Comparator.challenge311 := by
  intro R hR wf
  obtain ⟨validity, hvalid, hsyntax⟩ := Delta.BLProofProgram.valid_program_exists
  exact solution311_from_validity R hR wf validity hvalid

end Alexander313
