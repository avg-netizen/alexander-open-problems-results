import Alexander313.Thesis311
import Alexander313.Arithmetic.ExistentialCode

/-!
# All 3-1-1 schemas from a single source presentation

The known existential-code step is a consequence in Alexander's weak logic,
using the separately proved coherence of the arithmetic template. The family
and its compiler remain inputs to this conditional assembly. This declaration
is intentionally not the unconditional theorem `thesis311`.
-/

namespace Alexander313

theorem SourceInputs311.generator_member {R : Nat → Nat → Prop}
    (C : SourceInputs311 R) (i : Nat) {σ : Formula Nat}
    (hσ : C.generators i σ) : C.family.effective.proves i σ := by
  have hp := C.prefixes i σ hσ 0 (fun _ => 0)
  simpa only [Formula.«prefix»,
    Formula.close_eq_self_of_closed σ (C.generators_closed i hσ)] using hp

theorem SourceInputs311.subordinate_mechanical_member {R : Nat → Nat → Prop}
    (C : SourceInputs311 R) (coherent : CoherentArithmeticCoding C.arithmetic)
    (i j : Nat) (hji : R j i) (φ : UnaryFormula Nat) :
    C.family.effective.proves i (mechanicalSentence C.arithmetic j φ) := by
  have hc : C.family.effective.proves i
      (codeSentence C.arithmetic j φ (C.index j φ)) :=
    C.generator_member i ((C.generators_exact i _).mpr
      (Or.inr ⟨j, φ, hji, rfl⟩))
  apply (C.family.theory_closed i _ (mechanicalSentence_closed C.arithmetic j φ)).mp
  exact Provable.modus_ponens
    (Provable.of_valid (code_to_mechanical_valid C.arithmetic coherent j φ (C.index j φ)))
    (Provable.of_axiom hc)

theorem SourceInputs311.knows_subordinate_mechanicalness {R : Nat → Nat → Prop}
    (C : SourceInputs311 R) (coherent : CoherentArithmeticCoding C.arithmetic) :
    knowsSubordinateMechanicalness C.arithmetic C.family R := by
  intro i j hji φ s
  refine ⟨?_, trivial⟩
  simpa only [Formula.close_eq_self_of_closed _
    (mechanicalSentence_closed C.arithmetic j φ)] using
      C.subordinate_mechanical_member coherent i j hji φ

/-- Every target field is derived from the same source inputs and arithmetic
    coherence. Constructing these inputs from an arbitrary r.e. hierarchy is
    still required for the unconditional comparator target. -/
def source_inputs311_solution (R : Nat → Nat → Prop) (wf : WellFounded R)
    (C : SourceInputs311 R) (coherent : CoherentArithmeticCoding C.arithmetic) :
    Solution311 R := by
  obtain ⟨hea, ht, hc⟩ := source_inputs311_schemas R wf C
  exact {
    arithmetic := C.arithmetic
    family := C.family
    realization := C.realization.toActual (source_inputs311_sound R wf C)
    epistemic_arithmetic := hea
    mutual_truth := ht
    particular_codes := hc
    subordinate_mechanicalness := C.knows_subordinate_mechanicalness coherent }

theorem source_inputs311_solution_nonempty (R : Nat → Nat → Prop) (wf : WellFounded R)
    (C : SourceInputs311 R) (coherent : CoherentArithmeticCoding C.arithmetic) :
    Nonempty (Solution311 R) :=
  ⟨source_inputs311_solution R wf C coherent⟩

end Alexander313
