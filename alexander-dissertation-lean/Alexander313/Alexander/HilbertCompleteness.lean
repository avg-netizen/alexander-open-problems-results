import Alexander313.Alexander.HilbertWitnessSchedule
import Alexander313.Alexander.HilbertModelReduction

/-!
# Constructed countermodels and completeness for countable native languages

The symbol alphabets have actual encodings. The constructed dovetail therefore
provides a full witness theory in the concrete Nat-constant language. Its
proved conservativity keeps every original nonderivable sentence nonderivable.
An actual maximal consistent extension retains every witness implication.
The quantified term-model truth theorem then constructs a countermodel, and
the fieldwise language reduct returns it to the original alphabet.

No Henkin theory, fairness, witness property, model or completeness contract is
supplied. These are derived from original nonderivability. All proof terms
remain candidates awaiting the user's external Lean compilation.
-/

noncomputable section

namespace Alexander313.FirstOrderCalculus.HilbertCompleteness

universe u v

variable {L : FirstOrder.Language.{u, v}}

abbrev Expanded (L : FirstOrder.Language.{u, v}) := WitnessLimit.language L

def originalMap (L : FirstOrder.Language.{u, v}) : SymbolMap L (Expanded L) :=
  WitnessLimit.toLimit 0

def closedConstant (L : FirstOrder.Language.{u, v}) : (Expanded L).Term Empty :=
  ConstantExtension.constant 0

def reductStructure (U : (Expanded L).Theory) :
    L.Structure (HilbertTermQuotient.Domain U) :=
  SymbolMap.reduct (originalMap L) (HilbertTermQuotient.termStructure U)

section Construction

variable [Encodable (Σ n, L.Functions n)] [Encodable (Σ n, L.Relations n)]

theorem exists_maximal_henkin_refuting (T : L.Theory) (σ : L.Sentence)
    (hσ : ¬Derivation T (sentenceFormula σ)) :
    ∃ U : (Expanded L).Theory,
      (originalMap L).theoryMap T ⊆ U ∧ Maximal Consistent U ∧
      HilbertHenkinTruth.HasWitnesses U ∧ (originalMap L).formulaMap σ ∉ U := by
  let H := WitnessLimit.theory T (WitnessSchedule.choices (L := L))
  have hH : ¬Derivation H (sentenceFormula ((originalMap L).formulaMap σ)) := by
    intro h
    exact hσ ((WitnessLimit.theory_derivation_iff T
      (WitnessSchedule.choices (L := L)) σ).mp h)
  obtain ⟨U, hHU, hmax, hneg, hnot⟩ := exists_maximal_refuting H
    ((originalMap L).formulaMap σ) hH
  refine ⟨U, ?_, hmax, ?_, hnot⟩
  · rintro τ ⟨θ, hθ, rfl⟩
    exact hHU (WitnessLimit.original_sentence_mem T
      (WitnessSchedule.choices (L := L)) θ hθ)
  · exact (WitnessSchedule.theory_hasWitnesses T).mono hHU

/-- Both the model and the failure of the original sentence are constructed
    on the actual closed-term quotient, then reduced to the original alphabet. -/
theorem countermodel (T : L.Theory) (σ : L.Sentence)
    (hσ : ¬Derivation T (sentenceFormula σ)) :
    ∃ U : (Expanded L).Theory,
      Maximal Consistent U ∧ HilbertHenkinTruth.HasWitnesses U ∧
      (letI : Nonempty (HilbertTermQuotient.Domain U) :=
        HilbertTermQuotient.domain_nonempty U (closedConstant L)
       letI : L.Structure (HilbertTermQuotient.Domain U) := reductStructure U
       FirstOrder.Language.Theory.Model (HilbertTermQuotient.Domain U) T ∧
         ¬σ.Realize (HilbertTermQuotient.Domain U)) := by
  obtain ⟨U, hTU, hmax, hw, hnot⟩ := exists_maximal_henkin_refuting T σ hσ
  refine ⟨U, hmax, hw, ?_⟩
  letI : Nonempty (HilbertTermQuotient.Domain U) :=
    HilbertTermQuotient.domain_nonempty U (closedConstant L)
  let N : (Expanded L).Structure (HilbertTermQuotient.Domain U) :=
    HilbertTermQuotient.termStructure U
  have hmodel : FirstOrder.Language.Theory.Model (HilbertTermQuotient.Domain U) ((originalMap L).theoryMap T) := by
    refine ⟨?_⟩
    intro τ hτ
    exact (HilbertHenkinTruth.sentence_truth hmax hw (closedConstant L) τ).mpr (hTU hτ)
  have hn : ¬FirstOrder.Language.Sentence.Realize (HilbertTermQuotient.Domain U)
      ((originalMap L).formulaMap σ) :=
    HilbertHenkinTruth.sentence_counterexample hmax hw (closedConstant L) _ hnot
  exact ⟨SymbolMap.model_reduct (originalMap L) N T hmodel,
    SymbolMap.counterexample_reduct (originalMap L) N σ hn⟩

/-- Completeness against all actual nonempty structures on this universe.
    The only construction input is an encoding of the two symbol alphabets. -/
theorem sentence_complete (T : L.Theory) (σ : L.Sentence)
    (h : ∀ (D : Type u) (hD : Nonempty D) (N : L.Structure D),
      letI : Nonempty D := hD
      letI : L.Structure D := N
      FirstOrder.Language.Theory.Model D T → σ.Realize D) :
    Derivation T (sentenceFormula σ) := by
  classical
  by_contra hn
  obtain ⟨U, hmax, hw, hmodel, hnot⟩ := countermodel T σ hn
  exact hnot (h (HilbertTermQuotient.Domain U)
    (HilbertTermQuotient.domain_nonempty U (closedConstant L)) (reductStructure U) hmodel)

end Construction

theorem sentence_sound (T : L.Theory) (σ : L.Sentence)
    (hσ : Derivation T (sentenceFormula σ)) (D : Type u) (hD : Nonempty D)
    (N : L.Structure D) :
    letI : Nonempty D := hD
    letI : L.Structure D := N
    FirstOrder.Language.Theory.Model D T → σ.Realize D := by
  classical
  letI : Nonempty D := hD
  letI : L.Structure D := N
  intro hmodel
  letI : FirstOrder.Language.Theory.Model D T := hmodel
  let s : Nat → D := fun _ => Classical.choice hD
  exact (sentenceFormula_realize σ s).mp (hσ.sound s)

theorem sentence_derivation_iff_models
    [Encodable (Σ n, L.Functions n)] [Encodable (Σ n, L.Relations n)]
    (T : L.Theory) (σ : L.Sentence) :
    Derivation T (sentenceFormula σ) ↔
      ∀ (D : Type u) (hD : Nonempty D) (N : L.Structure D),
        letI : Nonempty D := hD
        letI : L.Structure D := N
        FirstOrder.Language.Theory.Model D T → σ.Realize D :=
  ⟨fun h D hD N => sentence_sound T σ h D hD N, sentence_complete T σ⟩

end Alexander313.FirstOrderCalculus.HilbertCompleteness
