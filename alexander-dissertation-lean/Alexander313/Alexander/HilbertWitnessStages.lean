import Alexander313.Alexander.HilbertWitnessConsistency

/-!
# Actual finite stages of fresh witness extension

Each stage adds one genuinely new nullary symbol and the literal witness
sentence for a supplied unary matrix in the previous language. Consistency
and original-sentence conservativity are proved from the one-step construction,
not stored as fields of a stage interface.

This constructs arbitrary finite witness schedules. It supplies neither a
fair enumeration of all matrices nor a common union language or Henkin model.
-/

namespace Alexander313.FirstOrderCalculus.WitnessStages

universe u v

def stageLanguage (L : FirstOrder.Language.{u, v}) : Nat → FirstOrder.Language.{u, v}
  | 0 => L
  | n + 1 => ConstantExtension.language (stageLanguage L n) Unit

structure UnaryChoice (L : FirstOrder.Language.{u, v}) where
  name : Nat
  matrix : L.Formula Nat
  support : matrix.freeVarFinset ⊆ {name}

variable {L : FirstOrder.Language.{u, v}}

def stageTheory (T : L.Theory) (choices : ∀ n, UnaryChoice (stageLanguage L n)) :
    (n : Nat) → (stageLanguage L n).Theory
  | 0 => T
  | n + 1 => ConstantExtension.witnessTheory (stageTheory T choices n) ()
      (choices n).name (choices n).matrix (choices n).support

def liftSentence (σ : L.Sentence) : (n : Nat) → (stageLanguage L n).Sentence
  | 0 => σ
  | n + 1 => ConstantExtension.embed (C := Unit) (liftSentence σ n)

theorem stageTheory_consistent (T : L.Theory) (hT : Consistent T)
    (choices : ∀ n, UnaryChoice (stageLanguage L n)) (n : Nat) :
    Consistent (stageTheory T choices n) := by
  induction n with
  | zero => exact hT
  | succ n ih =>
    exact ConstantExtension.witnessTheory_consistent (stageTheory T choices n) ih ()
      (choices n).name (choices n).matrix (choices n).support

theorem stageTheory_derivation_iff (T : L.Theory)
    (choices : ∀ n, UnaryChoice (stageLanguage L n)) (σ : L.Sentence) (n : Nat) :
    Derivation (stageTheory T choices n) (sentenceFormula (liftSentence σ n)) ↔
      Derivation T (sentenceFormula σ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Derivation
      (ConstantExtension.witnessTheory (stageTheory T choices n) ()
        (choices n).name (choices n).matrix (choices n).support)
      (sentenceFormula (ConstantExtension.embed (C := Unit) (liftSentence σ n))) ↔ _
    exact (ConstantExtension.witnessTheory_derivation_iff (stageTheory T choices n) ()
      (choices n).name (choices n).matrix (choices n).support (liftSentence σ n)).trans ih

theorem liftSentence_mem (T : L.Theory)
    (choices : ∀ n, UnaryChoice (stageLanguage L n)) (σ : L.Sentence)
    (hσ : σ ∈ T) (n : Nat) : liftSentence σ n ∈ stageTheory T choices n := by
  induction n with
  | zero => exact hσ
  | succ n ih =>
    exact Set.mem_insert_iff.mpr (Or.inr (⟨liftSentence σ n, ih, rfl⟩))

theorem witness_mem (T : L.Theory)
    (choices : ∀ n, UnaryChoice (stageLanguage L n)) (n : Nat) :
    ConstantExtension.witnessSentence (C := Unit) () (choices n).name
      (choices n).matrix (choices n).support ∈ stageTheory T choices (n + 1) :=
  Set.mem_insert _ _

theorem witness_derivation (T : L.Theory)
    (choices : ∀ n, UnaryChoice (stageLanguage L n)) (n : Nat) :
    Derivation (stageTheory T choices (n + 1))
      (ConstantExtension.witnessFormula (C := Unit) () (choices n).name (choices n).matrix) :=
  ConstantExtension.witnessTheory_witness (stageTheory T choices n) ()
    (choices n).name (choices n).matrix (choices n).support

theorem witness_instance (T : L.Theory)
    (choices : ∀ n, UnaryChoice (stageLanguage L n)) (n : Nat)
    (h : Derivation (stageTheory T choices (n + 1))
      (ConstantExtension.embed (C := Unit)
        (existsVariable (choices n).name (choices n).matrix))) :
    Derivation (stageTheory T choices (n + 1))
      (substituteVariable (choices n).name (ConstantExtension.constant ())
        (ConstantExtension.embed (choices n).matrix)) :=
  ConstantExtension.witnessTheory_instance (stageTheory T choices n) ()
    (choices n).name (choices n).matrix (choices n).support h

theorem original_not_derivable (T : L.Theory)
    (choices : ∀ n, UnaryChoice (stageLanguage L n)) (σ : L.Sentence)
    (hσ : ¬Derivation T (sentenceFormula σ)) (n : Nat) :
    ¬Derivation (stageTheory T choices n) (sentenceFormula (liftSentence σ n)) :=
  fun h => hσ ((stageTheory_derivation_iff T choices σ n).mp h)

theorem exists_maximal_refuting_stage (T : L.Theory)
    (choices : ∀ n, UnaryChoice (stageLanguage L n)) (σ : L.Sentence)
    (hσ : ¬Derivation T (sentenceFormula σ)) (n : Nat) :
    ∃ U : (stageLanguage L n).Theory,
      stageTheory T choices n ⊆ U ∧ Maximal Consistent U ∧
      (liftSentence σ n).not ∈ U ∧ liftSentence σ n ∉ U :=
  exists_maximal_refuting (stageTheory T choices n) (liftSentence σ n)
    (original_not_derivable T choices σ hσ n)

end Alexander313.FirstOrderCalculus.WitnessStages
