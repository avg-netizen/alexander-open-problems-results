import Alexander313.Alexander.HilbertWitnessSyntax
import Alexander313.Alexander.HilbertClosedSyntax

/-!
# Consistency of adjoining one literal fresh-constant witness

The witness implication uses an actually new nullary symbol. A contradiction
from its sentence form gives a negated witness implication by the proved
deduction theorem. Finite-proof replacement chooses a fresh variable beyond
the constructed proof bound and the original formula's finite free-variable
support. Literal substitution rollback and existing quantifier rules then
derive a contradiction already in the original theory.

The sentence identity in the core theorem is a syntax equality. The actual
closed witness sentence and its theory are then constructed from the original
formula's one-variable support. No witness consistency or completeness
principle is assumed by this argument.
-/

namespace Alexander313.FirstOrderCalculus.ConstantExtension

universe u v w

variable {L : FirstOrder.Language.{u, v}} {C : Type w}

def witnessFormula (c : C) (x : Nat) (φ : L.Formula Nat) :
    (language L C).Formula Nat :=
  (embed (existsVariable x φ)).imp (substituteVariable x (constant c) (embed φ))

theorem replace_witnessFormula (c : C) (x y : Nat) (φ : L.Formula Nat)
    (hxy : x ≠ y) :
    replaceFormula y (witnessFormula c x φ) =
      (existsVariable x φ).imp (substituteVariable x (.var y) φ) := by
  unfold witnessFormula
  rw [replaceFormula_imp, replaceFormula_embed,
    replaceFormula_substituteVariable y x hxy, replaceFormula_embed]
  rfl

theorem consistent_insert_witness_of_sentence (T : L.Theory) (hT : Consistent T)
    (c : C) (x : Nat) (φ : L.Formula Nat) (σ : (language L C).Sentence)
    (hσ : sentenceFormula σ = witnessFormula c x φ) :
    Consistent (insert σ (embedTheory T)) := by
  intro hfalse
  have hd : Derivation (embedTheory T) (witnessFormula c x φ).not := by
    have h := hfalse.deduction
    change Derivation (embedTheory T) (sentenceFormula σ).not at h
    rw [hσ] at h
    exact h
  obtain ⟨N, hN⟩ := derivation_replacement_bound hd
  let y := N + x + φ.freeVarFinset.sup id + 1
  have hNy : N ≤ y := by dsimp [y]; omega
  have hxy : x ≠ y := by dsimp [y]; omega
  have hy : y ∉ φ.freeVarFinset := by
    intro hmem
    have hb : y ≤ φ.freeVarFinset.sup id := Finset.le_sup (f := id) hmem
    dsimp [y] at hb
    omega
  have hr : Derivation T
      ((existsVariable x φ).imp (substituteVariable x (.var y) φ)).not := by
    simpa only [replaceFormula_not, replace_witnessFormula c x y φ hxy] using hN y hNy
  have hnφ : Derivation T φ.not := by
    have hs := Derivation.specialize y (.var x)
      (Derivation.generalize y hr.ofNotImp_right)
    simpa only [substituteVariable_not, WitnessSyntax.rollback x y φ hy] using hs
  exact hT (Derivation.mp hr.ofNotImp_left (Derivation.generalize x hnφ))

theorem sentence_derivation_insert_witness_of_sentence_iff (T : L.Theory)
    (c : C) (x : Nat) (φ : L.Formula Nat) (σ : (language L C).Sentence)
    (hσ : sentenceFormula σ = witnessFormula c x φ) (τ : L.Sentence) :
    Derivation (insert σ (embedTheory T)) (sentenceFormula (embed τ)) ↔
      Derivation T (sentenceFormula τ) := by
  classical
  constructor
  · intro h
    by_contra hτ
    let U := insert σ (embedTheory (C := C) (insert τ.not T))
    have hc : Consistent U := consistent_insert_witness_of_sentence
      (insert τ.not T) ((consistent_insert_not_iff T τ).mpr hτ) c x φ σ hσ
    have ht : Derivation U (sentenceFormula (embed τ)) := h.mono (by
      intro ρ hρ
      rcases Set.mem_insert_iff.mp hρ with rfl | hρ
      · exact Set.mem_insert _ _
      · obtain ⟨δ, hδ, rfl⟩ := hρ
        exact Set.mem_insert_iff.mpr (Or.inr
          (⟨δ, Set.mem_insert_iff.mpr (Or.inr hδ), rfl⟩)))
    have hn : Derivation U (sentenceFormula (embed τ)).not := by
      have hm : embed (C := C) τ.not ∈ U := Set.mem_insert_iff.mpr (Or.inr
        (⟨τ.not, Set.mem_insert τ.not T, rfl⟩))
      simpa only [embed, SymbolMap.formulaMap_not, sentenceFormula_not] using
        (Derivation.theory (embed τ.not) hm : Derivation U _)
    exact hc (Derivation.mp hn ht)
  · intro h
    simpa only [embed_sentenceFormula] using
      (derivation_embed (C := C) h).mono (Set.subset_insert σ (embedTheory T))

@[simp] theorem constant_varFinset (c : C) :
    (constant c : (language L C).Term Nat).varFinset = ∅ := by
  simp [constant]

theorem witnessFormula_closed (c : C) (x : Nat) (φ : L.Formula Nat)
    (hφ : φ.freeVarFinset ⊆ {x}) : (witnessFormula c x φ).freeVarFinset = ∅ := by
  have ha : (embed (C := C) (existsVariable x φ)).freeVarFinset = ∅ := by
    simpa only [embed, SymbolMap.formulaMap_freeVarFinset] using
      ClosedFormula.existsVariable_closed x φ hφ
  have hφe : (embed (C := C) φ).freeVarFinset ⊆ {x} := by
    simpa only [embed, SymbolMap.formulaMap_freeVarFinset] using hφ
  have hb := ClosedFormula.substituteVariable_closed x (constant (L := L) c)
    (constant_varFinset c) (embed φ) hφe
  simpa only [witnessFormula, FirstOrder.Language.BoundedFormula.freeVarFinset,
    ha, hb, Finset.union_empty]

def witnessSentence (c : C) (x : Nat) (φ : L.Formula Nat)
    (hφ : φ.freeVarFinset ⊆ {x}) : (language L C).Sentence :=
  ClosedFormula.sentence (witnessFormula c x φ) (witnessFormula_closed c x φ hφ)

@[simp] theorem sentenceFormula_witnessSentence (c : C) (x : Nat)
    (φ : L.Formula Nat) (hφ : φ.freeVarFinset ⊆ {x}) :
    sentenceFormula (witnessSentence c x φ hφ) = witnessFormula c x φ :=
  ClosedFormula.sentenceFormula_sentence _ _

def witnessTheory (T : L.Theory) (c : C) (x : Nat) (φ : L.Formula Nat)
    (hφ : φ.freeVarFinset ⊆ {x}) : (language L C).Theory :=
  insert (witnessSentence c x φ hφ) (embedTheory T)

theorem witnessTheory_consistent (T : L.Theory) (hT : Consistent T) (c : C)
    (x : Nat) (φ : L.Formula Nat) (hφ : φ.freeVarFinset ⊆ {x}) :
    Consistent (witnessTheory T c x φ hφ) :=
  consistent_insert_witness_of_sentence T hT c x φ (witnessSentence c x φ hφ)
    (sentenceFormula_witnessSentence c x φ hφ)

theorem witnessTheory_derivation_iff (T : L.Theory) (c : C) (x : Nat)
    (φ : L.Formula Nat) (hφ : φ.freeVarFinset ⊆ {x}) (τ : L.Sentence) :
    Derivation (witnessTheory T c x φ hφ) (sentenceFormula (embed τ)) ↔
      Derivation T (sentenceFormula τ) :=
  sentence_derivation_insert_witness_of_sentence_iff T c x φ
    (witnessSentence c x φ hφ) (sentenceFormula_witnessSentence c x φ hφ) τ

theorem witnessTheory_witness (T : L.Theory) (c : C) (x : Nat)
    (φ : L.Formula Nat) (hφ : φ.freeVarFinset ⊆ {x}) :
    Derivation (witnessTheory T c x φ hφ) (witnessFormula c x φ) := by
  simpa only [sentenceFormula_witnessSentence] using
    (Derivation.theory (witnessSentence c x φ hφ)
      (Set.mem_insert (witnessSentence c x φ hφ) (embedTheory T)) :
        Derivation (witnessTheory T c x φ hφ) _)

theorem witnessTheory_instance (T : L.Theory) (c : C) (x : Nat)
    (φ : L.Formula Nat) (hφ : φ.freeVarFinset ⊆ {x})
    (h : Derivation (witnessTheory T c x φ hφ) (embed (existsVariable x φ))) :
    Derivation (witnessTheory T c x φ hφ) (substituteVariable x (constant c) (embed φ)) :=
  Derivation.mp (witnessTheory_witness T c x φ hφ) h

end Alexander313.FirstOrderCalculus.ConstantExtension
