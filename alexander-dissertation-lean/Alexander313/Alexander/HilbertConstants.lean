import Alexander313.Alexander.HilbertLanguageMaps
import Alexander313.Alexander.DeltaEncoding

/-!
# Actual constant-language extensions and syntactic conservativity

Extra function symbols have arity zero, and original symbols embed literally.
When the original language has a designated nullary symbol, mapping every
new constant to that original symbol constructs a genuine retraction. Native
Hilbert proofs therefore add no original-language consequences, and consistency
is preserved. The Delta language has its actual arithmetic zero symbol, so
its constant extensions require no supplied language-effectivity or consistency
contract. No existential witness axiom is asserted by this retraction.
-/

namespace Alexander313.FirstOrderCalculus

universe u v w z

namespace ConstantExtension

inductive ConstantSymbol (C : Type w) : Nat → Type w
  | constant : C → ConstantSymbol C 0

def language (L : FirstOrder.Language.{u, v}) (C : Type w) : FirstOrder.Language where
  Functions := fun n => L.Functions n ⊕ ConstantSymbol C n
  Relations := L.Relations

variable {L : FirstOrder.Language.{u, v}} {C : Type w}

def inclusion : SymbolMap L (language L C) where
  onFunction := fun _ f => Sum.inl f
  onRelation := fun _ r => r

def retractFunction (zero : L.Functions 0) :
    {n : Nat} → (language L C).Functions n → L.Functions n
  | _, .inl f => f
  | _, .inr (.constant _) => zero

def retraction (zero : L.Functions 0) : SymbolMap (language L C) L where
  onFunction := fun _ f => retractFunction zero f
  onRelation := fun _ r => r

def constant {α : Type z} (c : C) : (language L C).Term α :=
  .func (.inr (.constant c)) Fin.elim0

def embedTerm {α : Type z} (t : L.Term α) : (language L C).Term α :=
  inclusion.termMap t

def embed {α : Type z} {n : Nat} (φ : L.BoundedFormula α n) :
    (language L C).BoundedFormula α n := inclusion.formulaMap φ

def embedTheory (T : L.Theory) : (language L C).Theory := inclusion.theoryMap T

@[simp] theorem retraction_embedTerm (zero : L.Functions 0) {α : Type z}
    (t : L.Term α) : (retraction zero).termMap (embedTerm (C := C) t) = t := by
  induction t <;>
    simp_all [embedTerm, inclusion, retraction, retractFunction, SymbolMap.termMap]

@[simp] theorem retraction_embed (zero : L.Functions 0) {α : Type z} {n : Nat}
    (φ : L.BoundedFormula α n) :
    (retraction zero).formulaMap (embed (C := C) φ) = φ := by
  induction φ with
  | falsum => rfl
  | equal t s =>
    simp only [embed, SymbolMap.formulaMap]
    exact congrArg₂ FirstOrder.Language.BoundedFormula.equal
      (retraction_embedTerm zero t) (retraction_embedTerm zero s)
  | rel r ts =>
    simp only [embed, SymbolMap.formulaMap]
    congr 1
    funext i
    exact retraction_embedTerm zero (ts i)
  | imp φ ψ ihφ ihψ =>
    simp_all [embed, SymbolMap.formulaMap]
  | all φ ih =>
    simp_all [embed, SymbolMap.formulaMap]

@[simp] theorem retraction_embedTheory (zero : L.Functions 0) (T : L.Theory) :
    (retraction zero).theoryMap (embedTheory (C := C) T) = T := by
  ext σ
  constructor
  · rintro ⟨τ, ⟨θ, hθ, rfl⟩, he⟩
    have hθσ : θ = σ := (retraction_embed zero θ).symm.trans he
    simpa only [hθσ] using hθ
  · intro hσ
    exact ⟨embed σ, ⟨σ, hσ, rfl⟩, retraction_embed zero σ⟩

@[simp] theorem embed_sentenceFormula (σ : L.Sentence) :
    embed (C := C) (sentenceFormula σ) = sentenceFormula (embed σ) :=
  (SymbolMap.sentenceFormula_map inclusion σ).symm

theorem derivation_embed {T : L.Theory} {φ : L.Formula Nat}
    (h : Derivation T φ) : Derivation (embedTheory (C := C) T) (embed φ) :=
  h.map inclusion

theorem derivation_retract (zero : L.Functions 0) {T : L.Theory}
    {φ : (language L C).Formula Nat} (h : Derivation (embedTheory T) φ) :
    Derivation T ((retraction zero).formulaMap φ) := by
  have hr := h.map (retraction zero)
  simpa only [retraction_embedTheory] using hr

/-- All original conclusions, including open formulas, are conservative. -/
theorem derivation_embed_iff (zero : L.Functions 0) (T : L.Theory)
    (φ : L.Formula Nat) :
    Derivation (embedTheory (C := C) T) (embed φ) ↔ Derivation T φ := by
  refine ⟨fun h => ?_, derivation_embed⟩
  simpa only [retraction_embed] using derivation_retract zero h

theorem consistent_embed_iff (zero : L.Functions 0) (T : L.Theory) :
    Consistent (embedTheory (C := C) T) ↔ Consistent T := by
  change (¬Derivation (embedTheory T) (embed (⊥ : L.Formula Nat))) ↔
    ¬Derivation T (⊥ : L.Formula Nat)
  exact not_congr (derivation_embed_iff zero T ⊥)

/-- Finite support can be taken in the original sentence theory before its
    literal embedding; added constants in intermediate proof lines disappear. -/
theorem original_finiteSupport (zero : L.Functions 0) {T : L.Theory}
    {φ : L.Formula Nat} (h : Derivation (embedTheory (C := C) T) (embed φ)) :
    ∃ F : Finset L.Sentence, (↑F : L.Theory) ⊆ T ∧ Derivation (↑F : L.Theory) φ :=
  ((derivation_embed_iff zero T φ).mp h).finiteSupport

end ConstantExtension

namespace DeltaConstants

variable {Owner : Type} {C : Type w}

abbrev language (Owner : Type) (C : Type w) :=
  ConstantExtension.language (Delta.language Owner) C

theorem derivation_embed_iff (T : (Delta.language Owner).Theory)
    (φ : (Delta.language Owner).Formula Nat) :
    Derivation (ConstantExtension.embedTheory (C := C) T) (ConstantExtension.embed φ) ↔
      Derivation T φ :=
  ConstantExtension.derivation_embed_iff Delta.ArithmeticSymbol.zero T φ

theorem consistent_embed_iff (T : (Delta.language Owner).Theory) :
    Consistent (ConstantExtension.embedTheory (C := C) T) ↔ Consistent T :=
  ConstantExtension.consistent_embed_iff Delta.ArithmeticSymbol.zero T

end DeltaConstants
end Alexander313.FirstOrderCalculus
