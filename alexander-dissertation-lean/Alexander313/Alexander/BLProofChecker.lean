import Alexander313.Alexander.Compactness
import Alexander313.Alexander.FirstOrderCalculus

/-!
# Checked finite BL instances and sound checked BL proofs

BL axioms are generated from explicit candidate data. The checker tests the
actual alpha and capture-safe variable conditions, and returns the actual
closed native first-order BL sentence. A proof carries a finite list of these
candidates and an ordinary first-order proof tree. This yields a concrete
terminating sound base-validity checker; no semantic validity test occurs in it.

The later `ProofTreeCoding` and `NativeProofChecker` modules construct numeric
proof coding and the effective native Hilbert kernel. `Effective.BLAdmission`
and `Effective.BLProofPrograms` prove the actual admission/computation laws and
construct a program recognizing exactly these native BL derivations. Semantic
completeness of the Hilbert calculus remains unproved, so this sound program
does not yet establish the source's r.e. validity theorem.
-/

namespace Alexander313

namespace Formula

def variableSubstitutable? {Owner : Type} (x y : Nat) : Formula Owner → Bool
  | .falsum => true
  | .equal _ _ => true
  | .imp φ ψ => variableSubstitutable? x y φ && variableSubstitutable? x y ψ
  | .conj φ ψ => variableSubstitutable? x y φ && variableSubstitutable? x y ψ
  | .disj φ ψ => variableSubstitutable? x y φ && variableSubstitutable? x y ψ
  | .neg φ => variableSubstitutable? x y φ
  | .all z φ => decide (z = x) ||
      ((decide (z ≠ y) || decide (x ∉ φ.freeVars)) && variableSubstitutable? x y φ)
  | .ex z φ => decide (z = x) ||
      ((decide (z ≠ y) || decide (x ∉ φ.freeVars)) && variableSubstitutable? x y φ)
  | .know _ φ => variableSubstitutable? x y φ

theorem variableSubstitutable?_eq_true {Owner : Type} (x y : Nat) (φ : Formula Owner) :
    variableSubstitutable? x y φ = true ↔ φ.VarSubstitutable x y := by
  induction φ <;> simp_all [variableSubstitutable?, VarSubstitutable]

end Formula

namespace Delta

inductive BLCandidate (Owner : Type)
  | alphabetic (a : Owner) (φ ψ : Formula Owner)
  | weakVariable (a : Owner) (φ : Formula Owner) (x y : Nat)

def candidateSentence? {Owner : Type} [DecidableEq Owner] :
    BLCandidate Owner → Option ((language Owner).Sentence)
  | .alphabetic a φ ψ => if φ.alpha [] = ψ.alpha [] then
      some (FirstOrderClosure.universalSentence (BL1 a φ ψ)) else none
  | .weakVariable a φ x y => if φ.variableSubstitutable? x y then
      some (FirstOrderClosure.universalSentence (BL2 a φ x y)) else none

theorem candidateSentence?_sound {Owner : Type} [DecidableEq Owner]
    (candidate : BLCandidate Owner) (σ : (language Owner).Sentence)
    (h : candidateSentence? candidate = some σ) : σ ∈ BLTheory Owner := by
  cases candidate with
  | alphabetic a φ ψ =>
    simp only [candidateSentence?] at h
    split at h
    next ha =>
      cases Option.some.inj h
      exact ⟨BL1 a φ ψ,
        Or.inl ⟨a, φ, ψ, ha, rfl⟩, rfl⟩
    next => cases h
  | weakVariable a φ x y =>
    simp only [candidateSentence?] at h
    split at h
    next hv =>
      cases Option.some.inj h
      exact ⟨BL2 a φ x y,
        Or.inr ⟨a, φ, x, y,
          (Formula.variableSubstitutable?_eq_true x y φ).mp hv, rfl⟩, rfl⟩
    next => cases h

theorem candidateSentence?_complete {Owner : Type} [DecidableEq Owner]
    (σ : (language Owner).Sentence) (h : σ ∈ BLTheory Owner) :
    ∃ candidate, candidateSentence? candidate = some σ := by
  obtain ⟨matrix, hm, rfl⟩ := h
  rcases hm with ⟨a, φ, ψ, ha, rfl⟩ | ⟨a, φ, x, y, hv, rfl⟩
  · refine ⟨.alphabetic a φ ψ, ?_⟩
    have ha' : φ.alpha [] = ψ.alpha [] := ha
    simp only [candidateSentence?, ha', ↓reduceIte]
  · exact ⟨.weakVariable a φ x y, by
      simp [candidateSentence?, (Formula.variableSubstitutable?_eq_true x y φ).mpr hv]⟩

def candidateSentences {Owner : Type} [DecidableEq Owner]
    (candidates : List (BLCandidate Owner)) : List ((language Owner).Sentence) :=
  candidates.filterMap candidateSentence?

theorem candidateSentences_subset {Owner : Type} [DecidableEq Owner]
    (candidates : List (BLCandidate Owner)) :
    {σ | σ ∈ candidateSentences candidates} ⊆ BLTheory Owner := by
  intro σ hσ
  obtain ⟨candidate, _, h⟩ := List.mem_filterMap.mp hσ
  exact candidateSentence?_sound candidate σ h

def candidateAdmission {Owner : Type} [DecidableEq Owner]
    (candidates : List (BLCandidate Owner)) (σ : (language Owner).Sentence) : Bool :=
  letI := NativeSyntaxCoding.formulaDecidableEqOfSymbols
    (L := language Owner) (α := Empty)
  decide (σ ∈ candidateSentences candidates)

theorem candidateAdmission_eq_true {Owner : Type} [DecidableEq Owner]
    (candidates : List (BLCandidate Owner)) (σ : (language Owner).Sentence) :
    candidateAdmission candidates σ = true ↔ σ ∈ candidateSentences candidates := by
  simp [candidateAdmission]

def checkBLProof {Owner : Type} [DecidableEq Owner]
    (candidates : List (BLCandidate Owner))
    (p : FirstOrderCalculus.ProofTree (language Owner)) :
    Option ((language Owner).Formula Nat) :=
  letI := NativeSyntaxCoding.formulaDecidableEqOfSymbols
    (L := language Owner) (α := Nat)
  FirstOrderCalculus.check (candidateAdmission candidates) p

theorem checkBLProof_valid {Owner : Type} [DecidableEq Owner]
    (candidates : List (BLCandidate Owner))
    (p : FirstOrderCalculus.ProofTree (language Owner)) (φ : Formula Owner)
    (h : checkBLProof candidates p = some (FirstOrderCalculus.sentenceFormula
      (FirstOrderClosure.universalSentence (formula φ)))) : Valid φ := by
  letI := NativeSyntaxCoding.formulaDecidableEqOfSymbols
    (L := language Owner) (α := Nat)
  have hp := FirstOrderCalculus.check_derivation (candidateAdmission candidates) p _ h
  intro D hD M s
  letI : Nonempty D := hD
  letI : (language Owner).Structure D := structureOfModal M
  have hBL : FirstOrder.Language.Theory.Model D (BLTheory Owner) :=
    (model_BLTheory_iff (structureOfModal M)).mpr (structureOfModal_satisfiesBL M)
  letI : FirstOrder.Language.Theory.Model
      D {σ | candidateAdmission candidates σ = true} := ⟨by
    intro σ hσ
    exact hBL.realize_of_mem σ (candidateSentences_subset candidates
      ((candidateAdmission_eq_true candidates σ).mp hσ))⟩
  have hsentence := (FirstOrderCalculus.sentenceFormula_realize
    (FirstOrderClosure.universalSentence (formula φ)) s).mp (hp.sound s)
  have hformula := (FirstOrderClosure.universalSentence_realize (formula φ)).mp hsentence s
  exact (formula_realize M φ s).mp hformula

end Delta

end Alexander313
