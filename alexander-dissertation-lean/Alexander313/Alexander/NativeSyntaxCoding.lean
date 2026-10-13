import Mathlib.ModelTheory.Encoding

/-!
# Concrete encodings of native first-order formulas

Mathlib already supplies a computable symbol-list encoder and decoder, with
their left-inverse theorem. Here these give actual `Encodable` structures for
bounded formulas, formulas and sentences, and a decidable syntax equality.
These constructions do not assert primitive recursiveness of the decoder.
-/

namespace Alexander313.NativeSyntaxCoding

universe u v w

variable {L : FirstOrder.Language.{u, v}} {α : Type w}

/-- Syntax equality can also be computed directly from decidable symbols,
    without first supplying a numeric encoding. -/
def formulaDecidableEqOfSymbols [DecidableEq α]
    [∀ n, DecidableEq (L.Functions n)] [∀ n, DecidableEq (L.Relations n)] :
    DecidableEq (L.Formula α) := fun φ ψ =>
  if h : φ.listEncode = ψ.listEncode then
    isTrue (eq_of_heq (Sigma.ext_iff.mp
      (FirstOrder.Language.BoundedFormula.listEncode_sigma_injective
        (a₁ := ⟨0, φ⟩) (a₂ := ⟨0, ψ⟩) h)).2)
  else isFalse (fun heq => h (congrArg
    (fun θ : L.Formula α => θ.listEncode) heq))

variable [Encodable α] [Encodable (Σ n, L.Functions n)]
  [Encodable (Σ n, L.Relations n)]

def boundedFormulaEncodable : Encodable (Σ n, L.BoundedFormula α n) :=
  Encodable.ofLeftInjection
    (fun φ : Σ n, L.BoundedFormula α n => φ.2.listEncode)
    (fun l => (FirstOrder.Language.BoundedFormula.listDecode l).head?)
    (fun φ => by
      rw [← List.flatMap_singleton (fun φ : Σ n, L.BoundedFormula α n => φ.2.listEncode),
        FirstOrder.Language.BoundedFormula.listDecode_encode_list]
      rfl)

def formulaEncodable : Encodable (L.Formula α) := by
  letI := boundedFormulaEncodable (L := L) (α := α)
  exact Encodable.ofLeftInjection
    (fun φ : L.Formula α => (⟨0, φ⟩ : Σ n, L.BoundedFormula α n))
    (fun φ => match φ with
      | ⟨0, ψ⟩ => some ψ
      | ⟨_ + 1, _⟩ => none)
    (fun _ => rfl)

def formulaDecidableEq : DecidableEq (L.Formula α) := by
  letI := formulaEncodable (L := L) (α := α)
  exact Encodable.decidableEqOfEncodable _

end Alexander313.NativeSyntaxCoding
