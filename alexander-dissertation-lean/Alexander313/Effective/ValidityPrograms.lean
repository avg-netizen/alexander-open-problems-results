import Alexander313.Effective.BLProofPrograms
import Alexander313.Alexander.HilbertCompleteness

/-!
# An exact executing program for the original unrestricted validity predicate

Countable native Hilbert completeness applies to the actual Delta language.
The existing BL model correspondence and sorted universal closure turn each
original valid formula into a derivation of the exact target sentence. The
already constructed finite proof search therefore recognizes original Valid
in both directions, including unrestricted formulas and self-occurrences.

No alternative syntactic validity predicate, supplied completeness premise or
non-exposure hypothesis is used. The executing program is the existing real
Partrec code for finite BL candidates and the native eleven-rule checker.
-/

noncomputable section

namespace Alexander313.Delta.BLProofProgram

theorem valid_derivable (φ : Formula Nat) (h : Valid φ) : Derivable φ := by
  letI : Encodable (Σ n, (language Nat).Functions n) :=
    arithmeticSigmaPrimcodable.toEncodable
  letI : Encodable (Σ n, (language Nat).Relations n) :=
    relationSigmaPrimcodable.toEncodable
  apply FirstOrderCalculus.HilbertCompleteness.sentence_complete (BLTheory Nat)
    (FirstOrderClosure.universalSentence (formula φ))
  intro D hD N hmodel
  letI : Nonempty D := hD
  letI : (language Nat).Structure D := N
  have hBL : SatisfiesBL N := (model_BLTheory_iff N).mp hmodel
  exact (FirstOrderClosure.universalSentence_realize (formula φ)).mpr
    ((valid_iff_firstOrder_BL φ).mp h D hD N hBL)

theorem derivable_iff_valid (φ : Formula Nat) : Derivable φ ↔ Valid φ :=
  ⟨fun h => h.valid, valid_derivable φ⟩

theorem exists_certificate_iff_valid (φ : Formula Nat) :
    (∃ w : Certificate, certificate φ w = true) ↔ Valid φ :=
  (exists_certificate_iff φ).trans (derivable_iff_valid φ)

/-- The exact original semantic validity program is now constructed from
    the proved Henkin countermodel argument and the actual native checker. -/
theorem valid_program_exists : ∃ p : Program,
    (∀ φ : Formula Nat, p.domain (φ.code id) ↔ Valid φ) ∧
    (∀ query, p.domain query → ∃ φ : Formula Nat,
      query = φ.code id ∧ Valid φ) := by
  obtain ⟨p, hp, hsyntax⟩ := program_exists
  refine ⟨p, ?_, ?_⟩
  · intro φ
    exact (hp φ).trans (derivable_iff_valid φ)
  · intro query hquery
    obtain ⟨φ, he, hφ⟩ := hsyntax query hquery
    exact ⟨φ, he, hφ.valid⟩

end Alexander313.Delta.BLProofProgram
