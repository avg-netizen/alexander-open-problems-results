import Alexander313.Carlson.PrimitiveGenerationChecks
import Alexander313.Carlson.PrimitiveEndpointIso

/-!
# Unconditional effective recognition of rational generating derivations

The finite recursive algebra now discharges the finite-checker premise of the
existing rational frame reduction. All checks use the original codecs and
checkers, uniformly in the grid size and every raw certificate code.
The resulting machines are total verifiers. Positive unbounded search is
partial when no derivation exists; no negative decision procedure is claimed.
-/

namespace Alexander313.Carlson.PrimitiveDerivationRecognition

open Encodable Finite PrimitiveRationalCertificate

theorem finite_rule_check_primrec : Primrec (fun c : RationalCertificate =>
    Finite.checkRule c.2.source c.2.target c.2.derivation) :=
  (PrimitiveRecursiveChecks.checkRule_primrec size_primrec sourceCode_primrec
    targetCode_primrec derivation_primrec).of_eq fun c =>
      PrimitiveRecursiveChecks.checkRule_encode_endpoints c.2.source c.2.target c.2.derivation

theorem finite_chain_check_primrec : Primrec (fun c : RationalCertificate =>
    Finite.checkChain c.2.source c.2.target c.2.derivation) :=
  (PrimitiveRecursiveChecks.checkChain_primrec size_primrec sourceCode_primrec
    targetCode_primrec derivation_primrec).of_eq fun c =>
      PrimitiveRecursiveChecks.checkChain_encode_endpoints c.2.source c.2.target c.2.derivation

theorem finite_generation_check_primrec : Primrec (fun c : RationalCertificate =>
    Finite.checkGeneration c.2.source c.2.target c.2.derivation) :=
  (PrimitiveGenerationChecks.checkGeneration_primrec size_primrec sourceCode_primrec
    targetCode_primrec derivation_primrec).of_eq fun c =>
      PrimitiveGenerationChecks.checkGeneration_encode_endpoints c.2.source c.2.target c.2.derivation

theorem rational_rule_check_primrec :
    Primrec (fun x : (RationalPresentation × RationalPresentation) × ℕ =>
      RationalPresentation.checkRule x.1.1 x.1.2 x.2) :=
  PrimitiveEndpointIso.checkRule_primrec_of_finite finite_rule_check_primrec

theorem rational_chain_check_primrec :
    Primrec (fun x : (RationalPresentation × RationalPresentation) × ℕ =>
      RationalPresentation.checkChain x.1.1 x.1.2 x.2) :=
  PrimitiveEndpointIso.checkChain_primrec_of_finite finite_chain_check_primrec

theorem rational_generation_check_primrec :
    Primrec (fun x : (RationalPresentation × RationalPresentation) × ℕ =>
      RationalPresentation.checkGeneration x.1.1 x.1.2 x.2) :=
  PrimitiveEndpointIso.checkGeneration_primrec_of_finite finite_generation_check_primrec

theorem rational_rule_check_program : ∃ machine : Nat.Partrec.Code,
    ∀ (P Q : RationalPresentation) (code : ℕ),
      machine.eval (encode ((P, Q), code)) =
        Part.some (encode (RationalPresentation.checkRule P Q code)) := by
  obtain ⟨machine, hm⟩ := PrimitiveRationalPresentation.exists_code rational_rule_check_primrec
  exact ⟨machine, fun P Q code => hm ((P, Q), code)⟩

theorem rational_chain_check_program : ∃ machine : Nat.Partrec.Code,
    ∀ (P Q : RationalPresentation) (code : ℕ),
      machine.eval (encode ((P, Q), code)) =
        Part.some (encode (RationalPresentation.checkChain P Q code)) := by
  obtain ⟨machine, hm⟩ := PrimitiveRationalPresentation.exists_code rational_chain_check_primrec
  exact ⟨machine, fun P Q code => hm ((P, Q), code)⟩

theorem rational_generation_check_program : ∃ machine : Nat.Partrec.Code,
    ∀ (P Q : RationalPresentation) (code : ℕ),
      machine.eval (encode ((P, Q), code)) =
        Part.some (encode (RationalPresentation.checkGeneration P Q code)) := by
  obtain ⟨machine, hm⟩ := PrimitiveRationalPresentation.exists_code rational_generation_check_primrec
  exact ⟨machine, fun P Q code => hm ((P, Q), code)⟩

/-- The actual total rule-verifier machine positively recognizes the original
rational generating relation by the existing soundness/completeness theorem. -/
theorem rational_rule_recognition : ∃ machine : Nat.Partrec.Code,
    (∀ (P Q : RationalPresentation) (code : ℕ),
      machine.eval (encode ((P, Q), code)) =
        Part.some (encode (RationalPresentation.checkRule P Q code))) ∧
    (∀ P Q : RationalPresentation, Str.GeneratingRule P.toStr Q.toStr ↔
      ∃ code : ℕ, machine.eval (encode ((P, Q), code)) = Part.some (encode true)) := by
  obtain ⟨machine, hm⟩ := rational_rule_check_program
  refine ⟨machine, hm, fun P Q => ?_⟩
  rw [RationalPresentation.generatingRule_iff_exists_code]
  simp only [hm, Part.some_inj, encode_inj]

theorem rational_chain_recognition : ∃ machine : Nat.Partrec.Code,
    (∀ (P Q : RationalPresentation) (code : ℕ),
      machine.eval (encode ((P, Q), code)) =
        Part.some (encode (RationalPresentation.checkChain P Q code))) ∧
    (∀ P Q : RationalPresentation, Str.ExactlyGenerates P.toStr Q.toStr ↔
      ∃ code : ℕ, machine.eval (encode ((P, Q), code)) = Part.some (encode true)) := by
  obtain ⟨machine, hm⟩ := rational_chain_check_program
  refine ⟨machine, hm, fun P Q => ?_⟩
  rw [RationalPresentation.exactlyGenerates_iff_exists_code]
  simp only [hm, Part.some_inj, encode_inj]

theorem rational_generation_recognition : ∃ machine : Nat.Partrec.Code,
    (∀ (P Q : RationalPresentation) (code : ℕ),
      machine.eval (encode ((P, Q), code)) =
        Part.some (encode (RationalPresentation.checkGeneration P Q code))) ∧
    (∀ P Q : RationalPresentation, Str.Generates P.toStr Q.toStr ↔
      ∃ code : ℕ, machine.eval (encode ((P, Q), code)) = Part.some (encode true)) := by
  obtain ⟨machine, hm⟩ := rational_generation_check_program
  refine ⟨machine, hm, fun P Q => ?_⟩
  rw [RationalPresentation.generates_iff_exists_code]
  simp only [hm, Part.some_inj, encode_inj]

end Alexander313.Carlson.PrimitiveDerivationRecognition
