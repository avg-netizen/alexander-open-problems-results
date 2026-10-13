import Alexander313.Carlson.PrimitiveRecursiveChecksExamples

open Encodable Alexander313.Carlson Alexander313.Carlson.Finite

-- Independent all-input equations refer to the original derived instances.
example (n raw : ℕ) : PrimitiveRecursiveChecks.summarizeRule n raw =
    (@decode (RuleCertificate n) (@instEncodableRuleCertificate n) raw).map
      (fun d => (encode d.source, encode d.target, d.check)) :=
  PrimitiveRecursiveChecks.summarizeRule_eq n raw

example (n raw : ℕ) : PrimitiveRecursiveChecks.summarizeChain n raw =
    (@decode (ChainCertificate n) (@instEncodableChainCertificate n) raw).map
      (fun d => (encode d.source, encode d.target, d.check)) :=
  PrimitiveRecursiveChecks.summarizeChain_eq n raw

example (n raw : ℕ) : PrimitiveGenerationChecks.summarizeGeneration n raw =
    (@decode (GenerationCertificate n) (@instEncodableGenerationCertificate n) raw).map
      (fun d => (encode d.source, encode d.target, d.check)) :=
  PrimitiveGenerationChecks.summarizeGeneration_eq n raw

example : ∃ machine : Nat.Partrec.Code, ∀ P Q : RationalPresentation, ∀ raw : ℕ,
    machine.eval (encode ((P, Q), raw)) =
      Part.some (encode (RationalPresentation.checkRule P Q raw)) :=
  PrimitiveDerivationRecognition.rational_rule_check_program

example : ∃ machine : Nat.Partrec.Code, ∀ P Q : RationalPresentation, ∀ raw : ℕ,
    machine.eval (encode ((P, Q), raw)) =
      Part.some (encode (RationalPresentation.checkChain P Q raw)) :=
  PrimitiveDerivationRecognition.rational_chain_check_program

example : ∃ machine : Nat.Partrec.Code, ∀ P Q : RationalPresentation, ∀ raw : ℕ,
    machine.eval (encode ((P, Q), raw)) =
      Part.some (encode (RationalPresentation.checkGeneration P Q raw)) :=
  PrimitiveDerivationRecognition.rational_generation_check_program

-- Audit every public theorem in the six new verifier modules.
#print axioms Alexander313.Carlson.PrimitiveCertificateAlgebra.carrier_primrec
#print axioms Alexander313.Carlson.PrimitiveCertificateAlgebra.carrier_encode
#print axioms Alexander313.Carlson.PrimitiveCertificateAlgebra.carrier_eq_iff
#print axioms Alexander313.Carlson.PrimitiveCertificateAlgebra.arithmetic_primrec
#print axioms Alexander313.Carlson.PrimitiveCertificateAlgebra.downward_primrec
#print axioms Alexander313.Carlson.PrimitiveCertificateAlgebra.upward_primrec
#print axioms Alexander313.Carlson.PrimitiveCertificateAlgebra.restriction_primrec
#print axioms Alexander313.Carlson.PrimitiveCertificateAlgebra.lifting_primrec
#print axioms Alexander313.Carlson.PrimitiveCertificateAlgebra.refl_primrec
#print axioms Alexander313.Carlson.PrimitiveCertificateAlgebra.tail_primrec
#print axioms Alexander313.Carlson.PrimitiveCertificateAlgebra.arithmetic_encode
#print axioms Alexander313.Carlson.PrimitiveCertificateAlgebra.downward_encode
#print axioms Alexander313.Carlson.PrimitiveCertificateAlgebra.upward_encode
#print axioms Alexander313.Carlson.PrimitiveCertificateAlgebra.restriction_encode
#print axioms Alexander313.Carlson.PrimitiveCertificateAlgebra.lifting_encode
#print axioms Alexander313.Carlson.PrimitiveCertificateAlgebra.refl_encode
#print axioms Alexander313.Carlson.PrimitiveCertificateAlgebra.tail_encode
#print axioms Alexander313.Carlson.PrimitiveRecursiveChecks.scalar_primrec
#print axioms Alexander313.Carlson.PrimitiveRecursiveChecks.ruleChild_primrec
#print axioms Alexander313.Carlson.PrimitiveRecursiveChecks.chainChild_primrec
#print axioms Alexander313.Carlson.PrimitiveRecursiveChecks.ruleStep_primrec
#print axioms Alexander313.Carlson.PrimitiveRecursiveChecks.chainStep_primrec
#print axioms Alexander313.Carlson.PrimitiveRecursiveChecks.atom_primrec
#print axioms Alexander313.Carlson.PrimitiveRecursiveChecks.cons_primrec
#print axioms Alexander313.Carlson.PrimitiveRecursiveChecks.evaluate_primrec
#print axioms Alexander313.Carlson.PrimitiveRecursiveChecks.ruleResult_primrec
#print axioms Alexander313.Carlson.PrimitiveRecursiveChecks.chainResult_primrec
#print axioms Alexander313.Carlson.PrimitiveRecursiveChecks.evaluate_atom
#print axioms Alexander313.Carlson.PrimitiveRecursiveChecks.evaluate_cons
#print axioms Alexander313.Carlson.PrimitiveRecursiveChecks.ruleResult_node
#print axioms Alexander313.Carlson.PrimitiveRecursiveChecks.chainResult_node
#print axioms Alexander313.Carlson.PrimitiveRecursiveChecks.ruleResult_encode
#print axioms Alexander313.Carlson.PrimitiveRecursiveChecks.chainResult_encode
#print axioms Alexander313.Carlson.PrimitiveRecursiveChecks.summarizeRule_primrec
#print axioms Alexander313.Carlson.PrimitiveRecursiveChecks.summarizeChain_primrec
#print axioms Alexander313.Carlson.PrimitiveRecursiveChecks.summarizeRule_eq
#print axioms Alexander313.Carlson.PrimitiveRecursiveChecks.summarizeChain_eq
#print axioms Alexander313.Carlson.PrimitiveRecursiveChecks.summarizeRule_encode
#print axioms Alexander313.Carlson.PrimitiveRecursiveChecks.summarizeChain_encode
#print axioms Alexander313.Carlson.PrimitiveRecursiveChecks.accepts_primrec
#print axioms Alexander313.Carlson.PrimitiveRecursiveChecks.checkRule_primrec
#print axioms Alexander313.Carlson.PrimitiveRecursiveChecks.checkChain_primrec
#print axioms Alexander313.Carlson.PrimitiveRecursiveChecks.checkRule_encode_endpoints
#print axioms Alexander313.Carlson.PrimitiveRecursiveChecks.checkChain_encode_endpoints
#print axioms Alexander313.Carlson.PrimitiveRecursiveChecks.rule_summary_program
#print axioms Alexander313.Carlson.PrimitiveRecursiveChecks.chain_summary_program
#print axioms Alexander313.Carlson.PrimitiveRecursiveChecks.original_ruleSummary_primrec
#print axioms Alexander313.Carlson.PrimitiveRecursiveChecks.original_chainSummary_primrec
#print axioms Alexander313.Carlson.PrimitiveRecursiveChecks.original_ruleSource_primrec
#print axioms Alexander313.Carlson.PrimitiveRecursiveChecks.original_ruleTarget_primrec
#print axioms Alexander313.Carlson.PrimitiveRecursiveChecks.original_ruleCheck_primrec
#print axioms Alexander313.Carlson.PrimitiveRecursiveChecks.original_chainSource_primrec
#print axioms Alexander313.Carlson.PrimitiveRecursiveChecks.original_chainTarget_primrec
#print axioms Alexander313.Carlson.PrimitiveRecursiveChecks.original_chainCheck_primrec
#print axioms Alexander313.Carlson.PrimitiveGenerationChecks.generation_primrec
#print axioms Alexander313.Carlson.PrimitiveGenerationChecks.generation_encode
#print axioms Alexander313.Carlson.PrimitiveGenerationChecks.parse_pack
#print axioms Alexander313.Carlson.PrimitiveGenerationChecks.generationResult_primrec
#print axioms Alexander313.Carlson.PrimitiveGenerationChecks.generationResult_encode
#print axioms Alexander313.Carlson.PrimitiveGenerationChecks.summarizeGeneration_primrec
#print axioms Alexander313.Carlson.PrimitiveGenerationChecks.summarizeGeneration_eq
#print axioms Alexander313.Carlson.PrimitiveGenerationChecks.summarizeGeneration_encode
#print axioms Alexander313.Carlson.PrimitiveGenerationChecks.checkGeneration_primrec
#print axioms Alexander313.Carlson.PrimitiveGenerationChecks.checkGeneration_encode_endpoints
#print axioms Alexander313.Carlson.PrimitiveGenerationChecks.generation_summary_program
#print axioms Alexander313.Carlson.PrimitiveGenerationChecks.original_generationSummary_primrec
#print axioms Alexander313.Carlson.PrimitiveGenerationChecks.original_generationSource_primrec
#print axioms Alexander313.Carlson.PrimitiveGenerationChecks.original_generationTarget_primrec
#print axioms Alexander313.Carlson.PrimitiveGenerationChecks.original_generationCheck_primrec
#print axioms Alexander313.Carlson.PrimitiveDerivationRecognition.finite_rule_check_primrec
#print axioms Alexander313.Carlson.PrimitiveDerivationRecognition.finite_chain_check_primrec
#print axioms Alexander313.Carlson.PrimitiveDerivationRecognition.finite_generation_check_primrec
#print axioms Alexander313.Carlson.PrimitiveDerivationRecognition.rational_rule_check_primrec
#print axioms Alexander313.Carlson.PrimitiveDerivationRecognition.rational_chain_check_primrec
#print axioms Alexander313.Carlson.PrimitiveDerivationRecognition.rational_generation_check_primrec
#print axioms Alexander313.Carlson.PrimitiveDerivationRecognition.rational_rule_check_program
#print axioms Alexander313.Carlson.PrimitiveDerivationRecognition.rational_chain_check_program
#print axioms Alexander313.Carlson.PrimitiveDerivationRecognition.rational_generation_check_program
#print axioms Alexander313.Carlson.PrimitiveDerivationRecognition.rational_rule_recognition
#print axioms Alexander313.Carlson.PrimitiveDerivationRecognition.rational_chain_recognition
#print axioms Alexander313.Carlson.PrimitiveDerivationRecognition.rational_generation_recognition
#print axioms Alexander313.Carlson.PrimitiveRecursiveChecksExamples.malformed_rule_child_rejected
#print axioms Alexander313.Carlson.PrimitiveRecursiveChecksExamples.empty_bound_accepts_all_three
#print axioms Alexander313.Carlson.PrimitiveRecursiveChecksExamples.false_downward_has_exact_endpoints
#print axioms Alexander313.Carlson.PrimitiveRecursiveChecksExamples.false_upward_child_conditions_rejected
#print axioms Alexander313.Carlson.PrimitiveRecursiveChecksExamples.restriction_requires_new_point
#print axioms Alexander313.Carlson.PrimitiveRecursiveChecksExamples.identity_lifting_accepted
#print axioms Alexander313.Carlson.PrimitiveRecursiveChecksExamples.lifting_checks_recursive_child
#print axioms Alexander313.Carlson.PrimitiveRecursiveChecksExamples.off_carrier_join_rejected
#print axioms Alexander313.Carlson.PrimitiveRecursiveChecksExamples.nested_chain_and_generation_accepted
#print axioms Alexander313.Carlson.PrimitiveRecursiveChecksExamples.generation_requires_source_carrier
#print axioms Alexander313.Carlson.PrimitiveRecursiveChecksExamples.rational_rule_machine_controls
#print axioms Alexander313.Carlson.PrimitiveRecursiveChecksExamples.rational_chain_generation_machine_controls
