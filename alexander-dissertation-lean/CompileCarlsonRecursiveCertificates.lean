import Alexander313.Carlson.PrimitiveRecursiveCertificatesExamples

open Encodable Alexander313.Carlson Alexander313.Carlson.Finite
open Alexander313.Carlson.PrimitiveRecursiveCertificates

-- Independent conclusions refer to the original derived codecs.
example (n c : ℕ) : normalizeRule n c =
    (@decode (RuleCertificate n) (@instEncodableRuleCertificate n) c).map encode :=
  normalizeRule_eq n c

example (n c : ℕ) : normalizeChain n c =
    (@decode (ChainCertificate n) (@instEncodableChainCertificate n) c).map encode :=
  normalizeChain_eq n c

example : ∃ c : Nat.Partrec.Code, ∀ n raw : ℕ,
    c.eval (Nat.pair n raw) = Part.some
      (encode (@decode (RuleCertificate n) (@instEncodableRuleCertificate n) raw)) := by
  obtain ⟨c, hc⟩ := rule_normalize_program
  exact ⟨c, fun n raw => (hc n raw).trans (congrArg Part.some (encode_normalizeRule n raw))⟩

example : ∃ c : Nat.Partrec.Code, ∀ n raw : ℕ,
    c.eval (Nat.pair n raw) = Part.some
      (encode (@decode (ChainCertificate n) (@instEncodableChainCertificate n) raw)) := by
  obtain ⟨c, hc⟩ := chain_normalize_program
  exact ⟨c, fun n raw => (hc n raw).trans (congrArg Part.some (encode_normalizeChain n raw))⟩

example (n c : ℕ) : PrimitiveGenerationCodec.normalize n c =
    (@decode (GenerationCertificate n) (@instEncodableGenerationCertificate n) c).map encode :=
  PrimitiveGenerationCodec.normalize_eq n c

example : ∃ c : Nat.Partrec.Code, ∀ n raw : ℕ,
    c.eval (Nat.pair n raw) = Part.some
      (encode (@decode (GenerationCertificate n) (@instEncodableGenerationCertificate n) raw)) :=
  PrimitiveGenerationCodec.generation_decode_program

-- Every new public theorem and coding instance is audited transitively.
#print axioms Alexander313.Carlson.PrimitiveRecursiveCertificates.atomCode_primrec
#print axioms Alexander313.Carlson.PrimitiveRecursiveCertificates.nodeCode_primrec
#print axioms Alexander313.Carlson.PrimitiveRecursiveCertificates.field_primrec
#print axioms Alexander313.Carlson.PrimitiveRecursiveCertificates.collect_primrec
#print axioms Alexander313.Carlson.PrimitiveRecursiveCertificates.fields_primrec
#print axioms Alexander313.Carlson.PrimitiveRecursiveCertificates.fields_comp_primrec
#print axioms Alexander313.Carlson.PrimitiveRecursiveCertificates.interpret_primrec
#print axioms Alexander313.Carlson.PrimitiveRecursiveCertificates.atom_primrec
#print axioms Alexander313.Carlson.PrimitiveRecursiveCertificates.cons_primrec
#print axioms Alexander313.Carlson.PrimitiveRecursiveCertificates.evaluate_primrec
#print axioms Alexander313.Carlson.PrimitiveRecursiveCertificates.normalizeRule_primrec
#print axioms Alexander313.Carlson.PrimitiveRecursiveCertificates.normalizeChain_primrec
#print axioms Alexander313.Carlson.PrimitiveRecursiveCertificates.evaluate_atom
#print axioms Alexander313.Carlson.PrimitiveRecursiveCertificates.evaluate_cons
#print axioms Alexander313.Carlson.PrimitiveRecursiveCertificates.normalizeRule_node
#print axioms Alexander313.Carlson.PrimitiveRecursiveCertificates.normalizeChain_node
#print axioms Alexander313.Carlson.PrimitiveRecursiveCertificates.normalizeRule_atom
#print axioms Alexander313.Carlson.PrimitiveRecursiveCertificates.normalizeChain_atom
#print axioms Alexander313.Carlson.PrimitiveRecursiveCertificates.encode_arithmetic
#print axioms Alexander313.Carlson.PrimitiveRecursiveCertificates.encode_refl
#print axioms Alexander313.Carlson.PrimitiveRecursiveCertificates.encode_downward
#print axioms Alexander313.Carlson.PrimitiveRecursiveCertificates.encode_upward
#print axioms Alexander313.Carlson.PrimitiveRecursiveCertificates.encode_finiteRestriction
#print axioms Alexander313.Carlson.PrimitiveRecursiveCertificates.encode_lifting
#print axioms Alexander313.Carlson.PrimitiveRecursiveCertificates.encode_tail
#print axioms Alexander313.Carlson.PrimitiveRecursiveCertificates.normalizeRule_eq
#print axioms Alexander313.Carlson.PrimitiveRecursiveCertificates.normalizeChain_eq
#print axioms Alexander313.Carlson.PrimitiveRecursiveCertificates.encode_normalizeRule
#print axioms Alexander313.Carlson.PrimitiveRecursiveCertificates.encode_normalizeChain
#print axioms Alexander313.Carlson.PrimitiveRecursiveCertificates.encoded_rule_decode_primrec
#print axioms Alexander313.Carlson.PrimitiveRecursiveCertificates.encoded_chain_decode_primrec
#print axioms Alexander313.Carlson.PrimitiveRecursiveCertificates.instPrimcodableRuleCertificate
#print axioms Alexander313.Carlson.PrimitiveRecursiveCertificates.instPrimcodableChainCertificate
#print axioms Alexander313.Carlson.PrimitiveRecursiveCertificates.rule_encoding_unchanged
#print axioms Alexander313.Carlson.PrimitiveRecursiveCertificates.chain_encoding_unchanged
#print axioms Alexander313.Carlson.PrimitiveRecursiveCertificates.normalizeRule_encode
#print axioms Alexander313.Carlson.PrimitiveRecursiveCertificates.normalizeChain_encode
#print axioms Alexander313.Carlson.PrimitiveRecursiveCertificates.rule_normalize_program
#print axioms Alexander313.Carlson.PrimitiveRecursiveCertificates.chain_normalize_program
#print axioms Alexander313.Carlson.PrimitiveGenerationCodec.pack_primrec
#print axioms Alexander313.Carlson.PrimitiveGenerationCodec.parse_primrec
#print axioms Alexander313.Carlson.PrimitiveGenerationCodec.normalize_primrec
#print axioms Alexander313.Carlson.PrimitiveGenerationCodec.encode_generation
#print axioms Alexander313.Carlson.PrimitiveGenerationCodec.normalize_eq
#print axioms Alexander313.Carlson.PrimitiveGenerationCodec.encode_normalize
#print axioms Alexander313.Carlson.PrimitiveGenerationCodec.encoded_generation_decode_primrec
#print axioms Alexander313.Carlson.PrimitiveGenerationCodec.instPrimcodableGenerationCertificate
#print axioms Alexander313.Carlson.PrimitiveGenerationCodec.generation_encoding_unchanged
#print axioms Alexander313.Carlson.PrimitiveGenerationCodec.normalize_encode
#print axioms Alexander313.Carlson.PrimitiveGenerationCodec.generation_normalize_program
#print axioms Alexander313.Carlson.PrimitiveGenerationCodec.generation_decode_program
#print axioms Alexander313.Carlson.PrimitiveRecursiveCertificatesExamples.rejects_atom_rule_child
#print axioms Alexander313.Carlson.PrimitiveRecursiveCertificatesExamples.rejects_atom_chain_children
#print axioms Alexander313.Carlson.PrimitiveRecursiveCertificatesExamples.arithmetic_not_chain
#print axioms Alexander313.Carlson.PrimitiveRecursiveCertificatesExamples.rejects_out_of_bound_anchor
#print axioms Alexander313.Carlson.PrimitiveRecursiveCertificatesExamples.empty_bound_anchor
#print axioms Alexander313.Carlson.PrimitiveRecursiveCertificatesExamples.off_carrier_join_control
#print axioms Alexander313.Carlson.PrimitiveRecursiveCertificatesExamples.invalid_downward_is_decodable
#print axioms Alexander313.Carlson.PrimitiveRecursiveCertificatesExamples.nested_mutual_roundtrip
#print axioms Alexander313.Carlson.PrimitiveRecursiveCertificatesExamples.generation_bad_chain
#print axioms Alexander313.Carlson.PrimitiveRecursiveCertificatesExamples.generation_requires_atom
#print axioms Alexander313.Carlson.PrimitiveRecursiveCertificatesExamples.nested_generation_roundtrip
