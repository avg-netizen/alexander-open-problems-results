import Alexander313.Carlson.PrimitiveGenerationCodec

/-!
# Controls for the original recursive certificate grammar

These controls distinguish recursive children from scalar atoms, distinguish
rule trees from chain trees, check bound failures after a valid recursive
child, and retain an off-carrier table disagreement in a decoded chain.
-/

namespace Alexander313.Carlson.PrimitiveRecursiveCertificatesExamples

open Encodable Finite PrimitiveRecursiveCertificates

/-- Even an atom containing a valid rule's code is not a recursive rule
child. All remaining scalar codes are arbitrary. -/
theorem rejects_atom_rule_child (n d a b s f : ℕ) :
    normalizeRule n (nodeCode 2
      [atomCode d, atomCode a, atomCode b, atomCode s, atomCode f]) = none := by
  rw [normalizeRule_node]
  simp [interpret, ruleSchemas, fields, List.range_succ, collect, field, atom]

/-- A chain tail must contain two recursive trees, not their scalar codes. -/
theorem rejects_atom_chain_children (n c d : ℕ) :
    normalizeChain n (nodeCode 1 [atomCode c, atomCode d]) = none := by
  rw [normalizeChain_node]
  simp [interpret, chainSchemas, fields, List.range_succ, collect, field, atom]

/-- The arithmetic rule's tag is also the reflexive chain tag, but their
field counts differ. A valid arithmetic rule is not a chain. -/
theorem arithmetic_not_chain {n : ℕ} (P Q : PatternCode n) :
    decode (α := ChainCertificate n) (encode (RuleCertificate.arithmetic P Q)) = none := by
  have hn : normalizeChain n (encode (RuleCertificate.arithmetic P Q)) = none := by
    rw [encode_arithmetic, normalizeChain_node]
    simp [interpret, chainSchemas, fields]
  rw [normalizeChain_eq] at hn
  exact Option.map_eq_none_iff.mp hn

/-- A valid nested rule does not remove the finite-label bound check. -/
theorem rejects_out_of_bound_anchor {n : ℕ} (d : RuleCertificate n)
    (a b s f : ℕ) (ha : n ≤ a) :
    normalizeRule n (nodeCode 2
      [encode d, atomCode a, atomCode b, atomCode s, atomCode f]) = none := by
  have hd : (evaluate n (encode d)).1.2.1 = some (encode d) := normalizeRule_encode d
  rw [normalizeRule_node]
  simp [interpret, ruleSchemas, fields, List.range_succ, collect, field, atom, hd,
    PrimitivePatternCode.decodeLabel, Nat.not_lt.mpr ha]

/-- The finite bound zero still has patterns and arithmetic/reflexive
certificates, but no anchor labels. -/
theorem empty_bound_anchor (d : RuleCertificate 0) (b s f : ℕ) :
    normalizeRule 0 (nodeCode 2
      [encode d, atomCode 0, atomCode b, atomCode s, atomCode f]) = none :=
  rejects_out_of_bound_anchor d 0 b s f (Nat.zero_le 0)

private def emptyFalse : PatternCode 1 := ⟨∅, fun _ _ => false, fun _ _ => false⟩
private def emptyOffCarrier : PatternCode 1 := ⟨∅, fun _ _ => true, fun _ _ => false⟩

/-- Only an off-carrier table entry differs at this join. Decoding retains
it, and the existing chain checker rejects the unequal full structures. -/
theorem off_carrier_join_control :
    let c : ChainCertificate 1 :=
      .tail (.refl emptyFalse) (.arithmetic emptyOffCarrier emptyOffCarrier)
    normalizeChain 1 (encode c) = some (encode c) ∧ c.check = false := by
  constructor
  · exact normalizeChain_encode _
  · decide +kernel

/-- A correctly shaped downward rule with a failed reflection side
condition is decoded, not treated as a malformed tree. -/
theorem invalid_downward_is_decodable :
    let d : RuleCertificate 1 := .downward emptyFalse .one 0 0 ∅ ∅ id
    normalizeRule 1 (encode d) = some (encode d) ∧ d.check = false := by
  constructor
  · exact normalizeRule_encode _
  · decide +kernel

/-- Interleaving both mutual certificate types and the lifting rule does
not flatten a recursive child into an atom. -/
theorem nested_mutual_roundtrip {n : ℕ} (P Q : PatternCode n) (a b : Fin n)
    (N : Finset (Fin n)) (g : Fin n → Fin n) :
    let r : RuleCertificate n :=
      .lifting (.finiteRestriction
        (.tail (.refl P) (.upward (.arithmetic P Q) a b N g)) Q a) P Q g g
    let c : ChainCertificate n := .tail (.refl P) r
    normalizeRule n (encode r) = some (encode r) ∧
      normalizeChain n (encode c) = some (encode c) := by
  exact ⟨normalizeRule_encode _, normalizeChain_encode _⟩


private theorem parse_generation_pack (chain target : ℕ) :
    PrimitiveGenerationCodec.parse (PrimitiveGenerationCodec.pack chain target) =
      some (chain, target) := by
  simp [PrimitiveGenerationCodec.parse, PrimitiveGenerationCodec.pack,
    PrimitiveRationalPresentation.decodeField]

/-- A well-shaped generation record still rejects an undecodable chain. -/
theorem generation_bad_chain (n target : ℕ) :
    PrimitiveGenerationCodec.normalize n (PrimitiveGenerationCodec.pack 0 target) = none := by
  have h : normalizeChain n 0 = none := normalizeChain_atom n 0
  simp [PrimitiveGenerationCodec.normalize, parse_generation_pack, h]

/-- The generation record stores a scalar chain code. An unwrapped chain
is not accepted as that scalar field. -/
theorem generation_requires_atom {n : ℕ} (P : PatternCode n) (target : ℕ) :
    PrimitiveGenerationCodec.normalize n
      (nodeCode 0 [encode (ChainCertificate.refl P), atomCode target]) = none := by
  rw [encode_refl]
  simp [PrimitiveGenerationCodec.normalize, PrimitiveGenerationCodec.parse,
    PrimitiveRationalPresentation.decodeField, nodeCode, atomCode]

/-- A nested mutual chain remains a scalar component of the unchanged
outer generation encoding. -/
theorem nested_generation_roundtrip {n : ℕ} (P Q : PatternCode n) :
    let c : GenerationCertificate n := ⟨.tail (.refl P) (.arithmetic P Q), Q⟩
    PrimitiveGenerationCodec.normalize n (encode c) = some (encode c) :=
  PrimitiveGenerationCodec.normalize_encode _

end Alexander313.Carlson.PrimitiveRecursiveCertificatesExamples
