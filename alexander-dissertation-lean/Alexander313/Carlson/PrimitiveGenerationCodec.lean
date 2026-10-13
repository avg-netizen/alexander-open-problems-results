import Alexander313.Carlson.PrimitiveRecursiveCertificates

/-!
# Primitive recursion for the original generation-certificate record

The original derived `GenerationCertificate n` codec stores a tag-zero record
with two scalar atoms: the encoded finite chain and the encoded target pattern.
The chain is a scalar field here because this record is outside the mutual
rule/chain declaration. The parser requires both atoms and the exact zero
terminator, and the component normalizers validate every raw scalar input.
-/

namespace Alexander313.Carlson.PrimitiveGenerationCodec

open Encodable Finite

set_option maxHeartbeats 400000

/-- Pack the two scalar fields in the original derived record format. -/
def pack (chain target : ℕ) : ℕ :=
  Nat.pair 1 (Nat.pair (Nat.pair 0 chain + 1)
    (Nat.pair (Nat.pair 0 target + 1) 0))

/-- Parse the original tag, two atom fields and exact empty terminator. -/
def parse (code : ℕ) : Option (ℕ × ℕ) :=
  (PrimitiveRationalPresentation.decodeField code).bind fun tagged =>
    if tagged.1 = 0 then
      (PrimitiveRationalPresentation.decodeField tagged.2).bind fun chain =>
        (PrimitiveRationalPresentation.decodeField chain.2).bind fun target =>
          if target.2 = 0 then some (chain.1, target.1) else none
    else none

theorem pack_primrec : Primrec₂ pack := by
  apply Primrec₂.mk
  exact Primrec₂.natPair.comp (Primrec.const 1)
    (Primrec₂.natPair.comp
      (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 0) Primrec.fst))
      (Primrec₂.natPair.comp
        (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 0) Primrec.snd))
        (Primrec.const 0)))

theorem parse_primrec : Primrec parse := by
  unfold parse
  refine Primrec.option_bind PrimitiveRationalPresentation.decodeField_primrec ?_
  apply Primrec₂.mk
  refine Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 0))
    ?_ (Primrec.const none)
  refine Primrec.option_bind
    (PrimitiveRationalPresentation.decodeField_primrec.comp
      (Primrec.snd.comp Primrec.snd)) ?_
  apply Primrec₂.mk
  refine Primrec.option_bind
    (PrimitiveRationalPresentation.decodeField_primrec.comp
      (Primrec.snd.comp Primrec.snd)) ?_
  apply Primrec₂.mk
  exact Primrec.ite (Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (Primrec.const 0))
    (Primrec.option_some.comp
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
        (Primrec.fst.comp Primrec.snd)))
    (Primrec.const none)

/-- Validate both scalar fields and re-encode with the unchanged record codec. -/
def normalize (n code : ℕ) : Option ℕ :=
  (parse code).bind fun fields =>
    (PrimitiveRecursiveCertificates.normalizeChain n fields.1).bind fun chain =>
      (PrimitivePatternCode.normalize n fields.2).map fun target => pack chain target

theorem normalize_primrec : Primrec₂ normalize := by
  apply Primrec₂.mk
  unfold normalize
  refine Primrec.option_bind (parse_primrec.comp Primrec.snd) ?_
  apply Primrec₂.mk
  refine Primrec.option_bind
    (PrimitiveRecursiveCertificates.normalizeChain_primrec.comp
      (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)) ?_
  apply Primrec₂.mk
  refine Primrec.option_map
    (PrimitivePatternCode.normalize_primrec.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))) ?_
  exact (pack_primrec.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂

section OriginalDerivedCodec

open private S S.nat S.cons S.encode S.decode S_equiv
  from Mathlib.Tactic.DeriveEncodable

-- The original generated names carry hygiene scopes. Open only name aliases;
-- the equation theorem and every codec constant still come from FiniteCertificates.
run_cmd do
  let env ← Lean.getEnv
  let auxiliaryNames := env.constants.toList.filter fun (name, _) =>
    name.eraseMacroScopes.toString.endsWith
      "instEncodableGenerationCertificate.encodable_toS"
  let [(name, _)] := auxiliaryNames | throwError "expected unique original generation encoder"
  Lean.Elab.Command.modifyScope fun scope =>
    { scope with openDecls := Lean.OpenDecl.explicit `originalToS name :: scope.openDecls }
  let equationName := Lean.Name.str name "eq_def"
  Lean.Elab.Command.liftCoreM (Lean.executeReservedNameAction equationName)
  unless (← Lean.getEnv).contains equationName do
    throwError "original generation encoder equation not found"
  Lean.Elab.Command.modifyScope fun scope =>
    { scope with openDecls := Lean.OpenDecl.explicit `originalToSEq equationName :: scope.openDecls }

private theorem encodeS_eq (s : S) : encode s = S.encode s := rfl

private theorem encodeGeneration_toS {n : ℕ} (c : GenerationCertificate n) :
    encode c = S.encode (@originalToS n c) := by
  delta encode instEncodableGenerationCertificate
  dsimp only [Encodable.ofLeftInjection]
  exact encodeS_eq (@originalToS n c)

/-- This is the existing record encoder, including its scalar chain field. -/
theorem encode_generation {n : ℕ} (c : GenerationCertificate n) :
    encode c = pack (encode c.chain) (encode c.target) := by
  rw [encodeGeneration_toS, originalToSEq]
  cases c
  simp only [S.encode, pack, show Nat.pair 0 0 = 0 from rfl]

private def fromS (n : ℕ) : S → Option (GenerationCertificate n)
  | S.cons (S.nat 0) (S.cons (S.nat chain) (S.cons (S.nat target) (S.nat 0))) =>
    match decode chain, decode target with
    | some chain, some target => some ⟨chain, target⟩
    | _, _ => none
  | _ => none

private theorem decode_fromS (n code : ℕ) :
    decode (α := GenerationCertificate n) code = fromS n (S.decode code) := rfl

private theorem decodeField_encode (s : S) :
    PrimitiveRationalPresentation.decodeField (S.encode s) =
      match s with
      | S.cons (S.nat a) b => some (a, S.encode b)
      | _ => none := by
  cases s with
  | nat n => simp [PrimitiveRationalPresentation.decodeField, S.encode]
  | cons a b => cases a <;> simp [PrimitiveRationalPresentation.decodeField, S.encode]

private theorem sEncode_eq_zero (s : S) :
    S.encode s = 0 ↔ s = S.nat 0 := by
  change S_equiv s = S_equiv (S.nat 0) ↔ _
  exact S_equiv.injective.eq_iff

private theorem normalize_encode_tree (n : ℕ) (s : S) :
    normalize n (S.encode s) = (fromS n s).map encode := by
  cases s with
  | nat a => simp [normalize, parse, decodeField_encode, fromS]
  | cons tag rest =>
    cases tag with
    | cons a b => simp [normalize, parse, decodeField_encode, fromS]
    | nat tag =>
      cases tag with
      | succ tag => simp [normalize, parse, decodeField_encode, fromS]
      | zero =>
        cases rest with
        | nat a => simp [normalize, parse, decodeField_encode, fromS]
        | cons chain rest =>
          cases chain with
          | cons a b => simp [normalize, parse, decodeField_encode, fromS]
          | nat chain =>
            cases rest with
            | nat a => simp [normalize, parse, decodeField_encode, fromS]
            | cons target rest =>
              cases target with
              | cons a b => simp [normalize, parse, decodeField_encode, fromS]
              | nat target =>
                cases rest with
                | cons a b =>
                  simp [normalize, parse, decodeField_encode, sEncode_eq_zero, fromS]
                | nat z =>
                  cases z with
                  | succ z =>
                    simp [normalize, parse, decodeField_encode, sEncode_eq_zero, fromS]
                  | zero =>
                    simp only [normalize, parse, decodeField_encode,
                      sEncode_eq_zero, Option.bind_some,
                      ↓reduceIte, PrimitiveRecursiveCertificates.normalizeChain_eq,
                      PrimitivePatternCode.normalize_eq]
                    cases hc : decode (α := ChainCertificate n) chain <;>
                      cases ht : decode (α := PatternCode n) target <;>
                      simp [fromS, hc, ht, encode_generation]

/-- Exact decoding and canonicalization for all raw inputs and finite bounds. -/
theorem normalize_eq (n code : ℕ) :
    normalize n code = (decode (α := GenerationCertificate n) code).map encode := by
  rw [decode_fromS, ← normalize_encode_tree]
  rw [show S.encode (S.decode code) = code from S_equiv.right_inv code]

end OriginalDerivedCodec

/-- Encoded optional output agrees with the original decoder even on rejection. -/
theorem encode_normalize (n code : ℕ) :
    encode (normalize n code) = encode (decode (α := GenerationCertificate n) code) := by
  rw [normalize_eq]
  cases decode (α := GenerationCertificate n) code <;>
    simp only [Option.map_none, Option.map_some, encode_none, encode_some, encode_nat]

theorem encoded_generation_decode_primrec (n : ℕ) :
    Primrec (fun code : ℕ => encode (decode (α := GenerationCertificate n) code)) :=
  (Primrec.encode.comp (normalize_primrec.comp (Primrec.const n) Primrec.id)).of_eq
    (encode_normalize n)

/-- The original derived record instance, now certified primitive recursive. -/
instance instPrimcodableGenerationCertificate (n : ℕ) :
    Primcodable (GenerationCertificate n) where
  toEncodable := @instEncodableGenerationCertificate n
  prim := Primrec.nat_iff.mp (encoded_generation_decode_primrec n)

@[simp] theorem generation_encoding_unchanged (n : ℕ) :
    (instPrimcodableGenerationCertificate n).toEncodable =
      @instEncodableGenerationCertificate n := rfl

@[simp] theorem normalize_encode {n : ℕ} (c : GenerationCertificate n) :
    normalize n (encode c) = some (encode c) := by
  rw [normalize_eq, Encodable.encodek]
  rfl

/-- One actual total machine normalizes the original generation codes at every
finite label bound, including malformed raw records and scalar components. -/
theorem generation_normalize_program : ∃ machine : Nat.Partrec.Code, ∀ n code : ℕ,
    machine.eval (Nat.pair n code) = Part.some (encode (normalize n code)) := by
  obtain ⟨machine, hm⟩ := PrimitiveRationalPresentation.exists_code normalize_primrec
  exact ⟨machine, fun n code => hm (n, code)⟩

/-- The same machine computes the original encoded optional decoder result. -/
theorem generation_decode_program : ∃ machine : Nat.Partrec.Code, ∀ n code : ℕ,
    machine.eval (Nat.pair n code) =
      Part.some (encode (decode (α := GenerationCertificate n) code)) := by
  obtain ⟨machine, hm⟩ := generation_normalize_program
  exact ⟨machine, fun n code => (hm n code).trans
    (congrArg Part.some (encode_normalize n code))⟩

end Alexander313.Carlson.PrimitiveGenerationCodec
