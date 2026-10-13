import Alexander313.Carlson.PrimitiveRationalPresentation
import Alexander313.Carlson.ComputableRequests

/-!
# Primitive recursive request data and scheduling

This module certifies the existing constructor-tagged encoding of requests
and the concrete source-index, decoding, target-fallback, and scheduling
operations. Each raw natural input has a total decoding and target program.
The finite generating-rule checker is a separate boundary.
-/

namespace Alexander313.Carlson.PrimitiveRequests

open Encodable Finite
open Finite.ComputableRequests (Request instEncodableRequest)

/-- The original constructor tag, target atom, certificate atom, and terminal zero. -/
def packCode (a b : ℕ) : ℕ :=
  Nat.pair 1 (Nat.pair (Nat.pair 0 a + 1) (Nat.pair (Nat.pair 0 b + 1) 0))

theorem encode_request (r : Request) :
    @encode Request instEncodableRequest r = packCode (encode r.target) r.certificate := rfl

/-- Parse exactly the two fields of the existing request S-expression. -/
def decodeFields (n : ℕ) : Option (ℕ × ℕ) :=
  (PrimitiveRationalPresentation.decodeField n).bind fun tag =>
    if tag.1 = 0 then
      (PrimitiveRationalPresentation.decodeField tag.2).bind fun a =>
        (PrimitiveRationalPresentation.decodeField a.2).bind fun b =>
          if b.2 = 0 then some (a.1, b.1) else none
    else none

/-- Decode the stored target, retaining every natural certificate value. -/
def decodeData (n : ℕ) : Option (RationalPresentation × ℕ) :=
  (decodeFields n).bind fun p =>
    (Encodable.decode p.1).map fun P => (P, p.2)

def ofFields (p : RationalPresentation × ℕ) : Request := ⟨p.1, p.2⟩

section OriginalDerivedCodec

open private S S.nat S.cons S.encode S.decode S_equiv
  from Mathlib.Tactic.DeriveEncodable

private def fromS : S → Option Request
  | S.cons (S.nat 0) (S.cons (S.nat a) (S.cons (S.nat b) (S.nat 0))) =>
    match Encodable.decode a, Encodable.decode b with
    | some P, some certificate => some ⟨P, certificate⟩
    | _, _ => none
  | _ => none

private theorem decode_eq_fromS (n : ℕ) :
    @Encodable.decode Request instEncodableRequest n = fromS (S.decode n) := rfl

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

private theorem decodeData_encode (s : S) :
    (decodeData (S.encode s)).map ofFields = fromS s := by
  cases s with
  | nat n => simp [decodeData, decodeFields, decodeField_encode, fromS]
  | cons tag rest =>
    cases tag with
    | cons a b => simp [decodeData, decodeFields, decodeField_encode, fromS]
    | nat tag =>
      cases tag with
      | succ tag => simp [decodeData, decodeFields, decodeField_encode, fromS]
      | zero =>
        cases rest with
        | nat n => simp [decodeData, decodeFields, decodeField_encode, fromS]
        | cons a rest =>
          cases a with
          | cons x y => simp [decodeData, decodeFields, decodeField_encode, fromS]
          | nat a =>
            cases rest with
            | nat n => simp [decodeData, decodeFields, decodeField_encode, fromS]
            | cons b rest =>
              cases b with
              | cons x y => simp [decodeData, decodeFields, decodeField_encode, fromS]
              | nat b =>
                cases rest with
                | cons x y =>
                  simp [decodeData, decodeFields, decodeField_encode, sEncode_eq_zero, fromS]
                | nat n =>
                  cases n with
                  | succ n =>
                    simp [decodeData, decodeFields, decodeField_encode, sEncode_eq_zero, fromS]
                  | zero =>
                    cases ha : Encodable.decode (α := RationalPresentation) a <;>
                      simp [decodeData, decodeFields, decodeField_encode, sEncode_eq_zero,
                        fromS, ha, ofFields]

/-- Exact behavior of the preexisting request decoder on every raw natural input. -/
theorem decode_request (n : ℕ) :
    @Encodable.decode Request instEncodableRequest n = (decodeData n).map ofFields := by
  rw [decode_eq_fromS, ← decodeData_encode]
  rw [show S.encode (S.decode n) = n from S_equiv.right_inv n]

end OriginalDerivedCodec

theorem packCode_primrec {α : Type*} [Primcodable α]
    {a b : α → ℕ} (ha : Primrec a) (hb : Primrec b) :
    Primrec (fun x => packCode (a x) (b x)) :=
  Primrec₂.natPair.comp (Primrec.const 1)
    (Primrec₂.natPair.comp
      (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 0) ha))
      (Primrec₂.natPair.comp
        (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 0) hb)) (Primrec.const 0)))

theorem decodeFields_primrec : Primrec decodeFields := by
  unfold decodeFields
  refine Primrec.option_bind PrimitiveRationalPresentation.decodeField_primrec ?_
  apply Primrec₂.mk
  refine Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 0))
    ?_ (Primrec.const none)
  refine Primrec.option_bind
    (PrimitiveRationalPresentation.decodeField_primrec.comp (Primrec.snd.comp Primrec.snd)) ?_
  apply Primrec₂.mk
  refine Primrec.option_bind
    (PrimitiveRationalPresentation.decodeField_primrec.comp (Primrec.snd.comp Primrec.snd)) ?_
  apply Primrec₂.mk
  exact Primrec.ite (Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (Primrec.const 0))
    (Primrec.option_some.comp
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
        (Primrec.fst.comp Primrec.snd)))
    (Primrec.const none)

theorem decodeData_primrec : Primrec decodeData := by
  unfold decodeData
  refine Primrec.option_bind decodeFields_primrec ?_
  apply Primrec₂.mk
  refine Primrec.option_map (Primrec.decode.comp (Primrec.fst.comp Primrec.snd)) ?_
  exact (Primrec.snd.pair (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).to₂

theorem encoded_ofFields_primrec :
    Primrec (fun p : RationalPresentation × ℕ => @encode Request instEncodableRequest (ofFields p)) :=
  packCode_primrec (Primrec.encode.comp Primrec.fst) Primrec.snd

theorem encoded_decode_primrec : Primrec (fun n : ℕ =>
    @encode (Option Request) (@Option.encodable Request instEncodableRequest)
      (@Encodable.decode Request instEncodableRequest n)) := by
  apply (Primrec.encode.comp
    ((Primrec.option_map₁ encoded_ofFields_primrec).comp decodeData_primrec)).of_eq
  intro n
  rw [decode_request]
  cases decodeData n <;> rfl

/-- The original derived request codec, with its encoder and decoder unchanged. -/
instance instPrimcodableRequest : Primcodable Request where
  toEncodable := instEncodableRequest
  prim := Primrec.nat_iff.mp encoded_decode_primrec

@[simp] theorem request_encoding_unchanged :
    instPrimcodableRequest.toEncodable = instEncodableRequest := rfl

theorem ofFields_primrec : Primrec ofFields :=
  Primrec.encode_iff.mp encoded_ofFields_primrec

theorem mk_primrec : Primrec₂ Request.mk := ofFields_primrec

theorem decodeData_encode_request (r : Request) :
    decodeData (encode r) = some (r.target, r.certificate) := by
  rw [encode_request]
  simp [decodeData, decodeFields, PrimitiveRationalPresentation.decodeField, packCode]

theorem fields_primrec : Primrec (fun r : Request => (r.target, r.certificate)) :=
  Primrec.option_some_iff.mp
    ((decodeData_primrec.comp Primrec.encode).of_eq decodeData_encode_request)

theorem request_target_primrec : Primrec Request.target :=
  Primrec.fst.comp fields_primrec

theorem certificate_primrec : Primrec Request.certificate :=
  Primrec.snd.comp fields_primrec

/-- The actual scheduled source-stage projection is primitive recursive. -/
theorem sourceIndex_primrec : Primrec ComputableRequests.sourceIndex :=
  Primrec.fst.comp Primrec.unpair

/-- The actual scheduler decoder, including all malformed input cases. -/
theorem decode_primrec : Primrec ComputableRequests.decode :=
  Primrec.decode.comp (Primrec.snd.comp Primrec.unpair)

/-- The actual target lookup, including the specified empty fallback. -/
theorem target_primrec : Primrec ComputableRequests.target := by
  have h := Primrec.option_casesOn decode_primrec
    (Primrec.const (⟨∅, ∅, ∅⟩ : RationalPresentation))
    (request_target_primrec.comp Primrec.snd).to₂
  apply h.of_eq
  intro k
  unfold ComputableRequests.target
  cases ComputableRequests.decode k <;> rfl

theorem index_primrec : Primrec₂ ComputableRequests.index :=
  Primrec₂.natPair.comp Primrec.fst (Primrec.encode.comp Primrec.snd)

/-- Every raw code has a total request-decoding program returning an encoded option. -/
theorem request_decode_program : ∃ c : Nat.Partrec.Code, ∀ n : ℕ,
    c.eval n = Part.some (encode (Encodable.decode (α := Request) n)) :=
  PrimitiveRationalPresentation.exists_code Primrec.decode

/-- The scheduled request decoder has a total program on every natural stage. -/
theorem schedule_decode_program : ∃ c : Nat.Partrec.Code, ∀ k : ℕ,
    c.eval k = Part.some (encode (ComputableRequests.decode k)) :=
  PrimitiveRationalPresentation.exists_code decode_primrec

/-- The scheduled target has a total program on every natural stage,
including stages whose request codes fail to decode. -/
theorem schedule_target_program : ∃ c : Nat.Partrec.Code, ∀ k : ℕ,
    c.eval k = Part.some (encode (ComputableRequests.target k)) :=
  PrimitiveRationalPresentation.exists_code target_primrec

theorem sourceIndex_program : ∃ c : Nat.Partrec.Code, ∀ k : ℕ,
    c.eval k = Part.some (ComputableRequests.sourceIndex k) :=
  PrimitiveRationalPresentation.exists_code sourceIndex_primrec

end Alexander313.Carlson.PrimitiveRequests
