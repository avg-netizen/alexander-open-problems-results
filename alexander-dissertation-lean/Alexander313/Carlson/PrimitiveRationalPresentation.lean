import Alexander313.Carlson.RationalPresentation
import Alexander313.Carlson.PrimitiveRationalData
import Alexander313.Carlson.PrimitiveFiniteData
import Batteries.Tactic.OpenPrivate

/-!
# Primitive recursive codes for rational presentations

The existing derived `Encodable` instance stores a constructor-tagged
S-expression. We make that precise at the natural-number level and parse
exactly its three fields. Component decoders retain their existing behavior,
including normalization of accepted noncanonical finite-set codes.

The primitive coding instance below preserves the original presentation
encoding. The product of its three fields is only an intermediate type used
to prove that the existing decoder is primitive recursive.
-/

namespace Alexander313.Carlson.PrimitiveRationalPresentation

open Encodable Finite

/-- The three independently stored finite sets. -/
abbrev Fields := Finset ℚ × Finset (ℚ × ℚ) × Finset (ℚ × ℚ)

/-- Reassemble the three fields of a rational presentation. -/
def ofFields (p : Fields) : RationalPresentation := ⟨p.1, p.2.1, p.2.2⟩

/-- The existing tagged S-expression encoding, with tag `0` and three fields. -/
def packCode (a b c : ℕ) : ℕ :=
  Nat.pair 1
    (Nat.pair (Nat.pair 0 a + 1)
      (Nat.pair (Nat.pair 0 b + 1) (Nat.pair (Nat.pair 0 c + 1) 0)))

theorem encode_presentation (P : RationalPresentation) :
    @encode RationalPresentation instEncodableRationalPresentation P =
      packCode (encode P.U) (encode P.r₁) (encode P.r₂) := rfl

/-- Decode one S-expression list cell whose head is a natural atom.
The second output is the raw code of the remaining list. -/
def decodeField (n : ℕ) : Option (ℕ × ℕ) :=
  let p := Nat.unpair n
  if p.1 = 0 then none else
    let a := Nat.unpair (p.1 - 1)
    if a.1 = 0 then some (a.2, p.2) else none

/-- Parse exactly the existing constructor tag and three field atoms,
including the terminating atom `0`. -/
def decodeFields (n : ℕ) : Option (ℕ × ℕ × ℕ) :=
  (decodeField n).bind fun tag =>
    if tag.1 = 0 then
      (decodeField tag.2).bind fun a =>
        (decodeField a.2).bind fun b =>
          (decodeField b.2).bind fun c =>
            if c.2 = 0 then some (a.1, b.1, c.1) else none
    else none

/-- Apply the existing finite-set decoders to the three parsed fields. -/
def decodeData (n : ℕ) : Option Fields :=
  (decodeFields n).bind fun p =>
    (decode p.1).bind fun U =>
      (decode p.2.1).bind fun r₁ =>
        (decode p.2.2).map fun r₂ => (U, r₁, r₂)

section OriginalDerivedCodec

-- These private declarations are inspected only to prove compatibility with
-- the pinned deriving handler. No new S-expression encoding is installed.
open private S S.nat S.cons S.encode S.decode S_equiv
  from Mathlib.Tactic.DeriveEncodable

private def fromS : S → Option RationalPresentation
  | S.cons (S.nat 0)
      (S.cons (S.nat a) (S.cons (S.nat b) (S.cons (S.nat c) (S.nat 0)))) =>
    match decode a, decode b, decode c with
    | some U, some r₁, some r₂ => some ⟨U, r₁, r₂⟩
    | _, _, _ => none
  | _ => none

private theorem decode_eq_fromS (n : ℕ) :
    @decode RationalPresentation instEncodableRationalPresentation n =
      fromS (S.decode n) := rfl

private theorem decodeField_encode (s : S) :
    decodeField (S.encode s) =
      match s with
      | S.cons (S.nat a) b => some (a, S.encode b)
      | _ => none := by
  cases s with
  | nat n => simp [decodeField, S.encode]
  | cons a b => cases a <;> simp [decodeField, S.encode]

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
                | nat n => simp [decodeData, decodeFields, decodeField_encode, fromS]
                | cons c rest =>
                  cases c with
                  | cons x y => simp [decodeData, decodeFields, decodeField_encode, fromS]
                  | nat c =>
                    cases rest with
                    | cons x y =>
                      simp [decodeData, decodeFields, decodeField_encode, sEncode_eq_zero, fromS]
                    | nat n =>
                      cases n with
                      | succ n =>
                        simp [decodeData, decodeFields, decodeField_encode, sEncode_eq_zero, fromS]
                      | zero =>
                        cases ha : decode (α := Finset ℚ) a <;>
                          cases hb : decode (α := Finset (ℚ × ℚ)) b <;>
                          cases hc : decode (α := Finset (ℚ × ℚ)) c <;>
                          simp [decodeData, decodeFields, decodeField_encode, sEncode_eq_zero,
                            fromS, ha, hb, hc, ofFields]

/-- Exact behavior of the existing decoder on every natural input,
including malformed tagged structures and noncanonical component codes. -/
theorem decode_presentation (n : ℕ) :
    @decode RationalPresentation instEncodableRationalPresentation n =
      (decodeData n).map ofFields := by
  rw [decode_eq_fromS, ← decodeData_encode]
  rw [show S.encode (S.decode n) = n from S_equiv.right_inv n]

end OriginalDerivedCodec

/-- Constructing a correctly tagged natural code is primitive recursive. -/
theorem packCode_primrec {α : Type*} [Primcodable α]
    {a b c : α → ℕ} (ha : Primrec a) (hb : Primrec b) (hc : Primrec c) :
    Primrec (fun x => packCode (a x) (b x) (c x)) := by
  exact Primrec₂.natPair.comp (Primrec.const 1)
    (Primrec₂.natPair.comp
      (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 0) ha))
      (Primrec₂.natPair.comp
        (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 0) hb))
        (Primrec₂.natPair.comp
          (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 0) hc))
          (Primrec.const 0))))

theorem decodeField_primrec : Primrec decodeField := by
  have hp := Primrec.fst.comp Primrec.unpair
  have ht := Primrec.snd.comp Primrec.unpair
  have ha := Primrec.unpair.comp (Primrec.pred.comp hp)
  exact Primrec.ite (Primrec.eq.comp hp (Primrec.const 0)) (Primrec.const none)
    (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp ha) (Primrec.const 0))
      (Primrec.option_some.comp ((Primrec.snd.comp ha).pair ht)) (Primrec.const none))

theorem decodeFields_primrec : Primrec decodeFields := by
  unfold decodeFields
  refine Primrec.option_bind decodeField_primrec ?_
  apply Primrec₂.mk
  refine Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 0))
    ?_ (Primrec.const none)
  refine Primrec.option_bind (decodeField_primrec.comp (Primrec.snd.comp Primrec.snd)) ?_
  apply Primrec₂.mk
  refine Primrec.option_bind (decodeField_primrec.comp (Primrec.snd.comp Primrec.snd)) ?_
  apply Primrec₂.mk
  refine Primrec.option_bind (decodeField_primrec.comp (Primrec.snd.comp Primrec.snd)) ?_
  apply Primrec₂.mk
  exact Primrec.ite (Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (Primrec.const 0))
    (Primrec.option_some.comp
      ((Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
        ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
          (Primrec.fst.comp Primrec.snd))))
    (Primrec.const none)

theorem decodeData_primrec : Primrec decodeData := by
  unfold decodeData
  refine Primrec.option_bind decodeFields_primrec ?_
  apply Primrec₂.mk
  refine Primrec.option_bind (Primrec.decode.comp (Primrec.fst.comp Primrec.snd)) ?_
  apply Primrec₂.mk
  refine Primrec.option_bind
    (Primrec.decode.comp
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))) ?_
  apply Primrec₂.mk
  refine Primrec.option_map
    (Primrec.decode.comp
      (Primrec.snd.comp (Primrec.snd.comp
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))) ?_
  exact ((Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).pair
    ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)).to₂

theorem encoded_ofFields_primrec :
    Primrec (fun p : Fields =>
      @encode RationalPresentation instEncodableRationalPresentation (ofFields p)) :=
  packCode_primrec (Primrec.encode.comp Primrec.fst)
    (Primrec.encode.comp (Primrec.fst.comp Primrec.snd))
    (Primrec.encode.comp (Primrec.snd.comp Primrec.snd))

/-- The original decoder's encoded output is primitive recursive without
assuming a primitive coding instance for presentations in advance. -/
theorem encoded_decode_primrec : Primrec (fun n : ℕ =>
    @encode (Option RationalPresentation)
      (@Option.encodable RationalPresentation instEncodableRationalPresentation)
      (@decode RationalPresentation instEncodableRationalPresentation n)) := by
  apply (Primrec.encode.comp
    ((Primrec.option_map₁ encoded_ofFields_primrec).comp decodeData_primrec)).of_eq
  intro n
  rw [decode_presentation]
  cases decodeData n <;> rfl

/-- Certify exactly the preexisting derived presentation codec. -/
instance instPrimcodableRationalPresentation : Primcodable RationalPresentation where
  toEncodable := instEncodableRationalPresentation
  prim := Primrec.nat_iff.mp encoded_decode_primrec

@[simp] theorem presentation_encoding_unchanged :
    instPrimcodableRationalPresentation.toEncodable = instEncodableRationalPresentation := rfl

theorem ofFields_primrec : Primrec ofFields :=
  Primrec.encode_iff.mp encoded_ofFields_primrec

/-- Construct a presentation from three primitive recursive finite-set fields. -/
theorem mk_primrec {α : Type*} [Primcodable α]
    {U : α → Finset ℚ} {r₁ r₂ : α → Finset (ℚ × ℚ)}
    (hU : Primrec U) (h₁ : Primrec r₁) (h₂ : Primrec r₂) :
    Primrec (fun a => RationalPresentation.mk (U a) (r₁ a) (r₂ a)) :=
  ofFields_primrec.comp (hU.pair (h₁.pair h₂))

theorem decodeData_encode_presentation (P : RationalPresentation) :
    decodeData (encode P) = some (P.U, P.r₁, P.r₂) := by
  rw [encode_presentation]
  simp [decodeData, decodeFields, decodeField, packCode]

theorem fields_primrec :
    Primrec (fun P : RationalPresentation => (P.U, P.r₁, P.r₂)) :=
  Primrec.option_some_iff.mp
    ((decodeData_primrec.comp Primrec.encode).of_eq decodeData_encode_presentation)

theorem carrier_primrec : Primrec RationalPresentation.U :=
  Primrec.fst.comp fields_primrec

theorem relation₁_primrec : Primrec RationalPresentation.r₁ :=
  Primrec.fst.comp (Primrec.snd.comp fields_primrec)

theorem relation₂_primrec : Primrec RationalPresentation.r₂ :=
  Primrec.snd.comp (Primrec.snd.comp fields_primrec)

theorem carrier_mem :
    PrimrecRel (fun (P : RationalPresentation) (x : ℚ) => x ∈ P.U) :=
  PrimitiveFiniteData.finset_mem.comp Primrec.snd (carrier_primrec.comp Primrec.fst)

theorem relation₁_mem :
    PrimrecRel (fun (P : RationalPresentation) (xy : ℚ × ℚ) => xy ∈ P.r₁) :=
  PrimitiveFiniteData.finset_mem.comp Primrec.snd (relation₁_primrec.comp Primrec.fst)

theorem relation₂_mem :
    PrimrecRel (fun (P : RationalPresentation) (xy : ℚ × ℚ) => xy ∈ P.r₂) :=
  PrimitiveFiniteData.finset_mem.comp Primrec.snd (relation₂_primrec.comp Primrec.fst)

/-- An actual partial-recursive machine code for a primitive recursive map,
on canonical encodings of its typed inputs and outputs. -/
theorem exists_code {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → β} (hf : Primrec f) :
    ∃ c : Nat.Partrec.Code, ∀ a,
      c.eval (encode a) = Part.some (encode (f a)) := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hf.to_comp
  refine ⟨c, fun a => ?_⟩
  rw [hc]
  simp

/-- The original presentation decoder has a total machine implementation
on every raw natural input, returning the encoded `Option` result. -/
theorem presentation_decode_program : ∃ c : Nat.Partrec.Code, ∀ n : ℕ,
    c.eval n = Part.some (encode (decode (α := RationalPresentation) n)) :=
  exists_code Primrec.decode

/-- Carrier membership returns an encoded Boolean answer for every typed
presentation and rational label. -/
theorem carrier_mem_program : ∃ c : Nat.Partrec.Code,
    ∀ (P : RationalPresentation) (x : ℚ),
      c.eval (Nat.pair (encode P) (encode x)) = Part.some (encode (decide (x ∈ P.U))) := by
  obtain ⟨c, hc⟩ := exists_code carrier_mem.decide
  exact ⟨c, fun P x => hc (P, x)⟩

/-- The first stored relation has a total encoded Boolean membership answer. -/
theorem relation₁_mem_program : ∃ c : Nat.Partrec.Code,
    ∀ (P : RationalPresentation) (xy : ℚ × ℚ),
      c.eval (Nat.pair (encode P) (encode xy)) = Part.some (encode (decide (xy ∈ P.r₁))) := by
  obtain ⟨c, hc⟩ := exists_code relation₁_mem.decide
  exact ⟨c, fun P xy => hc (P, xy)⟩

/-- The second stored relation has a total encoded Boolean membership answer. -/
theorem relation₂_mem_program : ∃ c : Nat.Partrec.Code,
    ∀ (P : RationalPresentation) (xy : ℚ × ℚ),
      c.eval (Nat.pair (encode P) (encode xy)) = Part.some (encode (decide (xy ∈ P.r₂))) := by
  obtain ⟨c, hc⟩ := exists_code relation₂_mem.decide
  exact ⟨c, fun P xy => hc (P, xy)⟩

end Alexander313.Carlson.PrimitiveRationalPresentation
