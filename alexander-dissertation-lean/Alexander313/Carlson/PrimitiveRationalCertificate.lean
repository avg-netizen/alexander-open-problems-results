import Alexander313.Carlson.PrimitivePatternCode
import Alexander313.Carlson.RationalRecognition

/-!
# Uniform primitive-recursive rational certificate coding

The original rational certificate stores its grid size and a four-field
constructor-tagged witness. Its label function and both Boolean endpoint
tables depend on that size. This module certifies the existing decoder on
every natural input, using the uniform finite-function and pattern-code
normalizers. Neither the grid size nor a dimension bound is fixed outside
the machine input.

These are data-decoding results. An accepted code may still fail the grid,
endpoint, or generating-derivation checks in `RationalWitness.check`.
No proof certificate is trusted by this decoder.
-/

namespace Alexander313.Carlson.PrimitiveRationalCertificate

open Encodable Finite

/-- Preserve the original dependent-sum encoding before certifying it. -/
abbrev originalCertificateEncoding : Encodable RationalCertificate := inferInstance

/-- The original witness tag, four field atoms, and terminal zero. -/
def packCode (a b c d : ℕ) : ℕ :=
  Nat.pair 1
    (Nat.pair (Nat.pair 0 a + 1)
      (Nat.pair (Nat.pair 0 b + 1)
        (Nat.pair (Nat.pair 0 c + 1) (Nat.pair (Nat.pair 0 d + 1) 0))))

theorem encode_witness {n : ℕ} (w : RationalWitness n) :
    @encode (RationalWitness n) (@instEncodableRationalWitness n) w =
      packCode (encode w.labels) (encode w.source) (encode w.target) w.derivation := rfl

/-- Parse exactly four fields of the existing tagged record. -/
def decodeFields (code : ℕ) : Option (ℕ × ℕ × ℕ × ℕ) :=
  (PrimitiveRationalPresentation.decodeField code).bind fun tag =>
    if tag.1 = 0 then
      (PrimitiveRationalPresentation.decodeField tag.2).bind fun a =>
        (PrimitiveRationalPresentation.decodeField a.2).bind fun b =>
          (PrimitiveRationalPresentation.decodeField b.2).bind fun c =>
            (PrimitiveRationalPresentation.decodeField c.2).bind fun d =>
              if d.2 = 0 then some (a.1, b.1, c.1, d.1) else none
    else none

/-- The typed component product used only to identify the original decoder. -/
abbrev TypedFields (n : ℕ) :=
  (Fin n → ℚ) × PatternCode n × PatternCode n × ℕ

def ofTypedFields {n : ℕ} (p : TypedFields n) : RationalWitness n :=
  ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩

def decodeTypedFields (n code : ℕ) : Option (TypedFields n) :=
  (decodeFields code).bind fun p =>
    (decode p.1).bind fun labels =>
      (decode p.2.1).bind fun source =>
        (decode p.2.2.1).map fun target => (labels, source, target, p.2.2.2)

section OriginalDerivedCodec

open private S S.nat S.cons S.encode S.decode S_equiv
  from Mathlib.Tactic.DeriveEncodable

private def fromS (n : ℕ) : S → Option (RationalWitness n)
  | S.cons (S.nat 0)
      (S.cons (S.nat a) (S.cons (S.nat b)
        (S.cons (S.nat c) (S.cons (S.nat d) (S.nat 0))))) =>
    match decode a, decode b, decode c, decode d with
    | some labels, some source, some target, some derivation =>
        some ⟨labels, source, target, derivation⟩
    | _, _, _, _ => none
  | _ => none

private theorem decode_eq_fromS (n code : ℕ) :
    @decode (RationalWitness n) (@instEncodableRationalWitness n) code =
      fromS n (S.decode code) := rfl

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

private theorem decodeTypedFields_encode (n : ℕ) (s : S) :
    (decodeTypedFields n (S.encode s)).map ofTypedFields = fromS n s := by
  cases s with
  | nat a => simp [decodeTypedFields, decodeFields, decodeField_encode, fromS]
  | cons tag rest =>
    cases tag with
    | cons a b => simp [decodeTypedFields, decodeFields, decodeField_encode, fromS]
    | nat tag =>
      cases tag with
      | succ tag => simp [decodeTypedFields, decodeFields, decodeField_encode, fromS]
      | zero =>
        cases rest with
        | nat a => simp [decodeTypedFields, decodeFields, decodeField_encode, fromS]
        | cons a rest =>
          cases a with
          | cons x y => simp [decodeTypedFields, decodeFields, decodeField_encode, fromS]
          | nat a =>
            cases rest with
            | nat b => simp [decodeTypedFields, decodeFields, decodeField_encode, fromS]
            | cons b rest =>
              cases b with
              | cons x y => simp [decodeTypedFields, decodeFields, decodeField_encode, fromS]
              | nat b =>
                cases rest with
                | nat c => simp [decodeTypedFields, decodeFields, decodeField_encode, fromS]
                | cons c rest =>
                  cases c with
                  | cons x y => simp [decodeTypedFields, decodeFields, decodeField_encode, fromS]
                  | nat c =>
                    cases rest with
                    | nat d => simp [decodeTypedFields, decodeFields, decodeField_encode, fromS]
                    | cons d rest =>
                      cases d with
                      | cons x y =>
                        simp [decodeTypedFields, decodeFields, decodeField_encode, fromS]
                      | nat d =>
                        cases rest with
                        | cons x y =>
                          simp [decodeTypedFields, decodeFields, decodeField_encode,
                            sEncode_eq_zero, fromS]
                        | nat e =>
                          cases e with
                          | succ e =>
                            simp [decodeTypedFields, decodeFields, decodeField_encode,
                              sEncode_eq_zero, fromS]
                          | zero =>
                            cases ha : decode (α := Fin n → ℚ) a <;>
                              cases hb : decode (α := PatternCode n) b <;>
                              cases hc : decode (α := PatternCode n) c <;>
                              simp [decodeTypedFields, decodeFields, decodeField_encode,
                                sEncode_eq_zero, fromS, ha, hb, hc, ofTypedFields]

/-- Exact original witness decoding, including every malformed raw input. -/
theorem decode_witness (n code : ℕ) :
    @decode (RationalWitness n) (@instEncodableRationalWitness n) code =
      (decodeTypedFields n code).map ofTypedFields := by
  rw [decode_eq_fromS, ← decodeTypedFields_encode]
  rw [show S.encode (S.decode code) = code from S_equiv.right_inv code]

end OriginalDerivedCodec

/-- Canonical component codes after all three dependent data fields decode. -/
def decodeData (n code : ℕ) : Option (ℕ × ℕ × ℕ × ℕ) :=
  (decodeFields code).bind fun p =>
    (PrimitiveFiniteFunctions.normalizeArrow (α := ℚ) n p.1).bind fun labels =>
      (PrimitivePatternCode.normalize n p.2.1).bind fun source =>
        (PrimitivePatternCode.normalize n p.2.2.1).map fun target =>
          (labels, source, target, p.2.2.2)

/-- Re-encoding an accepted witness preserves its original record format. -/
def normalizeWitness (n code : ℕ) : Option ℕ :=
  (decodeData n code).map fun p => packCode p.1 p.2.1 p.2.2.1 p.2.2.2

theorem decodeData_eq (n code : ℕ) :
    decodeData n code = (decodeTypedFields n code).map fun p =>
      (encode p.1, encode p.2.1, encode p.2.2.1, p.2.2.2) := by
  unfold decodeData decodeTypedFields
  cases hf : decodeFields code with
  | none => rfl
  | some p =>
    simp only [Option.bind_some, PrimitiveFiniteFunctions.normalizeArrow_eq,
      PrimitivePatternCode.normalize_eq]
    cases ha : decode (α := Fin n → ℚ) p.1 <;>
      cases hb : decode (α := PatternCode n) p.2.1 <;>
      cases hc : decode (α := PatternCode n) p.2.2.1 <;> rfl

theorem normalizeWitness_eq (n code : ℕ) :
    normalizeWitness n code =
      (@decode (RationalWitness n) (@instEncodableRationalWitness n) code).map encode := by
  rw [decode_witness]
  unfold normalizeWitness
  rw [decodeData_eq]
  cases decodeTypedFields n code <;> rfl

/-- Decode the actual dependent certificate and return its canonical natural code. -/
def normalizeCertificate (code : ℕ) : Option ℕ :=
  let p := Nat.unpair code
  (normalizeWitness p.1 p.2).map fun witness => Nat.pair p.1 witness

theorem normalizeCertificate_eq (code : ℕ) :
    normalizeCertificate code =
      (@decode RationalCertificate originalCertificateEncoding code).map
        (@encode RationalCertificate originalCertificateEncoding) := by
  dsimp only [normalizeCertificate]
  rw [normalizeWitness_eq]
  change _ = ((decode (α := RationalWitness (Nat.unpair code).1)
    (Nat.unpair code).2).map (Sigma.mk (Nat.unpair code).1)).map encode
  cases decode (α := RationalWitness (Nat.unpair code).1) (Nat.unpair code).2 <;> rfl

theorem packCode_primrec {α : Type*} [Primcodable α]
    {a b c d : α → ℕ} (ha : Primrec a) (hb : Primrec b)
    (hc : Primrec c) (hd : Primrec d) :
    Primrec (fun x => packCode (a x) (b x) (c x) (d x)) :=
  Primrec₂.natPair.comp (Primrec.const 1)
    (Primrec₂.natPair.comp
      (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 0) ha))
      (Primrec₂.natPair.comp
        (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 0) hb))
        (Primrec₂.natPair.comp
          (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 0) hc))
          (Primrec₂.natPair.comp
            (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 0) hd))
            (Primrec.const 0)))))

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
  refine Primrec.option_bind
    (PrimitiveRationalPresentation.decodeField_primrec.comp (Primrec.snd.comp Primrec.snd)) ?_
  apply Primrec₂.mk
  refine Primrec.option_bind
    (PrimitiveRationalPresentation.decodeField_primrec.comp (Primrec.snd.comp Primrec.snd)) ?_
  apply Primrec₂.mk
  exact Primrec.ite (Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (Primrec.const 0))
    (Primrec.option_some.comp
      ((Primrec.fst.comp (Primrec.snd.comp
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))).pair
        ((Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
          ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
            (Primrec.fst.comp Primrec.snd)))))
    (Primrec.const none)

theorem decodeData_primrec : Primrec₂ decodeData := by
  unfold decodeData
  refine Primrec.option_bind (decodeFields_primrec.comp Primrec.snd) ?_
  apply Primrec₂.mk
  refine Primrec.option_bind
    ((PrimitiveFiniteFunctions.normalizeArrow_primrec (α := ℚ)).comp
      (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)) ?_
  apply Primrec₂.mk
  refine Primrec.option_bind
    (PrimitivePatternCode.normalize_primrec.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))) ?_
  apply Primrec₂.mk
  refine Primrec.option_map
    (PrimitivePatternCode.normalize_primrec.comp
      (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))))) ?_
  exact ((Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).pair
    ((Primrec.snd.comp Primrec.fst).pair
      (Primrec.snd.pair
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
          (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))))))).to₂

/-- Primitive recursion is uniform in both the grid size and raw witness code. -/
theorem normalizeWitness_primrec : Primrec₂ normalizeWitness :=
  Primrec.option_map decodeData_primrec
    (packCode_primrec (Primrec.fst.comp Primrec.snd)
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))).to₂

theorem normalizeCertificate_primrec : Primrec normalizeCertificate :=
  Primrec.option_map
    (normalizeWitness_primrec.comp (Primrec.fst.comp Primrec.unpair)
      (Primrec.snd.comp Primrec.unpair))
    (Primrec₂.natPair.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst))
      Primrec.snd).to₂

theorem encoded_decode_primrec : Primrec (fun code : ℕ =>
    @encode (Option RationalCertificate)
      (@Option.encodable RationalCertificate originalCertificateEncoding)
      (@decode RationalCertificate originalCertificateEncoding code)) := by
  refine (Primrec.encode.comp normalizeCertificate_primrec).of_eq ?_
  intro code
  rw [normalizeCertificate_eq]
  cases @decode RationalCertificate originalCertificateEncoding code <;> rfl

/-- The preexisting dependent-sum codec, now certified without changing it. -/
instance instPrimcodableRationalCertificate : Primcodable RationalCertificate where
  toEncodable := originalCertificateEncoding
  prim := Primrec.nat_iff.mp encoded_decode_primrec

@[simp] theorem certificate_encoding_unchanged :
    instPrimcodableRationalCertificate.toEncodable = originalCertificateEncoding := rfl

/-- The stored grid size can be read from the original dependent-sum code. -/
theorem size_primrec : Primrec (fun c : RationalCertificate => c.1) :=
  (Primrec.fst.comp (Primrec.unpair.comp Primrec.encode)).of_eq fun c => by
    rcases c with ⟨n, w⟩
    simp [Encodable.encode_sigma_val]

theorem witnessCode_primrec :
    Primrec (fun c : RationalCertificate => encode c.2) :=
  (Primrec.snd.comp (Primrec.unpair.comp Primrec.encode)).of_eq fun c => by
    rcases c with ⟨n, w⟩
    simp [Encodable.encode_sigma_val]

/-- The four original fields exposed as canonical natural codes. -/
def fields (c : RationalCertificate) : ℕ × ℕ × ℕ × ℕ :=
  (encode c.2.labels, encode c.2.source, encode c.2.target, c.2.derivation)

theorem decodeData_encode {n : ℕ} (w : RationalWitness n) :
    decodeData n (encode w) =
      some (encode w.labels, encode w.source, encode w.target, w.derivation) := by
  have h := congrArg
    (Option.map (fun v : RationalWitness n =>
      (encode v.labels, encode v.source, encode v.target, v.derivation)))
    (decode_witness n (encode w))
  rw [Encodable.encodek] at h
  rw [decodeData_eq]
  simpa only [Option.map_map, Option.map_some, Function.comp_def, ofTypedFields] using h.symm

theorem fields_primrec : Primrec fields :=
  Primrec.option_some_iff.mp
    ((decodeData_primrec.comp size_primrec witnessCode_primrec).of_eq
      (fun c => decodeData_encode c.2))

theorem sourceCode_primrec :
    Primrec (fun c : RationalCertificate => encode c.2.source) :=
  Primrec.fst.comp (Primrec.snd.comp fields_primrec)

theorem targetCode_primrec :
    Primrec (fun c : RationalCertificate => encode c.2.target) :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp fields_primrec))

/-- Reading a certificate preserves every stored natural derivation value. -/
theorem derivation_primrec : Primrec (fun c : RationalCertificate => c.2.derivation) :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp fields_primrec))

/-- A uniform list view of every rational grid label, including unused labels. -/
def gridLabels (c : RationalCertificate) : List ℚ := List.ofFn c.2.labels

theorem gridLabels_primrec : Primrec gridLabels := by
  apply Primrec.option_some_iff.mp
  refine (PrimitiveFiniteFunctions.decodeArrowWith_primrec
    (Primrec.decode.comp Primrec.snd).to₂ size_primrec
    (Primrec.fst.comp fields_primrec)).of_eq ?_
  intro c
  simp [PrimitiveFiniteFunctions.decodeArrowWith_decode, fields, gridLabels]

/-- A lossless, primitive-recursive view of the source's entire Boolean tables. -/
theorem sourceData_primrec :
    Primrec (fun c : RationalCertificate => PrimitivePatternCode.dataView c.2.source) := by
  apply Primrec.option_some_iff.mp
  refine (PrimitivePatternCode.decodeData_primrec.comp size_primrec sourceCode_primrec).of_eq ?_
  intro c
  rw [PrimitivePatternCode.decodeData_eq, Encodable.encodek]
  rfl

theorem targetData_primrec :
    Primrec (fun c : RationalCertificate => PrimitivePatternCode.dataView c.2.target) := by
  apply Primrec.option_some_iff.mp
  refine (PrimitivePatternCode.decodeData_primrec.comp size_primrec targetCode_primrec).of_eq ?_
  intro c
  rw [PrimitivePatternCode.decodeData_eq, Encodable.encodek]
  rfl

/-- Pairwise checking uses a certified relation and finite list recursion. -/
theorem list_pairwise {α : Type*} [Primcodable α]
    {r : α → α → Prop} [DecidableRel r] (hr : PrimrecRel r) :
    PrimrecPred (List.Pairwise r) := by
  refine ⟨inferInstance, ?_⟩
  have hforall : PrimrecRel (fun a (l : List α) => ∀ b ∈ l, r a b) :=
    hr.swap.forall_mem_list.swap
  have hstep : Primrec₂ fun (_ : List α) (t : α × List α × Bool) =>
      decide (∀ b ∈ t.2.1, r t.1 b) && t.2.2 :=
    (Primrec.and.comp
      ((hforall.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))).decide)
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).to₂
  refine (Primrec.list_rec Primrec.id (Primrec.const true) hstep).of_eq ?_
  intro l
  induction l with
  | nil => rfl
  | cons a l ih =>
    simpa [List.pairwise_cons] using
      congrArg (fun b => decide (∀ x ∈ l, r a x) && b) ih

/-- The actual whole-grid condition from `RationalWitness.check`. -/
def checkGrid (c : RationalCertificate) : Bool :=
  decide (0 < c.1) && decide ((gridLabels c).Pairwise (· < ·))

@[simp] theorem checkGrid_eq_true (c : RationalCertificate) :
    checkGrid c = true ↔ 0 < c.1 ∧ StrictMono c.2.labels := by
  simp only [checkGrid, Bool.and_eq_true, decide_eq_true_eq, gridLabels,
    List.pairwise_ofFn, StrictMono]

/-- Positivity and strict increase of the entire grid have a uniform
primitive-recursive certificate; unused grid labels are checked too. -/
theorem checkGrid_primrec : Primrec checkGrid :=
  Primrec.and.comp ((Primrec.nat_lt.comp (Primrec.const 0) size_primrec).decide)
    (((list_pairwise PrimitiveRationalData.rat_lt).comp gridLabels_primrec).decide)

/-- A single machine decodes every raw natural certificate code. -/
theorem certificate_decode_program : ∃ c : Nat.Partrec.Code, ∀ code : ℕ,
    c.eval code = Part.some (encode (decode (α := RationalCertificate) code)) :=
  PrimitiveRationalPresentation.exists_code Primrec.decode

/-- A single machine normalizes witness codes at every finite grid size. -/
theorem witness_normalize_program : ∃ c : Nat.Partrec.Code, ∀ n code : ℕ,
    c.eval (Nat.pair n code) = Part.some (encode (normalizeWitness n code)) := by
  obtain ⟨c, hc⟩ := PrimitiveRationalPresentation.exists_code normalizeWitness_primrec
  exact ⟨c, fun n code => hc (n, code)⟩

/-- One machine checks the complete ordered grid of every typed certificate. -/
theorem grid_check_program : ∃ p : Nat.Partrec.Code, ∀ c : RationalCertificate,
    p.eval (encode c) = Part.some (encode (checkGrid c)) :=
  PrimitiveRationalPresentation.exists_code checkGrid_primrec

end Alexander313.Carlson.PrimitiveRationalCertificate
