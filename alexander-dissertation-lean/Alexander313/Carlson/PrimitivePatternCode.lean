import Alexander313.Carlson.PrimitiveFiniteFunctions
import Alexander313.Carlson.PrimitiveRationalPresentation
import Batteries.Tactic.OpenPrivate

/-!
# Uniform primitive-recursive decoding of finite pattern codes

The label bound is an input to these algorithms. The original derived
`PatternCode n` encoding retains a finite carrier and two complete Boolean
tables, including entries whose labels do not belong to the carrier.

The raw data view uses natural carrier labels and ordinary lists for the
two tables. Its decoder checks the carrier's label bound and duplicate
condition, the stored position tags, and both dimensions of each table.
The original table encoder's tags are reconstructed on re-encoding.
Accepted unsorted carrier
codes are canonicalized by the existing finite-set encoder. All the
compatibility statements quantify over arbitrary natural inputs, including
malformed constructor tags and invalid component codes.
-/

namespace Alexander313.Carlson.PrimitivePatternCode

open Encodable Finite PrimitiveFiniteData PrimitiveFiniteFunctions

/-- The three original fields, before erasing their finite index types. -/
abbrev TypedFields (n : ℕ) :=
  Finset (Fin n) × (Fin n → Fin n → Bool) × (Fin n → Fin n → Bool)

/-- Reassemble the original structure record. -/
def ofTypedFields {n : ℕ} (p : TypedFields n) : PatternCode n :=
  ⟨p.1, p.2.1, p.2.2⟩

/-- The original constructor tag and three field atoms. -/
theorem encode_pattern {n : ℕ} (C : PatternCode n) :
    @encode (PatternCode n) (@instEncodablePatternCode n) C =
      PrimitiveRationalPresentation.packCode (encode C.U) (encode C.r₁) (encode C.r₂) := rfl

/-- Parse the tagged structure, using the original component decoders. -/
def decodeTypedFields (n code : ℕ) : Option (TypedFields n) :=
  (PrimitiveRationalPresentation.decodeFields code).bind fun p =>
    (decode p.1).bind fun U =>
      (decode p.2.1).bind fun r₁ =>
        (decode p.2.2).map fun r₂ => (U, r₁, r₂)

section OriginalDerivedCodec

open private S S.nat S.cons S.encode S.decode S_equiv
  from Mathlib.Tactic.DeriveEncodable

private def fromS (n : ℕ) : S → Option (PatternCode n)
  | S.cons (S.nat 0)
      (S.cons (S.nat a) (S.cons (S.nat b) (S.cons (S.nat c) (S.nat 0)))) =>
    match decode a, decode b, decode c with
    | some U, some r₁, some r₂ => some ⟨U, r₁, r₂⟩
    | _, _, _ => none
  | _ => none

private theorem decode_eq_fromS (n code : ℕ) :
    @decode (PatternCode n) (@instEncodablePatternCode n) code =
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
  | nat a =>
    simp [decodeTypedFields, PrimitiveRationalPresentation.decodeFields,
      decodeField_encode, fromS]
  | cons tag rest =>
    cases tag with
    | cons a b =>
      simp [decodeTypedFields, PrimitiveRationalPresentation.decodeFields,
        decodeField_encode, fromS]
    | nat tag =>
      cases tag with
      | succ tag =>
        simp [decodeTypedFields, PrimitiveRationalPresentation.decodeFields,
          decodeField_encode, fromS]
      | zero =>
        cases rest with
        | nat a =>
          simp [decodeTypedFields, PrimitiveRationalPresentation.decodeFields,
            decodeField_encode, fromS]
        | cons a rest =>
          cases a with
          | cons x y =>
            simp [decodeTypedFields, PrimitiveRationalPresentation.decodeFields,
              decodeField_encode, fromS]
          | nat a =>
            cases rest with
            | nat b =>
              simp [decodeTypedFields, PrimitiveRationalPresentation.decodeFields,
                decodeField_encode, fromS]
            | cons b rest =>
              cases b with
              | cons x y =>
                simp [decodeTypedFields, PrimitiveRationalPresentation.decodeFields,
                  decodeField_encode, fromS]
              | nat b =>
                cases rest with
                | nat c =>
                  simp [decodeTypedFields, PrimitiveRationalPresentation.decodeFields,
                    decodeField_encode, fromS]
                | cons c rest =>
                  cases c with
                  | cons x y =>
                    simp [decodeTypedFields, PrimitiveRationalPresentation.decodeFields,
                      decodeField_encode, fromS]
                  | nat c =>
                    cases rest with
                    | cons x y =>
                      simp [decodeTypedFields, PrimitiveRationalPresentation.decodeFields,
                        decodeField_encode, sEncode_eq_zero, fromS]
                    | nat k =>
                      cases k with
                      | succ k =>
                        simp [decodeTypedFields, PrimitiveRationalPresentation.decodeFields,
                          decodeField_encode, sEncode_eq_zero, fromS]
                      | zero =>
                        cases ha : decode (α := Finset (Fin n)) a <;>
                          cases hb : decode (α := Fin n → Fin n → Bool) b <;>
                          cases hc : decode (α := Fin n → Fin n → Bool) c <;>
                          simp [decodeTypedFields, PrimitiveRationalPresentation.decodeFields,
                            decodeField_encode, sEncode_eq_zero, fromS,
                            ha, hb, hc, ofTypedFields]

/-- Exact behavior of the original derived decoder on every raw input. -/
theorem decode_pattern (n code : ℕ) :
    @decode (PatternCode n) (@instEncodablePatternCode n) code =
      (decodeTypedFields n code).map ofTypedFields := by
  rw [decode_eq_fromS, ← decodeTypedFields_encode]
  rw [show S.encode (S.decode code) = code from S_equiv.right_inv code]

end OriginalDerivedCodec

/-- The carrier with the proof that each label is below `n` erased. -/
def carrierView {n : ℕ} (U : Finset (Fin n)) : Finset ℕ :=
  U.map ⟨Fin.val, Fin.val_injective⟩

@[simp] theorem mem_carrierView {n : ℕ} (U : Finset (Fin n)) (i : Fin n) :
    i.val ∈ carrierView U ↔ i ∈ U := by
  simp [carrierView]

theorem carrierView_lt {n : ℕ} (U : Finset (Fin n)) {i : ℕ}
    (hi : i ∈ carrierView U) : i < n := by
  obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
  exact j.isLt

private theorem encode_list_fin_val {n : ℕ} (l : List (Fin n)) :
    encode (l.map Fin.val) = encode l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, encode_list_cons, encode_list_cons, ih]
    rfl

/-- Erasing finite-label bounds leaves the original carrier code unchanged. -/
theorem encode_carrierView {n : ℕ} (U : Finset (Fin n)) :
    encode (carrierView U) = encode U := by
  rw [encode_finset, encode_finset]
  have h : finsetView (carrierView U) = (finsetView U).map Fin.val := by
    exact (Finset.map_sort ⟨Fin.val, Fin.val_injective⟩ U codeLE codeLE
      (fun _ _ _ _ => Iff.rfl)).symm
  rw [h, encode_list_fin_val]

/-- A finite-label decoder whose output type does not depend on its bound. -/
def decodeLabel (n code : ℕ) : Option ℕ :=
  if code < n then some code else none

theorem decodeLabel_eq (n code : ℕ) :
    decodeLabel n code = (decode (α := Fin n) code).map Fin.val := by
  change (if code < n then some code else none) =
    ((((some code).bind fun a => if h : a < n then
      some (⟨a, h⟩ : {a : ℕ // a < n}) else none).bind
        fun a => some (Fin.equivSubtype.symm a))).map Fin.val
  by_cases h : code < n <;> simp [h]

theorem decodeLabel_primrec : Primrec₂ decodeLabel :=
  (Primrec.ite (Primrec.nat_lt.comp Primrec.snd Primrec.fst)
    (Primrec.option_some.comp Primrec.snd) (Primrec.const none)).to₂

/-- Decode the original carrier list, check duplicate-freedom, and store
the resulting finite set of natural labels. Its bound is an input. -/
def decodeCarrier (n code : ℕ) : Option (Finset ℕ) :=
  (decodeListWith (decodeLabel n) code).bind fun l =>
    if l.Nodup then some l.toFinset else none

/-- This raw carrier decoder has precisely the original decoder's
acceptance behavior, including unsorted, duplicate-free carrier lists. -/
theorem decodeCarrier_eq (n code : ℕ) :
    decodeCarrier n code =
      (decode (α := Finset (Fin n)) code).map carrierView := by
  unfold decodeCarrier
  have hlabel : decodeLabel n = fun c => (decode (α := Fin n) c).map Fin.val := by
    funext c
    exact decodeLabel_eq n c
  rw [hlabel, decodeListWith_map, PrimitiveFiniteData.decode_finset]
  cases h : decode (α := List (Fin n)) code with
  | none => rfl
  | some l =>
    by_cases hl : l.Nodup
    · simp only [Option.map_some, Option.bind_some,
        List.nodup_map_iff Fin.val_injective, hl, ↓reduceDIte, ↓reduceIte]
      congr 1
      ext i
      simp [carrierView]
    · simp [List.nodup_map_iff Fin.val_injective, hl]

theorem decodeCarrier_primrec : Primrec₂ decodeCarrier := by
  unfold decodeCarrier
  apply Primrec₂.mk
  refine Primrec.option_bind
    (decodeListWith_primrec
      (decodeLabel_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
      Primrec.snd) ?_
  exact (Primrec.ite (PrimitiveListData.list_nodup.comp Primrec.snd)
    (Primrec.option_some.comp (list_toFinset.comp Primrec.snd))
    (Primrec.const none)).to₂

/-- A successfully decoded raw carrier contains only labels below the
supplied bound. -/
theorem decodeCarrier_bounds {n code : ℕ} {U : Finset ℕ}
    (h : decodeCarrier n code = some U) : ∀ i ∈ U, i < n := by
  rw [decodeCarrier_eq] at h
  obtain ⟨V, _, rfl⟩ := Option.map_eq_some_iff.mp h
  exact fun _ hi => carrierView_lt V hi

/-- A fixed output type exposes variable-size carrier and table data. -/
abbrev Data := Finset ℕ × List (List Bool) × List (List Bool)

/-- All table entries are retained; carrier membership does not filter them. -/
def dataView {n : ℕ} (C : PatternCode n) : Data :=
  (carrierView C.U,
    List.ofFn (fun i => List.ofFn (C.r₁ i)),
    List.ofFn (fun i => List.ofFn (C.r₂ i)))

/-- The three original encoded fields are parsed into a uniform data type. -/
def decodeData (n code : ℕ) : Option Data :=
  (PrimitiveRationalPresentation.decodeFields code).bind fun p =>
    (decodeCarrier n p.1).bind fun U =>
      (decodeTable n p.2.1).bind fun r₁ =>
        (decodeTable n p.2.2).map fun r₂ => (U, r₁, r₂)

/-- Exact compatibility on all raw natural codes, with no canonical-input
precondition and no restriction to a fixed finite label bound. -/
theorem decodeData_eq (n code : ℕ) :
    decodeData n code =
      (@decode (PatternCode n) (@instEncodablePatternCode n) code).map dataView := by
  rw [decode_pattern]
  unfold decodeData decodeTypedFields
  cases hp : PrimitiveRationalPresentation.decodeFields code with
  | none => rfl
  | some p =>
    simp only [Option.bind_some, decodeCarrier_eq, decodeTable_eq]
    cases hU : decode (α := Finset (Fin n)) p.1 <;>
      cases h₁ : decode (α := Fin n → Fin n → Bool) p.2.1 <;>
      cases h₂ : decode (α := Fin n → Fin n → Bool) p.2.2 <;>
      rfl

@[simp] theorem decodeData_encode {n : ℕ} (C : PatternCode n) :
    decodeData n (encode C) = some (dataView C) := by
  rw [decodeData_eq, Encodable.encodek]
  rfl

/-- Success certifies the carrier bound and both dimensions of each
complete relation table. -/
theorem decodeData_bounds {n code : ℕ} {d : Data}
    (h : decodeData n code = some d) :
    (∀ i ∈ d.1, i < n) ∧
      d.2.1.length = n ∧ (∀ row ∈ d.2.1, row.length = n) ∧
      d.2.2.length = n ∧ (∀ row ∈ d.2.2, row.length = n) := by
  rw [decodeData_eq] at h
  obtain ⟨C, _, rfl⟩ := Option.map_eq_some_iff.mp h
  refine ⟨fun _ hi => carrierView_lt C.U hi, ?_⟩
  simp [dataView]

theorem decodeData_primrec : Primrec₂ decodeData := by
  unfold decodeData
  apply Primrec₂.mk
  refine Primrec.option_bind
    (PrimitiveRationalPresentation.decodeFields_primrec.comp Primrec.snd) ?_
  apply Primrec₂.mk
  refine Primrec.option_bind
    (decodeCarrier_primrec.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)) ?_
  apply Primrec₂.mk
  refine Primrec.option_bind
    (decodeTable_primrec.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))) ?_
  apply Primrec₂.mk
  refine Primrec.option_map
    (decodeTable_primrec.comp
      (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
        (Primrec.fst.comp Primrec.fst))))) ?_
  exact ((Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).pair
    ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)).to₂

/-- Packing the exposed data uses the original tagged structure format. -/
def encodeData (d : Data) : ℕ :=
  PrimitiveRationalPresentation.packCode (encode d.1)
    (encodeTableData d.2.1) (encodeTableData d.2.2)

theorem encodeData_dataView {n : ℕ} (C : PatternCode n) :
    encodeData (dataView C) = @encode (PatternCode n) (@instEncodablePatternCode n) C := by
  rw [encode_pattern]
  unfold encodeData dataView
  rw [encode_carrierView, ← encode_table, ← encode_table]

/-- The data view is lossless for the whole structure, including relation
entries outside the carrier. -/
theorem dataView_injective {n : ℕ} :
    Function.Injective (dataView (n := n)) := by
  intro C D h
  apply Encodable.encode_injective
  rw [← encodeData_dataView C, ← encodeData_dataView D, h]

theorem encodeData_primrec : Primrec encodeData :=
  PrimitiveRationalPresentation.packCode_primrec
    (Primrec.encode.comp Primrec.fst)
    (encodeTableData_primrec.comp (Primrec.fst.comp Primrec.snd))
    (encodeTableData_primrec.comp (Primrec.snd.comp Primrec.snd))

/-- Normalize the original code while retaining the complete tables. -/
def normalize (n code : ℕ) : Option ℕ :=
  (decodeData n code).map encodeData

/-- The result is exactly decoding and re-encoding with the preexisting
derived codec; malformed inputs return `none`. -/
theorem normalize_eq (n code : ℕ) :
    normalize n code =
      (@decode (PatternCode n) (@instEncodablePatternCode n) code).map
        (@encode (PatternCode n) (@instEncodablePatternCode n)) := by
  rw [normalize, decodeData_eq]
  cases decode (α := PatternCode n) code <;>
    simp only [Option.map_none, Option.map_some, encodeData_dataView]

/-- Encoding the normalized natural code is the original decoder's
encoded `Option` result. -/
theorem encode_normalize (n code : ℕ) :
    encode (normalize n code) =
      @encode (Option (PatternCode n))
        (@Option.encodable (PatternCode n) (@instEncodablePatternCode n))
        (@decode (PatternCode n) (@instEncodablePatternCode n) code) := by
  rw [normalize_eq]
  cases decode (α := PatternCode n) code <;> rfl

theorem normalize_primrec : Primrec₂ normalize :=
  (Primrec.option_map decodeData_primrec
    (encodeData_primrec.comp Primrec.snd).to₂).to₂

/-- Fixing one input of the uniform algorithm certifies the encoded
output of that bound's original decoder. -/
theorem encoded_decode_primrec (n : ℕ) : Primrec (fun code : ℕ =>
    @encode (Option (PatternCode n))
      (@Option.encodable (PatternCode n) (@instEncodablePatternCode n))
      (@decode (PatternCode n) (@instEncodablePatternCode n) code)) :=
  (Primrec.encode.comp
    (normalize_primrec.comp (Primrec.const n) Primrec.id)).of_eq
      (encode_normalize n)

/-- The primitive coding certificate reuses exactly the original derived
encoder and decoder. -/
instance instPrimcodablePatternCode (n : ℕ) : Primcodable (PatternCode n) where
  toEncodable := @instEncodablePatternCode n
  prim := Primrec.nat_iff.mp (encoded_decode_primrec n)

@[simp] theorem pattern_encoding_unchanged (n : ℕ) :
    (instPrimcodablePatternCode n).toEncodable = @instEncodablePatternCode n := rfl

@[simp] theorem normalize_encode {n : ℕ} (C : PatternCode n) :
    normalize n (encode C) = some (encode C) := by
  rw [normalize_eq, Encodable.encodek]
  rfl

/-- A primitive carrier membership test on the uniform data view. -/
def carrierMem (d : Data) (i : ℕ) : Bool := decide (i ∈ d.1)

theorem carrierMem_primrec : Primrec₂ carrierMem :=
  (PrimitiveFiniteData.finset_mem.comp Primrec.snd
    (Primrec.fst.comp Primrec.fst)).decide.to₂

@[simp] theorem carrierMem_dataView {n : ℕ} (C : PatternCode n) (i : Fin n) :
    carrierMem (dataView C) i.val = decide (i ∈ C.U) := by
  simp [carrierMem, dataView]

/-- A checked lookup in a complete raw table. Out-of-range indices return
`none`; no carrier test changes a stored Boolean entry. -/
def tableLookup (table : List (List Bool)) (ij : ℕ × ℕ) : Option Bool :=
  (table[ij.1]?).bind fun row => row[ij.2]?

theorem tableLookup_primrec : Primrec₂ tableLookup :=
  (Primrec.option_bind
    (Primrec.list_getElem?.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
    (Primrec.list_getElem?.comp Primrec.snd
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).to₂).to₂

@[simp] theorem tableLookup_ofFn {n : ℕ} (f : Fin n → Fin n → Bool)
    (i j : Fin n) :
    tableLookup (List.ofFn (fun x => List.ofFn (f x))) (i.val, j.val) =
      some (f i j) := by
  simp [tableLookup]

/-- First-table lookup uses both supplied natural indices. -/
def relation₁ (d : Data) (ij : ℕ × ℕ) : Option Bool := tableLookup d.2.1 ij

/-- Second-table lookup retains all off-carrier table entries. -/
def relation₂ (d : Data) (ij : ℕ × ℕ) : Option Bool := tableLookup d.2.2 ij

theorem relation₁_primrec : Primrec₂ relation₁ :=
  (tableLookup_primrec.comp
    (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd).to₂

theorem relation₂_primrec : Primrec₂ relation₂ :=
  (tableLookup_primrec.comp
    (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd).to₂

@[simp] theorem relation₁_dataView {n : ℕ} (C : PatternCode n) (i j : Fin n) :
    relation₁ (dataView C) (i.val, j.val) = some (C.r₁ i j) :=
  tableLookup_ofFn _ i j

@[simp] theorem relation₂_dataView {n : ℕ} (C : PatternCode n) (i j : Fin n) :
    relation₂ (dataView C) (i.val, j.val) = some (C.r₂ i j) :=
  tableLookup_ofFn _ i j

/-- One machine decodes the original finite pattern encoding for every
input label bound, including malformed raw codes. -/
theorem pattern_decode_program : ∃ c : Nat.Partrec.Code, ∀ n code : ℕ,
    c.eval (Nat.pair n code) = Part.some
      (@encode (Option (PatternCode n))
        (@Option.encodable (PatternCode n) (@instEncodablePatternCode n))
        (@decode (PatternCode n) (@instEncodablePatternCode n) code)) := by
  obtain ⟨c, hc⟩ := PrimitiveRationalPresentation.exists_code normalize_primrec
  exact ⟨c, fun n code =>
    (hc (n, code)).trans (congrArg Part.some (encode_normalize n code))⟩

end Alexander313.Carlson.PrimitivePatternCode
