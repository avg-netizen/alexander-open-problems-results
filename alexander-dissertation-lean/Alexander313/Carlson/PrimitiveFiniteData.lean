import Alexander313.Carlson.PrimitiveListData
import Mathlib.Logic.Equiv.Finset

/-!
# Primitive-recursive finite data with the existing encodings

The ordinary multiset encoding sorts its elements by their natural-number
codes. Its decoder accepts every successfully decoded list, so decoding and
re-encoding must actually sort the list. The ordinary finite-set decoder also
checks for duplicates; it accepts unsorted lists without duplicates.

The `Primcodable` instances below certify precisely those existing encodings.
They do not use the different denumerable multiset or finite-set encodings.
Canonical sorted-list views and their inverses connect finite data to the
primitive-recursive list operations.
-/

namespace Alexander313.Carlson.PrimitiveFiniteData

open Encodable

variable {α : Type*} [Primcodable α]

/-- The comparison used by the ordinary multiset and finite-set encoders. -/
def codeLE (a b : α) : Prop := encode a ≤ encode b

instance codeLE_decidable : DecidableRel (@codeLE α _) :=
  fun a b => inferInstanceAs (Decidable (encode a ≤ encode b))

instance codeLE_isLinearOrder : IsLinearOrder α (@codeLE α _) :=
  (RelEmbedding.preimage ⟨encode, encode_injective⟩ (· ≤ ·)).isLinearOrder

theorem codeLE_primrec : PrimrecRel (@codeLE α _) :=
  Primrec.nat_le.comp (Primrec.encode.comp Primrec.fst) (Primrec.encode.comp Primrec.snd)

/-- Sort a list by the exact comparison used in the stored finite codes. -/
def sortCodes (l : List α) : List α :=
  l.mergeSort (fun a b => decide (codeLE a b))

theorem sortCodes_primrec : Primrec (@sortCodes α _) :=
  PrimitiveListData.mergeSort codeLE_primrec

/-- The canonical list underlying the ordinary multiset encoding. -/
def multisetView (s : Multiset α) : List α := s.sort codeLE

@[simp] theorem multisetView_coe (l : List α) : multisetView (l : Multiset α) = sortCodes l :=
  rfl

@[simp] theorem coe_multisetView (s : Multiset α) : (multisetView s : Multiset α) = s :=
  Multiset.sort_eq s codeLE

@[simp] theorem mem_multisetView (a : α) (s : Multiset α) : a ∈ multisetView s ↔ a ∈ s :=
  Multiset.mem_sort codeLE

@[simp] theorem length_multisetView (s : Multiset α) : (multisetView s).length = s.card :=
  Multiset.length_sort codeLE

/-- Capture the existing multiset encoding before adding its certificate. -/
@[reducible] def multisetEncodable : Encodable (Multiset α) := Multiset.encodable

theorem encode_multiset (s : Multiset α) :
    @encode (Multiset α) multisetEncodable s = encode (multisetView s) := rfl

theorem decode_multiset (n : ℕ) :
    @decode (Multiset α) multisetEncodable n =
      (decode n : Option (List α)).map (fun l : List α => (l : Multiset α)) := rfl

/-- A raw multiset code is decoded as a list and then sorted on re-encoding.
Accepted noncanonical lists are preserved as multisets, not rejected. -/
theorem encode_decode_multiset (n : ℕ) :
    @encode (Option (Multiset α)) (@Option.encodable (Multiset α) multisetEncodable)
      (@decode (Multiset α) multisetEncodable n) =
        encode ((decode n : Option (List α)).map sortCodes) := by
  rw [decode_multiset]
  cases h : (decode n : Option (List α)) with
  | none => rfl
  | some l =>
      simp only [Option.map_some, Encodable.encode_some, encode_multiset, multisetView_coe]

/-- Primitive recursiveness of the ordinary multiset code normalization. -/
instance instPrimcodableMultiset : Primcodable (Multiset α) where
  toEncodable := multisetEncodable
  prim := (Primrec.nat_iff.mp (Primrec.encode.comp
    (Primrec.option_map Primrec.decode (sortCodes_primrec.comp Primrec.snd).to₂))).of_eq
      fun n => (encode_decode_multiset n).symm

@[simp] theorem multiset_encoding_unchanged :
    (instPrimcodableMultiset (α := α)).toEncodable = Multiset.encodable := rfl

/-- The canonical list can be recovered by the ordinary list decoder. -/
theorem decode_encode_multisetView (s : Multiset α) :
    (decode (encode s) : Option (List α)) = some (multisetView s) := by
  rw [encode_multiset, Encodable.encodek]

theorem multisetView_primrec : Primrec (@multisetView α _) :=
  Primrec.option_some_iff.mp
    (((@Primrec.decode (List α) _).comp Primrec.encode).of_eq decode_encode_multisetView)

/-- Passing from a list to its multiset is primitive recursive. -/
theorem list_toMultiset : Primrec (fun l : List α => (l : Multiset α)) :=
  Primrec.encode_iff.mp
    ((Primrec.encode.comp sortCodes_primrec).of_eq fun l =>
      (encode_multiset (l : Multiset α)).symm)

theorem multiset_nodup : PrimrecPred (@Multiset.Nodup α) :=
  (PrimitiveListData.list_nodup.comp multisetView_primrec).of_eq fun s => by
    rw [← Multiset.coe_nodup, coe_multisetView]

/-- The record equivalence used by the ordinary finite-set encoding. -/
def finsetEquiv : Finset α ≃ {s : Multiset α // s.Nodup} where
  toFun := fun ⟨s, hs⟩ => ⟨s, hs⟩
  invFun := fun ⟨s, hs⟩ => ⟨s, hs⟩

@[reducible] def finsetEncodable : Encodable (Finset α) := Finset.encodable

/-- Certify the existing finite-set encoding through its nodup-multiset
subtype, keeping the original encoder and decoder definitionally unchanged. -/
instance instPrimcodableFinset : Primcodable (Finset α) :=
  letI := Encodable.decidableEqOfEncodable α
  letI : Primcodable {s : Multiset α // s.Nodup} := Primcodable.subtype multiset_nodup
  { toEncodable := finsetEncodable
    prim := (Primcodable.ofEquiv {s : Multiset α // s.Nodup} finsetEquiv).prim }

@[simp] theorem finset_encoding_unchanged :
    (instPrimcodableFinset (α := α)).toEncodable = Finset.encodable := rfl

/-- A finite set's canonical list is sorted by element codes. -/
def finsetView (s : Finset α) : List α := multisetView s.val

theorem encode_finset (s : Finset α) : encode s = encode (finsetView s) := rfl

theorem finset_val : Primrec (fun s : Finset α => s.val) :=
  Primrec.encode_iff.mp (Primrec.encode.of_eq fun _ => rfl)

theorem finsetView_primrec : Primrec (@finsetView α _) :=
  multisetView_primrec.comp finset_val

@[simp] theorem mem_finsetView (a : α) (s : Finset α) : a ∈ finsetView s ↔ a ∈ s :=
  Finset.mem_sort codeLE

@[simp] theorem length_finsetView (s : Finset α) : (finsetView s).length = s.card :=
  Finset.length_sort codeLE

@[simp] theorem finsetView_nodup (s : Finset α) : (finsetView s).Nodup :=
  Finset.sort_nodup s codeLE

@[simp] theorem finsetView_toFinset [DecidableEq α] (s : Finset α) :
    (finsetView s).toFinset = s :=
  Finset.sort_toFinset s codeLE

/-- Sorting the duplicate-free list gives exactly the encoded finite set. -/
theorem finsetView_ofList [DecidableEq α] (l : List α) :
    finsetView l.toFinset = sortCodes l.dedup := rfl

/-- Ordinary list-to-finset conversion is primitive recursive, including
its duplicate removal and the canonical sorting performed by the encoder. -/
theorem list_toFinset [DecidableEq α] : Primrec (@List.toFinset α _) :=
  Primrec.encode_iff.mp
    ((Primrec.encode.comp (sortCodes_primrec.comp PrimitiveListData.list_dedup)).of_eq
      fun l => by rw [encode_finset, finsetView_ofList])

theorem finset_mem : PrimrecRel (fun (a : α) (s : Finset α) => a ∈ s) :=
  (PrimitiveListData.list_mem.comp Primrec.fst (finsetView_primrec.comp Primrec.snd)).of_eq
    fun p => mem_finsetView p.1 p.2

section Decoder

attribute [local instance] Encodable.decidableEqOfEncodable

/-- On every natural input, the ordinary finite-set decoder first decodes a
list and checks only for duplicates. Sorting is not a precondition for success. -/
theorem decode_finset (n : ℕ) :
    (decode n : Option (Finset α)) =
      (decode n : Option (List α)).bind
        (fun l : List α => if h : l.Nodup then
          some (⟨(l : Multiset α), Multiset.coe_nodup.mpr h⟩ : Finset α)
        else none) := by
  simp only [Encodable.decode_ofEquiv]
  dsimp only [Encodable.decode, Subtype.encodable, Encodable.decodeSubtype,
    Multiset.encodable, decodeMultiset]
  cases (decodeList n : Option (List α)) with
  | none => simp
  | some l =>
      by_cases hl : l.Nodup <;> simp [hl]

/-- An encoded list is accepted as a finite set exactly when it has no
duplicates; its original order does not affect decoder acceptance. -/
theorem decode_finset_encode_list (l : List α) :
    (decode (encode l) : Option (Finset α)) =
      if h : l.Nodup then
        some (⟨(l : Multiset α), Multiset.coe_nodup.mpr h⟩ : Finset α)
      else none := by
  rw [decode_finset, Encodable.encodek, Option.bind_some]

/-- Decode-and-re-encode for the existing finite-set encoding rejects failed
list decodes and duplicates, and sorts every accepted list by its element codes. -/
theorem encode_decode_finset (n : ℕ) :
    encode (decode n : Option (Finset α)) =
      encode ((decode n : Option (List α)).bind
        (fun l : List α => if l.Nodup then some (sortCodes l) else none)) := by
  rw [decode_finset]
  cases h : (decode n : Option (List α)) with
  | none => rfl
  | some l =>
      by_cases hl : l.Nodup <;>
        simp [hl, encode_finset, finsetView]

end Decoder

end Alexander313.Carlson.PrimitiveFiniteData
