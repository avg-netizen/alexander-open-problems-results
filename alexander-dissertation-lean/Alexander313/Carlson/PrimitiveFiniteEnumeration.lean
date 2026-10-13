import Alexander313.Carlson.PrimitiveEmbeddingChecks

/-!
# Uniform finite competitors for exhaustive minimality

Repeated finite products enumerate complete Boolean tables and total maps.
The lengths are machine inputs, and the enumeration itself is primitive
recursive. Pattern competitors use the supplied carrier and retain every
off-carrier relation entry. Their natural codes use the original tagged
pattern and finite-function encoders.

The completeness lemmas cover every original finite pattern with that
carrier and every total map. Downstream checks still decode each candidate,
so soundness never depends on trusting an unverified enumeration entry.
-/

namespace Alexander313.Carlson.PrimitiveFiniteEnumeration

open Encodable Finite PrimitivePatternCode PrimitiveFiniteFunctions
open PrimitiveEmbeddingChecks (mapView)

variable {α : Type*}

/-- Prepend each alphabet element to every already enumerated suffix. -/
def prependAll (alphabet : List α) (tails : List (List α)) : List (List α) :=
  alphabet.flatMap fun a => tails.map (List.cons a)

/-- All lists of the supplied length over the supplied finite alphabet. -/
def listsOfLength (alphabet : List α) : ℕ → List (List α)
  | 0 => [[]]
  | n + 1 => prependAll alphabet (listsOfLength alphabet n)

theorem prependAll_primrec [Primcodable α] : Primrec₂ (@prependAll α) := by
  apply Primrec₂.mk
  unfold prependAll
  refine Primrec.list_flatMap Primrec.fst ?_
  apply Primrec₂.mk
  refine Primrec.list_map (Primrec.snd.comp Primrec.fst) ?_
  exact (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂

theorem listsOfLength_primrec [Primcodable α] : Primrec₂ (@listsOfLength α) := by
  have hstep : Primrec₂ (fun (alphabet : List α) (p : ℕ × List (List α)) =>
      prependAll alphabet p.2) :=
    (prependAll_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.nat_rec (Primrec.const ([[]] : List (List α))) hstep).of_eq
    fun alphabet n => by
      induction n with
      | zero => rfl
      | succ n ih => simpa only [listsOfLength, Nat.rec_add_one, ih]

/-- Membership characterizes both the exact length and every entry. -/
theorem mem_listsOfLength (alphabet : List α) (n : ℕ) (l : List α) :
    l ∈ listsOfLength alphabet n ↔ l.length = n ∧ ∀ a ∈ l, a ∈ alphabet := by
  induction n generalizing l with
  | zero => cases l <;> simp [listsOfLength]
  | succ n ih =>
      cases l with
      | nil => simp [listsOfLength, prependAll]
      | cons a l =>
          simp [listsOfLength, prependAll, ih, and_assoc, and_left_comm, and_comm]

theorem ofFn_mem_listsOfLength {n : ℕ} (alphabet : List α) (f : Fin n → α)
    (hf : ∀ i, f i ∈ alphabet) :
    List.ofFn f ∈ listsOfLength alphabet n := by
  apply (mem_listsOfLength alphabet n _).mpr
  refine ⟨List.length_ofFn, ?_⟩
  intro a ha
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
  exact hf i

/-- Every square Boolean table, including its off-carrier entries. -/
def tables (n : ℕ) : List (List (List Bool)) :=
  listsOfLength (listsOfLength [false, true] n) n

theorem tables_primrec : Primrec tables :=
  listsOfLength_primrec.comp
    (listsOfLength_primrec.comp (Primrec.const [false, true]) Primrec.id) Primrec.id

theorem table_mem {n : ℕ} (r : Fin n → Fin n → Bool) :
    List.ofFn (fun i => List.ofFn (r i)) ∈ tables n := by
  apply ofFn_mem_listsOfLength
  intro i
  apply ofFn_mem_listsOfLength
  intro j
  cases r i j <;> simp

/-- Original pattern codes for every pair of complete tables on a fixed carrier. -/
def patternCodes (n : ℕ) (U : Finset ℕ) : List ℕ :=
  (tables n).flatMap fun r₁ =>
    (tables n).map fun r₂ => encodeData (U, r₁, r₂)

theorem patternCodes_primrec : Primrec₂ patternCodes := by
  apply Primrec₂.mk
  unfold patternCodes
  refine Primrec.list_flatMap (tables_primrec.comp Primrec.fst) ?_
  apply Primrec₂.mk
  refine Primrec.list_map (tables_primrec.comp (Primrec.fst.comp Primrec.fst)) ?_
  apply Primrec₂.mk
  exact encodeData_primrec.comp
    ((Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).pair
      ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))

/-- Exhaustiveness concerns the original encoder, not a replacement codec. -/
theorem encode_mem_patternCodes {n : ℕ} (C : PatternCode n) :
    encode C ∈ patternCodes n (carrierView C.U) := by
  apply List.mem_flatMap.mpr
  refine ⟨List.ofFn (fun i => List.ofFn (C.r₁ i)), table_mem C.r₁, ?_⟩
  apply List.mem_map.mpr
  refine ⟨List.ofFn (fun i => List.ofFn (C.r₂ i)), table_mem C.r₂, ?_⟩
  exact encodeData_dataView C

/-- Total-map competitors retain every source label, even away from its carrier. -/
def mapCodes (n m : ℕ) : List ℕ :=
  (listsOfLength (List.range m) n).map encodeArrowData

theorem mapCodes_primrec : Primrec₂ mapCodes := by
  apply Primrec₂.mk
  unfold mapCodes
  refine Primrec.list_map
    (listsOfLength_primrec.comp (Primrec.list_range.comp Primrec.snd) Primrec.fst) ?_
  exact (encodeArrowData_primrec.comp Primrec.snd).to₂

theorem mapView_mem {n m : ℕ} (f : Fin n → Fin m) :
    mapView f ∈ listsOfLength (List.range m) n := by
  apply ofFn_mem_listsOfLength
  intro i
  exact List.mem_range.mpr (f i).isLt

theorem encode_mem_mapCodes {n m : ℕ} (f : Fin n → Fin m) :
    encode f ∈ mapCodes n m := by
  apply List.mem_map.mpr
  refine ⟨mapView f, mapView_mem f, ?_⟩
  have hval : (fun i : Fin n => encode (f i)) = (fun i => (f i).val) := by
    funext i
    rfl
  simpa only [hval, mapView] using (encode_arrow f).symm

/-- The empty-domain case has its unique total map even when the codomain is empty. -/
theorem mapCodes_zero (m : ℕ) : mapCodes 0 m = [0] := by
  simp [mapCodes, listsOfLength, encodeArrowData]

/-- A nonempty domain has no maps to an empty codomain. -/
theorem mapCodes_succ_zero (n : ℕ) : mapCodes (n + 1) 0 = [] := by
  simp [mapCodes, listsOfLength, prependAll]

end Alexander313.Carlson.PrimitiveFiniteEnumeration
