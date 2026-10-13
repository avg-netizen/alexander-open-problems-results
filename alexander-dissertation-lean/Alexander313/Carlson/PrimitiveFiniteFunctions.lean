import Mathlib.Computability.Primrec.List
import Mathlib.Computability.PartrecCode

/-!
# Uniform primitive recursive finite-function codes

The original inferred `Encodable.finPi` instance stores a function on
`Fin n` as a list of index-tagged values. Its decoder checks the list length,
every index bound, and agreement of the stored indices with their positions.
Here the dimension and raw code are both machine inputs. Component decoders
may also vary with a coded parameter, allowing nested finite function spaces
whose domains grow with the same input.

The list traversal below preserves every component decoder, including its
normalization of accepted noncanonical codes. Its correctness statements
refer to the original encodings; no replacement instance is installed.
-/

namespace Alexander313.Carlson.PrimitiveFiniteFunctions

open Encodable

variable {α β σ : Type*}

/-- Read the original natural list skeleton and apply the supplied component
decoder. A failed component rejects the whole list. -/
def decodeListWith (d : ℕ → Option α) (code : ℕ) : Option (List α) :=
  (Denumerable.ofNat (List ℕ) code).foldr
    (fun c tail => (d c).bind fun a => tail.map (List.cons a)) (some [])

@[simp] theorem decodeListWith_zero (d : ℕ → Option α) :
    decodeListWith d 0 = some [] := by
  simp [decodeListWith]

theorem decodeListWith_succ (d : ℕ → Option α) (code : ℕ) :
    decodeListWith d (code + 1) =
      (d code.unpair.1).bind fun a =>
        (decodeListWith d code.unpair.2).map (List.cons a) := by
  simp [decodeListWith]

/-- List decoding commutes with any supplied observation of the decoded
components. This statement does not assume a primitive coding instance. -/
theorem decodeListWith_map [Encodable β] (f : β → α) (code : ℕ) :
    decodeListWith (fun c => (decode (α := β) c).map f) code =
      (decode (α := List β) code).map (List.map f) := by
  induction code using Nat.case_strong_induction_on with
  | hz => simp
  | hi code ih =>
      rw [decodeListWith_succ, decode_list_succ,
        ih _ (Nat.unpair_right_le code)]
      cases decode (α := β) code.unpair.1 <;>
        cases decode (α := List β) code.unpair.2 <;> rfl

/-- The componentwise traversal is exactly the preexisting list decoder. -/
theorem decodeListWith_decode [Encodable α] (code : ℕ) :
    decodeListWith (decode (α := α)) code = decode (α := List α) code := by
  simpa using decodeListWith_map (α := α) (β := α) id code

/-- A single primitive recursive traversal handles a varying input code
and a uniformly primitive recursive family of component decoders. -/
theorem decodeListWith_primrec [Primcodable σ] [Primcodable α]
    {d : σ → ℕ → Option α} {code : σ → ℕ}
    (hd : Primrec₂ d) (hc : Primrec code) :
    Primrec (fun x => decodeListWith (d x) (code x)) := by
  unfold decodeListWith
  refine Primrec.list_foldr
    (h := fun (x : σ) (p : ℕ × Option (List α)) =>
      (d x p.1).bind fun a => p.2.map (List.cons a))
    ((Primrec.ofNat (List ℕ)).comp hc)
    (Primrec.const (some ([] : List α))) ?_
  apply Primrec₂.mk
  refine Primrec.option_bind
    (hd.comp Primrec.fst (Primrec.fst.comp Primrec.snd)) ?_
  apply Primrec₂.mk
  exact Primrec.option_map
    (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
    (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂

/-- The list representation of a finite function is accepted precisely
when its decoded length matches the supplied domain size. -/
def decodeVectorWith (d : ℕ → Option α) (n code : ℕ) : Option (List α) :=
  (decodeListWith d code).bind fun l =>
    if l.length = n then some l else none

/-- The explicit vector-instance encoder stores exactly its list of values. -/
theorem encode_vector [Encodable α] {n : ℕ} (f : Fin n → α) :
    @encode (Fin n → α) Encodable.finArrow f = encode (List.ofFn f) := by
  change encode (List.Vector.ofFn f).toList = _
  rw [List.Vector.toList_ofFn]

private theorem ofFn_vector_get {n : ℕ} (v : List.Vector α n) :
    List.ofFn v.get = v.toList := by
  rw [← List.Vector.toList_ofFn, List.Vector.ofFn_get]

/-- Exact raw-input behavior of the explicit vector-instance decoder,
including failed component decoding and incorrect lengths. -/
theorem decodeVectorWith_decode [Encodable α] (n code : ℕ) :
    decodeVectorWith (decode (α := α)) n code =
      (@decode (Fin n → α) Encodable.finArrow code).map List.ofFn := by
  unfold decodeVectorWith
  rw [decodeListWith_decode]
  change (decode (α := List α) code).bind
      (fun l => if l.length = n then some l else none) =
    (((decode (α := List α) code).bind fun l =>
      if h : l.length = n then some (⟨l, h⟩ : List.Vector α n) else none).bind
        (fun v => some (List.Vector.get v))).map List.ofFn
  cases decode (α := List α) code with
  | none => rfl
  | some l =>
      by_cases h : l.length = n <;> simp [h, ofFn_vector_get]

/-- Finite-function decoding followed by an observation of each value.
The domain size remains a free natural-number input. -/
theorem decodeVectorWith_map [Encodable β] (f : β → α) (n code : ℕ) :
    decodeVectorWith (fun c => (decode (α := β) c).map f) n code =
      (@decode (Fin n → β) Encodable.finArrow code).map
        (fun g => List.ofFn (fun i => f (g i))) := by
  have hmap :
      (@decode (Fin n → β) Encodable.finArrow code).map
          (fun g => List.ofFn (fun i => f (g i))) =
        ((@decode (Fin n → β) Encodable.finArrow code).map List.ofFn).map (List.map f) := by
    simp only [Option.map_map, List.map_ofFn, Function.comp_def]
  rw [hmap, ← decodeVectorWith_decode]
  unfold decodeVectorWith
  rw [decodeListWith_map, decodeListWith_decode]
  cases decode (α := List β) code with
  | none => rfl
  | some l =>
      by_cases h : l.length = n <;> simp [h]

/-- Varying finite domains and varying component decoders share one
primitive recursive finite-function decoding operation. -/
theorem decodeVectorWith_primrec [Primcodable σ] [Primcodable α]
    {d : σ → ℕ → Option α} {n code : σ → ℕ}
    (hd : Primrec₂ d) (hn : Primrec n) (hc : Primrec code) :
    Primrec (fun x => decodeVectorWith (d x) (n x) (code x)) := by
  unfold decodeVectorWith
  refine Primrec.option_bind (decodeListWith_primrec hd hc) ?_
  apply Primrec₂.mk
  exact Primrec.ite
    (Primrec.eq.comp (Primrec.list_length.comp Primrec.snd) (hn.comp Primrec.fst))
    (Primrec.option_some.comp Primrec.snd) (Primrec.const none)

/-- Mapping values without changing their codes preserves the list code. -/
theorem encode_list_map [Encodable α] [Encodable β] (f : α → β)
    (hf : ∀ a, encode (f a) = encode a) (l : List α) :
    encode (l.map f) = encode l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, encode_list_cons, hf, ih]

def encodeArrowData (l : List ℕ) : ℕ :=
  encode ((List.range l.length).map fun i => Nat.pair i ((l[i]?).getD 0))

theorem encodeArrowData_primrec : Primrec encodeArrowData := by
  unfold encodeArrowData
  apply Primrec.encode.comp
  refine Primrec.list_map (Primrec.list_range.comp Primrec.list_length) ?_
  exact (Primrec₂.natPair.comp Primrec.snd
    (Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.fst Primrec.snd)
      (Primrec.const 0))).to₂

theorem encodeArrowData_ofFn {n : ℕ} (f : Fin n → ℕ) :
    encodeArrowData (List.ofFn f) =
      encode (List.ofFn fun i => Nat.pair i.val (f i)) := by
  unfold encodeArrowData
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have h : i < n := by simpa using hj
    simp [h, List.getElem?_ofFn]

theorem encode_arrow {α : Type*} [Encodable α] {n : ℕ} (f : Fin n → α) :
    encode f = encodeArrowData (List.ofFn (fun i => encode (f i))) := by
  rw [encodeArrowData_ofFn]
  change encode (List.Vector.ofFn
      (fun i : Fin n => (⟨i, f i⟩ : Σ _ : Fin n, α))).toList = _
  rw [List.Vector.toList_ofFn]
  have h := encode_list_map encode (fun (_ : Σ _ : Fin n, α) => rfl)
    (List.ofFn fun i : Fin n => (⟨i, f i⟩ : Σ _ : Fin n, α))
  rw [List.map_ofFn] at h
  exact h.symm

def encodeTableData (table : List (List Bool)) : ℕ :=
  encodeArrowData (table.map fun row => encodeArrowData (row.map encode))

theorem encodeTableData_primrec : Primrec encodeTableData := by
  unfold encodeTableData
  apply encodeArrowData_primrec.comp
  refine Primrec.list_map Primrec.id ?_
  exact (encodeArrowData_primrec.comp
    (Primrec.list_map Primrec.snd (Primrec.encode.comp Primrec.snd).to₂)).to₂

theorem encode_table {n : ℕ} (f : Fin n → Fin n → Bool) :
    encode f = encodeTableData (List.ofFn (fun i => List.ofFn (f i))) := by
  rw [encode_arrow]
  unfold encodeTableData
  congr 1
  rw [List.map_ofFn]
  congr 1
  funext i
  simpa only [Function.comp_apply, List.map_ofFn, Function.comp_def] using encode_arrow (f i)


private theorem inverse_section (n : ℕ) (g : Fin n → (Σ _ : Fin n, α))
    (h : ∀ i, (g i).1 = i) :
    (Equiv.piEquivSubtypeSigma (Fin n) (fun _ => α)).symm ⟨g, h⟩ =
      fun i => (g i).2 := by
  apply (Equiv.piEquivSubtypeSigma (Fin n) (fun _ => α)).injective
  rw [Equiv.apply_symm_apply]
  apply Subtype.ext
  funext i
  apply Sigma.ext (h i)
  rfl

/-- The existing inferred function decoder first decodes a vector of
dependent pairs, then verifies that the stored indices are a section. -/
theorem decode_finPi [Encodable α] (n code : ℕ) :
    @decode (Fin n → α) (Encodable.finPi n (fun _ => α)) code =
      (@decode (Fin n → (Σ _ : Fin n, α)) Encodable.finArrow code).bind
        (fun g => if ∀ i, (g i).1 = i then some (fun i => (g i).2) else none) := by
  change (((@decode (Fin n → (Σ _ : Fin n, α)) Encodable.finArrow code).bind
    (fun g => if h : ∀ i, (g i).1 = i then
      some (⟨g, h⟩ : {g : Fin n → (Σ _ : Fin n, α) // ∀ i, (g i).1 = i}) else none)).bind
    (fun g => some ((Equiv.piEquivSubtypeSigma (Fin n) (fun _ => α)).symm g))) = _
  cases hd : @decode (Fin n → (Σ _ : Fin n, α)) Encodable.finArrow code with
  | none => rfl
  | some g =>
    by_cases h : ∀ i, (g i).1 = i <;> simp [h, inverse_section]

/-- The original finite-index decoder checks the supplied natural bound. -/
theorem decode_fin (n code : ℕ) :
    decode (α := Fin n) code = if h : code < n then some ⟨code, h⟩ else none := by
  change (((some code).bind fun a => if h : a < n then
    some (⟨a, h⟩ : {a : ℕ // a < n}) else none).bind
      fun a => some (Fin.equivSubtype.symm a)) = _
  by_cases h : code < n <;> simp [h]

/-- Decode one original index-tagged component, retaining its index as
ordinary natural data and rejecting every out-of-bounds tag. -/
def decodeTaggedWith (d : ℕ → Option α) (n code : ℕ) : Option (ℕ × α) :=
  if code.unpair.1 < n then
    (d code.unpair.2).map fun a => (code.unpair.1, a)
  else none

theorem decodeTaggedWith_map [Encodable β] (f : β → α) (n code : ℕ) :
    decodeTaggedWith (fun c => (decode (α := β) c).map f) n code =
      (decode (α := Σ _ : Fin n, β) code).map fun p => (p.1.val, f p.2) := by
  rw [decode_sigma_val, decode_fin]
  by_cases h : code.unpair.1 < n <;>
    cases hd : decode (α := β) code.unpair.2 <;> simp [decodeTaggedWith, h, hd]

theorem decodeTaggedWith_primrec [Primcodable σ] [Primcodable α]
    {d : σ → ℕ → Option α} {n code : σ → ℕ}
    (hd : Primrec₂ d) (hn : Primrec n) (hc : Primrec code) :
    Primrec (fun x => decodeTaggedWith (d x) (n x) (code x)) := by
  unfold decodeTaggedWith
  refine Primrec.ite
    (Primrec.nat_lt.comp (Primrec.fst.comp (Primrec.unpair.comp hc)) hn)
    ?_ (Primrec.const none)
  exact Primrec.option_map
    (hd.comp Primrec.id (Primrec.snd.comp (Primrec.unpair.comp hc)))
    (((Primrec.fst.comp (Primrec.unpair.comp hc)).comp Primrec.fst).pair
      Primrec.snd).to₂

/-- Decode the original inferred finite-function code, checking both the
dimension and that every stored index agrees with its list position. -/
def decodeArrowWith (d : ℕ → Option α) (n code : ℕ) : Option (List α) :=
  (decodeVectorWith (decodeTaggedWith d n) n code).bind fun l =>
    if l.map Prod.fst = List.range n then some (l.map Prod.snd) else none

private theorem ofFn_val (n : ℕ) :
    List.ofFn (fun i : Fin n => i.val) = List.range n := by
  apply List.ext_getElem <;> simp

private theorem tags_eq_range_iff {n : ℕ} (g : Fin n → (Σ _ : Fin n, β)) :
    (List.ofFn (fun i => ((g i).1.val, (g i).2))).map Prod.fst = List.range n ↔
      ∀ i, (g i).1 = i := by
  rw [List.map_ofFn, ← ofFn_val, List.ofFn_inj]
  constructor
  · intro h i
    exact Fin.ext (congrFun h i)
  · intro h
    funext i
    exact congrArg Fin.val (h i)

/-- Exact arbitrary-input behavior of the original inferred finite-function
decoder, followed by an observation of each decoded component. -/
theorem decodeArrowWith_map [Encodable β] (f : β → α) (n code : ℕ) :
    decodeArrowWith (fun c => (decode (α := β) c).map f) n code =
      (decode (α := Fin n → β) code).map
        (fun g => List.ofFn (fun i => f (g i))) := by
  unfold decodeArrowWith
  have htag : decodeTaggedWith (fun c => (decode (α := β) c).map f) n =
      fun c => (decode (α := Σ _ : Fin n, β) c).map
        (fun p => (p.1.val, f p.2)) := by
    funext c
    exact decodeTaggedWith_map f n c
  rw [htag, decodeVectorWith_map, decode_finPi]
  cases hd : @decode (Fin n → (Σ _ : Fin n, β)) Encodable.finArrow code with
  | none => rfl
  | some g =>
      simp only [Option.map_some, Option.bind_some]
      have htags :
          (List.ofFn (fun i => ((g i).1.val, f (g i).2))).map Prod.fst = List.range n ↔
            ∀ i, (g i).1 = i := by
        simpa only [List.map_ofFn, Function.comp_def] using tags_eq_range_iff g
      by_cases h : ∀ i, (g i).1 = i
      · rw [if_pos (htags.mpr h), if_pos h]
        simp only [Option.map_some, List.map_ofFn, Function.comp_def]
      · simp only [if_neg (mt htags.mp h), if_neg h, Option.map_none]

theorem decodeArrowWith_decode [Encodable α] (n code : ℕ) :
    decodeArrowWith (decode (α := α)) n code =
      (decode (α := Fin n → α) code).map List.ofFn := by
  simpa using decodeArrowWith_map (α := α) (β := α) id n code

/-- A single primitive recursive decoder handles changing dimensions,
changing codes, and a uniformly primitive recursive component decoder. -/
theorem decodeArrowWith_primrec [Primcodable σ] [Primcodable α]
    {d : σ → ℕ → Option α} {n code : σ → ℕ}
    (hd : Primrec₂ d) (hn : Primrec n) (hc : Primrec code) :
    Primrec (fun x => decodeArrowWith (d x) (n x) (code x)) := by
  unfold decodeArrowWith
  refine Primrec.option_bind (decodeVectorWith_primrec ?_ hn hc) ?_
  · apply Primrec₂.mk
    exact decodeTaggedWith_primrec
      (hd.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
      (hn.comp Primrec.fst) Primrec.snd
  · apply Primrec₂.mk
    refine Primrec.ite
      (Primrec.eq.comp
        (Primrec.list_map Primrec.snd (Primrec.fst.comp Primrec.snd).to₂)
        (Primrec.list_range.comp (hn.comp Primrec.fst))) ?_ (Primrec.const none)
    exact Primrec.option_some.comp
      (Primrec.list_map Primrec.snd (Primrec.snd.comp Primrec.snd).to₂)

/-- Decode every row of the original square Boolean relation table.
The full table is retained, independently of any pattern carrier. -/
def decodeTable (n code : ℕ) : Option (List (List Bool)) :=
  decodeArrowWith (decodeArrowWith (decode (α := Bool)) n) n code

theorem decodeTable_eq (n code : ℕ) :
    decodeTable n code =
      (decode (α := Fin n → Fin n → Bool) code).map
        (fun f => List.ofFn (fun i => List.ofFn (f i))) := by
  unfold decodeTable
  have h : decodeArrowWith (decode (α := Bool)) n =
      fun c => (decode (α := Fin n → Bool) c).map List.ofFn := by
    funext c
    exact decodeArrowWith_decode n c
  rw [h]
  exact decodeArrowWith_map List.ofFn n code

theorem decodeTable_shape {n code : ℕ} {rows : List (List Bool)}
    (h : decodeTable n code = some rows) :
    rows.length = n ∧ ∀ row ∈ rows, row.length = n := by
  rw [decodeTable_eq] at h
  obtain ⟨f, _, rfl⟩ := Option.map_eq_some_iff.mp h
  refine ⟨List.length_ofFn, ?_⟩
  intro row hrow
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hrow
  exact List.length_ofFn

theorem decodeTable_primrec : Primrec₂ decodeTable := by
  apply Primrec₂.mk
  unfold decodeTable
  refine decodeArrowWith_primrec ?_ Primrec.fst Primrec.snd
  apply Primrec₂.mk
  exact decodeArrowWith_primrec (Primrec.decode.comp Primrec.snd).to₂
    (Primrec.fst.comp Primrec.fst) Primrec.snd

/-- Decode and re-encode an index-tagged function using a supplied
normalizer for the component codes. -/
def normalizeArrowWith (d : ℕ → Option ℕ) (n code : ℕ) : Option ℕ :=
  (decodeArrowWith d n code).map encodeArrowData

theorem normalizeArrowWith_eq [Encodable α] (n code : ℕ) :
    normalizeArrowWith (fun c => (decode (α := α) c).map encode) n code =
      (decode (α := Fin n → α) code).map encode := by
  unfold normalizeArrowWith
  rw [decodeArrowWith_map, Option.map_map]
  congr 1
  funext f
  exact (encode_arrow f).symm

theorem normalizeArrowWith_primrec [Primcodable σ]
    {d : σ → ℕ → Option ℕ} {n code : σ → ℕ}
    (hd : Primrec₂ d) (hn : Primrec n) (hc : Primrec code) :
    Primrec (fun x => normalizeArrowWith (d x) (n x) (code x)) :=
  (Primrec.option_map₁ encodeArrowData_primrec).comp
    (decodeArrowWith_primrec hd hn hc)

/-- Normalize the original inferred finite-function code, with its size
and raw natural code both supplied as inputs. -/
def normalizeArrow [Encodable α] (n code : ℕ) : Option ℕ :=
  normalizeArrowWith (fun c => (decode (α := α) c).map encode) n code

theorem normalizeArrow_eq [Encodable α] (n code : ℕ) :
    normalizeArrow (α := α) n code =
      (decode (α := Fin n → α) code).map encode :=
  normalizeArrowWith_eq n code

theorem normalizeArrow_primrec [Primcodable α] :
    Primrec₂ (normalizeArrow (α := α)) := by
  apply Primrec₂.mk
  unfold normalizeArrow
  refine normalizeArrowWith_primrec ?_ Primrec.fst Primrec.snd
  exact ((Primrec.option_map₁ Primrec.encode).comp
    (Primrec.decode.comp Primrec.snd)).to₂

/-- Reconstruct both levels of original index tags after table decoding. -/
def normalizeTable (n code : ℕ) : Option ℕ :=
  (decodeTable n code).map encodeTableData

theorem normalizeTable_eq (n code : ℕ) :
    normalizeTable n code =
      (decode (α := Fin n → Fin n → Bool) code).map encode := by
  unfold normalizeTable
  rw [decodeTable_eq, Option.map_map]
  congr 1
  funext f
  exact (encode_table f).symm

theorem normalizeTable_primrec : Primrec₂ normalizeTable :=
  (Primrec.option_map₁ encodeTableData_primrec).comp decodeTable_primrec

/-- Guarded finite-function evaluation at a natural-number index. -/
def lookup [Encodable α] (n code i : ℕ) : Option α :=
  (decodeArrowWith (decode (α := α)) n code).bind fun l => l[i]?

theorem lookup_eq [Encodable α] (n code i : ℕ) :
    lookup (α := α) n code i =
      (decode (α := Fin n → α) code).bind fun f =>
        if h : i < n then some (f ⟨i, h⟩) else none := by
  unfold lookup
  rw [decodeArrowWith_decode]
  cases decode (α := Fin n → α) code <;> simp [List.getElem?_ofFn]

theorem lookup_primrec [Primcodable α] :
    Primrec (fun x : ℕ × ℕ × ℕ => lookup (α := α) x.1 x.2.1 x.2.2) := by
  unfold lookup
  refine Primrec.option_bind
    (decodeArrowWith_primrec (Primrec.decode.comp Primrec.snd).to₂
      Primrec.fst (Primrec.fst.comp Primrec.snd)) ?_
  exact (Primrec.list_getElem?.comp Primrec.snd
    (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).to₂

theorem decodeTable_program : ∃ c : Nat.Partrec.Code, ∀ n code : ℕ,
    c.eval (Nat.pair n code) = Part.some (encode (decodeTable n code)) := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp decodeTable_primrec.to_comp
  refine ⟨c, fun n code => ?_⟩
  rw [hc]
  simp

theorem lookup_program [Primcodable α] : ∃ c : Nat.Partrec.Code, ∀ n code i : ℕ,
    c.eval (Nat.pair n (Nat.pair code i)) =
      Part.some (encode (lookup (α := α) n code i)) := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp (lookup_primrec (α := α)).to_comp
  refine ⟨c, fun n code i => ?_⟩
  rw [hc]
  simp

end Alexander313.Carlson.PrimitiveFiniteFunctions
