import Alexander313.Effective.OwnerMap
import Alexander313.RecordedBackground
import Alexander313.Effective.FiniteAssignments

/-!
# Literal coding of live, indexed and ghost syntax

Recorded heads use actual tag/pair codes, with a primitive-recursive exact
image and a total retraction. Recorded formulas use their original literal
tree codes with this owner encoding. A primitive-recursive fixed-image
subtype of the existing natural-owner syntax constructs their `Primcodable`
instance. Owner encoding is injective and has a section/retraction, so validity
is equivalent to validity of the encoded formula. Erasure is not used in that
equivalence, and every arithmetic term and program numeral is preserved.
-/

noncomputable section

namespace Alexander313
namespace RecordedHead

def code : RecordedHead Nat Nat → Nat
  | .live a => Nat.pair 0 a
  | .indexed a ν => Nat.pair 1 (Nat.pair a ν)
  | .ghost a => Nat.pair 2 a

def validCode (n : Nat) : Bool :=
  (n.unpair.1 == 0) || (n.unpair.1 == 1) || (n.unpair.1 == 2)

theorem validCode_primrec : Primrec validCode := by
  have ht := Primrec.fst.comp Primrec.unpair
  exact Primrec.or.comp
    (Primrec.or.comp (Primrec.beq.comp ht (Primrec.const 0))
      (Primrec.beq.comp ht (Primrec.const 1))) (Primrec.beq.comp ht (Primrec.const 2))

def ofCode (n : Nat) : RecordedHead Nat Nat :=
  if n.unpair.1 = 0 then .live n.unpair.2
  else if n.unpair.1 = 1 then .indexed n.unpair.2.unpair.1 n.unpair.2.unpair.2
  else if n.unpair.1 = 2 then .ghost n.unpair.2 else .live 0

@[simp] theorem ofCode_code (a : RecordedHead Nat Nat) : ofCode a.code = a := by
  cases a <;> simp [ofCode, code, Nat.unpair_pair]

theorem code_injective : Function.Injective code := by
  intro a b h
  simpa using congrArg ofCode h

@[simp] theorem validCode_code (a : RecordedHead Nat Nat) : validCode a.code = true := by
  cases a <;> simp [validCode, code, Nat.unpair_pair]

def normalizeCode (n : Nat) : Nat := cond (validCode n) n 0

theorem normalizeCode_primrec : Primrec normalizeCode :=
  validCode_primrec.cond Primrec.id (Primrec.const 0)

@[simp] theorem code_ofCode (n : Nat) : code (ofCode n) = normalizeCode n := by
  by_cases h0 : n.unpair.1 = 0
  · calc
      code (ofCode n) = Nat.pair 0 n.unpair.2 := by simp [ofCode, h0, code]
      _ = n := by simpa only [h0] using Nat.pair_unpair n
      _ = normalizeCode n := by simp [normalizeCode, validCode, h0]
  by_cases h1 : n.unpair.1 = 1
  · calc
      code (ofCode n) = Nat.pair 1 n.unpair.2 := by
        simp [ofCode, h0, h1, code, Nat.pair_unpair]
      _ = n := by simpa only [h1] using Nat.pair_unpair n
      _ = normalizeCode n := by simp [normalizeCode, validCode, h1]
  by_cases h2 : n.unpair.1 = 2
  · calc
      code (ofCode n) = Nat.pair 2 n.unpair.2 := by simp [ofCode, h0, h1, h2, code]
      _ = n := by simpa only [h2] using Nat.pair_unpair n
      _ = normalizeCode n := by simp [normalizeCode, validCode, h2]
  · simp [ofCode, h0, h1, h2, code, normalizeCode, validCode, Nat.pair,
      Bool.beq_eq_decide_eq]

theorem validCode_iff (n : Nat) : validCode n = true ↔ ∃ a : RecordedHead Nat Nat, a.code = n := by
  constructor
  · intro h
    exact ⟨ofCode n, by rw [code_ofCode]; simp [normalizeCode, h]⟩
  · rintro ⟨a, rfl⟩
    exact validCode_code a

def literalCodeEquiv : RecordedHead Nat Nat ≃ {n : Nat // validCode n = true} where
  toFun := fun a => ⟨a.code, validCode_code a⟩
  invFun := fun n => ofCode n.val
  left_inv := ofCode_code
  right_inv := fun n => by
    apply Subtype.ext
    change code (ofCode n.val) = n.val
    rw [code_ofCode]
    simp [normalizeCode, n.property]

instance literalPrimcodable : Primcodable (RecordedHead Nat Nat) := by
  letI : Primcodable {n : Nat // validCode n = true} :=
    Primcodable.subtype (Primrec.eq.comp validCode_primrec (Primrec.const true))
  exact Primcodable.ofEquiv {n : Nat // validCode n = true} literalCodeEquiv

@[simp] theorem encode_eq_code (a : RecordedHead Nat Nat) : Encodable.encode a = a.code := rfl

theorem code_primrec : Primrec code := by
  exact (Primrec.encode : Primrec (Encodable.encode (α := RecordedHead Nat Nat)))

theorem ofCode_primrec : Primrec ofCode := by
  apply Primrec.encode_iff.1
  simpa only [encode_eq_code, code_ofCode] using normalizeCode_primrec

theorem live_primrec : Primrec (live : Nat → RecordedHead Nat Nat) := by
  apply Primrec.encode_iff.1
  simpa only [encode_eq_code, code, id_eq] using Primrec₂.natPair.comp (Primrec.const 0) Primrec.id

theorem indexed_primrec : Primrec₂ (indexed : Nat → Nat → RecordedHead Nat Nat) := by
  apply Primrec.encode_iff.1
  simpa only [encode_eq_code, code] using
    Primrec₂.natPair.comp (Primrec.const 1) Primrec₂.natPair

theorem ghost_primrec : Primrec (ghost : Nat → RecordedHead Nat Nat) := by
  apply Primrec.encode_iff.1
  simpa only [encode_eq_code, code, id_eq] using Primrec₂.natPair.comp (Primrec.const 2) Primrec.id

theorem erase_primrec : Primrec (erase : RecordedHead Nat Nat → Nat) := by
  have ht := Primrec.fst.comp (Primrec.unpair.comp code_primrec)
  have hp := Primrec.snd.comp (Primrec.unpair.comp code_primrec)
  exact ((Primrec.beq.comp ht (Primrec.const 1)).cond
    (Primrec.fst.comp (Primrec.unpair.comp hp)) hp).of_eq (by
      intro a; cases a <;> simp [code, erase, Nat.unpair_pair])

end RecordedHead

namespace RecordedFormula

abbrev Head := RecordedHead Nat Nat
abbrev Syntax := Formula Head

def encode (φ : Syntax) : Formula Nat := φ.mapOwner RecordedHead.code
def decode (φ : Formula Nat) : Syntax := φ.mapOwner RecordedHead.ofCode

@[simp] theorem decode_encode (φ : Syntax) : decode (encode φ) = φ := by
  induction φ <;> simp_all [decode, encode, Formula.mapOwner]

@[simp] theorem encode_code (φ : Syntax) :
    (encode φ).code id = φ.code RecordedHead.code := by
  induction φ <;> simp_all [encode, Formula.mapOwner, Formula.code]

@[simp] theorem encode_decode (φ : Formula Nat) :
    encode (decode φ) = φ.mapOwner RecordedHead.normalizeCode := by
  induction φ <;> simp_all [decode, encode, Formula.mapOwner]

theorem encode_injective : Function.Injective encode := by
  intro φ ψ h
  simpa using congrArg decode h

theorem valid_encode (φ : Syntax) : Valid (encode φ) ↔ Valid φ := by
  constructor
  · intro h
    have hd : Valid (decode (encode φ)) := h.mapOwner RecordedHead.ofCode
    simpa only [decode_encode] using hd
  · intro h
    exact h.mapOwner RecordedHead.code

def Fixed (φ : Formula Nat) : Prop := encode (decode φ) = φ

theorem fixed_primrec : PrimrecPred Fixed := by
  have hcode := (Formula.mapOwnerCode_primrec RecordedHead.normalizeCode
    RecordedHead.normalizeCode_primrec).comp Formula.code_primrec
  exact (Primrec.eq.comp hcode Formula.code_primrec).of_eq (fun φ => by
    rw [Formula.mapOwnerCode_code]
    exact (Formula.code_injective id Function.injective_id).eq_iff.trans
      (by simp only [Fixed, encode_decode]))

def literalFormulaEquiv : Syntax ≃ {φ : Formula Nat // Fixed φ} where
  toFun := fun φ => ⟨encode φ, by simp [Fixed]⟩
  invFun := fun φ => decode φ.val
  left_inv := decode_encode
  right_inv := fun φ => Subtype.ext φ.property

instance literalPrimcodable : Primcodable Syntax := by
  classical
  letI : Primcodable {φ : Formula Nat // Fixed φ} := Primcodable.subtype fixed_primrec
  exact Primcodable.ofEquiv {φ : Formula Nat // Fixed φ} literalFormulaEquiv

@[simp] theorem encode_eq_code (φ : Syntax) : Encodable.encode φ = φ.code RecordedHead.code := by
  change Encodable.encode (encode φ) = _
  simp only [Formula.encode_eq_code, encode_code]

theorem code_primrec : Primrec (fun φ : Syntax => φ.code RecordedHead.code) := by
  exact Primrec.encode.of_eq encode_eq_code

theorem encode_primrec : Primrec encode := by
  apply Primrec.encode_iff.1
  simpa only [Formula.encode_eq_code, encode_code] using code_primrec

theorem decode_primrec : Primrec decode := by
  apply Primrec.encode_iff.1
  simpa only [encode_eq_code, ← encode_code, encode_decode, Formula.mapOwnerCode_code] using
    (Formula.mapOwnerCode_primrec RecordedHead.normalizeCode RecordedHead.normalizeCode_primrec).comp
      Formula.code_primrec

def isCode (n : Nat) : Bool := Formula.isCode n &&
  (Formula.mapOwnerCode RecordedHead.normalizeCode n == n)

theorem isCode_primrec : Primrec isCode :=
  Primrec.and.comp Formula.isCode_primrec
    (Primrec.beq.comp (Formula.mapOwnerCode_primrec RecordedHead.normalizeCode
      RecordedHead.normalizeCode_primrec) Primrec.id)

theorem isCode_iff (n : Nat) : isCode n = true ↔ ∃ φ : Syntax, φ.code RecordedHead.code = n := by
  constructor
  · intro h
    obtain ⟨hc, hm⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨φ, hφ⟩ := (Formula.isCode_iff n).mp hc
    have hf : encode (decode φ) = φ := by
      apply Formula.code_injective id Function.injective_id
      simpa only [encode_decode, ← Formula.mapOwnerCode_code, hφ] using beq_iff_eq.mp hm
    exact ⟨decode φ, by rw [← encode_code, hf, hφ]⟩
  · rintro ⟨φ, rfl⟩
    rw [← encode_code]
    have hf : (encode φ).mapOwner RecordedHead.normalizeCode = encode φ := by
      rw [← encode_decode, decode_encode]
    simp only [isCode, Formula.isCode_code, Formula.mapOwnerCode_code, hf,
      beq_self_eq_true, Bool.true_and]

@[simp] theorem freeVars_encode (φ : Syntax) : (encode φ).freeVars = φ.freeVars :=
  Formula.freeVars_mapOwner φ _

@[simp] theorem encode_close (φ : Syntax) (s : Assignment) :
    encode (φ.close s) = (encode φ).close s := Formula.mapOwner_close φ _ s

@[simp] theorem encode_universalClosure (φ : Syntax) :
    encode φ.universalClosure = (encode φ).universalClosure :=
  Formula.mapOwner_universalClosure φ _

theorem imp_primrec : Primrec₂ (Formula.imp : Syntax → Syntax → Syntax) := by
  apply Primrec.encode_iff.1
  simpa only [encode_eq_code, Formula.code, EncodedSyntax.binary, EncodedSyntax.node] using
    (EncodedSyntax.binary_primrec 2).comp (code_primrec.comp Primrec.fst) (code_primrec.comp Primrec.snd)

theorem conj_primrec : Primrec₂ (Formula.conj : Syntax → Syntax → Syntax) := by
  apply Primrec.encode_iff.1
  simpa only [encode_eq_code, Formula.code, EncodedSyntax.binary, EncodedSyntax.node] using
    (EncodedSyntax.binary_primrec 3).comp (code_primrec.comp Primrec.fst) (code_primrec.comp Primrec.snd)

theorem disj_primrec : Primrec₂ (Formula.disj : Syntax → Syntax → Syntax) := by
  apply Primrec.encode_iff.1
  simpa only [encode_eq_code, Formula.code, EncodedSyntax.binary, EncodedSyntax.node] using
    (EncodedSyntax.binary_primrec 4).comp (code_primrec.comp Primrec.fst) (code_primrec.comp Primrec.snd)

theorem neg_primrec : Primrec (Formula.neg : Syntax → Syntax) := by
  apply Primrec.encode_iff.1
  simpa only [encode_eq_code, Formula.code, EncodedSyntax.node] using
    EncodedSyntax.node_primrec.comp (Primrec.const 5) code_primrec

theorem know_primrec : Primrec₂ (Formula.know : Head → Syntax → Syntax) := by
  apply Primrec.encode_iff.1
  simpa only [encode_eq_code, Formula.code, EncodedSyntax.binary, EncodedSyntax.node] using
    (EncodedSyntax.binary_primrec 8).comp (RecordedHead.code_primrec.comp Primrec.fst)
      (code_primrec.comp Primrec.snd)

theorem all_primrec : Primrec₂ (Formula.all : Nat → Syntax → Syntax) := by
  apply Primrec.encode_iff.1
  simpa only [encode_eq_code, Formula.code, EncodedSyntax.binary, EncodedSyntax.node] using
    (EncodedSyntax.binary_primrec 6).comp Primrec.fst (code_primrec.comp Primrec.snd)

theorem ex_primrec : Primrec₂ (Formula.ex : Nat → Syntax → Syntax) := by
  apply Primrec.encode_iff.1
  simpa only [encode_eq_code, Formula.code, EncodedSyntax.binary, EncodedSyntax.node] using
    (EncodedSyntax.binary_primrec 7).comp Primrec.fst (code_primrec.comp Primrec.snd)

theorem iff_primrec : Primrec₂ (Formula.iff : Syntax → Syntax → Syntax) := by
  apply Primrec.encode_iff.1
  simpa only [encode_eq_code, Formula.iff, Formula.code,
    EncodedSyntax.equivalence, EncodedSyntax.binary, EncodedSyntax.node] using
    EncodedSyntax.equivalence_primrec.comp (code_primrec.comp Primrec.fst) (code_primrec.comp Primrec.snd)

theorem universalClosure_primrec : Primrec (Formula.universalClosure : Syntax → Syntax) := by
  apply Primrec.encode_iff.1
  simpa only [encode_eq_code, ← encode_code, encode_universalClosure, Formula.encode_eq_code] using
    Primrec.encode.comp (Formula.universalClosure_primrec.comp encode_primrec)

theorem reflection_primrec : Primrec₂ (reflection (Owner := Head)) :=
  (universalClosure_primrec.comp
    (imp_primrec.comp (know_primrec.comp Primrec.fst Primrec.snd) Primrec.snd)).to₂

def close (φ : Syntax) (L : List Nat) : Syntax := φ.close (FiniteAssignment.assignment L)

theorem close_primrec : Primrec₂ close := by
  apply Primrec.encode_iff.1
  simpa only [encode_eq_code, ← encode_code, close, encode_close,
    ← FiniteAssignment.close_eq, Formula.encode_eq_code] using
    Primrec.encode.comp (FiniteAssignment.close_primrec.comp (encode_primrec.comp Primrec.fst) Primrec.snd)

theorem close_represents (φ : Syntax) (s : Assignment) :
    ∃ L : List Nat, φ.close s = close φ L := by
  obtain ⟨L, hL⟩ := FiniteAssignment.represents (encode φ) s
  refine ⟨L, encode_injective ?_⟩
  simpa only [close, encode_close, FiniteAssignment.close_eq] using hL

end RecordedFormula
end Alexander313
