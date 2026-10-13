import Alexander313.Carlson.Rules
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Logic.Encodable.Pi
import Mathlib.Tactic.DeriveEncodable

/-!
# Executable finite presentations of pure patterns

A `PatternCode n` stores a finite carrier inside `Fin n` and two Boolean
relation tables. Its interpretation is the existing `Str (Fin n)`; a true
table entry is exactly an edge of the corresponding relation. Neither
patternhood nor any rule conclusion is built into the code format.

The finite structural predicates have explicit computable decision
instances. The Boolean checks below therefore inspect all required order,
membership and relation conditions. Their correctness lemmas identify
acceptance with the original Carlson predicates.

All code operations, finite enumeration, natural-number coding and checks
are computable. The separate `PatternCode.encode` uses classical decisions
only to express that every arbitrary propositional structure on `Fin n`
has an exact Boolean presentation. A supplied pair of executable relation
deciders instead gives the computable operation `PatternCode.ofDecidable`.
-/

namespace Alexander313.Carlson

namespace Str

variable {α β : Type*} [LinearOrder α] [LinearOrder β] [Fintype α]

omit [Fintype α] in
/-- The eight pattern fields, written as finite logical conditions for
the executable decision procedure. -/
theorem isPattern_iff_conditions (P : Str α) : P.IsPattern ↔
    (∀ x ∈ P.U, ∀ y ∈ P.U, P.r₁ x y → x ≤ y) ∧
    (∀ x ∈ P.U, ∀ y ∈ P.U, P.r₂ x y → P.r₁ x y) ∧
    (∀ x ∈ P.U, P.r₁ x x) ∧
    (∀ x ∈ P.U, P.r₂ x x) ∧
    (∀ x ∈ P.U, ∀ y ∈ P.U, ∀ z ∈ P.U, P.r₁ x y → P.r₁ y z → P.r₁ x z) ∧
    (∀ x ∈ P.U, ∀ y ∈ P.U, ∀ z ∈ P.U, P.r₂ x y → P.r₂ y z → P.r₂ x z) ∧
    (∀ x ∈ P.U, ∀ y ∈ P.U, ∀ z ∈ P.U, x ≤ y → y ≤ z → P.r₁ x z → P.r₁ x y) ∧
    (∀ x ∈ P.U, ∀ y ∈ P.U, ∀ z ∈ P.U, x ≤ y → y ≤ z → P.r₂ x z → P.r₁ y z →
      P.r₂ x y) := by
  constructor
  · intro h
    exact ⟨h.le₁, h.sub₂, h.refl₁, h.refl₂, h.trans₁, h.trans₂, h.convex₁, h.respect₂⟩
  · rintro ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩
    exact ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩

set_option synthInstance.maxSize 1024 in
instance instDecidableIsPattern (P : Str α) [DecidableRel P.r₁] [DecidableRel P.r₂] :
    Decidable P.IsPattern :=
  decidable_of_iff _ (isPattern_iff_conditions P).symm

instance instDecidableAgree (P Q : Str α) (S : Finset α)
    [DecidableRel P.r₁] [DecidableRel P.r₂] [DecidableRel Q.r₁] [DecidableRel Q.r₂] :
    Decidable (Agree P Q S) := by
  unfold Agree
  infer_instance

instance instDecidableIsSub (P Q : Str α)
    [DecidableRel P.r₁] [DecidableRel P.r₂] [DecidableRel Q.r₁] [DecidableRel Q.r₂] :
    Decidable (IsSub P Q) := by
  unfold IsSub
  infer_instance

set_option synthInstance.maxSize 1024 in
instance instDecidableIsCovering (P : Str α) (S₁ S₂ : β → β → Prop) (f : α → β)
    [DecidableRel P.r₁] [DecidableRel P.r₂] [DecidableRel S₁] [DecidableRel S₂] :
    Decidable (IsCovering P S₁ S₂ f) := by
  unfold IsCovering
  infer_instance

instance instDecidableCoversInto (P : Str α) (Q : Str β) (f : α → β)
    [DecidableRel P.r₁] [DecidableRel P.r₂] [DecidableRel Q.r₁] [DecidableRel Q.r₂] :
    Decidable (CoversInto P Q f) := by
  unfold CoversInto
  infer_instance

instance instDecidableIsIso (P : Str α) (Q : Str β) (f : α → β)
    [DecidableRel P.r₁] [DecidableRel P.r₂] [DecidableRel Q.r₁] [DecidableRel Q.r₂] :
    Decidable (IsIso P Q f) := by
  unfold IsIso
  infer_instance

instance instDecidableRel (P : Str α) (k : Lvl)
    [DecidableRel P.r₁] [DecidableRel P.r₂] : DecidableRel (P.rel k) := by
  cases k <;> dsimp only [rel] <;> infer_instance

instance instDecidableLeastGE (S : Finset α) (x p : α) : Decidable (LeastGE S x p) := by
  unfold LeastGE
  infer_instance

instance instDecidableJustBelow (S : Finset α) (a b : α) : Decidable (JustBelow S a b) := by
  unfold JustBelow
  infer_instance

instance instDecidableKCorrect (P Q : Str α) (k : Lvl)
    [DecidableRel P.r₁] [DecidableRel P.r₂] [DecidableRel Q.r₁] [DecidableRel Q.r₂] :
    Decidable (KCorrect P Q k) := by
  unfold KCorrect
  infer_instance

instance instDecidableContinuous (P Q : Str α)
    [DecidableRel P.r₁] [DecidableRel P.r₂] [DecidableRel Q.r₁] [DecidableRel Q.r₂] :
    Decidable (Continuous P Q) := by
  unfold Continuous
  infer_instance

instance instDecidableExtensionAt (P Q : Str α) (a : α)
    [DecidableRel P.r₁] [DecidableRel P.r₂] [DecidableRel Q.r₁] [DecidableRel Q.r₂] :
    Decidable (ExtensionAt P Q a) := by
  unfold ExtensionAt
  infer_instance

end Str

namespace Finite

/-- A finite carrier and two Boolean relation tables. Table entries outside
the carrier are retained, so decoding and re-encoding preserve the entire
structure record, not just its induced finite substructure. -/
structure PatternCode (n : ℕ) where
  U : Finset (Fin n)
  r₁ : Fin n → Fin n → Bool
  r₂ : Fin n → Fin n → Bool
  deriving DecidableEq, Encodable

namespace PatternCode

variable {n m : ℕ}

/-- The raw finite tables are equivalent to an ordinary finite product. -/
def tableEquiv (n : ℕ) : PatternCode n ≃
    Finset (Fin n) × (Fin n → Fin n → Bool) × (Fin n → Fin n → Bool) where
  toFun C := ⟨C.U, C.r₁, C.r₂⟩
  invFun t := ⟨t.1, t.2.1, t.2.2⟩
  left_inv := by intro C; cases C; rfl
  right_inv := by intro t; cases t; rfl

instance instFintype (n : ℕ) : Fintype (PatternCode n) :=
  Fintype.ofEquiv _ (tableEquiv n).symm

/-- Interpret each Boolean table entry as the proposition that it is true. -/
def toStr (C : PatternCode n) : Str (Fin n) where
  U := C.U
  r₁ x y := C.r₁ x y = true
  r₂ x y := C.r₂ x y = true

@[simp] theorem toStr_U (C : PatternCode n) : C.toStr.U = C.U := rfl

@[simp] theorem toStr_r₁ (C : PatternCode n) (x y : Fin n) :
    C.toStr.r₁ x y ↔ C.r₁ x y = true := Iff.rfl

@[simp] theorem toStr_r₂ (C : PatternCode n) (x y : Fin n) :
    C.toStr.r₂ x y ↔ C.r₂ x y = true := Iff.rfl

instance instDecidableRelToStrOne (C : PatternCode n) : DecidableRel C.toStr.r₁ :=
  fun x y => inferInstanceAs (Decidable (C.r₁ x y = true))

instance instDecidableRelToStrTwo (C : PatternCode n) : DecidableRel C.toStr.r₂ :=
  fun x y => inferInstanceAs (Decidable (C.r₂ x y = true))

/-- The complete executable finite enumeration of raw codes at label bound `n`. -/
def all (n : ℕ) : Finset (PatternCode n) := Finset.univ

@[simp] theorem mem_all (C : PatternCode n) : C ∈ all n := Finset.mem_univ C

/-- Check all eight pattern conditions. -/
def checkPattern (C : PatternCode n) : Bool := decide C.toStr.IsPattern

@[simp] theorem checkPattern_eq_true (C : PatternCode n) :
    C.checkPattern = true ↔ C.toStr.IsPattern := by simp [checkPattern]

def checkAgree (C D : PatternCode n) (S : Finset (Fin n)) : Bool :=
  decide (Str.Agree C.toStr D.toStr S)

@[simp] theorem checkAgree_eq_true (C D : PatternCode n) (S : Finset (Fin n)) :
    checkAgree C D S = true ↔ Str.Agree C.toStr D.toStr S := by simp [checkAgree]

def checkSub (C D : PatternCode n) : Bool := decide (Str.IsSub C.toStr D.toStr)

@[simp] theorem checkSub_eq_true (C D : PatternCode n) :
    checkSub C D = true ↔ Str.IsSub C.toStr D.toStr := by simp [checkSub]

def checkCoversInto (C : PatternCode n) (D : PatternCode m) (f : Fin n → Fin m) : Bool :=
  decide (Str.CoversInto C.toStr D.toStr f)

@[simp] theorem checkCoversInto_eq_true
    (C : PatternCode n) (D : PatternCode m) (f : Fin n → Fin m) :
    checkCoversInto C D f = true ↔ Str.CoversInto C.toStr D.toStr f := by simp [checkCoversInto]

def checkIso (C : PatternCode n) (D : PatternCode m) (f : Fin n → Fin m) : Bool :=
  decide (Str.IsIso C.toStr D.toStr f)

@[simp] theorem checkIso_eq_true (C : PatternCode n) (D : PatternCode m) (f : Fin n → Fin m) :
    checkIso C D f = true ↔ Str.IsIso C.toStr D.toStr f := by simp [checkIso]

def checkKCorrect (C D : PatternCode n) (k : Lvl) : Bool :=
  decide (Str.KCorrect C.toStr D.toStr k)

@[simp] theorem checkKCorrect_eq_true (C D : PatternCode n) (k : Lvl) :
    checkKCorrect C D k = true ↔ Str.KCorrect C.toStr D.toStr k := by simp [checkKCorrect]

def checkContinuous (C D : PatternCode n) : Bool := decide (Str.Continuous C.toStr D.toStr)

@[simp] theorem checkContinuous_eq_true (C D : PatternCode n) :
    checkContinuous C D = true ↔ Str.Continuous C.toStr D.toStr := by simp [checkContinuous]

def checkExtensionAt (C D : PatternCode n) (a : Fin n) : Bool :=
  decide (Str.ExtensionAt C.toStr D.toStr a)

@[simp] theorem checkExtensionAt_eq_true (C D : PatternCode n) (a : Fin n) :
    checkExtensionAt C D a = true ↔ Str.ExtensionAt C.toStr D.toStr a := by simp [checkExtensionAt]

/-- Enumerate precisely the codes that satisfy the pattern axioms. -/
def patterns (n : ℕ) : Finset (PatternCode n) := (all n).filter (fun C => C.checkPattern)

@[simp] theorem mem_patterns (C : PatternCode n) : C ∈ patterns n ↔ C.toStr.IsPattern := by
  simp [patterns]

/-- Encode a structure using its supplied executable relation deciders. -/
def ofDecidable (P : Str (Fin n)) [DecidableRel P.r₁] [DecidableRel P.r₂] : PatternCode n where
  U := P.U
  r₁ x y := decide (P.r₁ x y)
  r₂ x y := decide (P.r₂ x y)

/-- A decidably presented structure is recovered exactly, including its
off-carrier relations. -/
@[simp] theorem toStr_ofDecidable (P : Str (Fin n)) [DecidableRel P.r₁] [DecidableRel P.r₂] :
    (ofDecidable P).toStr = P := by
  cases P with
  | mk U r₁ r₂ =>
    unfold ofDecidable toStr
    congr 1 <;> funext x y <;> simp

/-- Classical presentation of an arbitrary finite propositional structure.
This operation belongs to the proof-side completeness argument and is not
used by any checker or finite enumeration. -/
noncomputable def encode (P : Str (Fin n)) : PatternCode n := by
  classical
  exact ofDecidable P

@[simp] theorem encode_U (P : Str (Fin n)) : (encode P).U = P.U := rfl

@[simp] theorem toStr_encode (P : Str (Fin n)) : (encode P).toStr = P := by
  classical
  exact toStr_ofDecidable P

@[simp] theorem encode_toStr (C : PatternCode n) : encode C.toStr = C := by
  classical
  cases C with
  | mk U r₁ r₂ =>
    unfold encode ofDecidable toStr
    congr 1 <;> funext x y <;> simp

/-- No information is lost by interpreting the Boolean tables. -/
theorem toStr_injective : Function.Injective (@toStr n) := by
  intro C D h
  have hcode := congrArg encode h
  simpa only [encode_toStr] using hcode

/-- Exact decode-after-encode identity for arbitrary finite structures. -/
theorem decode_encode (P : Str (Fin n)) : (encode P).toStr = P := toStr_encode P

end PatternCode
end Finite
end Alexander313.Carlson
