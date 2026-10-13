import Alexander313.Semantics

/-!
# Recorded heads and source erasure

A ghost carries its original owner. It is not identified with a different
original spare. Numeric terms and hence source program numerals are fixed
by every map in this file. No converse-to-erasure validity rule is present.
-/

namespace Alexander313

inductive RecordedHead (Owner Label : Type) where
  | live : Owner → RecordedHead Owner Label
  | indexed : Owner → Label → RecordedHead Owner Label
  | ghost : Owner → RecordedHead Owner Label
  deriving DecidableEq, Repr

def RecordedHead.erase {Owner Label : Type} : RecordedHead Owner Label → Owner
  | .live a => a
  | .indexed a _ => a
  | .ghost a => a

namespace Formula

variable {Owner Label : Type}

def record (head : Owner → Shape Owner → RecordedHead Owner Label) :
    Formula Owner → Formula (RecordedHead Owner Label)
  | .falsum => .falsum
  | .equal t u => .equal t u
  | .imp φ ψ => .imp (φ.record head) (ψ.record head)
  | .conj φ ψ => .conj (φ.record head) (ψ.record head)
  | .disj φ ψ => .disj (φ.record head) (ψ.record head)
  | .neg φ => .neg (φ.record head)
  | .all x φ => .all x (φ.record head)
  | .ex x φ => .ex x (φ.record head)
  | .know a φ => .know (head a φ.shape) (φ.record head)

def erase : Formula (RecordedHead Owner Label) → Formula Owner :=
  mapOwner RecordedHead.erase

@[simp] theorem erase_record (φ : Formula Owner)
    (head : Owner → Shape Owner → RecordedHead Owner Label)
    (hhead : ∀ a sh, (head a sh).erase = a) : (φ.record head).erase = φ := by
  induction φ <;> simp_all [record, erase, mapOwner]

@[simp] theorem record_subst (φ : Formula Owner)
    (head : Owner → Shape Owner → RecordedHead Owner Label)
    (σ : NumericalSubstitution) :
    (φ.subst σ).record head = (φ.record head).subst σ := by
  induction φ generalizing σ <;> simp_all [record, subst]

@[simp] theorem record_close (φ : Formula Owner)
    (head : Owner → Shape Owner → RecordedHead Owner Label) (s : Assignment) :
    (φ.close s).record head = (φ.record head).close s := by
  simp [close]

@[simp] theorem erase_prefix (a : RecordedHead Owner Label) (n : Nat)
    (φ : Formula (RecordedHead Owner Label)) :
    («prefix» a n φ).erase = «prefix» a.erase n φ.erase := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Formula.know a.erase ((«prefix» a n φ).erase) =
      Formula.know a.erase («prefix» a.erase n φ.erase)
    rw [ih]

end Formula

def sourceQueries {Owner Label : Type} (P : RawPredicates Owner)
    (cuts : Owner → Label → Formula (RecordedHead Owner Label) → Prop) :
    RawPredicates (RecordedHead Owner Label)
  | .live a, θ => P a θ.erase
  | .indexed a ν, θ => cuts a ν θ
  | .ghost _, _ => False

@[simp] theorem live_query_record {Owner Label : Type} (P : RawPredicates Owner)
    (cuts : Owner → Label → Formula (RecordedHead Owner Label) → Prop)
    (head : Owner → Shape Owner → RecordedHead Owner Label)
    (hhead : ∀ a sh, (head a sh).erase = a)
    (a : Owner) (φ : Formula Owner) (s : Assignment) :
    sourceQueries P cuts (.live a) ((φ.record head).close s) ↔ P a (φ.close s) := by
  change P a (((φ.record head).close s).erase) ↔ P a (φ.close s)
  rw [← Formula.record_close, Formula.erase_record _ _ hhead]

@[simp] theorem ghost_empty {Owner Label : Type} (P : RawPredicates Owner)
    (cuts : Owner → Label → Formula (RecordedHead Owner Label) → Prop)
    (a : Owner) (φ : Formula (RecordedHead Owner Label)) (s : Assignment) :
    ¬ filteredTruth (sourceQueries P cuts) (.know (.ghost a) φ) s := by
  simp [truth, sourceQueries]

end Alexander313
