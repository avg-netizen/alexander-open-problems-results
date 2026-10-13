import Mathlib.Computability.RE
import Alexander313.Semantics
import Alexander313.Encoding

/-!
# Actual machine codes and fixed points

Computability here means mathlib's `Computable`/`Partrec`, not an arbitrary
Lean function or an arbitrary decidable predicate. Obtaining a computable
generator/consequence compiler is a separate construction obligation.
-/

namespace Alexander313

abbrev Program := Nat.Partrec.Code

def W (e n : Nat) : Prop := ((Nat.Partrec.Code.ofNatCode e).eval n).Dom

def Program.domain (c : Program) (n : Nat) : Prop := (c.eval n).Dom

theorem program_domain_re (c : Program) : REPred c.domain :=
  (Nat.Partrec.Code.eval_part.comp (Computable.const c) Computable.id).dom_re

theorem program_fixed_point (f : Program → Program) (hf : Computable f) :
    ∃ q : Program, ∀ n, (f q).domain n ↔ q.domain n := by
  obtain ⟨q, hq⟩ := Nat.Partrec.Code.fixed_point hf
  refine ⟨q, fun n => ?_⟩
  change ((f q).eval n).Dom ↔ (q.eval n).Dom
  rw [hq]

/-- The primitive-recursive bounded evaluation used for finite halting
    certificates. It is a real algorithm from the pinned mathlib source. -/
def boundedEvaluation (e n k : Nat) : Option Nat :=
  Nat.Partrec.Code.evaln k (Nat.Partrec.Code.ofNatCode e) n

theorem boundedEvaluation_primrec :
    Primrec (fun p : (Nat × Nat) × Nat => boundedEvaluation p.1.1 p.1.2 p.2) := by
  have hcode : Primrec (fun p : (Nat × Nat) × Nat =>
      Nat.Partrec.Code.ofNatCode p.1.1) :=
    (Primrec.ofNat Program).comp (Primrec.fst.comp Primrec.fst)
  exact Nat.Partrec.Code.primrec_evaln.comp
    ((Primrec.snd.pair hcode).pair (Primrec.snd.comp Primrec.fst))

/-- Every halting claim has a finite computation certificate, and every
    accepted certificate is sound. This supplies the concrete semantic
    target of the remaining arithmetic trace formula. -/
theorem W_iff_finite_computation (e n : Nat) :
    W e n ↔ ∃ k y, y ∈ boundedEvaluation e n k := by
  rw [W, Part.dom_iff_mem]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp hy
    exact ⟨k, y, hk⟩
  · rintro ⟨k, y, hy⟩
    exact ⟨y, Nat.Partrec.Code.evaln_sound hy⟩

namespace Program

/-- Concrete s-m-n specialization of a joint recognizer. -/
def column (c : Program) (key : Nat) : Program := Nat.Partrec.Code.curry c key

def columnIndex (c : Program) (key : Nat) : Nat := Encodable.encode (c.column key)

theorem column_primrec : Primrec₂ column := Nat.Partrec.Code.primrec₂_curry

theorem columnIndex_primrec : Primrec₂ columnIndex :=
  Primrec.encode.comp₂ column_primrec

@[simp] theorem column_domain (c : Program) (key n : Nat) :
    (c.column key).domain n ↔ c.domain (Nat.pair key n) := by
  change ((Nat.Partrec.Code.curry c key).eval n).Dom ↔ (c.eval (Nat.pair key n)).Dom
  rw [Nat.Partrec.Code.eval_curry]

@[simp] theorem W_columnIndex (c : Program) (key n : Nat) :
    W (c.columnIndex key) n ↔ c.domain (Nat.pair key n) := by
  have hdecode : Nat.Partrec.Code.ofNatCode (c.columnIndex key) = c.column key :=
    Denumerable.ofNat_encode (c.column key)
  simp only [W, hdecode]
  exact column_domain c key n

end Program

/-- One joint recursion-theorem fixed point determines every column at
    once. The construction of the source consequence transformer `f` is
    still required; independent fixed points for different columns are
    unnecessary and are not used here. -/
theorem joint_fixed_point_columns (f : Program → Program) (hf : Computable f) :
    ∃ q : Program, ∀ key n,
      W (q.columnIndex key) n ↔ (f q).domain (Nat.pair key n) := by
  obtain ⟨q, hq⟩ := program_fixed_point f hf
  exact ⟨q, fun key n => (Program.W_columnIndex q key n).trans (hq _).symm⟩

/-- A family is uniformly r.e. only when its encoded *joint* membership
    predicate has a genuine partial-recursive implementation. -/
structure EffectiveFamily (Owner : Type) where
  encodeOwner : Owner → Nat
  encodeFormula : Formula Owner → Nat
  owner_injective : Function.Injective encodeOwner
  formula_injective : Function.Injective encodeFormula
  formula_coding : ∀ φ, encodeFormula φ = φ.code encodeOwner
  recognizes : Program
  proves : RawPredicates Owner
  recognizes_correct : ∀ a φ,
    recognizes.domain (Nat.pair (encodeOwner a) (encodeFormula φ)) ↔ proves a φ
  recognizes_only_syntax : ∀ n, recognizes.domain n →
    ∃ a φ, n = Nat.pair (encodeOwner a) (encodeFormula φ)

def EffectiveFamily.EncodedMembership {Owner : Type} (F : EffectiveFamily Owner)
    (p : Nat × Nat) : Prop := F.recognizes.domain (Nat.pair p.1 p.2)

theorem EffectiveFamily.joint_re {Owner : Type} (F : EffectiveFamily Owner) :
    REPred (fun n => F.recognizes.domain n) := program_domain_re F.recognizes

end Alexander313
