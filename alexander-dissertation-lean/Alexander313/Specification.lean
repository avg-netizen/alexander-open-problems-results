import Alexander313.ArithmeticCoding
import Alexander313.Alexander.BaseLogic

/-!
# Exact targets for the three thesis questions

The family is genuinely uniformly r.e., proof-closed in Alexander's base
logic, and interpreted by actual consequence membership. All three targets
quantify over the same family for every unrestricted unary formula.
-/

namespace Alexander313

namespace Formula

variable {Owner : Type}

def universalClosure (φ : Formula Owner) : Formula Owner :=
  (φ.freeVars.sort (· ≤ ·)).foldr Formula.all φ

end Formula

def reflection {Owner : Type} (j : Owner) (φ : Formula Owner) : Formula Owner :=
  Formula.universalClosure (.imp (.know j φ) φ)

inductive PAInstance (Owner : Type) : Formula Owner → Prop where
  | successor_ne_zero : PAInstance Owner
      (.all 0 (.neg (.equal (.succ (.var 0)) .zero)))
  | successor_injective : PAInstance Owner
      (.all 0 (.all 1 (.imp (.equal (.succ (.var 0)) (.succ (.var 1)))
        (.equal (.var 0) (.var 1)))))
  | add_zero : PAInstance Owner (.all 0 (.equal (.add (.var 0) .zero) (.var 0)))
  | add_succ : PAInstance Owner
      (.all 0 (.all 1 (.equal (.add (.var 0) (.succ (.var 1)))
        (.succ (.add (.var 0) (.var 1))))))
  | mul_zero : PAInstance Owner (.all 0 (.equal (.mul (.var 0) .zero) .zero))
  | mul_succ : PAInstance Owner
      (.all 0 (.all 1 (.equal (.mul (.var 0) (.succ (.var 1)))
        (.add (.mul (.var 0) (.var 1)) (.var 0)))))
  | induction (φ : Formula Owner) (x : Nat) : PAInstance Owner
      (Formula.universalClosure (.imp
        (φ.subst (fun y => if y = x then some 0 else none))
        (.imp (.all x (.imp φ (φ.substTerm x (.succ (.var x))))) (.all x φ))))

inductive StructuralInstance {Owner : Type} (i : Owner) : Formula Owner → Prop where
  | validity (φ : Formula Owner) : Valid φ →
      StructuralInstance i (Formula.universalClosure (.know i φ))
  | reasoning (φ ψ : Formula Owner) : StructuralInstance i
      (Formula.universalClosure (.imp (.know i (.imp φ ψ))
        (.imp (.know i φ) (.know i ψ))))
  | introspection (φ : Formula Owner) : StructuralInstance i
      (Formula.universalClosure (.imp (.know i φ) (.know i (.know i φ))))

inductive EAInstance {Owner : Type} (i : Owner) : Formula Owner → Prop where
  | structural {φ} : StructuralInstance i φ → EAInstance i φ
  | known_structural {φ} : StructuralInstance i φ → EAInstance i (.know i φ)
  | truth (φ : Formula Owner) : EAInstance i (reflection i φ)
  | arithmetic {φ} : PAInstance Owner φ → EAInstance i φ
  | known_arithmetic {φ} : PAInstance Owner φ → EAInstance i (.know i φ)

structure MachineFamily where
  effective : EffectiveFamily Nat
  canonical_owners : ∀ i, effective.encodeOwner i = i
  sentences : ∀ i φ, effective.proves i φ → φ.Closed
  theory_closed : ∀ i φ, φ.Closed →
    (Provable (effective.proves i) φ ↔ effective.proves i φ)

def satisfiesEA (F : MachineFamily) : Prop :=
  ∀ i φ, EAInstance i φ → ∀ s, actualTruth F.effective.proves φ s

def knowsTruth (F : MachineFamily) : Prop :=
  ∀ i j φ s, actualTruth F.effective.proves (.know i (reflection j φ)) s

def knowsParticularCodes (A : ArithmeticCoding Nat) (F : MachineFamily)
    (R : Nat → Nat → Prop) : Prop :=
  ∀ i j, R j i → ∀ φ : UnaryFormula Nat,
    ∃ e, ∀ s, actualTruth F.effective.proves (.know i (codeSentence A j φ e)) s

def knowsOwnMechanicalness (A : ArithmeticCoding Nat) (F : MachineFamily) : Prop :=
  ∀ i (φ : UnaryFormula Nat) s,
    actualTruth F.effective.proves (.know i (mechanicalSentence A i φ)) s

def knowsSubordinateMechanicalness (A : ArithmeticCoding Nat) (F : MachineFamily)
    (R : Nat → Nat → Prop) : Prop :=
  ∀ i j, R j i → ∀ (φ : UnaryFormula Nat) s,
    actualTruth F.effective.proves (.know i (mechanicalSentence A j φ)) s

def knowsAllMechanicalness (A : ArithmeticCoding Nat) (F : MachineFamily) : Prop :=
  ∀ i j (φ : UnaryFormula Nat) s,
    actualTruth F.effective.proves (.know i (mechanicalSentence A j φ)) s

structure Solution311 (R : Nat → Nat → Prop) where
  arithmetic : ArithmeticCoding Nat
  family : MachineFamily
  realization : ActualRealization family.effective.proves
  epistemic_arithmetic : satisfiesEA family
  mutual_truth : knowsTruth family
  particular_codes : knowsParticularCodes arithmetic family R
  subordinate_mechanicalness : knowsSubordinateMechanicalness arithmetic family R

structure Solution312 (R : Nat → Nat → Prop) extends Solution311 R where
  own_mechanicalness : knowsOwnMechanicalness arithmetic family

structure Solution313 (R : Nat → Nat → Prop) extends Solution312 R where
  all_mechanicalness : knowsAllMechanicalness arithmetic family

def HierarchyRE (R : Nat → Nat → Prop) : Prop :=
  REPred (fun p : Nat × Nat => R p.1 p.2)

def Statement311 : Prop := ∀ R : Nat → Nat → Prop,
  HierarchyRE R → WellFounded R → Nonempty (Solution311 R)

def Statement312 : Prop := ∀ R : Nat → Nat → Prop,
  HierarchyRE R → WellFounded R → Nonempty (Solution312 R)

def Statement313 : Prop := ∀ R : Nat → Nat → Prop,
  HierarchyRE R → WellFounded R → Nonempty (Solution313 R)

end Alexander313
