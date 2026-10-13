import Alexander313.PaperComparison
import Alexander313.ComparatorChallenge

open Alexander313

-- Independently spell out the paper's quantifier order, keeping one witness
-- for the main theorem, parameter schemas and entire-theory inheritance.
example : ∀ R : Nat → Nat → Prop, HierarchyRE R → WellFounded R →
    ∃ S : Solution313 R, S.arithmetic = canonicalArithmeticCoding Nat ∧
      (∀ i j, StrictBelow R j i → ∀ (φ : UnaryFormula Nat) s,
        actualTruth S.family.effective.proves
          (.ex (φ.input + 1) (.know i (.all φ.input
            (.iff (.know j φ.body)
              (S.arithmetic.member (.var (φ.input + 1)) (.var φ.input)))))) s) ∧
      (∀ i j x e (φ : Formula Nat), e ∉ φ.freeVars → e ≠ x → ∀ s,
        actualTruth S.family.effective.proves
          (.know i (Formula.universalClosure (.ex e (.all x
            (.iff (.know j φ) (S.arithmetic.member (.var e) (.var x))))))) s) ∧
      (∀ i j, StrictBelow R j i → ∀ φ,
        S.family.effective.proves j φ → S.family.effective.proves i φ) :=
  thesis313_revised_paper

example : Comparator.challenge313 := by
  intro R hR wf
  obtain ⟨S, _⟩ := thesis313_revised_paper R hR wf
  exact ⟨S⟩

-- Freeze the meaning of the witness fields as well as the theorem's type.
example (R : Nat → Nat → Prop) (S : Solution313 R) (i : Nat) (φ : Formula Nat)
    (closed : φ.Closed) :
    Provable (S.family.effective.proves i) φ ↔ S.family.effective.proves i φ :=
  S.family.theory_closed i φ closed

example (R : Nat → Nat → Prop) (S : Solution313 R) :
    REPred (fun n => S.family.effective.recognizes.domain n) :=
  S.family.effective.joint_re

example (R : Nat → Nat → Prop) (S : Solution313 R) (i : Nat) (φ : Formula Nat) :
    S.family.effective.recognizes.domain
      (Nat.pair (S.family.effective.encodeOwner i) (S.family.effective.encodeFormula φ)) ↔
      S.family.effective.proves i φ :=
  S.family.effective.recognizes_correct i φ

#print axioms Alexander313.thesis313_revised_paper
#print axioms Alexander313.CommonCorePresentation.original_parameter_mechanical
#print axioms Alexander313.CommonCorePresentation.original_inherits
#print axioms Alexander313.inheritsTheories.transitive
#print axioms Alexander313.sourceParticularCodes.transitive
#print axioms Alexander313.canonical_common_core_with_source_particular_family
