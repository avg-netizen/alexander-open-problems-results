import Alexander313.OriginalReduct
import Alexander313.Thesis313

/-!
# The original reduct preserves EA and all three known schemas

Arithmetic templates are owner-free, so the same code numeral and the same
arithmetical member formula survive owner relabelling. The preservation
theorems construct target solutions from a supplied enlarged source solution;
they do not supply that solution or assume a new proof of genericity.
-/

namespace Alexander313
namespace Formula

theorem Arithmetic.mapOwner_eq_self {Owner : Type} {φ : Formula Owner}
    (hφ : φ.Arithmetic) (f : Owner → Owner) : φ.mapOwner f = φ := by
  induction φ with
  | falsum => rfl
  | equal t u => rfl
  | imp φ ψ ihφ ihψ => rw [mapOwner, ihφ hφ.1, ihψ hφ.2]
  | conj φ ψ ihφ ihψ => rw [mapOwner, ihφ hφ.1, ihψ hφ.2]
  | disj φ ψ ihφ ihψ => rw [mapOwner, ihφ hφ.1, ihψ hφ.2]
  | neg φ ih => rw [mapOwner, ih hφ]
  | all x φ ih => rw [mapOwner, ih hφ]
  | ex x φ ih => rw [mapOwner, ih hφ]
  | know a φ ih => exact False.elim hφ

@[simp] theorem mapOwner_all_foldr {Owner Other : Type} (f : Owner → Other)
    (xs : List Nat) (φ : Formula Owner) :
    (xs.foldr Formula.all φ).mapOwner f = xs.foldr Formula.all (φ.mapOwner f) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.foldr_cons, mapOwner, ih]

@[simp] theorem mapOwner_universalClosure {Owner Other : Type}
    (φ : Formula Owner) (f : Owner → Other) :
    φ.universalClosure.mapOwner f = (φ.mapOwner f).universalClosure := by
  simp only [universalClosure, freeVars_mapOwner, mapOwner_all_foldr]

end Formula

def UnaryFormula.mapOwner {Owner Other : Type} (φ : UnaryFormula Owner)
    (f : Owner → Other) : UnaryFormula Other where
  input := φ.input
  body := φ.body.mapOwner f
  freeVars_exact := by simpa only [Formula.freeVars_mapOwner] using φ.freeVars_exact

@[simp] theorem mapOwner_reflection {Owner Other : Type} (j : Owner)
    (φ : Formula Owner) (f : Owner → Other) :
    (reflection j φ).mapOwner f = reflection (f j) (φ.mapOwner f) := by
  simp only [reflection, Formula.mapOwner_universalClosure, Formula.mapOwner]

@[simp] theorem mapOwner_codeSentence (A : ArithmeticCoding Nat) (j : Nat)
    (φ : UnaryFormula Nat) (e : Nat) (f : Nat → Nat) :
    (codeSentence A j φ e).mapOwner f =
      codeSentence A (f j) (φ.mapOwner f) e := by
  simp only [codeSentence, Formula.iff, Formula.mapOwner, UnaryFormula.mapOwner,
    (A.arithmetic (Term.numeral e) (.var φ.input)).mapOwner_eq_self f]

@[simp] theorem mapOwner_mechanicalSentence (A : ArithmeticCoding Nat) (j : Nat)
    (φ : UnaryFormula Nat) (f : Nat → Nat) :
    (mechanicalSentence A j φ).mapOwner f =
      mechanicalSentence A (f j) (φ.mapOwner f) := by
  simp only [mechanicalSentence, Formula.iff, Formula.mapOwner, UnaryFormula.mapOwner,
    (A.arithmetic (.var (φ.input + 1)) (.var φ.input)).mapOwner_eq_self f]

theorem PAInstance.mapOwner {Owner Other : Type} {φ : Formula Owner}
    (hφ : PAInstance Owner φ) (f : Owner → Other) :
    PAInstance Other (φ.mapOwner f) := by
  cases hφ with
  | successor_ne_zero => exact .successor_ne_zero
  | successor_injective => exact .successor_injective
  | add_zero => exact .add_zero
  | add_succ => exact .add_succ
  | mul_zero => exact .mul_zero
  | mul_succ => exact .mul_succ
  | induction ψ x =>
    simpa only [Formula.mapOwner_universalClosure, Formula.mapOwner,
      Formula.mapOwner_subst, Formula.mapOwner_substTerm] using
      PAInstance.induction (ψ.mapOwner f) x

theorem StructuralInstance.mapOwner {Owner Other : Type} {i : Owner}
    {φ : Formula Owner} (hφ : StructuralInstance i φ) (f : Owner → Other) :
    StructuralInstance (f i) (φ.mapOwner f) := by
  cases hφ with
  | validity ψ hψ =>
    simpa only [Formula.mapOwner_universalClosure, Formula.mapOwner] using
      StructuralInstance.validity (i := f i) (ψ.mapOwner f) (hψ.mapOwner f)
  | reasoning ψ θ =>
    simpa only [Formula.mapOwner_universalClosure, Formula.mapOwner] using
      StructuralInstance.reasoning (i := f i) (ψ.mapOwner f) (θ.mapOwner f)
  | introspection ψ =>
    simpa only [Formula.mapOwner_universalClosure, Formula.mapOwner] using
      StructuralInstance.introspection (i := f i) (ψ.mapOwner f)

theorem EAInstance.mapOwner {Owner Other : Type} {i : Owner}
    {φ : Formula Owner} (hφ : EAInstance i φ) (f : Owner → Other) :
    EAInstance (f i) (φ.mapOwner f) := by
  cases hφ with
  | structural h => exact .structural (h.mapOwner f)
  | known_structural h => exact .known_structural (h.mapOwner f)
  | truth ψ =>
    simpa only [mapOwner_reflection] using EAInstance.truth (i := f i) (ψ.mapOwner f)
  | arithmetic h => exact .arithmetic (h.mapOwner f)
  | known_arithmetic h => exact .known_arithmetic (h.mapOwner f)

theorem satisfiesEA_ownerMapped (F : MachineFamily) (f : Nat → Nat) (hf : Primrec f)
    (h : satisfiesEA F) : satisfiesEA (F.ownerMapped f hf) := by
  intro i φ hφ s
  exact (F.truth_ownerMapped f hf false φ s).mpr (h (f i) _ (hφ.mapOwner f) s)

theorem knowsTruth_ownerMapped (F : MachineFamily) (f : Nat → Nat) (hf : Primrec f)
    (h : knowsTruth F) : knowsTruth (F.ownerMapped f hf) := by
  intro i j φ s
  apply (F.truth_ownerMapped f hf false (.know i (reflection j φ)) s).mpr
  simpa only [Formula.mapOwner, mapOwner_reflection] using h (f i) (f j) (φ.mapOwner f) s

theorem knowsParticularCodes_ownerMapped (A : ArithmeticCoding Nat)
    (F : MachineFamily) (f : Nat → Nat) (hf : Primrec f)
    (R S : Nat → Nat → Prop) (hR : ∀ j i, R j i → S (f j) (f i))
    (h : knowsParticularCodes A F S) :
    knowsParticularCodes A (F.ownerMapped f hf) R := by
  intro i j hji φ
  obtain ⟨e, he⟩ := h (f i) (f j) (hR j i hji) (φ.mapOwner f)
  refine ⟨e, fun s => ?_⟩
  apply (F.truth_ownerMapped f hf false (.know i (codeSentence A j φ e)) s).mpr
  simpa only [Formula.mapOwner, mapOwner_codeSentence] using he s

theorem knowsAllMechanicalness_ownerMapped (A : ArithmeticCoding Nat)
    (F : MachineFamily) (f : Nat → Nat) (hf : Primrec f)
    (h : knowsAllMechanicalness A F) :
    knowsAllMechanicalness A (F.ownerMapped f hf) := by
  intro i j φ s
  apply (F.truth_ownerMapped f hf false (.know i (mechanicalSentence A j φ)) s).mpr
  simpa only [Formula.mapOwner, mapOwner_mechanicalSentence] using
    h (f i) (f j) (φ.mapOwner f) s

noncomputable def Solution313.ownerMapped {R S : Nat → Nat → Prop}
    (source : Solution313 S) (f : Nat → Nat) (hf : Primrec f)
    (hR : ∀ j i, R j i → S (f j) (f i)) : Solution313 R := by
  let F := source.family.ownerMapped f hf
  have hall : knowsAllMechanicalness source.arithmetic F :=
    knowsAllMechanicalness_ownerMapped source.arithmetic source.family f hf
      source.all_mechanicalness
  exact {
    toSolution312 := {
      toSolution311 := {
        arithmetic := source.arithmetic
        family := F
        realization := F.actualRealization
        epistemic_arithmetic := satisfiesEA_ownerMapped source.family f hf
          source.epistemic_arithmetic
        mutual_truth := knowsTruth_ownerMapped source.family f hf source.mutual_truth
        particular_codes := knowsParticularCodes_ownerMapped source.arithmetic
          source.family f hf R S hR source.particular_codes
        subordinate_mechanicalness := fun i j _ φ s => hall i j φ s }
      own_mechanicalness := fun i φ s => hall i i φ s }
    all_mechanicalness := hall }

noncomputable def Solution313.originalReduct {R S : Nat → Nat → Prop}
    (source : Solution313 S) (hR : ∀ j i, R j i → S (j + 1) (i + 1)) :
    Solution313 R :=
  source.ownerMapped Nat.succ Primrec.succ hR

end Alexander313
