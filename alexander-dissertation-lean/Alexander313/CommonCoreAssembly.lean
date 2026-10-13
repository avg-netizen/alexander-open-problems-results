import Alexander313.CoreInheritance
import Alexander313.OriginalSchemas

/-!
# Assembly from the literal common-core source presentation

Owner 0 denotes U; successors denote the original owners. U has the
parameter mechanicalness generators, while each original theory has the
fixed particular U codes and its subordinate codes. Prefix closure is
literal syntax. Inheritance and the effective reduct derive all target
schema fields; no SchemaMembership313 premise is used.

This is still conditional on constructing the exact effective presentation,
its soundness, and the canonical arithmetic trace certificates. In particular
it is not the unconditional comparator theorem `thesis313`.
-/

namespace Alexander313

def parameterMechanicalSentence (A : ArithmeticCoding Nat) (j x e : Nat)
    (φ : Formula Nat) : Formula Nat :=
  Formula.universalClosure (.ex e (.all x (.iff (.know j φ)
    (A.member (.var e) (.var x)))))

inductive CommonCoreGenerator (R : Nat → Nat → Prop) (A : ArithmeticCoding Nat)
    (F : MachineFamily) : Nat → Formula Nat → Prop where
  | background (i : Nat) {σ} : BackgroundGenerator i σ → CommonCoreGenerator R A F i σ
  | core_mechanical (j x e : Nat) (φ : Formula Nat)
      (fresh : e ∉ φ.freeVars) (distinct : e ≠ x) :
      CommonCoreGenerator R A F 0 (parameterMechanicalSentence A (j + 1) x e φ)
  | core_code (i : Nat) (φ : UnaryFormula Nat) :
      CommonCoreGenerator R A F (i + 1)
        (codeSentence A 0 φ (F.unaryColumnIndex 0 φ))
  | subordinate_code (i j : Nat) (below : R j i) (φ : UnaryFormula Nat) :
      CommonCoreGenerator R A F (i + 1)
        (codeSentence A (j + 1) φ (F.unaryColumnIndex (j + 1) φ))

theorem CommonCoreGenerator.closed {R : Nat → Nat → Prop}
    {A : ArithmeticCoding Nat} {F : MachineFamily} {i : Nat} {σ : Formula Nat}
    (h : CommonCoreGenerator R A F i σ) : σ.Closed := by
  cases h with
  | background i h => exact h.closed
  | core_mechanical j x e φ fresh distinct => exact Formula.universalClosure_closed _
  | core_code i φ => exact codeSentence_closed _ _ _ _
  | subordinate_code i j below φ => exact codeSentence_closed _ _ _ _

structure CommonCorePresentation (R : Nat → Nat → Prop) where
  arithmetic : ArithmeticCoding Nat
  family : MachineFamily
  proofs : ∀ i θ, θ.Closed → (family.effective.proves i θ ↔
    Provable (PrefixedAxioms i (CommonCoreGenerator R arithmetic family i)) θ)

theorem CommonCorePresentation.member {R : Nat → Nat → Prop}
    (C : CommonCorePresentation R) {i : Nat} {σ : Formula Nat}
    (h : CommonCoreGenerator R C.arithmetic C.family i σ) :
    C.family.effective.proves i σ := by
  apply (C.proofs i σ h.closed).mpr
  exact Provable.of_axiom ⟨σ, 0, h, rfl⟩

theorem CommonCorePresentation.prefix_member {R : Nat → Nat → Prop}
    (C : CommonCorePresentation R) {i : Nat} {σ : Formula Nat}
    (h : CommonCoreGenerator R C.arithmetic C.family i σ) (n : Nat) :
    C.family.effective.proves i (Formula.«prefix» i n σ) := by
  apply (C.proofs i _ (by
    simpa only [Formula.Closed, Formula.freeVars_prefix] using h.closed)).mpr
  exact Provable.of_axiom ⟨σ, n, h, rfl⟩

theorem CommonCorePresentation.prefix_instance {R : Nat → Nat → Prop}
    (C : CommonCorePresentation R) {i : Nat} {σ : Formula Nat}
    (h : CommonCoreGenerator R C.arithmetic C.family i σ) (n : Nat) (s : Assignment) :
    C.family.effective.proves i ((Formula.«prefix» i n σ).close s) := by
  have hc : (Formula.«prefix» i n σ).Closed := by
    simpa only [Formula.Closed, Formula.freeVars_prefix] using h.closed
  rw [Formula.close_eq_self_of_closed _ hc]
  exact C.prefix_member h n

theorem CommonCorePresentation.background_member {R : Nat → Nat → Prop}
    (C : CommonCorePresentation R) (i : Nat) {σ : Formula Nat}
    (h : BackgroundGenerator i σ) : C.family.effective.proves i σ :=
  C.member (.background i h)

theorem CommonCorePresentation.necessity {R : Nat → Nat → Prop}
    (C : CommonCorePresentation R) (i : Nat) {φ : Formula Nat}
    (hp : C.family.effective.proves i φ) : C.family.effective.proves i (.know i φ) := by
  have hc := C.family.sentences i φ hp
  obtain ⟨c⟩ := (C.proofs i φ hc).mp hp
  apply C.family.knowledge_of_certificate i c hc
  · intro θ hθ
    obtain ⟨σ, n, hσ, rfl⟩ := hθ
    simpa only [Formula.Closed, Formula.freeVars_prefix] using hσ.closed
  · intro θ hθ
    obtain ⟨σ, n, hσ, rfl⟩ := hθ
    simpa only [Formula.«prefix»] using C.prefix_member hσ (n + 1)
  · intro θ hv hθ
    have hk : (Formula.know i θ).Closed := hθ
    simpa only [Formula.universalClosure_eq_self_of_closed _ hk] using
      C.background_member i (.structural (StructuralInstance.validity θ hv))
  · intro θ η hθ hη
    have hfθ : θ.freeVars = ∅ := hθ
    have hfη : η.freeVars = ∅ := hη
    have hk : (Formula.imp (.know i (.imp θ η))
        (.imp (.know i θ) (.know i η))).Closed := by
      simp [Formula.Closed, Formula.freeVars, hfθ, hfη]
    simpa only [Formula.universalClosure_eq_self_of_closed _ hk] using
      C.background_member i (.structural (StructuralInstance.reasoning θ η))

theorem CommonCorePresentation.background_true {R : Nat → Nat → Prop}
    (C : CommonCorePresentation R) (i : Nat) {σ : Formula Nat}
    (h : BackgroundGenerator i σ) (s : Assignment) :
    filteredTruth C.family.effective.proves σ s := by
  cases h with
  | arithmetic h => exact truth_pa_instance true _ h s
  | assigned φ t h => exact filtered_assigned_validity _ C.family.filteredRealization φ h t s
  | structural h =>
    apply filtered_structural _ C.family.filteredRealization i _ _ _ h s
    · intro φ hv t
      exact C.background_member i (.assigned φ t hv)
    · intro φ ψ hi hp
      exact C.family.modus_ponens i hi hp
    · intro φ hp
      exact C.necessity i hp
  | reflection j φ => exact filtered_reflection _ j φ s

theorem CommonCorePresentation.satisfiesEA {R : Nat → Nat → Prop}
    (C : CommonCorePresentation R) (sound : ∀ i, RawSound C.family.effective.proves i) :
    satisfiesEA C.family := by
  intro i φ hφ s
  apply (filtered_eq_actual C.family.effective.proves sound φ s).mp
  cases hφ with
  | structural h => exact C.background_true i (.structural h) s
  | truth φ => exact C.background_true i (.reflection i φ) s
  | arithmetic h => exact C.background_true i (.arithmetic h) s
  | known_structural h =>
    exact filtered_prefix C.family.effective.proves i _ s
      (fun n => C.prefix_instance (.background i (.structural h)) n s)
      (C.background_true i (.structural h) s) 1
  | known_arithmetic h =>
    exact filtered_prefix C.family.effective.proves i _ s
      (fun n => C.prefix_instance (.background i (.arithmetic h)) n s)
      (C.background_true i (.arithmetic h) s) 1

theorem CommonCorePresentation.knowsTruth {R : Nat → Nat → Prop}
    (C : CommonCorePresentation R) : knowsTruth C.family := by
  intro i j φ s
  have hc : (reflection j φ).Closed := Formula.universalClosure_closed _
  exact ⟨by
    rw [Formula.close_eq_self_of_closed _ hc]
    exact C.background_member i (.reflection j φ), trivial⟩

theorem CommonCorePresentation.inherits_core {R : Nat → Nat → Prop}
    (C : CommonCorePresentation R) (coherent : CoherentArithmeticCoding C.arithmetic)
    (trace : ∀ e n, W e n → Provable (PAInstance Nat)
      (C.arithmetic.member (Term.numeral e) (Term.numeral n))) (i : Nat) :
    ∀ σ, C.family.effective.proves 0 σ → C.family.effective.proves (i + 1) σ :=
  common_core_inheritance C.arithmetic coherent C.family 0 (i + 1)
    (fun θ t h => C.background_member _ (.assigned θ t h))
    (fun θ h => C.background_member _ (.arithmetic h))
    (fun φ => C.member (.core_code i φ))
    (fun φ => C.background_member _ (.reflection 0 φ)) trace

theorem CommonCorePresentation.core_mechanical_member {R : Nat → Nat → Prop}
    (C : CommonCorePresentation R) (j : Nat) (φ : UnaryFormula Nat) :
    C.family.effective.proves 0 (mechanicalSentence C.arithmetic (j + 1) φ) := by
  have fresh : φ.input + 1 ∉ φ.body.freeVars := by
    rw [φ.freeVars_exact]
    simp
  have distinct : φ.input + 1 ≠ φ.input := by omega
  have hp := C.member (.core_mechanical j φ.input (φ.input + 1) φ.body fresh distinct)
  change C.family.effective.proves 0
    (mechanicalSentence C.arithmetic (j + 1) φ).universalClosure at hp
  simpa only [Formula.universalClosure_eq_self_of_closed _
    (mechanicalSentence_closed C.arithmetic (j + 1) φ)] using hp

/-- Every target field follows from the common source presentation. All
    actual code numerals are source-family unary-column indices, preserved
    by the reduct. The three substantial construction inputs stay visible. -/
theorem common_core_presentation_solution_nonempty (R : Nat → Nat → Prop)
    (C : CommonCorePresentation R) (coherent : CoherentArithmeticCoding C.arithmetic)
    (trace : ∀ e n, W e n → Provable (PAInstance Nat)
      (C.arithmetic.member (Term.numeral e) (Term.numeral n)))
    (sound : ∀ i, RawSound C.family.effective.proves i) : Nonempty (Solution313 R) := by
  let F := C.family.originalReduct
  have hall : knowsAllMechanicalness C.arithmetic F := by
    intro i j φ s
    apply (C.family.originalReduct_actualTruth (.know i
      (mechanicalSentence C.arithmetic j φ)) s).mpr
    simp only [Formula.mapOwner, mapOwner_mechanicalSentence]
    have hp := C.inherits_core coherent trace i _
      (C.core_mechanical_member j (φ.mapOwner Nat.succ))
    exact ⟨by
      rw [Formula.close_eq_self_of_closed _
        (mechanicalSentence_closed C.arithmetic (j + 1) (φ.mapOwner Nat.succ))]
      exact hp, trivial⟩
  have hcodes : knowsParticularCodes C.arithmetic F R := by
    intro i j hji φ
    let ψ := φ.mapOwner Nat.succ
    let e := C.family.unaryColumnIndex (j + 1) ψ
    refine ⟨e, fun s => ?_⟩
    apply (C.family.originalReduct_actualTruth
      (.know i (codeSentence C.arithmetic j φ e)) s).mpr
    simp only [Formula.mapOwner, mapOwner_codeSentence]
    exact ⟨by
      rw [Formula.close_eq_self_of_closed _ (codeSentence_closed C.arithmetic (j + 1) ψ e)]
      exact C.member (.subordinate_code i j hji ψ), trivial⟩
  exact ⟨{
    toSolution312 := {
      toSolution311 := {
        arithmetic := C.arithmetic
        family := F
        realization := F.actualRealization
        epistemic_arithmetic := satisfiesEA_ownerMapped C.family Nat.succ Primrec.succ
          (C.satisfiesEA sound)
        mutual_truth := knowsTruth_ownerMapped C.family Nat.succ Primrec.succ C.knowsTruth
        particular_codes := hcodes
        subordinate_mechanicalness := fun i j _ φ s => hall i j φ s }
      own_mechanicalness := fun i φ s => hall i i φ s }
    all_mechanicalness := hall }⟩

end Alexander313
