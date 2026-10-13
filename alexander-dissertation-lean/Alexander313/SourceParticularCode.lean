import Alexander313.ArithmeticInstances
import Alexander313.Thesis311Complete
import Alexander313.Thesis313FromPackage

/-!
# Literal external-existential particular-code schemas

The frozen comparator expresses a particular code by an external natural
witness and the arithmetic template applied to its numeral. Alexander's
displayed schema has an object-language existential outside knowledge.
These are not identified by an unrestricted modal substitution rule.
Arithmetic coherence in every weak structure proves a valid equivalence
between the two closed inner sentences; consequence closure then transfers
their membership. The constructed canonical template supplies coherence.
-/

namespace Alexander313

def sourceCodeMatrix {Owner : Type} (A : ArithmeticCoding Owner) (j : Owner)
    (φ : UnaryFormula Owner) : Formula Owner :=
  .all φ.input (.iff (.know j φ.body)
    (A.member (.var (φ.input + 1)) (.var φ.input)))

def sourceParticularCodeSentence {Owner : Type} (A : ArithmeticCoding Owner)
    (i j : Owner) (φ : UnaryFormula Owner) : Formula Owner :=
  .ex (φ.input + 1) (.know i (sourceCodeMatrix A j φ))

theorem sourceParticularCodeSentence_closed {Owner : Type} (A : ArithmeticCoding Owner)
    (i j : Owner) (φ : UnaryFormula Owner) : (sourceParticularCodeSentence A i j φ).Closed := by
  change (mechanicalSentence A j φ).Closed
  exact mechanicalSentence_closed A j φ

/-- Only the arithmetic subformula is numerically substituted in an arbitrary
weak model. The knowledge argument has no free variable other than the input
that remains bound by the matrix's universal quantifier. -/
theorem sourceCodeMatrix_close_valid {Owner : Type} (A : ArithmeticCoding Owner)
    (C : CoherentArithmeticCoding A) (j : Owner) (φ : UnaryFormula Owner)
    (e : Nat) (s : Assignment) :
    Valid (.iff ((sourceCodeMatrix A j φ).close
      (Function.update s (φ.input + 1) e)) (codeSentence A j φ e)) := by
  intro D hD M t
  let σ : NumericalSubstitution :=
    NumericalSubstitution.remove
      (fun v => some ((Function.update s (φ.input + 1) e) v)) φ.input
  have hbody : φ.body.subst σ = φ.body := by
    calc
      φ.body.subst σ = φ.body.subst (fun _ => none) :=
        φ.body.subst_eq_of_agree σ (fun _ => none) (by
          intro v hv
          have hvx : v = φ.input := by
            simpa only [φ.freeVars_exact, Finset.mem_singleton] using hv
          subst v
          simp only [σ, NumericalSubstitution.remove, if_pos rfl, ite_true])
      _ = φ.body := φ.body.subst_none
  have hne : φ.input + 1 ≠ φ.input := by omega
  have hmember (d : D) :
      generalTruth M
        ((A.member (.var (φ.input + 1)) (.var φ.input)).subst σ)
        (Function.update t φ.input d) ↔
      generalTruth M (A.member (Term.numeral e) (.var φ.input))
        (Function.update t φ.input d) := by
    rw [arithmeticTruth_numericalSubst M _ σ _ (A.arithmetic _ _), C.coherent, C.coherent]
    simp only [generalTermEval, generalTermEval_numeralValue,
      generalNumericalOverride, σ, NumericalSubstitution.remove, if_neg hne,
      if_pos rfl, ite_true, Function.update_self]
  have hmatrix : generalTruth M ((sourceCodeMatrix A j φ).close
      (Function.update s (φ.input + 1) e)) t ↔
      generalTruth M (codeSentence A j φ e) t := by
    change (∀ d, (M.modal j (φ.body.subst σ) (Function.update t φ.input d) →
        generalTruth M ((A.member (.var (φ.input + 1)) (.var φ.input)).subst σ)
          (Function.update t φ.input d)) ∧
      (generalTruth M ((A.member (.var (φ.input + 1)) (.var φ.input)).subst σ)
          (Function.update t φ.input d) →
        M.modal j (φ.body.subst σ) (Function.update t φ.input d))) ↔
      (∀ d, (M.modal j φ.body (Function.update t φ.input d) →
        generalTruth M (A.member (Term.numeral e) (.var φ.input))
          (Function.update t φ.input d)) ∧
      (generalTruth M (A.member (Term.numeral e) (.var φ.input))
          (Function.update t φ.input d) → M.modal j φ.body (Function.update t φ.input d)))
    rw [hbody]
    exact forall_congr' fun d =>
      and_congr (imp_congr Iff.rfl (hmember d)) (imp_congr (hmember d) Iff.rfl)
  exact ⟨hmatrix.mp, hmatrix.mpr⟩

theorem MachineFamily.sourceParticular_of_codeMember (F : MachineFamily)
    (A : ArithmeticCoding Nat) (C : CoherentArithmeticCoding A)
    (i j : Nat) (φ : UnaryFormula Nat) (e : Nat)
    (hcode : F.effective.proves i (codeSentence A j φ e)) (s : Assignment) :
    actualTruth F.effective.proves (sourceParticularCodeSentence A i j φ) s := by
  refine ⟨e, ?_, trivial⟩
  apply (F.theory_closed i _ ((sourceCodeMatrix A j φ).close_closed _)).mp
  apply Provable.modus_ponens ?_ (Provable.of_axiom hcode)
  apply Provable.of_valid
  intro D hD M t
  exact (sourceCodeMatrix_close_valid A C j φ e s D hD M t).2

def knowsSourceParticularCodes (A : ArithmeticCoding Nat) (F : MachineFamily)
    (R : Nat → Nat → Prop) : Prop :=
  ∀ i j, R j i → ∀ (φ : UnaryFormula Nat) s,
    actualTruth F.effective.proves (sourceParticularCodeSentence A i j φ) s

theorem knowsParticularCodes_to_source (A : ArithmeticCoding Nat)
    (C : CoherentArithmeticCoding A) (F : MachineFamily)
    (R : Nat → Nat → Prop) (h : knowsParticularCodes A F R) :
    knowsSourceParticularCodes A F R := by
  intro i j hji φ s
  obtain ⟨e, he⟩ := h i j hji φ
  have hp := (he s).1
  rw [Formula.close_eq_self_of_closed _ (codeSentence_closed A j φ e)] at hp
  exact F.sourceParticular_of_codeMember A C i j φ e hp s

theorem canonical_knowsParticularCodes_to_source (F : MachineFamily)
    (R : Nat → Nat → Prop)
    (h : knowsParticularCodes (canonicalArithmeticCoding Nat) F R) :
    knowsSourceParticularCodes (canonicalArithmeticCoding Nat) F R :=
  knowsParticularCodes_to_source _ (canonicalArithmeticCodingCoherent Nat) F R h

/-- The already constructed unconditional 3-1-1 family also satisfies the
literal source formula. Coherence is constructed, not an additional premise. -/
theorem thesis311_with_source_particular (R : Nat → Nat → Prop)
    (hR : HierarchyRE R) (wf : WellFounded R) :
    ∃ S : Solution311 R, S.arithmetic = canonicalArithmeticCoding Nat ∧
      knowsSourceParticularCodes S.arithmetic S.family R := by
  obtain ⟨validity, hvalid, _⟩ := Delta.BLProofProgram.valid_program_exists
  obtain ⟨C, hcanonical⟩ := source_inputs311_from_validity hR validity hvalid
  have coherent : CoherentArithmeticCoding C.arithmetic := by
    rw [hcanonical]
    exact canonicalArithmeticCodingCoherent Nat
  let S := source_inputs311_solution R wf C coherent
  have hS : S.arithmetic = C.arithmetic := by
    dsimp only [S, source_inputs311_solution]
    cases source_inputs311_schemas R wf C with
    | intro hea rest => cases rest; rfl
  refine ⟨S, hS.trans hcanonical, ?_⟩
  have hcoherent : CoherentArithmeticCoding S.arithmetic := hS.symm ▸ coherent
  exact knowsParticularCodes_to_source S.arithmetic hcoherent S.family R S.particular_codes

/-- The canonical common-core assembly, retaining its concrete arithmetic
witness and its literal source-schema consequence. The family and all its
other fields are exactly the original successor reduct used by the existing
assembly; no source-schema membership premise is supplied. -/
theorem canonical_common_core_with_source_particular_family (R : Nat → Nat → Prop)
    (C : CanonicalCommonCorePresentation R)
    (sound : ∀ i, RawSound C.family.effective.proves i) :
    ∃ S : Solution313 R, S.arithmetic = canonicalArithmeticCoding Nat ∧
      knowsSourceParticularCodes S.arithmetic S.family R ∧
      S.family = C.family.originalReduct := by
  let D := C.toCommonCorePresentation
  let A := canonicalArithmeticCoding Nat
  let F := C.family.originalReduct
  have hall : knowsAllMechanicalness A F := by
    intro i j φ s
    apply (C.family.originalReduct_actualTruth (.know i (mechanicalSentence A j φ)) s).mpr
    simp only [Formula.mapOwner, mapOwner_mechanicalSentence]
    have hp := D.inherits_core (canonicalArithmeticCodingCoherent Nat)
      canonicalArithmeticCoding_pa i _ (D.core_mechanical_member j (φ.mapOwner Nat.succ))
    refine ⟨?_, trivial⟩
    rw [Formula.close_eq_self_of_closed _
      (mechanicalSentence_closed A (j + 1) (φ.mapOwner Nat.succ))]
    exact hp
  have hcodes : knowsParticularCodes A F R := by
    intro i j hji φ
    let ψ := φ.mapOwner Nat.succ
    let e := C.family.unaryColumnIndex (j + 1) ψ
    refine ⟨e, fun s => ?_⟩
    apply (C.family.originalReduct_actualTruth (.know i (codeSentence A j φ e)) s).mpr
    simp only [Formula.mapOwner, mapOwner_codeSentence]
    refine ⟨?_, trivial⟩
    rw [Formula.close_eq_self_of_closed _ (codeSentence_closed A (j + 1) ψ e)]
    exact D.member (.subordinate_code i j hji ψ)
  let S : Solution313 R := {
    toSolution312 := {
      toSolution311 := {
        arithmetic := A
        family := F
        realization := F.actualRealization
        epistemic_arithmetic := satisfiesEA_ownerMapped C.family Nat.succ Primrec.succ
          (D.satisfiesEA sound)
        mutual_truth := knowsTruth_ownerMapped C.family Nat.succ Primrec.succ D.knowsTruth
        particular_codes := hcodes
        subordinate_mechanicalness := fun i j _ φ s => hall i j φ s }
      own_mechanicalness := fun i φ s => hall i i φ s }
    all_mechanicalness := hall }
  exact ⟨S, rfl, canonical_knowsParticularCodes_to_source F R hcodes, rfl⟩

theorem canonical_common_core_with_source_particular (R : Nat → Nat → Prop)
    (C : CanonicalCommonCorePresentation R)
    (sound : ∀ i, RawSound C.family.effective.proves i) :
    ∃ S : Solution313 R, S.arithmetic = canonicalArithmeticCoding Nat ∧
      knowsSourceParticularCodes S.arithmetic S.family R := by
  obtain ⟨S, hcanonical, hsource, _⟩ :=
    canonical_common_core_with_source_particular_family R C sound
  exact ⟨S, hcanonical, hsource⟩

/-- With the same sole ordinal input as the checked 3-1-3 gate, the actual
constructed family satisfies the literal external-existential source schema.
Arithmetic coherence is discharged by the canonical arithmetic construction. -/
theorem thesis313_with_source_particular (P : OrdinalPackage)
    (R : Nat → Nat → Prop) (hR : HierarchyRE R) (wf : WellFounded R) :
    ∃ S : Solution313 R, S.arithmetic = canonicalArithmeticCoding Nat ∧
      knowsSourceParticularCodes S.arithmetic S.family R := by
  obtain ⟨validity, hvalid, _⟩ := Delta.BLProofProgram.valid_program_exists
  obtain ⟨C⟩ := canonical_common_core_presentation_exists hR validity hvalid
  obtain ⟨eff⟩ := StageEffectivity.nonempty hR C
  exact canonical_common_core_with_source_particular R C (family_sound P eff wf)

end Alexander313
