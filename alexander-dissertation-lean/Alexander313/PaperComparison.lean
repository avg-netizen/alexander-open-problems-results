import Alexander313.SourceUnconditional

/-!
# The revised paper's parameter schema and transitive inheritance

Sections 17.4 and 18.1 put the universal parameter quantifiers inside knowledge,
outside the code existential. Section 18.2 transfers entire theories along
subordinate paths. These conclusions are proved for the same single witness
that satisfies the unchanged comparator and the literal source-code schema.
The ordinal package and arithmetic representation are constructed imports.

This does not identify Carlson's covering relations with the pure elementary
relations in paper §6, or prove the auxiliary comparisons in §§18.3–18.6.
-/

namespace Alexander313

def knowsParameterMechanicalness (A : ArithmeticCoding Nat) (F : MachineFamily) : Prop :=
  ∀ i j x e (φ : Formula Nat), e ∉ φ.freeVars → e ≠ x → ∀ s,
    actualTruth F.effective.proves (.know i (parameterMechanicalSentence A j x e φ)) s

def inheritsTheories (F : MachineFamily) (R : Nat → Nat → Prop) : Prop :=
  ∀ i j, R j i → ∀ φ, F.effective.proves j φ → F.effective.proves i φ

@[simp] theorem mapOwner_parameterMechanicalSentence (A : ArithmeticCoding Nat)
    (j x e : Nat) (φ : Formula Nat) (f : Nat → Nat) :
    (parameterMechanicalSentence A j x e φ).mapOwner f =
      parameterMechanicalSentence A (f j) x e (φ.mapOwner f) := by
  simp only [parameterMechanicalSentence, Formula.mapOwner_universalClosure,
    Formula.iff, Formula.mapOwner, (A.arithmetic (.var e) (.var x)).mapOwner_eq_self f]

theorem CommonCorePresentation.original_parameter_mechanical
    {R : Nat → Nat → Prop} (C : CommonCorePresentation R)
    (coherent : CoherentArithmeticCoding C.arithmetic)
    (trace : ∀ e n, W e n → Provable (PAInstance Nat)
      (C.arithmetic.member (Term.numeral e) (Term.numeral n))) :
    knowsParameterMechanicalness C.arithmetic C.family.originalReduct := by
  intro i j x e φ fresh distinct s
  apply (C.family.originalReduct_actualTruth
    (.know i (parameterMechanicalSentence C.arithmetic j x e φ)) s).mpr
  simp only [Formula.mapOwner, mapOwner_parameterMechanicalSentence]
  have fresh' : e ∉ (φ.mapOwner Nat.succ).freeVars := by
    simpa only [Formula.freeVars_mapOwner] using fresh
  have hp := C.inherits_core coherent trace i _
    (C.member (.core_mechanical j x e (φ.mapOwner Nat.succ) fresh' distinct))
  have hc : (parameterMechanicalSentence C.arithmetic (j + 1) x e
      (φ.mapOwner Nat.succ)).Closed := Formula.universalClosure_closed _
  refine ⟨?_, trivial⟩
  rw [Formula.close_eq_self_of_closed _ hc]
  exact hp

theorem CommonCorePresentation.original_inherits
    {R : Nat → Nat → Prop} (C : CommonCorePresentation R)
    (coherent : CoherentArithmeticCoding C.arithmetic)
    (trace : ∀ e n, W e n → Provable (PAInstance Nat)
      (C.arithmetic.member (Term.numeral e) (Term.numeral n))) :
    inheritsTheories C.family.originalReduct R := by
  intro i j hji φ hp
  apply (C.family.originalReduct_proves i φ).mpr
  exact common_core_inheritance C.arithmetic coherent C.family (j + 1) (i + 1)
    (fun θ t h => C.background_member _ (.assigned θ t h))
    (fun θ h => C.background_member _ (.arithmetic h))
    (fun ψ => C.member (.subordinate_code i j hji ψ))
    (fun ψ => C.background_member _ (.reflection (j + 1) ψ)) trace
    (φ.mapOwner Nat.succ) ((C.family.originalReduct_proves j φ).mp hp)

theorem inheritsTheories.transitive {F : MachineFamily} {R : Nat → Nat → Prop}
    (h : inheritsTheories F R) : inheritsTheories F (StrictBelow R) := by
  intro i j hji
  induction hji with
  | @edge j i hji => exact h i j hji
  | trans _ _ ih₁ ih₂ => exact fun φ hp => ih₂ φ (ih₁ φ hp)

theorem sourceParticularCodes.transitive {A : ArithmeticCoding Nat} {F : MachineFamily}
    {R : Nat → Nat → Prop} (codes : knowsSourceParticularCodes A F R)
    (inherits : inheritsTheories F R) : knowsSourceParticularCodes A F (StrictBelow R) := by
  intro i j hji
  induction hji with
  | @edge j i hji => exact codes i j hji
  | @trans j k i hjk hki ih₁ ih₂ =>
    intro φ s
    obtain ⟨e, hp, _⟩ := ih₁ φ s
    exact ⟨e, inherits.transitive i k hki _ hp, trivial⟩

/-- One family for the main theorem and revised paper §§18.1–18.2, with no
ordinal, source-soundness, validity, or arithmetic-representation premise. -/
theorem thesis313_revised_paper (R : Nat → Nat → Prop)
    (hR : HierarchyRE R) (wf : WellFounded R) :
    ∃ S : Solution313 R, S.arithmetic = canonicalArithmeticCoding Nat ∧
      knowsSourceParticularCodes S.arithmetic S.family (StrictBelow R) ∧
      knowsParameterMechanicalness S.arithmetic S.family ∧
      inheritsTheories S.family (StrictBelow R) := by
  obtain ⟨validity, hvalid, _⟩ := Delta.BLProofProgram.valid_program_exists
  obtain ⟨C⟩ := canonical_common_core_presentation_exists hR validity hvalid
  obtain ⟨eff⟩ := StageEffectivity.nonempty hR C
  obtain ⟨S, hcanonical, hsource, hfamily⟩ :=
    canonical_common_core_with_source_particular_family R C
      (family_sound Carlson.EffectiveCorePackage.package eff wf)
  have hparam := C.toCommonCorePresentation.original_parameter_mechanical
    (canonicalArithmeticCodingCoherent Nat) canonicalArithmeticCoding_pa
  have hinherit := C.toCommonCorePresentation.original_inherits
    (canonicalArithmeticCodingCoherent Nat) canonicalArithmeticCoding_pa
  change inheritsTheories C.family.originalReduct R at hinherit
  rw [← hfamily] at hinherit
  have hparam' : knowsParameterMechanicalness S.arithmetic S.family := by
    rw [hcanonical, hfamily]
    exact hparam
  exact ⟨S, hcanonical, sourceParticularCodes.transitive hsource hinherit,
    hparam', hinherit.transitive⟩

end Alexander313
