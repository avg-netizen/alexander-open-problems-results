import Alexander313.GenericityConstructionSupport
import Alexander313.CanonicalCoreAssembly

/-!
# Direct genericity of the literal common core

Retain the entire original core predicate and replace the positive owners by
an actual effective alphabetic predicate family. If those external predicates
are fully sound in the same filtered interpretation, the full core is sound
there too. The core mechanicalness generators quantify only over positive
owners; their witnesses are actual numerical program columns.

This proves the core-only genericity lemma without ordinal stages. It does not
establish whole-ideal genericity or soundness of the positive original owners.
No global source soundness or stage recovery premise is supplied.
-/

namespace Alexander313

theorem CommonCorePresentation.background_true_in_core_extension
    {R : Nat → Nat → Prop} (C : CommonCorePresentation R)
    (P : RawPredicates Nat) (alphabetic : RawAlphabetic P)
    (retained : ∀ θ, P 0 θ ↔ C.family.effective.proves 0 θ)
    {σ : Formula Nat} (h : BackgroundGenerator 0 σ) (s : Assignment) :
    filteredTruth P σ s := by
  let M := FilteredRealization.ofAlphabetic P alphabetic
  cases h with
  | arithmetic h => exact truth_pa_instance true P h s
  | assigned φ t h => exact filtered_assigned_validity P M φ h t s
  | structural h =>
    apply filtered_structural P M 0 _ _ _ h s
    · intro φ hv t
      exact (retained _).mpr (C.background_member 0 (.assigned φ t hv))
    · intro φ ψ hi hp
      exact (retained _).mpr
        (C.family.modus_ponens 0 ((retained _).mp hi) ((retained _).mp hp))
    · intro φ hp
      exact (retained _).mpr (C.necessity 0 ((retained _).mp hp))
  | reflection j φ => exact filtered_reflection P j φ s

/-- Source note 26's G_U for the actual literal common core: the external
soundness assumptions are the genericity hypotheses, while no soundness of
the retained core is assumed. All numerical parameter instances are included. -/
theorem CommonCorePresentation.core_genericity {R : Nat → Nat → Prop}
    (C : CommonCorePresentation R) (F : EffectiveFamily Nat)
    (owners : ∀ a, F.encodeOwner a = a) (alphabetic : RawAlphabetic F.proves)
    (retained : ∀ θ, F.proves 0 θ ↔ C.family.effective.proves 0 θ)
    (outside : ∀ j, RawSound F.proves (j + 1)) : RawSound F.proves 0 := by
  apply sound_of_true_generators F.proves
    (FilteredRealization.ofAlphabetic F.proves alphabetic) 0
    (CommonCoreGenerator R C.arithmetic C.family 0)
  · intro σ hσ n s
    exact (retained _).mpr (C.prefix_instance hσ n s)
  · intro θ hθ
    exact (retained θ).trans (C.proofs 0 θ hθ)
  · intro σ hσ s
    cases hσ with
    | background i h =>
      exact C.background_true_in_core_extension F.proves alphabetic retained h s
    | core_mechanical j x e φ fresh distinct =>
      exact F.parameter_mechanical_truth owners C.arithmetic (j + 1) x e φ
        fresh distinct (outside j) s

theorem CanonicalCommonCorePresentation.core_genericity {R : Nat → Nat → Prop}
    (C : CanonicalCommonCorePresentation R) (F : EffectiveFamily Nat)
    (owners : ∀ a, F.encodeOwner a = a) (alphabetic : RawAlphabetic F.proves)
    (retained : ∀ θ, F.proves 0 θ ↔ C.family.effective.proves 0 θ)
    (outside : ∀ j, RawSound F.proves (j + 1)) : RawSound F.proves 0 :=
  C.toCommonCorePresentation.core_genericity F owners alphabetic retained outside

end Alexander313
