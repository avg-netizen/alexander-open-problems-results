import Alexander313.IdealGenericityInduction
import Alexander313.SourceFixedPoint
import Alexander313.ComparatorChallenge
import Alexander313.Thesis313

/-!
# Thesis 3-1-3 and 3-1-2 from an effective order-2 ordinal package

The constructed canonical common-core presentation, the exact validity
program and the hierarchy-edge program are combined with the stage soundness
of `family_sound`. The only remaining input is an `OrdinalPackage`: a
recursively presented well-ordered label domain with positively recognised
order, R₁ and R₂, finite covering reflection, connectedness, separated guard
room and guards of every finite rank (note 24 §1, with the hand proof's
infinite chain weakened to finite ranks). No source presentation,
soundness, schema membership or arithmetic-coding input remains.

The unconditional declarations `thesis312` and `thesis313` are assembled in
`Thesis313Unconditional` from `Carlson.EffectiveCorePackage.package_exists`.
Both implications have compiled against the unchanged comparator. The
reproducible gate and axiom reports are `Compile313Package.lean` and the
logs recorded by `scripts/verify_checked.py`.
-/

namespace Alexander313

/-- Note 26, conditional only on the abstract ordinal package O₂*. -/
theorem challenge313_of_package (P : OrdinalPackage) : Comparator.challenge313 := by
  intro R hR wf
  obtain ⟨validity, hvalid, _⟩ := Delta.BLProofProgram.valid_program_exists
  obtain ⟨C⟩ := canonical_common_core_presentation_exists hR validity hvalid
  obtain ⟨eff⟩ := StageEffectivity.nonempty hR C
  exact canonical_common_core_solution_nonempty R C (family_sound P eff wf)

theorem challenge312_of_package (P : OrdinalPackage) : Comparator.challenge312 := by
  intro R hR wf
  obtain ⟨S⟩ := challenge313_of_package P R hR wf
  exact ⟨S.toSolution312⟩

theorem challenge313_of_nonempty_package (h : Nonempty OrdinalPackage) :
    Comparator.challenge313 := by
  obtain ⟨P⟩ := h
  exact challenge313_of_package P

theorem challenge312_of_nonempty_package (h : Nonempty OrdinalPackage) :
    Comparator.challenge312 := by
  obtain ⟨P⟩ := h
  exact challenge312_of_package P

end Alexander313
