import Alexander313.SourceFixedPoint
import Alexander313.Source311Assembly

/-!
# The 3-1-1 source theories from an exact validity program

The positive source-generator compiler is closed under finite consequences
and one joint fixed point supplies the actual sentence family. Thus the
remaining exact source presentation is constructed, rather than passed in
as a `SourceInputs311` hypothesis. This still requires the unconstructed
exact validity program from Alexander A02. In contrast to the common-core
3-1-3 presentation, well-founded source soundness here is already derived.
-/

namespace Alexander313

theorem source_inputs311_from_validity {R : Nat → Nat → Prop}
    (hR : HierarchyRE R) (validity : Program)
    (hvalid : ∀ φ : Formula Nat, validity.domain (φ.code id) ↔ Valid φ) :
    ∃ C : SourceInputs311 R, C.arithmetic = canonicalArithmeticCoding Nat := by
  obtain ⟨edge, hedge⟩ := PositiveIdeal.hierarchy_program hR
  obtain ⟨prefixes, hprefixPR, hprefix, _, _⟩ := positiveSourceCompiler_exists
  let generator (source : Program) := prefixes ((source, edge), validity)
  have hgenerator : Primrec generator := hprefixPR.comp
    ((Primrec.id.pair (Primrec.const edge)).pair (Primrec.const validity))
  obtain ⟨F, hF⟩ := consequence_family_fixed_point generator hgenerator.to_comp validity hvalid
  let G := ProgramSourceGenerator F.effective.recognizes edge validity
  have haxioms (i : Nat) (θ : Formula Nat) :
      ConsequenceProgram.axioms (generator F.effective.recognizes) i θ ↔
        PrefixedAxioms i (G i) θ := by
    constructor
    · intro h
      exact (hprefix F.effective.recognizes edge validity i θ).mp h.2
    · intro h
      have hclosed : θ.Closed := by
        obtain ⟨σ, n, hσ, rfl⟩ := h
        simpa only [Formula.Closed, Formula.freeVars_prefix] using ProgramSourceGenerator.closed hσ
      exact ⟨hclosed, (hprefix F.effective.recognizes edge validity i θ).mpr h⟩
  refine ⟨{
    arithmetic := canonicalArithmeticCoding Nat
    family := F
    generators := G
    generators_exact := ?_
    proofs := ?_ }, rfl⟩
  · intro i σ
    exact (programSourceGenerator_exact F.effective.recognizes edge validity hvalid i σ).trans
      (or_congr Iff.rfl (subordinate_generators_exact F edge hedge i σ))
  · intro i θ hθ
    rw [hF, ConsequenceProgram.generated_iff_provable _ validity hvalid]
    simp only [hθ, true_and]
    exact ⟨fun h => h.mono (fun σ hs => (haxioms i σ).mp hs),
      fun h => h.mono (fun σ hs => (haxioms i σ).mpr hs)⟩

/-- All 3-1-1 target fields follow without a supplied source-family contract
    or soundness premise. Exact semantic validity is the outstanding A02 input;
    this is therefore deliberately not the unconditional `thesis311`. -/
theorem solution311_from_validity (R : Nat → Nat → Prop) (hR : HierarchyRE R)
    (wf : WellFounded R) (validity : Program)
    (hvalid : ∀ φ : Formula Nat, validity.domain (φ.code id) ↔ Valid φ) :
    Nonempty (Solution311 R) := by
  obtain ⟨C, hcanonical⟩ := source_inputs311_from_validity hR validity hvalid
  have coherent : CoherentArithmeticCoding C.arithmetic := by
    rw [hcanonical]
    exact canonicalArithmeticCodingCoherent Nat
  exact source_inputs311_solution_nonempty R wf C coherent

end Alexander313
