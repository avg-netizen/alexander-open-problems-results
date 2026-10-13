import Alexander313.ConsequencePrograms
import Alexander313.Effective.CommonCorePrograms
import Alexander313.CanonicalCoreAssembly
import Alexander313.EffectiveIdeals

/-!
# The joint source-family fixed point from actual program transformers

The finite-consequence compiler and the complete common-core generator
compiler are composed before taking one recursion-theorem fixed point.
No source family or exact source-consequence presentation is supplied as an
input. The remaining logical input is an actual program recognizing exactly
valid formulas; `Delta.BLProofProgram.valid_program_exists` constructs it.
The fixed point gives an exact presentation. Global soundness is proved
separately by `IdealGenericityInduction.family_sound`.
-/

namespace Alexander313

/-- An actual computable generator transformation has a joint, sentence-only,
    consequence-closed fixed-point family, provided the supplied validity
    program is exact. This is a construction from numerical program data. -/
theorem consequence_family_fixed_point (generator : Program → Program)
    (hgenerator : Computable generator) (validity : Program)
    (hvalid : ∀ φ : Formula Nat, validity.domain (φ.code id) ↔ Valid φ) :
    ∃ F : MachineFamily, ∀ i φ,
      F.effective.proves i φ ↔ ConsequenceProgram.generated
        (generator F.effective.recognizes) validity i φ := by
  obtain ⟨compiler, hcompilerPR, hcompiler, hsentences⟩ :=
    ConsequenceProgram.compiler_exists
  let transform (source : Program) := compiler (generator source, validity)
  have htransform : Computable transform := hcompilerPR.to_comp.comp
    (hgenerator.pair (Computable.const validity))
  obtain ⟨source, hsource⟩ := program_fixed_point transform htransform
  let E : EffectiveFamily Nat := {
    encodeOwner := id
    encodeFormula := fun φ => φ.code id
    owner_injective := Function.injective_id
    formula_injective := Formula.code_injective id Function.injective_id
    formula_coding := fun _ => rfl
    recognizes := source
    proves := ConsequenceProgram.generated (generator source) validity
    recognizes_correct := fun i φ =>
      (hsource _).symm.trans (hcompiler (generator source) validity i φ)
    recognizes_only_syntax := by
      intro query hquery
      obtain ⟨i, φ, hφ, _⟩ := hsentences (generator source, validity) query
        ((hsource query).mpr hquery)
      exact ⟨i, φ, hφ⟩ }
  let F : MachineFamily := {
    effective := E
    canonical_owners := fun _ => rfl
    sentences := fun _ _ h => h.1
    theory_closed := ConsequenceProgram.theory_closed (generator source) validity hvalid }
  exact ⟨F, fun _ _ => Iff.rfl⟩

/-- The complete common-core presentation is now constructed from the actual
    edge and validity programs. Exact validity is still an explicit input;
    no soundness or ordinal-transport theorem is assumed in this construction. -/
theorem canonical_common_core_presentation_exists {R : Nat → Nat → Prop}
    (hR : HierarchyRE R) (validity : Program)
    (hvalid : ∀ φ : Formula Nat, validity.domain (φ.code id) ↔ Valid φ) :
    Nonempty (CanonicalCommonCorePresentation R) := by
  obtain ⟨edge, hedge⟩ := PositiveIdeal.hierarchy_program hR
  obtain ⟨prefixes, hprefixPR, hprefix, hsyntax, _⟩ := commonCorePrefixCompiler_exists
  let generator (source : Program) := prefixes ((source, edge), validity)
  have hgenerator : Primrec generator := hprefixPR.comp
    ((Primrec.id.pair (Primrec.const edge)).pair (Primrec.const validity))
  obtain ⟨F, hF⟩ := consequence_family_fixed_point generator hgenerator.to_comp validity hvalid
  have hgeneratorExact (i : Nat) (θ : Formula Nat) :
      (generator F.effective.recognizes).domain (Nat.pair i (θ.code id)) ↔
        PrefixedAxioms i (CommonCoreGenerator R (canonicalArithmeticCoding Nat) F i) θ := by
    rw [hprefix]
    constructor
    · rintro ⟨σ, n, hσ, rfl⟩
      exact ⟨σ, n, (commonCoreProgramGenerator_exact F _ edge validity rfl hedge hvalid i σ).mp hσ,
        rfl⟩
    · rintro ⟨σ, n, hσ, rfl⟩
      exact ⟨σ, n, (commonCoreProgramGenerator_exact F _ edge validity rfl hedge hvalid i σ).mpr hσ,
        rfl⟩
  have haxioms (i : Nat) (θ : Formula Nat) :
      ConsequenceProgram.axioms (generator F.effective.recognizes) i θ ↔
        PrefixedAxioms i (CommonCoreGenerator R (canonicalArithmeticCoding Nat) F i) θ := by
    constructor
    · exact fun h => (hgeneratorExact i θ).mp h.2
    · intro h
      have hdomain := (hgeneratorExact i θ).mpr h
      obtain ⟨j, σ, heq, hclosed⟩ := hsyntax
        ((F.effective.recognizes, edge), validity) (Nat.pair i (θ.code id)) hdomain
      have hcode : θ.code id = σ.code id := by
        have heq' := congrArg (fun n : Nat => n.unpair.2) heq
        simpa only [Nat.unpair_pair] using heq'
      have hθ : θ = σ := Formula.code_injective id Function.injective_id hcode
      exact ⟨hθ.symm ▸ hclosed, hdomain⟩
  refine ⟨{ family := F, proofs := ?_ }⟩
  intro i θ hθ
  rw [hF, ConsequenceProgram.generated_iff_provable _ validity hvalid]
  simp only [hθ, true_and]
  exact ⟨fun h => h.mono (fun σ hs => (haxioms i σ).mp hs),
    fun h => h.mono (fun σ hs => (haxioms i σ).mpr hs)⟩

end Alexander313
