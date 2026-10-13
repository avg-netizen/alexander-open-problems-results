import Alexander313.Effective.RecordedLabelCutPrograms
import Alexander313.Effective.ValidityPrograms
import Alexander313.ColumnGenericity
import Alexander313.OrdinalPackage
import Alexander313.EffectiveIdeals

/-!
# Every stage-cut column is an actual program column

The ordinal package recognises its order and both relations positively. With
the source recognizer, a hierarchy-edge program and the exact validity
program, `RecordedLabelCutProgram.stage_exact` identifies one actual program
with the literal stage cut predicate. Freezing the owner and the argument
skeleton then gives an actual W column for every numerical parameter
instance. This is the effectivity fact behind note 24 §7's claim that the
reconstructed predicates are column-wise r.e. The final source family has a
separate joint recognizer; no joint recognizer is required for reconstructions.
-/

namespace Alexander313

/-- Program data for the actual stage cuts of a canonical source presentation. -/
structure StageEffectivity {R : Nat → Nat → Prop} (C : CommonCorePresentation R) where
  edge : Program
  edge_exact : ∀ j i, edge.domain (Nat.pair j i) ↔ R j i
  validity : Program
  validity_exact : ∀ φ : Formula Nat, validity.domain (φ.code id) ↔ Valid φ
  arithmetic : C.arithmetic = canonicalArithmeticCoding Nat

theorem StageEffectivity.nonempty {R : Nat → Nat → Prop} (hR : HierarchyRE R)
    (C : CanonicalCommonCorePresentation R) :
    Nonempty (StageEffectivity C.toCommonCorePresentation) := by
  obtain ⟨edge, hedge⟩ := PositiveIdeal.hierarchy_program hR
  obtain ⟨validity, hvalid, _⟩ := Delta.BLProofProgram.valid_program_exists
  exact ⟨{
    edge := edge
    edge_exact := hedge
    validity := validity
    validity_exact := hvalid
    arithmetic := rfl }⟩

namespace RecordedStage

variable (P : OrdinalPackage) {R : Nat → Nat → Prop} {C : CommonCorePresentation R}

/-- The literal label-cut program parameters of one presentation and cut. -/
noncomputable def cutParameters (eff : StageEffectivity C) (A E : Finset Nat) (ν : P.Label) :
    RecordedLabelCutProgram.Parameters :=
  (((((A.toList, E.toList), ((C.family.effective.recognizes, eff.edge),
    (P.R₁Program, P.R₂Program))), eff.validity), P.ltProgram), ν)

theorem cutProgram_exact (eff : StageEffectivity C) (A E : Finset Nat) (b : Nat)
    (ν : P.Label) (θ : Formula (RecordedHead Nat P.Label)) :
    (RecordedLabelCutProgram.theoryCompiler (cutParameters P eff A E ν)).domain
        (Nat.pair b (θ.code RecordedHead.code)) ↔
      cuts C A E P.R₁ P.R₂ b ν θ := by
  have h := @RecordedLabelCutProgram.stage_exact P.order R C (cutParameters P eff A E ν)
    P.R₁ P.R₂ eff.arithmetic rfl eff.edge_exact eff.validity_exact P.lt_program
    P.R₁_program P.R₂_program b θ
  simpa only [cutParameters, Finset.toList_toFinset, CodedLabel,
    CodedLabel.instLinearOrder] using h

/-- An actual W column for every numerical parameter instance of a cut. -/
theorem cut_column (eff : StageEffectivity C) (A E : Finset Nat) (b : Nat) (ν : P.Label)
    (ψ : Formula (RecordedHead Nat P.Label)) (x : Nat) (s : Assignment) :
    ∃ c : Nat, ∀ n, W c n ↔ cuts C A E P.R₁ P.R₂ b ν (ψ.close (Function.update s x n)) := by
  obtain ⟨c, hc⟩ := program_parameter_column
    (RecordedLabelCutProgram.theoryCompiler (cutParameters P eff A E ν)) b
    (RecordedFormula.encode ψ) x s
  refine ⟨c, fun n => (hc n).trans ?_⟩
  rw [← RecordedFormula.encode_close, RecordedFormula.encode_code]
  exact cutProgram_exact P eff A E b ν _

end RecordedStage

end Alexander313
