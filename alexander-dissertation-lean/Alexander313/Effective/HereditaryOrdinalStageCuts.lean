import Alexander313.Effective.HereditaryOrdinalLinearOrder
import Alexander313.Effective.HereditaryOrdinalFormation
import Alexander313.Effective.RecordedBoundedGuardSemantics

/-!
# Main stage cuts from executing formation and finite guard witnesses

The label order is the genuine coherent small ordinal order. A literal PR
test checks whole source admission, every indexed source label below the
original admitted cut, and all original label-domain guards. Its executing
Program has an exact typed/raw syntax image. The actual bounded-guard compiler
supplies the distinguished atom's finite room. These computed facts instantiate
the original main-source cut theorem after literal head-table relabeling.

The original source row, exact mask/table, heredity, owner disjointness and two
genuine ordinal edge Program identities remain explicit. No universal table,
chain, reflection, recovery or source truth is inferred. Uncompiled.
-/

noncomputable section

namespace Alexander313.HereditaryOrdinalStageCuts

open RecordedFormula RecordedGuardProgram
open Wilken.RelativeTerm.Hereditary
open HereditaryOrdinalLabels (Label value labelOf labelOf_value labelLE labelLT labelLinearOrder
  label_lt_iff)
open HereditaryOrdinalFormation
open RecordedBoundedGuardProgram (EdgeCorrect labelEdge)

local instance stageLabelLE : LE Label := labelLE
local instance stageLabelLT : LT Label := labelLT
local instance stageLabelOrder : LinearOrder Label := labelLinearOrder

/-- The literal list includes labels in every live, ghost and indexed context.
Each comparison is the actual total hereditary union-order decision. -/
def belowCutCode (δ n : Nat) : Bool :=
  allCheck (fun μ => unionLess μ δ) (labelListCode n)

theorem belowCutCode_primrec : Primrec₂ belowCutCode := by
  have ht : Primrec₂ (fun δ μ : Nat => unionLess μ δ) :=
    (unionLess_primrec.comp Primrec.snd Primrec.fst).to₂
  exact ((allCheck_primrec _ ht).comp Primrec.fst
    (labelListCode_primrec.comp Primrec.snd)).to₂

def belowCutCheck (δ : Nat) (φ : Syntax) : Bool := belowCutCode δ (φ.code RecordedHead.code)

theorem belowCutCheck_primrec : Primrec₂ belowCutCheck :=
  (belowCutCode_primrec.comp Primrec.fst (code_primrec.comp Primrec.snd)).to₂

theorem belowCutCheck_exact (δ : Nat) (φ : Syntax) : belowCutCheck δ φ = true ↔
    (letI : LT Nat := Program.orderLT ordinalOrder
     ∀ μ ∈ φ.labelSupport, μ < δ) := by
  simp only [belowCutCheck, belowCutCode, labelListCode_code, allCheck_iff,
    Formula.mem_labelList_iff, unionLess_orderLT]

abbrev CutParameters := (List Nat × List Nat) × Nat

def cutFormationCode (p : CutParameters) (n : Nat) : Bool :=
  unionCheck p.2 && (admissionCheckCode p.1 n && belowCutCode p.2 n)

theorem cutFormationCode_primrec : Primrec₂ cutFormationCode :=
  (Primrec.and.comp (Uniform.unionCheck_primrec.comp (Primrec.snd.comp Primrec.fst))
    (Primrec.and.comp
      (admissionCheckCode_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
      (belowCutCode_primrec.comp (Primrec.snd.comp Primrec.fst) Primrec.snd))).to₂

def cutFormationCheck (p : CutParameters) (φ : Syntax) : Bool :=
  cutFormationCode p (φ.code RecordedHead.code)

theorem cutFormationCheck_primrec : Primrec₂ cutFormationCheck :=
  (cutFormationCode_primrec.comp Primrec.fst (code_primrec.comp Primrec.snd)).to₂

def CutTarget (p : CutParameters) (φ : Syntax) : Prop :=
  Supported φ ∧ unionCheck p.2 = true ∧
    (denotation φ).RecordedAdmissible p.1.1.toFinset p.1.2.toFinset ∧
      ∀ μ ∈ (denotation φ).labelSupport, μ < labelOf p.2

theorem cutFormationCheck_exact (p : CutParameters) (φ : Syntax) :
    cutFormationCheck p φ = true ↔ CutTarget p φ := by
  change (unionCheck p.2 && (admissionCheck p.1 φ && belowCutCheck p.2 φ)) = true ↔ _
  rw [Bool.and_eq_true, Bool.and_eq_true, admissionCheck_exact, belowCutCheck_exact]
  constructor
  · rintro ⟨hδ, ⟨hφ, hadm⟩, below⟩
    exact ⟨hφ, hδ, hadm, (support_below_exact φ hφ p.2 hδ).mp below⟩
  · rintro ⟨hφ, hδ, hadm, below⟩
    exact ⟨hδ, ⟨hφ, hadm⟩, (support_below_exact φ hφ p.2 hδ).mpr below⟩

theorem cutTarget_value_bound {p : CutParameters} {φ : Syntax} (h : CutTarget p φ) :
    ∀ μ ∈ (denotation φ).labelSupport, value μ < unionInterpretation p.2 := by
  intro μ hμ
  simpa only [labelOf_value p.2 h.2.1] using (label_lt_iff _ _).mp (h.2.2.2 μ hμ)

def defaultCutParameters : CutParameters := (([], []), 0)

def decodeCutParameters (n : Nat) : CutParameters :=
  (Encodable.decode (α := CutParameters) n).getD defaultCutParameters

theorem decodeCutParameters_primrec : Primrec decodeCutParameters :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const defaultCutParameters)

@[simp] theorem decodeCutParameters_encode (p : CutParameters) :
    decodeCutParameters (Encodable.encode p) = p := by
  simp only [decodeCutParameters, Encodable.encodek, Option.getD_some]

def cutRawCheck (key query : Nat) : Bool :=
  isCode query && cutFormationCode (decodeCutParameters key) query

theorem cutRawCheck_primrec : Primrec₂ cutRawCheck :=
  (Primrec.and.comp (isCode_primrec.comp Primrec.snd)
    (cutFormationCode_primrec.comp (decodeCutParameters_primrec.comp Primrec.fst)
      Primrec.snd)).to₂

def cutEvaluation (key query : Nat) : Part Nat :=
  Nat.rfind (fun _ => Part.some (cutRawCheck key query))

theorem cutEvaluation_partrec : Partrec₂ cutEvaluation := by
  have h : Primrec (fun p : (Nat × Nat) × Nat => cutRawCheck p.1.1 p.1.2) :=
    cutRawCheck_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)
  exact (Partrec.rfind h.to_comp.partrec.to₂).to₂

theorem cutEvaluation_domain (key query : Nat) :
    (cutEvaluation key query).Dom ↔ cutRawCheck key query = true := by
  simp only [cutEvaluation, Nat.rfind_dom, Part.mem_some_iff,
    Part.some_dom, implies_true, and_true, Bool.true_eq, exists_const]

theorem cutEvaluation_correct (p : CutParameters) (φ : Syntax) :
    (cutEvaluation (Encodable.encode p) (φ.code RecordedHead.code)).Dom ↔ CutTarget p φ := by
  rw [cutEvaluation_domain]
  have hsyntax : isCode (φ.code RecordedHead.code) = true :=
    (isCode_iff _).mpr ⟨φ, rfl⟩
  simp only [cutRawCheck, decodeCutParameters_encode, hsyntax, Bool.true_and]
  exact cutFormationCheck_exact p φ

theorem cutEvaluation_raw_exact (key query : Nat) : (cutEvaluation key query).Dom ↔
    ∃ φ : Syntax, query = φ.code RecordedHead.code ∧ CutTarget (decodeCutParameters key) φ := by
  constructor
  · intro h
    obtain ⟨hsyntax, hformed⟩ := Bool.and_eq_true_iff.mp ((cutEvaluation_domain _ _).mp h)
    obtain ⟨φ, hφ⟩ := (isCode_iff query).mp hsyntax
    refine ⟨φ, hφ.symm, (cutFormationCheck_exact _ φ).mp ?_⟩
    simpa only [cutFormationCheck, hφ] using hformed
  · rintro ⟨φ, rfl, hφ⟩
    apply (cutEvaluation_domain _ _).mpr
    have hsyntax : isCode (φ.code RecordedHead.code) = true :=
      (isCode_iff _).mpr ⟨φ, rfl⟩
    exact Bool.and_eq_true_iff.mpr ⟨hsyntax, (cutFormationCheck_exact _ φ).mpr hφ⟩

/-- Exact executing source-formation image. This is a formation test on the
literal recorded input; the original source-row relation is checked separately
in the stage theorem below, with its original arithmetic/program numerals. -/
theorem cutFormationCompiler_exists :
    ∃ compiler : CutParameters → Program, Primrec compiler ∧
      (∀ p φ, (compiler p).domain (φ.code RecordedHead.code) ↔ CutTarget p φ) ∧
      (∀ p query, (compiler p).domain query ↔
        ∃ φ : Syntax, query = φ.code RecordedHead.code ∧ CutTarget p φ) := by
  obtain ⟨kernel, hkernel⟩ := Nat.Partrec.Code.exists_code.mp
    (Partrec₂.unpaired'.mpr cutEvaluation_partrec)
  let compiler : CutParameters → Program := fun p => Nat.Partrec.Code.curry kernel (Encodable.encode p)
  have heval (p : CutParameters) (query : Nat) :
      (compiler p).eval query = cutEvaluation (Encodable.encode p) query := by
    change (Nat.Partrec.Code.curry kernel _).eval query = _
    rw [Nat.Partrec.Code.eval_curry, hkernel]
    simp only [Nat.unpaired, Nat.unpair_pair]
  refine ⟨compiler, Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const kernel) Primrec.encode, ?_, ?_⟩
  · intro p φ
    change ((compiler p).eval _).Dom ↔ _
    rw [heval]
    exact cutEvaluation_correct p φ
  · intro p query
    change ((compiler p).eval query).Dom ↔ _
    rw [heval]
    simpa only [decodeCutParameters_encode] using cutEvaluation_raw_exact (Encodable.encode p) query

def cutFormationCompiler : CutParameters → Program := Classical.choose cutFormationCompiler_exists

theorem cutFormationCompiler_primrec : Primrec cutFormationCompiler :=
  (Classical.choose_spec cutFormationCompiler_exists).1

theorem cutFormationCompiler_domain (p : CutParameters) (φ : Syntax) :
    (cutFormationCompiler p).domain (φ.code RecordedHead.code) ↔ CutTarget p φ :=
  (Classical.choose_spec cutFormationCompiler_exists).2.1 p φ

theorem cutFormationCompiler_raw_domain (p : CutParameters) (query : Nat) :
    (cutFormationCompiler p).domain query ↔
      ∃ φ : Syntax, query = φ.code RecordedHead.code ∧ CutTarget p φ :=
  (Classical.choose_spec cutFormationCompiler_exists).2.2 p query

def boundedGuardCompiler : RecordedBoundedGuardProgram.Parameters → Program :=
  Classical.choose RecordedBoundedGuardProgram.compiler_exists

theorem boundedGuardCompiler_primrec : Primrec boundedGuardCompiler :=
  (Classical.choose_spec RecordedBoundedGuardProgram.compiler_exists).1

theorem boundedGuardCompiler_domain (p : RecordedBoundedGuardProgram.Parameters) (φ : Syntax) :
    (boundedGuardCompiler p).domain (φ.code RecordedHead.code) ↔
      RecordedBoundedGuardProgram.Target p φ :=
  (Classical.choose_spec RecordedBoundedGuardProgram.compiler_exists).2.1 p φ

theorem boundedGuardCompiler_raw_domain (p : RecordedBoundedGuardProgram.Parameters) (query : Nat) :
    (boundedGuardCompiler p).domain query ↔
      ∃ φ : Syntax, query = φ.code RecordedHead.code ∧ RecordedBoundedGuardProgram.Target p φ :=
  (Classical.choose_spec RecordedBoundedGuardProgram.compiler_exists).2.2 p query

/-- Successful raw executions recover both literal typed formulas; their
whole source support has an actual original ordinal bound. No source-row or
table existence is inferred just from these independent positive tests. -/
theorem raw_halting_outputs (AE : List Nat × List Nat) (δ : Nat) (c₁ c₂ : Program)
    (sourceQuery atomQuery : Nat)
    (formed : (cutFormationCompiler (AE, δ)).domain sourceQuery)
    (guard : (boundedGuardCompiler ((AE.2, δ), (c₁, c₂))).domain atomQuery) :
    ∃ φ ψ : Syntax, sourceQuery = φ.code RecordedHead.code ∧
      atomQuery = ψ.code RecordedHead.code ∧ CutTarget (AE, δ) φ ∧
        RecordedBoundedGuardProgram.Target ((AE.2, δ), (c₁, c₂)) ψ ∧
          ∀ μ ∈ (denotation φ).labelSupport, value μ < unionInterpretation δ := by
  obtain ⟨φ, hφ, hf⟩ := (cutFormationCompiler_raw_domain _ _).mp formed
  obtain ⟨ψ, hψ, hg⟩ := (boundedGuardCompiler_raw_domain _ _).mp guard
  exact ⟨φ, ψ, hφ, hψ, hf, hg, cutTarget_value_bound hf⟩

@[simp] theorem denotation_main_record (AE : List Nat × List Nat)
    (H : Finset (Nat × Shape Nat)) (labels : Nat → Shape Nat → Nat) (σ : Formula Nat) :
    denotation (σ.record (mainHeads AE.1.toFinset AE.2.toFinset H labels)) =
      σ.record (mainHeads AE.1.toFinset AE.2.toFinset H (fun a sh => labelOf (labels a sh))) := by
  rw [denotation, Formula.relabel_record]
  apply congrArg (fun h => σ.record h)
  funext a sh
  exact mainHeads_relabel _ _ H labels labelOf a sh

/-- A displayed finite positive guard witness plus the literal computed
formation test give actual cut membership. Admission and the whole source
cut bound are derived from the check, not assumed as semantic oracles. -/
theorem main_source_from_checks {R : Nat → Nat → Prop} (C : CommonCorePresentation R)
    (AE : List Nat × List Nat) (c₁ c₂ : Program)
    (R₁ R₂ : Ordinal.{0} → Ordinal.{0} → Prop)
    (edges₁ : EdgeCorrect c₁ R₁) (edges₂ : EdgeCorrect c₂ R₂)
    (a δ : Nat) (σ atom : Formula Nat) (H : Finset (Nat × Shape Nat))
    (labels : Nat → Shape Nat → Nat)
    (source : RecordedMainSource C AE.1.toFinset AE.2.toFinset a σ atom)
    (hereditary : HereditaryQueries H) (disjoint : Disjoint AE.1.toFinset AE.2.toFinset)
    (formed : cutFormationCheck (AE, δ)
      (σ.record (mainHeads AE.1.toFinset AE.2.toFinset H labels)) = true)
    (w : RecordedBoundedGuardProgram.Witness)
    (guard : RecordedBoundedGuardProgram.condition ((AE.2, δ), (c₁, c₂))
      ((atom.record (mainHeads AE.1.toFinset AE.2.toFinset H labels)).mainGuardRequirements
        AE.2.toFinset) w = true) :
    RecordedStage.cuts C AE.1.toFinset AE.2.toFinset (labelEdge R₁) (labelEdge R₂)
      a (labelOf δ) (denotation (σ.record (mainHeads AE.1.toFinset AE.2.toFinset H labels))) := by
  have hf := (cutFormationCheck_exact _ _).mp formed
  have ha : Supported (atom.record (mainHeads AE.1.toFinset AE.2.toFinset H labels)) := by
    intro μ hμ
    exact hf.1 μ (source.atom_support _ hμ)
  have hg : RecordedBoundedGuardProgram.Target ((AE.2, δ), (c₁, c₂))
      (atom.record (mainHeads AE.1.toFinset AE.2.toFinset H labels)) :=
    ⟨ha, (RecordedBoundedGuardProgram.condition_correct _ _).mp ⟨w, guard⟩⟩
  have bounded := ((RecordedBoundedGuardProgram.target_label_exact _ _ R₁ R₂ edges₁ edges₂).mp hg).2.2
  change GuardRequirements.Bounded (labelEdge R₁) (labelEdge R₂) (labelOf δ)
    ((denotation (atom.record (mainHeads AE.1.toFinset AE.2.toFinset H labels))).mainGuardRequirements
      AE.2.toFinset) at bounded
  rw [denotation_main_record] at bounded
  have hadm := hf.2.2.1
  have below := hf.2.2.2
  rw [denotation_main_record] at hadm below ⊢
  exact RecordedStage.main_source_bounded_cuts C AE.1.toFinset AE.2.toFinset
    (labelEdge R₁) (labelEdge R₂) a (labelOf δ) σ atom H
    (fun a sh => labelOf (labels a sh)) source hereditary disjoint bounded hadm below

/-- Both Programs are actually constructed above. Positive halting produces
the finite guard witness and source admission/cut bounds used in the original
stage theorem, at the unchanged literal source/table input. -/
theorem main_source_from_halting {R : Nat → Nat → Prop} (C : CommonCorePresentation R)
    (AE : List Nat × List Nat) (c₁ c₂ : Program)
    (R₁ R₂ : Ordinal.{0} → Ordinal.{0} → Prop)
    (edges₁ : EdgeCorrect c₁ R₁) (edges₂ : EdgeCorrect c₂ R₂)
    (a δ : Nat) (σ atom : Formula Nat) (H : Finset (Nat × Shape Nat))
    (labels : Nat → Shape Nat → Nat)
    (source : RecordedMainSource C AE.1.toFinset AE.2.toFinset a σ atom)
    (hereditary : HereditaryQueries H) (disjoint : Disjoint AE.1.toFinset AE.2.toFinset)
    (formed : (cutFormationCompiler (AE, δ)).domain
      ((σ.record (mainHeads AE.1.toFinset AE.2.toFinset H labels)).code RecordedHead.code))
    (guard : (boundedGuardCompiler ((AE.2, δ), (c₁, c₂))).domain
      ((atom.record (mainHeads AE.1.toFinset AE.2.toFinset H labels)).code RecordedHead.code)) :
    RecordedStage.cuts C AE.1.toFinset AE.2.toFinset (labelEdge R₁) (labelEdge R₂)
      a (labelOf δ) (denotation (σ.record (mainHeads AE.1.toFinset AE.2.toFinset H labels))) := by
  have hf := (cutFormationCompiler_domain _ _).mp formed
  have hg := (boundedGuardCompiler_domain _ _).mp guard
  obtain ⟨w, hw⟩ := (RecordedBoundedGuardProgram.condition_correct _ _).mpr hg.2
  exact main_source_from_checks C AE c₁ c₂ R₁ R₂ edges₁ edges₂ a δ σ atom H labels
    source hereditary disjoint ((cutFormationCheck_exact _ _).mpr hf) w hw

/-- Finite positive execution bounds suffice; a halting promise or semantic
admission/support/room contract is not an additional premise. -/
theorem main_source_from_positive_runs {R : Nat → Nat → Prop} (C : CommonCorePresentation R)
    (AE : List Nat × List Nat) (c₁ c₂ : Program)
    (R₁ R₂ : Ordinal.{0} → Ordinal.{0} → Prop)
    (edges₁ : EdgeCorrect c₁ R₁) (edges₂ : EdgeCorrect c₂ R₂)
    (a δ : Nat) (σ atom : Formula Nat) (H : Finset (Nat × Shape Nat))
    (labels : Nat → Shape Nat → Nat)
    (source : RecordedMainSource C AE.1.toFinset AE.2.toFinset a σ atom)
    (hereditary : HereditaryQueries H) (disjoint : Disjoint AE.1.toFinset AE.2.toFinset)
    (formationCutoff guardCutoff : Nat)
    (formed : RecordedBackgroundProgram.positive formationCutoff (cutFormationCompiler (AE, δ))
      ((σ.record (mainHeads AE.1.toFinset AE.2.toFinset H labels)).code RecordedHead.code) = true)
    (guard : RecordedBackgroundProgram.positive guardCutoff
      (boundedGuardCompiler ((AE.2, δ), (c₁, c₂)))
      ((atom.record (mainHeads AE.1.toFinset AE.2.toFinset H labels)).code RecordedHead.code) = true) :
    RecordedStage.cuts C AE.1.toFinset AE.2.toFinset (labelEdge R₁) (labelEdge R₂)
      a (labelOf δ) (denotation (σ.record (mainHeads AE.1.toFinset AE.2.toFinset H labels))) := by
  exact main_source_from_halting C AE c₁ c₂ R₁ R₂ edges₁ edges₂ a δ σ atom H labels
    source hereditary disjoint
    ((RecordedBackgroundProgram.positive_iff _ _).mp ⟨formationCutoff, formed⟩)
    ((RecordedBackgroundProgram.positive_iff _ _).mp ⟨guardCutoff, guard⟩)

/-- Raw queries are tied to the exact original source and atom recordings.
The compiler's exact raw image recovers the same typed formulas, then yields
the real source cut together with its genuine ordinal support bound. -/
theorem main_source_from_raw_halting {R : Nat → Nat → Prop} (C : CommonCorePresentation R)
    (AE : List Nat × List Nat) (c₁ c₂ : Program)
    (R₁ R₂ : Ordinal.{0} → Ordinal.{0} → Prop)
    (edges₁ : EdgeCorrect c₁ R₁) (edges₂ : EdgeCorrect c₂ R₂)
    (a δ : Nat) (σ atom : Formula Nat) (H : Finset (Nat × Shape Nat))
    (labels : Nat → Shape Nat → Nat)
    (source : RecordedMainSource C AE.1.toFinset AE.2.toFinset a σ atom)
    (hereditary : HereditaryQueries H) (disjoint : Disjoint AE.1.toFinset AE.2.toFinset)
    (sourceQuery atomQuery : Nat)
    (sourceCode : sourceQuery =
      (σ.record (mainHeads AE.1.toFinset AE.2.toFinset H labels)).code RecordedHead.code)
    (atomCode : atomQuery =
      (atom.record (mainHeads AE.1.toFinset AE.2.toFinset H labels)).code RecordedHead.code)
    (formed : (cutFormationCompiler (AE, δ)).domain sourceQuery)
    (guard : (boundedGuardCompiler ((AE.2, δ), (c₁, c₂))).domain atomQuery) :
    ∃ φ ψ : Syntax, sourceQuery = φ.code RecordedHead.code ∧ atomQuery = ψ.code RecordedHead.code ∧
      φ = σ.record (mainHeads AE.1.toFinset AE.2.toFinset H labels) ∧
      ψ = atom.record (mainHeads AE.1.toFinset AE.2.toFinset H labels) ∧
      RecordedStage.cuts C AE.1.toFinset AE.2.toFinset (labelEdge R₁) (labelEdge R₂)
        a (labelOf δ) (denotation φ) ∧
        ∀ μ ∈ (denotation φ).labelSupport, value μ < unionInterpretation δ := by
  obtain ⟨φ, hφ, hf⟩ := (cutFormationCompiler_raw_domain _ _).mp formed
  obtain ⟨ψ, hψ, _⟩ := (boundedGuardCompiler_raw_domain _ _).mp guard
  have hφeq : φ = σ.record (mainHeads AE.1.toFinset AE.2.toFinset H labels) :=
    Formula.code_injective RecordedHead.code RecordedHead.code_injective (hφ.symm.trans sourceCode)
  have hψeq : ψ = atom.record (mainHeads AE.1.toFinset AE.2.toFinset H labels) :=
    Formula.code_injective RecordedHead.code RecordedHead.code_injective (hψ.symm.trans atomCode)
  have hcut := main_source_from_halting C AE c₁ c₂ R₁ R₂ edges₁ edges₂ a δ σ atom H labels
    source hereditary disjoint (by simpa only [sourceCode] using formed)
    (by simpa only [atomCode] using guard)
  exact ⟨φ, ψ, hφ, hψ, hφeq, hψeq, by simpa only [hφeq] using hcut, cutTarget_value_bound hf⟩

end Alexander313.HereditaryOrdinalStageCuts
