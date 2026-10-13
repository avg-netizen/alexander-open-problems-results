import Alexander313.RecordedStageContexts
import Alexander313.RecordedStageMainColumns

/-!
# Finite generator lifts into the actual full recorded cuts

The reasoning lift uses admitted contextual-collapse rows to align its three
literal source-shared labels. The main lift constructs fresh holder-local
markers from the displayed finite guard-point set, admits the padded row, and
discharges its markers in the same cut. No source-body truth or recovery
assumption is used. Existence of the finite guard room and of a suitable label
table is separate from these finite proof transformations.
-/

namespace Alexander313
namespace Formula
namespace Context

def quantify {Owner : Type} (xs : List Nat) (c : Context Owner) : Context Owner :=
  xs.foldr Context.all c

@[simp] theorem fill_quantify {Owner : Type} (xs : List Nat) (c : Context Owner)
    (φ : Formula Owner) : (quantify xs c).fill φ = xs.foldr Formula.all (c.fill φ) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change Formula.all x ((quantify xs c).fill φ) = Formula.all x _
    rw [ih]

end Context

def mixedIndexedDeduction {Label : Type} (a : Nat) (γ μ ν : Label)
    (φ ψ : Formula (RecordedHead Nat Label)) : Formula (RecordedHead Nat Label) :=
  (Formula.imp (.know (.indexed a γ) (.imp φ ψ))
    (.imp (.know (.indexed a μ) φ) (.know (.indexed a ν) ψ))).universalClosure

@[simp] theorem mixedIndexedDeduction_support {Label : Type} [DecidableEq Label]
    (a : Nat) (γ μ ν : Label) (φ ψ : Formula (RecordedHead Nat Label)) :
    (mixedIndexedDeduction a γ μ ν φ ψ).labelSupport =
      insert γ (insert μ (insert ν (φ.labelSupport ∪ ψ.labelSupport))) := by
  ext ξ
  simp only [mixedIndexedDeduction, labelSupport_universalClosure, labelSupport,
    Finset.mem_union, Finset.mem_insert]
  tauto

theorem mixedIndexedDeduction_admissible_iff {Label : Type}
    [DecidableEq Label] [LT Label] (A E : Finset Nat) (a : Nat) (γ μ ν : Label)
    (φ ψ : Formula (RecordedHead Nat Label)) :
    (mixedIndexedDeduction a γ μ ν φ ψ).RecordedAdmissible A E ↔
      a ∈ A ∧ φ.RecordedAdmissible A E ∧ ψ.RecordedAdmissible A E ∧
      (∀ ξ ∈ φ.labelSupport, ξ < γ) ∧ (∀ ξ ∈ ψ.labelSupport, ξ < γ) ∧
      (∀ ξ ∈ φ.labelSupport, ξ < μ) ∧ (∀ ξ ∈ ψ.labelSupport, ξ < ν) := by
  simp only [mixedIndexedDeduction, recordedAdmissible_universalClosure,
    recordedAdmissible_imp_iff, recordedAdmissible_know_indexed,
    labelSupport, Finset.mem_union, or_imp, forall_and]
  tauto

end Formula

theorem mainHeads_active {Label : Type} (A E : Finset Nat)
    (H : Finset (Nat × Shape Nat)) (labels : Nat → Shape Nat → Label)
    (a : Nat) (sh : Shape Nat) (ha : a ∈ A) (hd : Disjoint A E) :
    mainHeads A E H labels a sh = .indexed a (labels a sh) := by
  have he : a ∉ E := fun he => Finset.disjoint_left.mp hd ha he
  simp [mainHeads, maskedHeads, he, ha]

/-- These are the two actual label links required by a source reasoning row.
Only syntactic occurrences of that row are tested. -/
def ReasoningLinks {Label : Type} (a : Nat) (labels : Nat → Shape Nat → Label)
    (R₁ : Label → Label → Prop) (σ : Formula Nat) : Prop :=
  ∀ φ ψ, σ = (Formula.imp (.know a (.imp φ ψ))
      (.imp (.know a φ) (.know a ψ))).universalClosure →
    R₁ (labels a φ.shape) (labels a (Formula.imp φ ψ).shape) ∧
      R₁ (labels a ψ.shape) (labels a (Formula.imp φ ψ).shape)

namespace RecordedStage

variable {Label : Type} [LinearOrder Label] {R : Nat → Nat → Prop}
    (C : CommonCorePresentation R) (A E : Finset Nat)
    (R₁ R₂ : Label → Label → Prop)

/-- Closed contextual fillings can be moved inside the actual cut without
changing their literal binders or making a numerical substitution. -/
theorem cuts_contextual_closed (a : Nat) (δ : Label)
    (c : Formula.Context (RecordedHead Nat Label)) (b : Nat) (μ ν : Label)
    (φ : Formula (RecordedHead Nat Label)) (hμν : R₁ μ ν)
    (hleft : (c.fill (.know (.indexed b μ) φ)).RecordedAdmissible A E)
    (hright : (c.fill (.know (.indexed b ν) φ)).RecordedAdmissible A E)
    (closedLeft : (c.fill (.know (.indexed b μ) φ)).Closed)
    (closedRight : (c.fill (.know (.indexed b ν) φ)).Closed)
    (belowLeft : ∀ ξ ∈ (c.fill (.know (.indexed b μ) φ)).labelSupport, ξ < δ)
    (belowRight : ∀ ξ ∈ (c.fill (.know (.indexed b ν) φ)).labelSupport, ξ < δ) :
    cuts C A E R₁ R₂ a δ (c.fill (.know (.indexed b μ) φ)) ↔
      cuts C A E R₁ R₂ a δ (c.fill (.know (.indexed b ν) φ)) := by
  have h := cuts_contextual_query C A E R₁ R₂ a δ c b μ ν φ hμν
    hleft hright belowLeft belowRight (fun _ => 0)
  simpa only [Formula.close_eq_self_of_closed _ closedLeft,
    Formula.close_eq_self_of_closed _ closedRight] using h

/-- The actual recorded reasoning row generally has three different labels.
Two concrete contextual-collapse admissions reduce it to the admitted
same-label reasoning row. No ordinal reflection or cut soundness is used. -/
theorem mixed_deduction_cuts (a : Nat) (δ γ μ ν : Label)
    (φ ψ : Formula (RecordedHead Nat Label)) (leftLink : R₁ μ γ) (rightLink : R₁ ν γ)
    (hadm : (Formula.mixedIndexedDeduction a γ μ ν φ ψ).RecordedAdmissible A E)
    (below : ∀ ξ ∈ (Formula.mixedIndexedDeduction a γ μ ν φ ψ).labelSupport, ξ < δ) :
    cuts C A E R₁ R₂ a δ (Formula.mixedIndexedDeduction a γ μ ν φ ψ) := by
  obtain ⟨ha, hφ, hψ, φγ, ψγ, φμ, ψν⟩ :=
    (Formula.mixedIndexedDeduction_admissible_iff A E a γ μ ν φ ψ).mp hadm
  have adm₂ : (Formula.mixedIndexedDeduction a γ γ ν φ ψ).RecordedAdmissible A E :=
    (Formula.mixedIndexedDeduction_admissible_iff A E a γ γ ν φ ψ).mpr
      ⟨ha, hφ, hψ, φγ, ψγ, φγ, ψν⟩
  have adm₃ : (Formula.mixedIndexedDeduction a γ γ γ φ ψ).RecordedAdmissible A E :=
    (Formula.mixedIndexedDeduction_admissible_iff A E a γ γ γ φ ψ).mpr
      ⟨ha, hφ, hψ, φγ, ψγ, φγ, ψγ⟩
  have γδ : γ < δ := below γ (by simp)
  have νδ : ν < δ := below ν (by simp)
  have bodyBelow : ∀ ξ ∈ φ.labelSupport ∪ ψ.labelSupport, ξ < δ := by
    intro ξ hξ
    apply below ξ
    rw [Formula.mixedIndexedDeduction_support]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hξ))
  have below₂ : ∀ ξ ∈ (Formula.mixedIndexedDeduction a γ γ ν φ ψ).labelSupport,
      ξ < δ := by
    intro ξ hξ
    simp only [Formula.mixedIndexedDeduction_support, Finset.mem_insert] at hξ
    rcases hξ with rfl | rfl | rfl | hξ
    · exact γδ
    · exact γδ
    · exact νδ
    · exact bodyBelow ξ hξ
  have below₃ : ∀ ξ ∈ (Formula.mixedIndexedDeduction a γ γ γ φ ψ).labelSupport,
      ξ < δ := by
    intro ξ hξ
    simp only [Formula.mixedIndexedDeduction_support, Finset.mem_insert] at hξ
    rcases hξ with rfl | rfl | rfl | hξ
    · exact γδ
    · exact γδ
    · exact γδ
    · exact bodyBelow ξ hξ
  let xs := ((Formula.imp (.know (.indexed a γ) (.imp φ ψ))
    (.imp (.know (.indexed a μ) φ) (.know (.indexed a ν) ψ))).freeVars.sort (· ≤ ·))
  let c₁ : Formula.Context (RecordedHead Nat Label) := .quantify xs
    (.impRight (.know (.indexed a γ) (.imp φ ψ))
      (.impLeft .hole (.know (.indexed a ν) ψ)))
  let c₂ : Formula.Context (RecordedHead Nat Label) := .quantify xs
    (.impRight (.know (.indexed a γ) (.imp φ ψ))
      (.impRight (.know (.indexed a γ) φ) .hole))
  have fill₁μ : c₁.fill (.know (.indexed a μ) φ) =
      Formula.mixedIndexedDeduction a γ μ ν φ ψ := by
    simp only [c₁, Formula.Context.fill_quantify, Formula.Context.fill,
      Formula.mixedIndexedDeduction, Formula.universalClosure, xs]
  have fill₁γ : c₁.fill (.know (.indexed a γ) φ) =
      Formula.mixedIndexedDeduction a γ γ ν φ ψ := by
    simp only [c₁, Formula.Context.fill_quantify, Formula.Context.fill,
      Formula.mixedIndexedDeduction, Formula.universalClosure, xs, Formula.freeVars]
  have fill₂ν : c₂.fill (.know (.indexed a ν) ψ) =
      Formula.mixedIndexedDeduction a γ γ ν φ ψ := by
    simp only [c₂, Formula.Context.fill_quantify, Formula.Context.fill,
      Formula.mixedIndexedDeduction, Formula.universalClosure, xs, Formula.freeVars]
  have fill₂γ : c₂.fill (.know (.indexed a γ) ψ) =
      Formula.mixedIndexedDeduction a γ γ γ φ ψ := by
    simp only [c₂, Formula.Context.fill_quantify, Formula.Context.fill,
      Formula.mixedIndexedDeduction, Formula.universalClosure, xs, Formula.freeVars]
  have closed (α β : Label) : (Formula.mixedIndexedDeduction a γ α β φ ψ).Closed :=
    Formula.universalClosure_closed _
  have move₁ := cuts_contextual_closed C A E R₁ R₂ a δ c₁ a μ γ φ leftLink
    (by simpa only [fill₁μ] using hadm) (by simpa only [fill₁γ] using adm₂)
    (by simpa only [fill₁μ] using closed μ ν) (by simpa only [fill₁γ] using closed γ ν)
    (by simpa only [fill₁μ] using below) (by simpa only [fill₁γ] using below₂)
  have move₂ := cuts_contextual_closed C A E R₁ R₂ a δ c₂ a ν γ ψ rightLink
    (by simpa only [fill₂ν] using adm₂) (by simpa only [fill₂γ] using adm₃)
    (by simpa only [fill₂ν] using closed γ ν) (by simpa only [fill₂γ] using closed γ γ)
    (by simpa only [fill₂ν] using below₂) (by simpa only [fill₂γ] using below₃)
  rw [fill₁μ, fill₁γ] at move₁
  rw [fill₂ν, fill₂γ] at move₂
  have base : cuts C A E R₁ R₂ a δ (Formula.mixedIndexedDeduction a γ γ γ φ ψ) := by
    apply cuts_of_admission C A E R₁ R₂ a δ (.background (.deduction γ φ ψ adm₃))
    exact below₃
  exact move₁.mpr (move₂.mpr base)

/-- Every displayed finite guard set with room in the requested cut gives an
actual main admission. Freshness is constructed from the literal source
subshapes; the source program numeral and all binder names are preserved. -/
theorem main_source_cuts (a : Nat) (δ : Label) (σ atom : Formula Nat)
    (H : Finset (Nat × Shape Nat)) (labels : Nat → Shape Nat → Label)
    (B : Finset Label) (source : RecordedMainSource C A E a σ atom)
    (hereditary : HereditaryQueries H) (disjoint : Disjoint A E)
    (guard : (atom.record (mainHeads A E H labels)).MainGuarded R₁ R₂ E B)
    (hadm : (σ.record (mainHeads A E H labels)).RecordedAdmissible A E)
    (below : ∀ μ ∈ (σ.record (mainHeads A E H labels)).labelSupport, μ < δ)
    (room : ∀ μ ∈ B, μ < δ) :
    cuts C A E R₁ R₂ a δ (σ.record (mainHeads A E H labels)) := by
  obtain ⟨ms, points, nodup, fresh⟩ := freshMarkerBundle σ.shape.subshapes B
  have hmain : RecordedMain C A E a R₁ R₂
      (markerPadding a ms (σ.record (mainHeads A E H labels))) := by
    refine ⟨σ, atom, H, labels, ms, source, hereditary, disjoint, nodup, fresh, ?_, rfl, ?_⟩
    · simpa only [points] using guard
    · exact markerPadding_admissible A E a source.holder_active ms _ hadm
  apply main_unpadded_cuts C A E R₁ R₂ a δ ms _ hmain
  intro μ hμ
  rw [markerPadding_support, points] at hμ
  exact (Finset.mem_union.mp hμ).elim (room μ) (below μ)

/-- Every original background constructor has a literal lift. Reasoning uses
the two displayed table links; introspection obtains its strict label order
from the actual recorded nesting check. -/
theorem background_source_cuts (a : Nat) (δ : Label) (σ : Formula Nat)
    (H : Finset (Nat × Shape Nat)) (labels : Nat → Shape Nat → Label)
    (ha : a ∈ A) (disjoint : Disjoint A E) (source : BackgroundGenerator a σ)
    (links : ReasoningLinks a labels R₁ σ)
    (hadm : (σ.record (mainHeads A E H labels)).RecordedAdmissible A E)
    (below : ∀ μ ∈ (σ.record (mainHeads A E H labels)).labelSupport, μ < δ) :
    cuts C A E R₁ R₂ a δ (σ.record (mainHeads A E H labels)) := by
  let head := mainHeads A E H labels
  have own (sh : Shape Nat) : head a sh = .indexed a (labels a sh) :=
    mainHeads_active A E H labels a sh ha disjoint
  cases source with
  | arithmetic hp =>
    exact cuts_of_admission C A E R₁ R₂ a δ
      (.background (.arithmetic (hp.record head) hadm)) below
  | assigned φ s hv =>
    rw [Formula.record_close] at hadm below ⊢
    exact cuts_assigned_validity C A E R₁ R₂ a δ (φ.record head) s (hv.record head)
      ((Formula.recordedAdmissible_close A E _ s).mp hadm)
      (by simpa only [Formula.labelSupport_close] using below)
  | reflection b φ =>
    have hrec : (reflection b φ).record head =
        reflection (head b φ.shape) (φ.record head) := by
      simp only [reflection, Formula.record_universalClosure, Formula.record]
    rw [hrec] at hadm below ⊢
    exact cuts_of_admission C A E R₁ R₂ a δ
      (.background (.reflection (head b φ.shape) (φ.record head) hadm)) below
  | structural hs =>
    cases hs with
    | validity φ hv =>
      have hrec : (Formula.universalClosure (.know a φ)).record head =
          Formula.universalClosure (.know (.indexed a (labels a φ.shape)) (φ.record head)) := by
        simp only [Formula.record_universalClosure, Formula.record, own]
      rw [hrec] at hadm below ⊢
      exact cuts_of_admission C A E R₁ R₂ a δ
        (.background (.own_validity (labels a φ.shape) (φ.record head) (hv.record head) hadm))
        below
    | reasoning φ ψ =>
      have hrec : (Formula.universalClosure (.imp (.know a (.imp φ ψ))
          (.imp (.know a φ) (.know a ψ)))).record head =
          Formula.mixedIndexedDeduction a (labels a (Formula.imp φ ψ).shape)
            (labels a φ.shape) (labels a ψ.shape) (φ.record head) (ψ.record head) := by
        simp only [Formula.record_universalClosure, Formula.record, own,
          Formula.mixedIndexedDeduction]
      have hl := links φ ψ rfl
      rw [hrec] at hadm below ⊢
      exact mixed_deduction_cuts C A E R₁ R₂ a δ _ _ _ _ _ hl.1 hl.2 hadm below
    | introspection φ =>
      have hrec : (Formula.universalClosure (.imp (.know a φ) (.know a (.know a φ)))).record
          head = Formula.indexedIntrospection a (labels a φ.shape)
            (labels a (Formula.know a φ).shape) (φ.record head) := by
        simp only [Formula.record_universalClosure, Formula.record, own,
          Formula.indexedIntrospection]
      rw [hrec] at hadm below ⊢
      have ha' := (Formula.recordedAdmissible_universalClosure A E _).mp hadm
      have pair := (Formula.recordedAdmissible_imp_iff A E _ _).mp ha'
      have outer := (Formula.recordedAdmissible_know_indexed A E a
        (labels a (Formula.know a φ).shape) _).mp pair.2
      have hμν : labels a φ.shape < labels a (Formula.know a φ).shape :=
        outer.2.2 _ (by simp [Formula.labelSupport])
      exact cuts_of_admission C A E R₁ R₂ a δ
        (.background (.introspection _ _ _ hμν hadm)) below

end RecordedStage

/-- Finite lift data lists actual source generators, with the additional
literal links or finite guard witnesses they need. It is neither a stage
admission contract nor a source-recovery predicate. -/
inductive GeneratorLiftData {Label : Type} [LinearOrder Label]
    {R : Nat → Nat → Prop} (C : CommonCorePresentation R) (A E : Finset Nat)
    (a : Nat) (H : Finset (Nat × Shape Nat)) (labels : Nat → Shape Nat → Label)
    (R₁ R₂ : Label → Label → Prop) (B : Finset Label) : Formula Nat → Prop where
  | background {σ} : BackgroundGenerator a σ → ReasoningLinks a labels R₁ σ →
      GeneratorLiftData C A E a H labels R₁ R₂ B σ
  | main {σ} (atom : Formula Nat) : RecordedMainSource C A E a σ atom →
      (atom.record (mainHeads A E H labels)).MainGuarded R₁ R₂ E B →
      GeneratorLiftData C A E a H labels R₁ R₂ B σ

namespace GeneratorLiftData

variable {Label : Type} [LinearOrder Label] {R : Nat → Nat → Prop}
    {C : CommonCorePresentation R} {A E : Finset Nat} {a : Nat}
    {H : Finset (Nat × Shape Nat)} {labels : Nat → Shape Nat → Label}
    {R₁ R₂ : Label → Label → Prop} {B : Finset Label} {σ : Formula Nat}

theorem generator (data : GeneratorLiftData C A E a H labels R₁ R₂ B σ) :
    CommonCoreGenerator R C.arithmetic C.family a σ := by
  cases data with
  | background source links => exact .background a source
  | main atom source guard => exact source.generator

theorem cuts (data : GeneratorLiftData C A E a H labels R₁ R₂ B σ)
    (ha : a ∈ A) (hereditary : HereditaryQueries H) (disjoint : Disjoint A E)
    (δ : Label) (hadm : (σ.record (mainHeads A E H labels)).RecordedAdmissible A E)
    (below : ∀ μ ∈ (σ.record (mainHeads A E H labels)).labelSupport, μ < δ)
    (room : ∀ μ ∈ B, μ < δ) :
    RecordedStage.cuts C A E R₁ R₂ a δ (σ.record (mainHeads A E H labels)) := by
  cases data with
  | background source links =>
    exact RecordedStage.background_source_cuts C A E R₁ R₂ a δ σ H labels ha disjoint
      source links hadm below
  | main atom source guard =>
    exact RecordedStage.main_source_cuts C A E R₁ R₂ a δ σ atom H labels B source hereditary
      disjoint guard hadm below room

end GeneratorLiftData
end Alexander313
