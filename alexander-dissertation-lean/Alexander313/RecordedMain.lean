import Alexander313.RecordedMarkers
import Alexander313.RecordedReconstruction

/-!
# Literal guarded mechanicalness and code-image admissions

Each main row records its entire original source sentence and its distinguished
modal atom using one hereditary mask and one owner/argument-shape label table.
Code numerals are the original source family's actual column indices. The
finite guard witnesses occur as holder-local markers with distinct fresh
arithmetic shapes. This constructs the rows and their finite-pattern
preservation; it does not construct a prescribed ordinal lift, the ordinal
reflection theorem, the effective admission program or local truth verification.
-/

namespace Alexander313
namespace Formula

@[simp] theorem record_iff {Owner Label : Type} (φ ψ : Formula Owner)
    (head : Owner → Shape Owner → RecordedHead Owner Label) :
    (Formula.iff φ ψ).record head = Formula.iff (φ.record head) (ψ.record head) := rfl

@[simp] theorem record_all_foldr {Owner Label : Type} (xs : List Nat) (φ : Formula Owner)
    (head : Owner → Shape Owner → RecordedHead Owner Label) :
    (xs.foldr Formula.all φ).record head = xs.foldr Formula.all (φ.record head) := by
  induction xs <;> simp_all [Formula.record]

@[simp] theorem record_universalClosure {Owner Label : Type} (φ : Formula Owner)
    (head : Owner → Shape Owner → RecordedHead Owner Label) :
    φ.universalClosure.record head = (φ.record head).universalClosure := by
  simp only [Formula.universalClosure, Formula.freeVars_record, record_all_foldr]

@[simp] theorem relabel_record {Owner Label Other : Type} (φ : Formula Owner)
    (head : Owner → Shape Owner → RecordedHead Owner Label) (f : Label → Other) :
    (φ.record head).relabel f = φ.record (fun a sh => (head a sh).mapLabel f) := by
  induction φ <;> simp_all [Formula.record, Formula.relabel, Formula.mapOwner]

theorem record_iff_support_left {Owner Label : Type} [DecidableEq Label]
    (φ ψ : Formula Owner) (head : Owner → Shape Owner → RecordedHead Owner Label) :
    (φ.record head).labelSupport ⊆ ((Formula.iff φ ψ).record head).labelSupport := by
  rw [record_iff, labelSupport_iff]
  exact Finset.subset_union_left

end Formula

def mainHeads {Label : Type} (A E : Finset Nat) (H : Finset (Nat × Shape Nat))
    (labels : Nat → Shape Nat → Label) (a : Nat) (sh : Shape Nat) : RecordedHead Nat Label :=
  maskedHeads E H (fun b s => if b ∈ A then .indexed b (labels b s) else .live b) a sh

@[simp] theorem mainHeads_erase {Label : Type} (A E : Finset Nat)
    (H : Finset (Nat × Shape Nat)) (labels : Nat → Shape Nat → Label) (a : Nat) (sh : Shape Nat) :
    (mainHeads A E H labels a sh).erase = a := by
  apply maskedHeads_erase
  intro b s
  by_cases hb : b ∈ A <;> simp [hb, RecordedHead.erase]

@[simp] theorem mainHeads_relabel {Label Other : Type} (A E : Finset Nat)
    (H : Finset (Nat × Shape Nat)) (labels : Nat → Shape Nat → Label)
    (f : Label → Other) (a : Nat) (sh : Shape Nat) :
    (mainHeads A E H labels a sh).mapLabel f =
      mainHeads A E H (fun b s => f (labels b s)) a sh := by
  by_cases he : a ∈ E <;> by_cases hh : (a, sh) ∈ H <;> by_cases ha : a ∈ A <;>
    simp [mainHeads, maskedHeads, he, hh, ha, RecordedHead.mapLabel]

/-- Literal source rows. Core mechanicalness has only owner 0 active; code
    rows retain the source head outside the active/external sets. -/
inductive RecordedMainSource {R : Nat → Nat → Prop} (C : CommonCorePresentation R)
    (A E : Finset Nat) : Nat → Formula Nat → Formula Nat → Prop where
  | core_mechanical (j x e : Nat) (φ : Formula Nat) (core : A = {0})
      (fresh : e ∉ φ.freeVars) (distinct : e ≠ x) :
      RecordedMainSource C A E 0
        (parameterMechanicalSentence C.arithmetic (j + 1) x e φ) (.know (j + 1) φ)
  | core_code (i : Nat) (φ : UnaryFormula Nat) (active : i + 1 ∈ A)
      (outsideA : 0 ∉ A) (outsideE : 0 ∉ E) :
      RecordedMainSource C A E (i + 1)
        (codeSentence C.arithmetic 0 φ (C.family.unaryColumnIndex 0 φ)) (.know 0 φ.body)
  | subordinate_code (i j : Nat) (φ : UnaryFormula Nat) (below : R j i)
      (active : i + 1 ∈ A) (outsideA : j + 1 ∉ A) (outsideE : j + 1 ∉ E) :
      RecordedMainSource C A E (i + 1)
        (codeSentence C.arithmetic (j + 1) φ (C.family.unaryColumnIndex (j + 1) φ))
        (.know (j + 1) φ.body)

namespace RecordedMainSource

variable {R : Nat → Nat → Prop} {C : CommonCorePresentation R} {A E : Finset Nat}
    {a : Nat} {σ atom : Formula Nat}

theorem generator (h : RecordedMainSource C A E a σ atom) :
    CommonCoreGenerator R C.arithmetic C.family a σ := by
  cases h with
  | core_mechanical j x e φ core fresh distinct => exact .core_mechanical j x e φ fresh distinct
  | core_code i φ active outsideA outsideE => exact .core_code i φ
  | subordinate_code i j φ below active outsideA outsideE => exact .subordinate_code i j below φ

theorem holder_active (h : RecordedMainSource C A E a σ atom) : a ∈ A := by
  cases h with
  | core_mechanical j x e φ core fresh distinct => simp [core]
  | core_code i φ active outsideA outsideE => exact active
  | subordinate_code i j φ below active outsideA outsideE => exact active

theorem atom_support {Label : Type} [DecidableEq Label]
    (h : RecordedMainSource C A E a σ atom)
    (head : Nat → Shape Nat → RecordedHead Nat Label) :
    (atom.record head).labelSupport ⊆ (σ.record head).labelSupport := by
  cases h with
  | core_mechanical j x e φ core fresh distinct =>
    rw [parameterMechanicalSentence, Formula.record_universalClosure,
      Formula.labelSupport_universalClosure]
    exact Formula.record_iff_support_left (.know (j + 1) φ)
      (C.arithmetic.member (.var e) (.var x)) head
  | core_code i φ active outsideA outsideE =>
    exact Formula.record_iff_support_left (.know 0 φ.body)
      (C.arithmetic.member (Term.numeral (C.family.unaryColumnIndex 0 φ)) (.var φ.input)) head
  | subordinate_code i j φ below active outsideA outsideE =>
    exact Formula.record_iff_support_left (.know (j + 1) φ.body)
      (C.arithmetic.member (Term.numeral (C.family.unaryColumnIndex (j + 1) φ))
        (.var φ.input)) head

end RecordedMainSource

/-- Admission data for one actual padded main sentence. Fresh tags are chosen
    against all subshapes of that literal source sentence, and every guard point
    is a marker point. Semantic validity is not an admission test for these rows. -/
def RecordedMain {Label : Type} [DecidableEq Label] [LT Label]
    {R : Nat → Nat → Prop} (C : CommonCorePresentation R) (A E : Finset Nat)
    (a : Nat) (R₁ R₂ : Label → Label → Prop) (φ : Formula (RecordedHead Nat Label)) : Prop :=
  ∃ (σ atom : Formula Nat) (H : Finset (Nat × Shape Nat))
    (labels : Nat → Shape Nat → Label) (ms : List (Label × Nat)),
    RecordedMainSource C A E a σ atom ∧ HereditaryQueries H ∧ Disjoint A E ∧
    (ms.map Prod.snd).Nodup ∧
    (∀ p ∈ ms, (markerTag Nat p.2).shape ∉ σ.shape.subshapes) ∧
    (atom.record (mainHeads A E H labels)).MainGuarded R₁ R₂ E (markerPoints ms) ∧
    φ = markerPadding a ms (σ.record (mainHeads A E H labels)) ∧
    φ.RecordedAdmissible A E

namespace RecordedMain

variable {Label : Type} [DecidableEq Label] [LT Label]
    {R : Nat → Nat → Prop} {C : CommonCorePresentation R} {A E : Finset Nat}
    {a : Nat} {R₁ R₂ : Label → Label → Prop} {φ : Formula (RecordedHead Nat Label)}

theorem closed (h : RecordedMain C A E a R₁ R₂ φ) : φ.Closed := by
  obtain ⟨σ, atom, H, labels, ms, hs, _, _, _, _, _, rfl, _⟩ := h
  exact markerPadding_closed a ms _ ((Formula.closed_record _ _).mpr hs.generator.closed)

theorem admissible (h : RecordedMain C A E a R₁ R₂ φ) : φ.RecordedAdmissible A E := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, ha⟩ := h
  exact ha

theorem erased_member (h : RecordedMain C A E a R₁ R₂ φ) :
    C.family.effective.proves a φ.erase := by
  obtain ⟨σ, atom, H, labels, ms, hs, _, _, _, _, _, rfl, _⟩ := h
  apply markerPadding_source_member C a ms _
    ((Formula.closed_record _ _).mpr hs.generator.closed)
  simpa only [Formula.erase_record _ _ (mainHeads_erase A E H labels)] using C.member hs.generator

end RecordedMain

namespace RecordedMain

variable {Label : Type} [LinearOrder Label]
    {R : Nat → Nat → Prop} {C : CommonCorePresentation R} {A E : Finset Nat}
    {a : Nat} {R₁ R₂ : Label → Label → Prop} {φ : Formula (RecordedHead Nat Label)}

/-- All guard witnesses are in the actual padded support, so finite pattern
    preservation suffices for the whole literal main row, with no new ordinal
    room or source-code recompilation assumption. -/
theorem relabel (F : Finset Label) (f : Label → Label)
    (pattern : CoversLabelPattern R₁ R₂ F f) (h : RecordedMain C A E a R₁ R₂ φ)
    (support : φ.labelSupport ⊆ F) : RecordedMain C A E a R₁ R₂ (φ.relabel f) := by
  obtain ⟨σ, atom, H, labels, ms, hs, hh, hd, hn, hf, hg, rfl, ha⟩ := h
  have points : markerPoints ms ⊆ F := by
    intro μ hμ
    exact support (by rw [markerPadding_support]; exact Finset.mem_union_left _ hμ)
  have main : (σ.record (mainHeads A E H labels)).labelSupport ⊆ F := by
    intro μ hμ
    exact support (by rw [markerPadding_support]; exact Finset.mem_union_right _ hμ)
  refine ⟨σ, atom, H, (fun b sh => f (labels b sh)), ms.map (fun p => (f p.1, p.2)),
    hs, hh, hd, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [List.map_map, Function.comp_def] using hn
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact hf q hq
  · have guard := Formula.mainGuarded_relabel R₁ R₂ E (markerPoints ms) F
      (atom.record (mainHeads A E H labels)) f pattern points
      (fun μ hμ => main (hs.atom_support _ hμ)) hg
    simpa only [Formula.relabel_record, mainHeads_relabel, markerPoints_relabel] using guard
  · simp only [markerPadding_relabel, Formula.relabel_record, mainHeads_relabel]
  · exact Formula.recordedAdmissible_relabel A E _ f
      (fun μ hμ ν hν => (pattern.2.1 μ (support hμ) ν (support hν)).mpr) ha

end RecordedMain
end Alexander313
