import Alexander313.RecordedSupport
import Alexander313.RecordedLogic
import Mathlib.Data.Finset.Sort

/-!
# Literal finite label renaming

Only indexed modal labels change. Owners, live and ghost modes, arithmetic
terms, binder names and source program numerals stay literal. Renaming commutes
with every numerical instance and arbitrary syntactic term replacement.
Finite order compression below proves preservation of strict nesting only;
it is not a Wilken <=1/<=2 pattern reflection or an effective ordinal code.
-/

namespace Alexander313

namespace RecordedHead

def mapLabel {Owner Label Other : Type} (f : Label → Other) :
    RecordedHead Owner Label → RecordedHead Owner Other
  | .live a => .live a
  | .indexed a ν => .indexed a (f ν)
  | .ghost a => .ghost a

@[simp] theorem erase_mapLabel {Owner Label Other : Type}
    (f : Label → Other) (a : RecordedHead Owner Label) :
    (a.mapLabel f).erase = a.erase := by
  cases a <;> rfl

end RecordedHead

namespace Formula

variable {Owner Label Other : Type}

def relabel (φ : Formula (RecordedHead Owner Label)) (f : Label → Other) :
    Formula (RecordedHead Owner Other) := φ.mapOwner (RecordedHead.mapLabel f)

@[simp] theorem relabel_subst (φ : Formula (RecordedHead Owner Label))
    (f : Label → Other) (σ : NumericalSubstitution) :
    (φ.subst σ).relabel f = (φ.relabel f).subst σ :=
  mapOwner_subst φ _ σ

@[simp] theorem relabel_close (φ : Formula (RecordedHead Owner Label))
    (f : Label → Other) (s : Assignment) :
    (φ.close s).relabel f = (φ.relabel f).close s :=
  mapOwner_close φ _ s

@[simp] theorem relabel_substTerm (φ : Formula (RecordedHead Owner Label))
    (f : Label → Other) (x : Nat) (t : Term) :
    (φ.substTerm x t).relabel f = (φ.relabel f).substTerm x t :=
  mapOwner_substTerm φ _ x t

@[simp] theorem freeVars_relabel (φ : Formula (RecordedHead Owner Label))
    (f : Label → Other) : (φ.relabel f).freeVars = φ.freeVars :=
  freeVars_mapOwner φ _

@[simp] theorem erase_relabel (φ : Formula (RecordedHead Owner Label))
    (f : Label → Other) : (φ.relabel f).erase = φ.erase := by
  induction φ <;> simp_all [relabel, mapOwner, erase, RecordedHead.erase_mapLabel]

@[simp] theorem relabel_id (φ : Formula (RecordedHead Owner Label)) :
    φ.relabel id = φ := by
  induction φ with
  | know a φ ih => cases a <;> simp_all [relabel, mapOwner, RecordedHead.mapLabel]
  | _ => simp_all [relabel, mapOwner]

@[simp] theorem labelSupport_relabel [DecidableEq Label] [DecidableEq Other]
    (φ : Formula (RecordedHead Owner Label)) (f : Label → Other) :
    (φ.relabel f).labelSupport = φ.labelSupport.image f := by
  induction φ with
  | know a φ ih =>
    cases a <;>
      simp_all [relabel, mapOwner, RecordedHead.mapLabel, labelSupport,
        Finset.image_insert]
  | _ => simp_all [relabel, mapOwner, labelSupport, Finset.image_union]

theorem relabel_congr [DecidableEq Label]
    (φ : Formula (RecordedHead Owner Label)) (f g : Label → Other)
    (h : ∀ ν ∈ φ.labelSupport, f ν = g ν) : φ.relabel f = φ.relabel g := by
  revert h
  induction φ with
  | falsum => intro _; rfl
  | equal t u => intro _; rfl
  | imp φ ψ ihφ ihψ =>
    intro h
    have hφ := ihφ (fun ν hν => h ν (Finset.mem_union_left _ hν))
    have hψ := ihψ (fun ν hν => h ν (Finset.mem_union_right _ hν))
    exact congrArg₂ Formula.imp hφ hψ
  | conj φ ψ ihφ ihψ =>
    intro h
    have hφ := ihφ (fun ν hν => h ν (Finset.mem_union_left _ hν))
    have hψ := ihψ (fun ν hν => h ν (Finset.mem_union_right _ hν))
    exact congrArg₂ Formula.conj hφ hψ
  | disj φ ψ ihφ ihψ =>
    intro h
    have hφ := ihφ (fun ν hν => h ν (Finset.mem_union_left _ hν))
    have hψ := ihψ (fun ν hν => h ν (Finset.mem_union_right _ hν))
    exact congrArg₂ Formula.disj hφ hψ
  | neg φ ih => intro h; exact congrArg Formula.neg (ih h)
  | all x φ ih => intro h; exact congrArg (Formula.all x) (ih h)
  | ex x φ ih => intro h; exact congrArg (Formula.ex x) (ih h)
  | know a φ ih =>
    intro h
    cases a with
    | live a => exact congrArg (Formula.know (.live a)) (ih h)
    | ghost a => exact congrArg (Formula.know (.ghost a)) (ih h)
    | indexed a ν =>
      have hν := h ν (Finset.mem_insert_self _ _)
      have hφ := ih (fun μ hμ => h μ (Finset.mem_insert_of_mem hμ))
      change Formula.know (.indexed a (f ν)) (φ.relabel f) =
        Formula.know (.indexed a (g ν)) (φ.relabel g)
      rw [hν, hφ]

theorem relabel_fixed [DecidableEq Label]
    (φ : Formula (RecordedHead Owner Label)) (f : Label → Label)
    (fixed : ∀ ν ∈ φ.labelSupport, f ν = ν) : φ.relabel f = φ := by
  exact (relabel_congr φ f id fixed).trans (relabel_id φ)

/-- A finite pattern map only needs strict-order preservation on this formula's
    support. No total monotonicity outside the support is assumed. -/
theorem globallyStratified_relabel [LinearOrder Label] [LinearOrder Other]
    (φ : Formula (RecordedHead Owner Label)) (f : Label → Other)
    (strict : ∀ μ ∈ φ.labelSupport, ∀ ν ∈ φ.labelSupport,
      μ < ν → f μ < f ν) (hφ : φ.GloballyStratified) :
    (φ.relabel f).GloballyStratified := by
  revert strict hφ
  induction φ with
  | falsum => intro _ _; trivial
  | equal t u => intro _ _; trivial
  | imp φ ψ ihφ ihψ =>
    intro strict hφ
    exact ⟨ihφ (fun μ hμ ν hν => strict μ (Finset.mem_union_left _ hμ)
      ν (Finset.mem_union_left _ hν)) hφ.1,
      ihψ (fun μ hμ ν hν => strict μ (Finset.mem_union_right _ hμ)
      ν (Finset.mem_union_right _ hν)) hφ.2⟩
  | conj φ ψ ihφ ihψ =>
    intro strict hφ
    exact ⟨ihφ (fun μ hμ ν hν => strict μ (Finset.mem_union_left _ hμ)
      ν (Finset.mem_union_left _ hν)) hφ.1,
      ihψ (fun μ hμ ν hν => strict μ (Finset.mem_union_right _ hμ)
      ν (Finset.mem_union_right _ hν)) hφ.2⟩
  | disj φ ψ ihφ ihψ =>
    intro strict hφ
    exact ⟨ihφ (fun μ hμ ν hν => strict μ (Finset.mem_union_left _ hμ)
      ν (Finset.mem_union_left _ hν)) hφ.1,
      ihψ (fun μ hμ ν hν => strict μ (Finset.mem_union_right _ hμ)
      ν (Finset.mem_union_right _ hν)) hφ.2⟩
  | neg φ ih => intro strict hφ; exact ih strict hφ
  | all x φ ih => intro strict hφ; exact ih strict hφ
  | ex x φ ih => intro strict hφ; exact ih strict hφ
  | know a φ ih =>
    intro strict hφ
    cases a with
    | live a => exact ih strict hφ
    | ghost a => exact ih strict hφ
    | indexed a ν =>
      refine ⟨ih (fun μ hμ ξ hξ => strict μ (Finset.mem_insert_of_mem hμ)
        ξ (Finset.mem_insert_of_mem hξ)) hφ.1, ?_⟩
      intro ξ hξ
      change ξ ∈ (φ.relabel f).labelSupport at hξ
      rw [labelSupport_relabel] at hξ
      obtain ⟨μ, hμ, rfl⟩ := Finset.mem_image.mp hξ
      exact strict μ (Finset.mem_insert_of_mem hμ) ν
        (Finset.mem_insert_self _ _) (hφ.2 μ hμ)

end Formula

/-- An actual finite order compression, using the increasing enumeration of F.
    Values outside F are auxiliary and are never used in a supported formula. -/
def finiteLabelRank {Label : Type} [LinearOrder Label]
    (F : Finset Label) (ν : Label) : Nat :=
  if h : ν ∈ F then ((F.orderIsoOfFin rfl).symm ⟨ν, h⟩).val else 0

theorem finiteLabelRank_lt_card {Label : Type} [LinearOrder Label]
    (F : Finset Label) {ν : Label} (hν : ν ∈ F) :
    finiteLabelRank F ν < F.card := by
  simpa only [finiteLabelRank, dif_pos hν] using
    ((F.orderIsoOfFin rfl).symm ⟨ν, hν⟩).isLt

theorem finiteLabelRank_lt_iff {Label : Type} [LinearOrder Label]
    (F : Finset Label) {μ ν : Label} (hμ : μ ∈ F) (hν : ν ∈ F) :
    finiteLabelRank F μ < finiteLabelRank F ν ↔ μ < ν := by
  simp only [finiteLabelRank, dif_pos hμ, dif_pos hν]
  change (F.orderIsoOfFin rfl).symm ⟨μ, hμ⟩ <
    (F.orderIsoOfFin rfl).symm ⟨ν, hν⟩ ↔ μ < ν
  exact (F.orderIsoOfFin rfl).symm.lt_iff_lt

theorem finiteLabelRank_stratified {Owner Label : Type} [LinearOrder Label]
    (φ : Formula (RecordedHead Owner Label)) (hφ : φ.GloballyStratified) :
    (φ.relabel (finiteLabelRank φ.labelSupport)).GloballyStratified :=
  φ.globallyStratified_relabel _
    (fun μ hμ ν hν => (finiteLabelRank_lt_iff _ hμ hν).mpr) hφ

end Alexander313
