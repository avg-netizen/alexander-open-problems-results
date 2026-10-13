import Alexander313.FiniteCertificateTransport
import Alexander313.OriginalSchemas

/-!
# Literal one-hole contexts for contextual label collapse

The hole occurs exactly once. Every surrounding term, binder, modal owner and
source program numeral stays literal. Erasure identifies the two fillings that
differ only at the selected indexed head. The erased collapse is therefore a
base validity; the recorded collapse itself is a stage generator, not a base
validity inferred from erasure.
-/

namespace Alexander313
namespace Formula

@[simp] theorem relabel_universalClosure {Owner Label Other : Type}
    (φ : Formula (RecordedHead Owner Label)) (f : Label → Other) :
    φ.universalClosure.relabel f = (φ.relabel f).universalClosure :=
  mapOwner_universalClosure φ _

@[simp] theorem closed_erase {Owner Label : Type}
    (φ : Formula (RecordedHead Owner Label)) : φ.erase.Closed ↔ φ.Closed := by
  simp only [erase, Closed, freeVars_mapOwner]

inductive Context (Owner : Type) where
  | hole
  | impLeft : Context Owner → Formula Owner → Context Owner
  | impRight : Formula Owner → Context Owner → Context Owner
  | conjLeft : Context Owner → Formula Owner → Context Owner
  | conjRight : Formula Owner → Context Owner → Context Owner
  | disjLeft : Context Owner → Formula Owner → Context Owner
  | disjRight : Formula Owner → Context Owner → Context Owner
  | neg : Context Owner → Context Owner
  | all : Nat → Context Owner → Context Owner
  | ex : Nat → Context Owner → Context Owner
  | know : Owner → Context Owner → Context Owner

namespace Context

def fill {Owner : Type} : Context Owner → Formula Owner → Formula Owner
  | .hole, φ => φ
  | .impLeft c ψ, φ => .imp (c.fill φ) ψ
  | .impRight ψ c, φ => .imp ψ (c.fill φ)
  | .conjLeft c ψ, φ => .conj (c.fill φ) ψ
  | .conjRight ψ c, φ => .conj ψ (c.fill φ)
  | .disjLeft c ψ, φ => .disj (c.fill φ) ψ
  | .disjRight ψ c, φ => .disj ψ (c.fill φ)
  | .neg c, φ => .neg (c.fill φ)
  | .all x c, φ => .all x (c.fill φ)
  | .ex x c, φ => .ex x (c.fill φ)
  | .know a c, φ => .know a (c.fill φ)

def mapOwner {Owner Other : Type} (f : Owner → Other) : Context Owner → Context Other
  | .hole => .hole
  | .impLeft c ψ => .impLeft (c.mapOwner f) (ψ.mapOwner f)
  | .impRight ψ c => .impRight (ψ.mapOwner f) (c.mapOwner f)
  | .conjLeft c ψ => .conjLeft (c.mapOwner f) (ψ.mapOwner f)
  | .conjRight ψ c => .conjRight (ψ.mapOwner f) (c.mapOwner f)
  | .disjLeft c ψ => .disjLeft (c.mapOwner f) (ψ.mapOwner f)
  | .disjRight ψ c => .disjRight (ψ.mapOwner f) (c.mapOwner f)
  | .neg c => .neg (c.mapOwner f)
  | .all x c => .all x (c.mapOwner f)
  | .ex x c => .ex x (c.mapOwner f)
  | .know a c => .know (f a) (c.mapOwner f)

@[simp] theorem mapOwner_fill {Owner Other : Type} (c : Context Owner)
    (f : Owner → Other) (φ : Formula Owner) :
    (c.fill φ).mapOwner f = (c.mapOwner f).fill (φ.mapOwner f) := by
  induction c <;> simp_all [fill, mapOwner, Formula.mapOwner]

theorem support_subset_fill {Owner Label : Type} [DecidableEq Label]
    (c : Context (RecordedHead Owner Label)) (φ : Formula (RecordedHead Owner Label)) :
    φ.labelSupport ⊆ (c.fill φ).labelSupport := by
  induction c with
  | hole => exact fun _ h => h
  | impLeft c ψ ih => exact fun _ h => Finset.mem_union_left _ (ih h)
  | impRight ψ c ih => exact fun _ h => Finset.mem_union_right _ (ih h)
  | conjLeft c ψ ih => exact fun _ h => Finset.mem_union_left _ (ih h)
  | conjRight ψ c ih => exact fun _ h => Finset.mem_union_right _ (ih h)
  | disjLeft c ψ ih => exact fun _ h => Finset.mem_union_left _ (ih h)
  | disjRight ψ c ih => exact fun _ h => Finset.mem_union_right _ (ih h)
  | neg c ih => exact ih
  | all x c ih => exact ih
  | ex x c ih => exact ih
  | know a c ih =>
    cases a with
    | live a => exact ih
    | ghost a => exact ih
    | indexed a ν => exact fun _ h => Finset.mem_insert_of_mem (ih h)

end Context

@[simp] theorem labelSupport_all_foldr {Owner Label : Type} [DecidableEq Label]
    (xs : List Nat) (φ : Formula (RecordedHead Owner Label)) :
    (xs.foldr Formula.all φ).labelSupport = φ.labelSupport := by
  induction xs <;> simp_all [labelSupport]

@[simp] theorem labelSupport_universalClosure {Owner Label : Type} [DecidableEq Label]
    (φ : Formula (RecordedHead Owner Label)) :
    φ.universalClosure.labelSupport = φ.labelSupport :=
  labelSupport_all_foldr _ _

@[simp] theorem labelSupport_iff {Owner Label : Type} [DecidableEq Label]
    (φ ψ : Formula (RecordedHead Owner Label)) :
    (Formula.iff φ ψ).labelSupport = φ.labelSupport ∪ ψ.labelSupport := by
  simp [Formula.iff, labelSupport, Finset.union_assoc, Finset.union_comm,
    Finset.union_left_comm]

theorem valid_iff_self {Owner : Type} (φ : Formula Owner) : Valid (Formula.iff φ φ) := by
  intro D hD M s
  exact ⟨fun h => h, fun h => h⟩

theorem valid_universalClosure {Owner : Type} {φ : Formula Owner} (h : Valid φ) :
    Valid φ.universalClosure := by
  intro D hD M s
  exact generalTruth_universalClosure M φ (fun t => h D hD M t) s

def contextualCollapse {Owner Label : Type}
    (c : Context (RecordedHead Owner Label)) (a : Owner) (α β : Label)
    (φ : Formula (RecordedHead Owner Label)) : Formula (RecordedHead Owner Label) :=
  (Formula.iff (c.fill (.know (.indexed a α) φ))
    (c.fill (.know (.indexed a β) φ))).universalClosure

@[simp] theorem erase_contextualCollapse {Owner Label : Type}
    (c : Context (RecordedHead Owner Label)) (a : Owner) (α β : Label)
    (φ : Formula (RecordedHead Owner Label)) :
    (contextualCollapse c a α β φ).erase =
      (Formula.iff ((c.mapOwner RecordedHead.erase).fill (.know a φ.erase))
        ((c.mapOwner RecordedHead.erase).fill (.know a φ.erase))).universalClosure := by
  simp only [contextualCollapse, erase, mapOwner_universalClosure, Formula.iff,
    mapOwner, Context.mapOwner_fill, RecordedHead.erase]

theorem contextualCollapse_erasure_valid {Owner Label : Type}
    (c : Context (RecordedHead Owner Label)) (a : Owner) (α β : Label)
    (φ : Formula (RecordedHead Owner Label)) : Valid (contextualCollapse c a α β φ).erase := by
  rw [erase_contextualCollapse]
  exact valid_universalClosure (valid_iff_self _)

@[simp] theorem contextualCollapse_relabel {Owner Label Other : Type}
    (c : Context (RecordedHead Owner Label)) (a : Owner) (α β : Label)
    (φ : Formula (RecordedHead Owner Label)) (f : Label → Other) :
    (contextualCollapse c a α β φ).relabel f =
      contextualCollapse (c.mapOwner (RecordedHead.mapLabel f)) a (f α) (f β) (φ.relabel f) := by
  simp only [contextualCollapse, relabel, mapOwner_universalClosure, Formula.iff,
    mapOwner, Context.mapOwner_fill, RecordedHead.mapLabel]

theorem contextualCollapse_left_mem {Owner Label : Type} [DecidableEq Label]
    (c : Context (RecordedHead Owner Label)) (a : Owner) (α β : Label)
    (φ : Formula (RecordedHead Owner Label)) :
    α ∈ (contextualCollapse c a α β φ).labelSupport := by
  rw [contextualCollapse, labelSupport_universalClosure, labelSupport_iff]
  exact Finset.mem_union_left _
    (c.support_subset_fill _ (Finset.mem_insert_self _ _))

theorem contextualCollapse_right_mem {Owner Label : Type} [DecidableEq Label]
    (c : Context (RecordedHead Owner Label)) (a : Owner) (α β : Label)
    (φ : Formula (RecordedHead Owner Label)) :
    β ∈ (contextualCollapse c a α β φ).labelSupport := by
  rw [contextualCollapse, labelSupport_universalClosure, labelSupport_iff]
  exact Finset.mem_union_right _
    (c.support_subset_fill _ (Finset.mem_insert_self _ _))

end Formula
end Alexander313
