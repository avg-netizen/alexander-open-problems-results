import Alexander313.Specification
import Alexander313.FreeVariables

/-!
# Universal closure and sentence operations

These lemmas supply the closure facts needed for the background schemas and
finite knowledge certificates. They use the existing weak semantics; no
substitution principle for arbitrary terms inside knowledge is added.
-/

namespace Alexander313

namespace Formula

variable {Owner : Type}

theorem mem_freeVars_all_foldr (xs : List Nat) (φ : Formula Owner) (v : Nat) :
    v ∈ (xs.foldr Formula.all φ).freeVars ↔ v ∈ φ.freeVars ∧ v ∉ xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldr_cons, freeVars, Finset.mem_erase, ih, List.mem_cons]
    tauto

theorem universalClosure_closed (φ : Formula Owner) : φ.universalClosure.Closed := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  have h := (mem_freeVars_all_foldr (φ.freeVars.sort (· ≤ ·)) φ v).mp hv
  exact h.2 (by simpa only [Finset.mem_sort] using h.1)

theorem universalClosure_eq_self_of_closed (φ : Formula Owner) (h : φ.Closed) :
    φ.universalClosure = φ := by
  simp [universalClosure, show φ.freeVars = ∅ from h]

theorem chain_closed (Γ : List (Formula Owner)) (φ : Formula Owner)
    : (∀ θ ∈ Γ, θ.Closed) → φ.Closed → (Formula.chain Γ φ).Closed := by
  induction Γ with
  | nil => intro _ hφ; exact hφ
  | cons θ Γ ih =>
    intro hΓ hφ
    have hθ := hΓ θ List.mem_cons_self
    have ht := ih (fun η hη => hΓ η (List.mem_cons_of_mem _ hη)) hφ
    change θ.freeVars ∪ (Formula.chain Γ φ).freeVars = ∅
    rw [hθ, ht]
    simp

end Formula

theorem truth_all_foldr {Owner : Type} (filtered : Bool) (P : RawPredicates Owner)
    (xs : List Nat) (φ : Formula Owner) (h : ∀ s, truth filtered P φ s) :
    ∀ s, truth filtered P (xs.foldr Formula.all φ) s := by
  induction xs with
  | nil => exact h
  | cons x xs ih =>
    intro s n
    exact ih (Function.update s x n)

theorem truth_universalClosure {Owner : Type} (filtered : Bool)
    (P : RawPredicates Owner) (φ : Formula Owner)
    (h : ∀ s, truth filtered P φ s) :
    ∀ s, truth filtered P φ.universalClosure s :=
  truth_all_foldr filtered P _ φ h

theorem generalTruth_all_foldr {Owner D : Type} (M : ModalModel Owner D)
    (xs : List Nat) (φ : Formula Owner) (h : ∀ s, generalTruth M φ s) :
    ∀ s, generalTruth M (xs.foldr Formula.all φ) s := by
  induction xs with
  | nil => exact h
  | cons x xs ih =>
    intro s n
    exact ih (Function.update s x n)

theorem generalTruth_universalClosure {Owner D : Type} (M : ModalModel Owner D)
    (φ : Formula Owner) (h : ∀ s, generalTruth M φ s) :
    ∀ s, generalTruth M φ.universalClosure s :=
  generalTruth_all_foldr M _ φ h

theorem filtered_reflection {Owner : Type} (P : RawPredicates Owner)
    (j : Owner) (φ : Formula Owner) (s : Assignment) :
    filteredTruth P (reflection j φ) s :=
  truth_universalClosure true P (.imp (.know j φ) φ)
    (fun t => filtered_factive P j φ t) s

end Alexander313
