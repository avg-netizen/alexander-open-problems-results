import Mathlib.SetTheory.Ordinal.Family
import Mathlib.Tactic.Common

/-!
# The finite-level closure rules in Wilken Definition 2.1

The theta family is a parameter of the hull *definition*. The actual
descending-level recursion is constructed in `FiniteCollapse`. This
module also proves the finite-witness continuity of Definition 2.1;
it does not identify arbitrary supplied families with the source functions.
-/

namespace Alexander313.Wilken

inductive Hull (omega : Nat → Ordinal) (theta : Nat → Ordinal → Ordinal)
    (n m : Nat) (α β : Ordinal) : Ordinal → Prop where
  | below_base {ξ} : ξ < omega m → Hull omega theta n m α β ξ
  | below_parameter {ξ} : ξ < β → Hull omega theta n m α β ξ
  | add {ξ η} : Hull omega theta n m α β ξ → Hull omega theta n m α β η →
      Hull omega theta n m α β (ξ + η)
  | higher {k ξ} : m < k → k < n → ξ < omega (k + 2) →
      Hull omega theta n m α β ξ → Hull omega theta n m α β (theta k ξ)
  | «local» {ξ} : ξ < α → Hull omega theta n m α β ξ →
      Hull omega theta n m α β (theta m ξ)

/-- Wilken Lemma 2.2(b), at the inductively defined hull level. -/
theorem hull_mono {omega : Nat → Ordinal} {theta : Nat → Ordinal → Ordinal}
    {n m : Nat} {α β α' β' ξ : Ordinal}
    (hα : α ≤ α') (hβ : β ≤ β') (h : Hull omega theta n m α β ξ) :
    Hull omega theta n m α' β' ξ := by
  induction h with
  | below_base h => exact .below_base h
  | below_parameter h => exact .below_parameter (lt_of_lt_of_le h hβ)
  | add _ _ ihξ ihη => exact .add ihξ ihη
  | higher hmk hkn hsort _ ih => exact .higher hmk hkn hsort ih
  | «local» hξ _ ih => exact .«local» (lt_of_lt_of_le hξ hα) ih

/-- Wilken Lemma 2.2(a), without using an effectiveness or minimum oracle. -/
theorem hull_absorb {omega : Nat → Ordinal} {theta : Nat → Ordinal → Ordinal}
    {n m : Nat} {α β δ ξ : Ordinal}
    (hδ : ∀ η < δ, Hull omega theta n m α β η)
    (h : Hull omega theta n m α δ ξ) : Hull omega theta n m α β ξ := by
  induction h with
  | below_base h => exact .below_base h
  | below_parameter h => exact hδ _ h
  | add _ _ ihξ ihη => exact .add ihξ ihη
  | higher hmk hkn hsort _ ih => exact .higher hmk hkn hsort ih
  | «local» hξ _ ih => exact .«local» hξ ih

/-- Only the higher-sort calls and already-defined local calls affect a hull.
This permits well-founded recursion without supplying future local values. -/
theorem hull_family_congr {omega : Nat → Ordinal}
    {theta theta' : Nat → Ordinal → Ordinal} {n m : Nat} {α β ξ : Ordinal}
    (higher : ∀ k, m < k → k < n → ∀ η, η < omega (k + 2) →
      theta k η = theta' k η)
    («local» : ∀ η, η < α → theta m η = theta' m η) :
    Hull omega theta n m α β ξ ↔ Hull omega theta' n m α β ξ := by
  have forward : ∀ {first second : Nat → Ordinal → Ordinal},
      (∀ k, m < k → k < n → ∀ η, η < omega (k + 2) → first k η = second k η) →
      (∀ η, η < α → first m η = second m η) →
      Hull omega first n m α β ξ → Hull omega second n m α β ξ := by
    intro first second hh hl h
    induction h with
    | below_base h => exact .below_base h
    | below_parameter h => exact .below_parameter h
    | add _ _ ihξ ihη => exact .add ihξ ihη
    | higher hmk hkn hsort _ ih =>
      rw [hh _ hmk hkn _ hsort]
      exact .higher hmk hkn hsort ih
    | «local» hξ _ ih =>
      rw [hl _ hξ]
      exact .«local» hξ ih
  exact ⟨forward higher «local»,
    forward (fun k hmk hkn η hη => (higher k hmk hkn η hη).symm)
      (fun η hη => («local» η hη).symm)⟩

/-- Wilken Lemma 2.2(c), continuity in the recursion argument.
Each hull derivation contains finitely many local calls, so their bounds
can be moved below a nonzero limit. -/
theorem hull_limit_argument {omega : Nat → Ordinal}
    {theta : Nat → Ordinal → Ordinal} {n m : Nat} {α β ξ : Ordinal}
    (hα : Order.IsSuccLimit α) :
    Hull omega theta n m α β ξ ↔
      ∃ γ < α, Hull omega theta n m γ β ξ := by
  constructor
  · intro h
    induction h with
    | below_base h => exact ⟨0, hα.pos, .below_base h⟩
    | below_parameter h => exact ⟨0, hα.pos, .below_parameter h⟩
    | add _ _ ihξ ihη =>
      obtain ⟨γ, hγ, ihξ⟩ := ihξ
      obtain ⟨δ, hδ, ihη⟩ := ihη
      exact ⟨max γ δ, max_lt hγ hδ,
        .add (hull_mono (le_max_left _ _) le_rfl ihξ)
          (hull_mono (le_max_right _ _) le_rfl ihη)⟩
    | higher hmk hkn hsort _ ih =>
      obtain ⟨γ, hγ, ih⟩ := ih
      exact ⟨γ, hγ, .higher hmk hkn hsort ih⟩
    | «local» hξ _ ih =>
      obtain ⟨γ, hγ, ih⟩ := ih
      obtain ⟨δ, hδ, hξδ⟩ := hα.lt_iff_exists_lt.mp hξ
      exact ⟨max γ δ, max_lt hγ hδ,
        .«local» (lt_of_lt_of_le hξδ (le_max_right _ _))
          (hull_mono (le_max_left _ _) le_rfl ih)⟩
  · rintro ⟨γ, hγ, h⟩
    exact hull_mono hγ.le le_rfl h

/-- Wilken Lemma 2.2(c), continuity in the parameter segment. -/
theorem hull_limit_parameter {omega : Nat → Ordinal}
    {theta : Nat → Ordinal → Ordinal} {n m : Nat} {α β ξ : Ordinal}
    (hβ : Order.IsSuccLimit β) :
    Hull omega theta n m α β ξ ↔
      ∃ δ < β, Hull omega theta n m α δ ξ := by
  constructor
  · intro h
    induction h with
    | below_base h => exact ⟨0, hβ.pos, .below_base h⟩
    | below_parameter h =>
      obtain ⟨δ, hδ, hξδ⟩ := hβ.lt_iff_exists_lt.mp h
      exact ⟨δ, hδ, .below_parameter hξδ⟩
    | add _ _ ihξ ihη =>
      obtain ⟨γ, hγ, ihξ⟩ := ihξ
      obtain ⟨δ, hδ, ihη⟩ := ihη
      exact ⟨max γ δ, max_lt hγ hδ,
        .add (hull_mono le_rfl (le_max_left _ _) ihξ)
          (hull_mono le_rfl (le_max_right _ _) ihη)⟩
    | higher hmk hkn hsort _ ih =>
      obtain ⟨δ, hδ, ih⟩ := ih
      exact ⟨δ, hδ, .higher hmk hkn hsort ih⟩
    | «local» hξ _ ih =>
      obtain ⟨δ, hδ, ih⟩ := ih
      exact ⟨δ, hδ, .«local» hξ ih⟩
  · rintro ⟨δ, hδ, h⟩
    exact hull_mono le_rfl hδ.le h

/-- Finite hull derivations commute with an increasing countable union
of parameter segments. This also covers a sequence that stabilizes. -/
theorem hull_nat_sup_parameter {omega : Nat → Ordinal}
    {theta : Nat → Ordinal → Ordinal} {n m : Nat} {α ξ : Ordinal}
    (f : Nat → Ordinal) (hf : Monotone f) :
    Hull omega theta n m α (⨆ k, f k) ξ ↔
      ∃ k, Hull omega theta n m α (f k) ξ := by
  constructor
  · intro h
    induction h with
    | below_base h => exact ⟨0, .below_base h⟩
    | below_parameter h =>
      obtain ⟨k, hk⟩ := Ordinal.lt_iSup_iff.mp h
      exact ⟨k, .below_parameter hk⟩
    | add _ _ ihξ ihη =>
      obtain ⟨j, ihξ⟩ := ihξ
      obtain ⟨k, ihη⟩ := ihη
      exact ⟨max j k,
        .add (hull_mono le_rfl (hf (le_max_left _ _)) ihξ)
          (hull_mono le_rfl (hf (le_max_right _ _)) ihη)⟩
    | higher hmk hkn hsort _ ih =>
      obtain ⟨k, ih⟩ := ih
      exact ⟨k, .higher hmk hkn hsort ih⟩
    | «local» hξ _ ih =>
      obtain ⟨k, ih⟩ := ih
      exact ⟨k, .«local» hξ ih⟩
  · rintro ⟨k, h⟩
    exact hull_mono le_rfl (Ordinal.le_iSup f k) h

end Alexander313.Wilken
