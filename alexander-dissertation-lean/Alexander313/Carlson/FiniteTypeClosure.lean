import Alexander313.Carlson.Order
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.Data.Countable.Basic

/-!
# Finite type closure below the first uncountable ordinal

This is the finite witness part of the pure-case alternative to Carlson's
Lemma 15.11. A request records optional fixed anchors, three finite forward
relation tables (order, first and second), and unary first-relation links to
the ambient endpoint. Only finite tables are quantified over when bounding
chosen witnesses. Neither coveredness nor tallness is assumed.
-/

noncomputable section

namespace Alexander313.Carlson

open Ordinal Cardinal

/-- Three forward binary tables and a unary endpoint-link table. -/
abbrev WitnessType (n : ℕ) :=
  (Fin n → Fin n → Prop) × (Fin n → Fin n → Prop) ×
    (Fin n → Fin n → Prop) × (Fin n → Prop)

/-- A finite type with some positions fixed at old anchors at most `ξ`. -/
abbrev WitnessRequest (ξ : Ordinal.{0}) :=
  Σ n : ℕ, (Fin n → Option (Set.Iic ξ)) × WitnessType n

def WitnessRequest.Realizes {ξ : Ordinal.{0}} (r : WitnessRequest ξ)
    (κ : Ordinal.{0}) (u : Fin r.1 → Ordinal.{0}) : Prop :=
  (∀ i, u i < κ) ∧
  (∀ i, match r.2.1 i with
    | some x => u i = x
    | none => ξ < u i) ∧
  (∀ i j, r.2.2.1 i j → u i < u j) ∧
  (∀ i j, r.2.2.2.1 i j → R1 (u i) (u j)) ∧
  (∀ i j, r.2.2.2.2.1 i j → R2 (u i) (u j)) ∧
  (∀ i, r.2.2.2.2.2 i → R1 (u i) κ)

def WitnessRequest.chosen {ξ : Ordinal.{0}} (r : WitnessRequest ξ) (κ : Ordinal.{0})
    (h : ∃ u, r.Realizes κ u) : Fin r.1 → Ordinal.{0} := Classical.choose h

theorem WitnessRequest.chosen_realizes {ξ : Ordinal.{0}} (r : WitnessRequest ξ)
    (κ : Ordinal.{0}) (h : ∃ u, r.Realizes κ u) :
    r.Realizes κ (r.chosen κ h) := Classical.choose_spec h

/-- A strict bound for every point of one chosen realization, or zero when
the request has no realization. -/
def WitnessRequest.bound {ξ : Ordinal.{0}} (r : WitnessRequest ξ) (κ : Ordinal.{0}) :
    Ordinal.{0} := by
  classical
  exact if h : ∃ u, r.Realizes κ u then ⨆ i, r.chosen κ h i + 1 else 0

theorem WitnessRequest.bound_lt_omega_one {ξ : Ordinal.{0}} (r : WitnessRequest ξ) :
    r.bound ω₁ < ω₁ := by
  unfold bound
  split_ifs with h
  · apply Ordinal.iSup_lt_omega_one
    intro i
    exact (Cardinal.isSuccLimit_omega 1).add_one_lt ((r.chosen_realizes ω₁ h).1 i)
  · exact (Cardinal.isSuccLimit_omega 1).pos

theorem WitnessRequest.exists_below_bound {ξ : Ordinal.{0}} (r : WitnessRequest ξ)
    (κ : Ordinal.{0}) (h : ∃ u, r.Realizes κ u) :
    ∃ u, r.Realizes κ u ∧ ∀ i, u i < r.bound κ := by
  refine ⟨r.chosen κ h, r.chosen_realizes κ h, fun i => ?_⟩
  simp only [bound, h, ↓reduceDIte]
  exact Ordinal.lt_iSup_add_one _ i

/-- All finite type requests over anchors at most `ξ` have countably many
possible descriptions when `ξ` is countable. -/
theorem countable_Iic_of_lt_omega_one {ξ : Ordinal.{0}} (hξ : ξ < ω₁) :
    Countable (Set.Iic ξ) := by
  have hs : ξ + 1 < ω₁ := (Cardinal.isSuccLimit_omega 1).add_one_lt hξ
  have hc : Countable (Set.Iio (ξ + 1)) := by
    apply Cardinal.mk_le_aleph0_iff.mp
    rw [Cardinal.mk_Iio_ordinal, Cardinal.lift_le_aleph0]
    apply Cardinal.lt_aleph_one_iff.mp
    exact Cardinal.lt_ord.mp (by simpa only [Cardinal.ord_aleph] using hs)
  letI := hc
  let f := fun x : Set.Iic ξ =>
    (⟨x.1, x.2.trans_lt (lt_add_one ξ)⟩ : Set.Iio (ξ + 1))
  exact (show Function.Injective f from
    fun x y h => Subtype.ext (congrArg (fun z : Set.Iio (ξ + 1) => z.1) h)).countable

theorem countable_witnessRequest {ξ : Ordinal.{0}} (hξ : ξ < ω₁) :
    Countable (WitnessRequest ξ) := by
  letI := countable_Iic_of_lt_omega_one hξ
  infer_instance

/-- Bound every chosen realization of a finite request over `ξ`. -/
def witnessBound (ξ : Ordinal.{0}) : Ordinal.{0} :=
  ⨆ r : WitnessRequest ξ, r.bound ω₁

theorem witnessBound_lt_omega_one {ξ : Ordinal.{0}} (hξ : ξ < ω₁) :
    witnessBound ξ < ω₁ := by
  letI := countable_witnessRequest hξ
  exact Ordinal.iSup_lt_omega_one fun r => r.bound_lt_omega_one

/-- A closure point reflects every realizable finite request into its initial
segment, preserving the unary links to the ambient endpoint. -/
theorem reflect_request {a ξ : Ordinal.{0}} (hξ : ξ < a) (ha : a < ω₁)
    (closed : ∀ ξ < a, witnessBound ξ < a) (r : WitnessRequest ξ)
    (h : ∃ u, r.Realizes ω₁ u) :
    ∃ u, r.Realizes ω₁ u ∧ ∀ i, u i < a := by
  letI := countable_witnessRequest (hξ.trans ha)
  obtain ⟨u, hu, hb⟩ := r.exists_below_bound ω₁ h
  exact ⟨u, hu, fun i => (hb i).trans_le
    ((Ordinal.le_iSup (fun r : WitnessRequest ξ => r.bound ω₁) r).trans
      (closed ξ hξ).le)⟩

end Alexander313.Carlson
