import Alexander313.Carlson.FiniteTypeClosure

/-!
# Unbounded finite reflection points below `ω₁`

Besides chosen finite type witnesses, closure must include a cutoff witnessing
the boundedness of each noncofinal finite-copy family. Otherwise clause 2 of
Carlson's second relation would not follow. All cutoffs are chosen from the
actual relations; there is no reflection principle or semantic hypothesis.
-/

noncomputable section

namespace Alexander313.Carlson

open Ordinal Cardinal

abbrev CofinalRequest (ξ : Ordinal.{0}) :=
  Σ n : ℕ, Finset (Set.Iic ξ) ×
    (Fin n → Fin n → Prop) × (Fin n → Fin n → Prop)

def CofinalRequest.anchors {ξ : Ordinal.{0}} (r : CofinalRequest ξ) :
    Finset Ordinal.{0} := r.2.1.image Subtype.val

def CofinalRequest.Unbounded {ξ : Ordinal.{0}} (r : CofinalRequest ξ) : Prop :=
  CofinalCopies R1 R2 r.anchors r.2.2.1 r.2.2.2 ω₁

def CofinalRequest.Blocks {ξ : Ordinal.{0}} (r : CofinalRequest ξ)
    (η : Ordinal.{0}) : Prop :=
  ¬∃ Y : Finset Ordinal.{0}, (∀ y ∈ Y, η < y ∧ y < ω₁) ∧
    CoversStructure R1 R2 (r.anchors ∪ Y) r.2.2.1 r.2.2.2

theorem CofinalRequest.exists_blocker {ξ : Ordinal.{0}} (r : CofinalRequest ξ)
    (h : ¬r.Unbounded) : ∃ η, η < ω₁ ∧ r.Blocks η := by
  classical
  simpa only [Unbounded, CofinalCopies, Blocks, not_forall, exists_prop] using h

def CofinalRequest.blocker {ξ : Ordinal.{0}} (r : CofinalRequest ξ) : Ordinal.{0} := by
  classical
  exact if h : ¬r.Unbounded then Classical.choose (r.exists_blocker h) else 0

theorem CofinalRequest.blocker_lt {ξ : Ordinal.{0}} (r : CofinalRequest ξ) :
    r.blocker < ω₁ := by
  classical
  by_cases h : ¬r.Unbounded
  · simpa [blocker, h] using
      (Classical.choose_spec (r.exists_blocker h)).1
  · simpa [blocker, h] using (Cardinal.isSuccLimit_omega 1).pos

theorem CofinalRequest.blocker_blocks {ξ : Ordinal.{0}} (r : CofinalRequest ξ)
    (h : ¬r.Unbounded) : r.Blocks r.blocker := by
  simp [blocker, h]
  exact (Classical.choose_spec (r.exists_blocker h)).2

theorem countable_cofinalRequest {ξ : Ordinal.{0}} (hξ : ξ < ω₁) :
    Countable (CofinalRequest ξ) := by
  letI := countable_Iic_of_lt_omega_one hξ
  infer_instance

def obstructionBound (ξ : Ordinal.{0}) : Ordinal.{0} :=
  ⨆ r : CofinalRequest ξ, r.blocker

theorem obstructionBound_lt_omega_one {ξ : Ordinal.{0}} (hξ : ξ < ω₁) :
    obstructionBound ξ < ω₁ := by
  letI := countable_cofinalRequest hξ
  exact Ordinal.iSup_lt_omega_one fun r => r.blocker_lt

/-- Simultaneous closure under finite witnesses and boundedness cutoffs. -/
structure ReflectionPoint (a : Ordinal.{0}) : Prop where
  pos : 0 < a
  below : a < ω₁
  witnesses : ∀ ξ < a, witnessBound ξ < a
  obstructions : ∀ ξ < a, obstructionBound ξ < a

def closureStep (ξ : Ordinal.{0}) : Ordinal.{0} :=
  max (ξ + 1) ((⨆ η : Set.Iic ξ, max (witnessBound η) (obstructionBound η)) + 1)

theorem closureStep_lt_omega_one {ξ : Ordinal.{0}} (hξ : ξ < ω₁) :
    closureStep ξ < ω₁ := by
  letI := countable_Iic_of_lt_omega_one hξ
  apply max_lt
  · exact (Cardinal.isSuccLimit_omega 1).add_one_lt hξ
  · apply (Cardinal.isSuccLimit_omega 1).add_one_lt
    apply Ordinal.iSup_lt_omega_one
    intro η
    exact max_lt (witnessBound_lt_omega_one (η.2.trans_lt hξ))
      (obstructionBound_lt_omega_one (η.2.trans_lt hξ))

theorem lt_closureStep (ξ : Ordinal.{0}) : ξ < closureStep ξ :=
  (lt_add_one ξ).trans_le (le_max_left _ _)

theorem witnessBound_lt_closureStep {ξ η : Ordinal.{0}} (h : η ≤ ξ) :
    witnessBound η < closureStep ξ := by
  have hsup := Ordinal.le_iSup
    (fun η : Set.Iic ξ => max (witnessBound η) (obstructionBound η)) ⟨η, h⟩
  exact ((le_max_left _ _).trans hsup).trans_lt
    ((lt_add_one _).trans_le (le_max_right _ _))

theorem obstructionBound_lt_closureStep {ξ η : Ordinal.{0}} (h : η ≤ ξ) :
    obstructionBound η < closureStep ξ := by
  have hsup := Ordinal.le_iSup
    (fun η : Set.Iic ξ => max (witnessBound η) (obstructionBound η)) ⟨η, h⟩
  exact ((le_max_right _ _).trans hsup).trans_lt
    ((lt_add_one _).trans_le (le_max_right _ _))

/-- A countable iteration gives reflection points above every countable
ordinal. This establishes existence, rather than taking closure points as
an additional ordinal-package input. -/
theorem exists_reflectionPoint_above {γ : Ordinal.{0}} (hγ : γ < ω₁) :
    ∃ a, γ < a ∧ ReflectionPoint a := by
  let t : ℕ → Ordinal.{0} := fun n => closureStep^[n] (γ + 1)
  have tzero : t 0 = γ + 1 := rfl
  have tnext (n : ℕ) : t (n + 1) = closureStep (t n) := by
    exact Function.iterate_succ_apply' closureStep n (γ + 1)
  have ht : ∀ n, t n < ω₁ := by
    intro n
    induction n with
    | zero => exact (Cardinal.isSuccLimit_omega 1).add_one_lt hγ
    | succ n hn => rw [tnext]; exact closureStep_lt_omega_one hn
  let a := ⨆ n, t n
  have ha : a < ω₁ := Ordinal.iSup_lt_omega_one ht
  have hta (n : ℕ) : t n < a := by
    exact (lt_closureStep (t n)).trans_le
      ((tnext n) ▸ Ordinal.le_iSup t (n + 1))
  have hγa : γ < a := (lt_add_one γ).trans_le
    (tzero ▸ Ordinal.le_iSup t 0)
  refine ⟨a, hγa, ⟨(show 0 ≤ γ from zero_le).trans_lt hγa, ha, ?_, ?_⟩⟩
  · intro ξ hξ
    obtain ⟨n, hn⟩ := Ordinal.lt_iSup_iff.mp hξ
    exact (witnessBound_lt_closureStep hn.le).trans ((tnext n) ▸ hta (n + 1))
  · intro ξ hξ
    obtain ⟨n, hn⟩ := Ordinal.lt_iSup_iff.mp hξ
    exact (obstructionBound_lt_closureStep hn.le).trans ((tnext n) ▸ hta (n + 1))

end Alexander313.Carlson
