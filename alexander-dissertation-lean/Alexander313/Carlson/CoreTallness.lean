import Alexander313.Carlson.Core
import Mathlib.Logic.Denumerable

/-!
# Tallness in the common classical core

Finite guards are now placed in one fixed countable initial segment,
`coreBound`, using the least exact copies of finite rational chain patterns.
This is stronger than global ordinal tallness and does not assume tallness
inside any one finite seed's realization.
-/

noncomputable section

namespace Alexander313.Carlson

open Ordinal Cardinal

def rationalFullChain (n : ℕ) : Str ℚ :=
  ⟨(Finset.range n).image (fun i : ℕ => (i : ℚ)), (· ≤ ·), (· ≤ ·)⟩

theorem rationalFullChain_isPattern (n : ℕ) : (rationalFullChain n).IsPattern := by
  exact ⟨fun _ _ _ _ h => h, fun _ _ _ _ h => h, fun _ _ => le_rfl,
    fun _ _ => le_rfl, fun _ _ _ _ _ _ h₁ h₂ => h₁.trans h₂,
    fun _ _ _ _ _ _ h₁ h₂ => h₁.trans h₂, fun _ _ _ _ _ _ h _ _ => h,
    fun _ _ _ _ _ _ h _ _ _ => h⟩

theorem rationalFullChain_mem {n i : ℕ} (hi : i < n) :
    (i : ℚ) ∈ (rationalFullChain n).U :=
  Finset.mem_image_of_mem _ (Finset.mem_range.mpr hi)

/-- Every finite guard lies in the same classical core initial segment. -/
theorem exists_guard_in_core (k : ℕ) :
    ∃ top : Ordinal.{0}, ∃ tail : List Ordinal.{0}, tail.length = k ∧
      (top :: tail).Pairwise (· < ·) ∧ (top :: tail).Pairwise R2 ∧
      ∀ z ∈ top :: tail, z < coreBound := by
  obtain ⟨h, e, hcore, _⟩ := exists_minimal_copy_in_core
    (rationalFullChain (k + 1)) (rationalFullChain_isPattern (k + 1))
  let g (i : ℕ) := h (i : ℚ)
  let tail := List.ofFn (fun i : Fin k => g (i.val + 1))
  have hlist : g 0 :: tail = List.ofFn (fun i : Fin (k + 1) => g i.val) := by
    rw [List.ofFn_succ]
    rfl
  refine ⟨g 0, tail, List.length_ofFn, ?_, ?_, ?_⟩
  · rw [hlist]
    apply List.pairwise_ofFn.mpr
    intro i j hij
    exact e.2.1 _ (rationalFullChain_mem i.isLt) _ (rationalFullChain_mem j.isLt)
      (Nat.cast_lt.mpr hij)
  · rw [hlist]
    apply List.pairwise_ofFn.mpr
    intro i j hij
    exact (e.2.2 _ (rationalFullChain_mem i.isLt) _ (rationalFullChain_mem j.isLt)).2.mp
      (Nat.cast_le.mpr hij.le)
  · intro z hz
    rw [hlist] at hz
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    exact hcore _ (rationalFullChain_mem i.isLt)

theorem exists_finite_second_chain_in_core (n : ℕ) :
    ∃ xs : List Ordinal.{0}, xs.length = n ∧ xs.Pairwise (· < ·) ∧
      xs.Pairwise R2 ∧ ∀ z ∈ xs, z < coreBound := by
  cases n with
  | zero => exact ⟨[], rfl, by simp, by simp, by simp⟩
  | succ n =>
    obtain ⟨top, tail, hlen, hord, hrel, hcore⟩ := exists_guard_in_core n
    exact ⟨top :: tail, by simp only [List.length_cons, hlen], hord, hrel, hcore⟩

theorem coreBound_pos : 0 < coreBound := by
  obtain ⟨top, tail, _, _, _, hcore⟩ := exists_guard_in_core 0
  exact (show 0 ≤ top from zero_le).trans_lt (hcore top List.mem_cons_self)

theorem corePoint_zero : CorePoint 0 := (corePoint_iff_lt_coreBound 0).mpr coreBound_pos

theorem countable_core : Countable (Set.Iio coreBound) := by
  letI := countable_Iic_of_lt_omega_one coreBound_lt_omega_one
  let f : Set.Iio coreBound → Set.Iic coreBound := fun a =>
    ⟨a.1, (show a.1 < coreBound from a.2).le⟩
  exact (show Function.Injective f from
    fun x y h => Subtype.ext (congrArg (fun a : Set.Iic coreBound => a.1) h)).countable

theorem infinite_core : Infinite (Set.Iio coreBound) := by
  classical
  apply Infinite.of_not_fintype
  intro inst
  letI := inst
  let n := Fintype.card (Set.Iio coreBound) + 1
  obtain ⟨h, e, hcore, _⟩ := exists_minimal_copy_in_core
    (rationalFullChain n) (rationalFullChain_isPattern n)
  let f : Fin n → Set.Iio coreBound := fun i =>
    ⟨h (i.val : ℚ), hcore _ (rationalFullChain_mem i.isLt)⟩
  have hf : StrictMono f := by
    intro i j hij
    exact e.2.1 _ (rationalFullChain_mem i.isLt) _ (rationalFullChain_mem j.isLt)
      (Nat.cast_lt.mpr hij)
  have hcard := Fintype.card_le_of_injective f hf.injective
  simp only [Fintype.card_fin] at hcard
  dsimp [n] at hcard
  omega

/-- A classical bijection with natural numbers exists. Its relation
recognizers and computational behavior are separate obligations. -/
theorem exists_core_nat_equiv : Nonempty (ℕ ≃ Set.Iio coreBound) := by
  letI := countable_core
  letI := infinite_core
  infer_instance

end Alexander313.Carlson
