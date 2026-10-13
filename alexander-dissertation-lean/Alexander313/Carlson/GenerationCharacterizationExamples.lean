import Alexander313.Carlson.GenerationCharacterization
import Alexander313.Carlson.ExactnessExamples

/-! Controls for finite proof-frame transport and the full generation criterion. -/

noncomputable section

namespace Alexander313.Carlson

/-- Extending a prescribed endpoint map makes room between old labels,
while preserving their actual values rather than merely their order type. -/
theorem finite_extension_preserves_endpoints_and_gap :
    ∃ F : FiniteRelabeling ({0, 1, 2} : Finset ℕ) ℚ,
      F.toFun 0 = 0 ∧ F.toFun 2 = 4 ∧ 0 < F.toFun 1 ∧ F.toFun 1 < 4 := by
  have hs : ({0, 2} : Finset ℕ) ⊆ {0, 1, 2} := by decide
  have hm : ∀ x ∈ ({0, 2} : Finset ℕ), ∀ y ∈ ({0, 2} : Finset ℕ),
      x < y → (2 : ℚ) * x < 2 * y := by
    intro x _ y _ hxy
    exact mul_lt_mul_of_pos_left (Nat.cast_lt.mpr hxy) (by norm_num)
  obtain ⟨F, hF⟩ := exists_rational_relabeling_extending hs (fun x : ℕ => (2 : ℚ) * x) hm
  have h0 : F.toFun 0 = 0 := by simpa using hF 0 (by simp)
  have h2 : F.toFun 2 = 4 := by
    have h := hF 2 (by simp)
    norm_num at h
    exact h
  refine ⟨F, h0, h2, ?_, ?_⟩
  · rw [← h0]
    exact F.mono 0 (by simp) 1 (by simp) (by decide)
  · rw [← h2]
    exact F.mono 1 (by simp) 2 (by simp) (by decide)

/-- The extension also supplies points on both sides of a fixed old label. -/
theorem finite_extension_preserves_middle_and_both_sides :
    ∃ F : FiniteRelabeling ({0, 1, 2} : Finset ℕ) ℚ,
      F.toFun 1 = 0 ∧ F.toFun 0 < 0 ∧ 0 < F.toFun 2 := by
  have hs : ({1} : Finset ℕ) ⊆ {0, 1, 2} := by decide
  have hm : ∀ x ∈ ({1} : Finset ℕ), ∀ y ∈ ({1} : Finset ℕ),
      x < y → (0 : ℚ) < 0 := by
    intro x hx y hy hxy
    have hx' := Finset.mem_singleton.mp hx
    have hy' := Finset.mem_singleton.mp hy
    exact (lt_irrefl 1 (hx' ▸ hy' ▸ hxy)).elim
  obtain ⟨F, hF⟩ := exists_rational_relabeling_extending hs (fun _ : ℕ => (0 : ℚ)) hm
  have h1 := hF 1 (Finset.mem_singleton_self 1)
  refine ⟨F, h1, ?_, ?_⟩
  · rw [← h1]
    exact F.mono 0 (by simp) 1 (by simp) (by decide)
  · rw [← h1]
    exact F.mono 1 (by simp) 2 (by simp) (by decide)

/-- The order hypothesis cannot be omitted from endpoint transport. -/
theorem reversed_endpoints_have_no_relabeling :
    ¬∃ F : FiniteRelabeling ({0, 1, 2} : Finset ℕ) ℚ,
      F.toFun 0 = 4 ∧ F.toFun 2 = 0 := by
  rintro ⟨F, h0, h2⟩
  have h := F.mono 0 (by simp) 2 (by simp) (by decide)
  rw [h0, h2] at h
  norm_num at h

private theorem singleton_label_zero {P : Str ℚ} {a : ℚ} (hU : P.U = {a})
    (A : PatternRealization P) : A.label a = 0 := by
  have cov : P.CoveringR (fun _ => 0) := by
    refine ⟨?_, fun _ _ _ _ _ => R1_refl 0, fun _ _ _ _ _ => R2_refl 0⟩
    intro x hx y hy hxy
    rw [hU] at hx hy
    have hx' := Finset.mem_singleton.mp hx
    have hy' := Finset.mem_singleton.mp hy
    rw [hx', hy'] at hxy
    exact (lt_irrefl a hxy).elim
  exact (A.seed_minimal cov (hU ▸ Finset.mem_singleton_self a)).antisymm zero_le

/-- Boundedness alone does not imply generation. The last singleton of
a strict two-point chain has least label zero, whereas the chain's last
least label is positive. It is neither valid nor generated. -/
theorem bounded_last_singleton_not_generated :
    (∀ x ∈ (rationalFullChain 2).U,
      ∃ p ∈ ((rationalFullChain 2).restrict {1}).U, x ≤ p) ∧
    ¬Str.Valid ((rationalFullChain 2).restrict {1}) (rationalFullChain 2) ∧
    ¬Str.Generates ((rationalFullChain 2).restrict {1}) (rationalFullChain 2) := by
  let P := (rationalFullChain 2).restrict {1}
  let Q := rationalFullChain 2
  have hsub : Str.IsSub P Q := Q.restrict_isSub (by
    exact Finset.singleton_subset_iff.mpr (rationalFullChain_mem (by decide : 1 < 2)))
  let A := PatternRealization.ofPattern P ((rationalFullChain_isPattern 2).mono hsub)
  let B := PatternRealization.ofPattern Q (rationalFullChain_isPattern 2)
  have h0 : (0 : ℚ) ∈ Q.U := rationalFullChain_mem (by decide : 0 < 2)
  have h1 : (1 : ℚ) ∈ Q.U := rationalFullChain_mem (by decide : 1 < 2)
  have hlt : B.label 0 < B.label 1 := B.seed_isIso.2.1 0 h0 1 h1 (by norm_num)
  have hzero : A.label 1 = 0 := singleton_label_zero rfl A
  have hnot : ¬Str.Valid P Q := by
    intro hv
    have he := hv.least_copy_agrees A B 1 (Finset.mem_singleton_self 1)
    rw [hzero] at he
    exact (not_lt_of_ge zero_le) (he ▸ hlt)
  refine ⟨?_, hnot, fun d => hnot d.valid⟩
  intro x hx
  refine ⟨1, Finset.mem_singleton_self 1, ?_⟩
  simp only [rationalFullChain, Finset.mem_image, Finset.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  have hi' : i ≤ 1 := by omega
  exact_mod_cast hi'

/-- Least labels agree vacuously on an empty source. Validity still
does not replace the largest-point condition for generation. -/
theorem valid_empty_source_not_generated :
    Str.Valid ((rationalFullChain 1).restrict ∅) (rationalFullChain 1) ∧
    ¬Str.Generates ((rationalFullChain 1).restrict ∅) (rationalFullChain 1) := by
  let Q := rationalFullChain 1
  have hsub : Str.IsSub (Q.restrict ∅) Q := Q.restrict_isSub (Finset.empty_subset _)
  have cov : Q.CoveringR (fun _ => 0) := by
    refine ⟨?_, fun _ _ _ _ _ => R1_refl 0, fun _ _ _ _ _ => R2_refl 0⟩
    intro x hx y hy hxy
    have hx' : x = 0 := by simpa [Q, rationalFullChain, Finset.range_one] using hx
    have hy' : y = 0 := by simpa [Q, rationalFullChain, Finset.range_one] using hy
    exact (lt_irrefl 0 (hx' ▸ hy' ▸ hxy)).elim
  refine ⟨⟨hsub, fun _ _ => ⟨fun _ => 0, cov, fun _ hx => (Finset.notMem_empty _ hx).elim⟩⟩, ?_⟩
  intro d
  obtain ⟨p, hp, _⟩ := d.continuous.2.1 0 (rationalFullChain_mem (by decide : 0 < 1))
  exact Finset.notMem_empty p hp

end Alexander313.Carlson
