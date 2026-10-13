import Alexander313.Carlson.LeastCopyCompleteness
import Alexander313.Carlson.ExactnessExamples

/-! Boundary and hypothesis controls for least-copy correctness and generation. -/

noncomputable section

namespace Alexander313.Carlson

/-- The theorem includes empty patterns, and adds no point to them. -/
theorem empty_ordinal_generates_iff (V : Finset Ordinal.{0}) :
    Str.Generates (Str.ofOrdinals ∅) (Str.ofOrdinals V) ↔ V = ∅ := by
  rw [empty_ordinal_set_isominimal.generates_iff (Finset.empty_subset V)]
  constructor
  · intro hb
    apply Finset.eq_empty_of_forall_notMem
    intro z hz
    obtain ⟨p, hp, _⟩ := hb z hz
    exact Finset.notMem_empty p hp
  · rintro rfl
    simp

/-- Correctness is tested against arbitrary finite ordinal ambient sets,
for both levels, rather than only extensions lying inside a chosen limit. -/
theorem singleton_zero_kCorrect (T : Finset Ordinal.{0}) (k : Lvl) :
    Str.KCorrect (Str.ofOrdinals {0}) (Str.ofOrdinals T) k :=
  ((singleton_isominimal_iff_zero 0).mpr rfl).kCorrect T k

/-- A source containing only zero cannot generate an extra ordinal point. -/
theorem singleton_zero_generates_iff (V : Finset Ordinal.{0}) (hzero : 0 ∈ V) :
    Str.Generates (Str.ofOrdinals {0}) (Str.ofOrdinals V) ↔ V = {0} := by
  rw [((singleton_isominimal_iff_zero 0).mpr rfl).generates_iff
    (Finset.singleton_subset_iff.mpr hzero)]
  constructor
  · intro hb
    apply Finset.Subset.antisymm _ (Finset.singleton_subset_iff.mpr hzero)
    intro z hz
    obtain ⟨p, hp, hzp⟩ := hb z hz
    rw [Finset.mem_singleton.mp hp] at hzp
    exact Finset.mem_singleton.mpr (le_antisymm hzp zero_le)
  · rintro rfl
    intro z hz
    exact ⟨z, hz, le_rfl⟩

/-- The boundedness hypothesis cannot be removed, even for a least source. -/
theorem singleton_zero_unbounded_extension_rejected :
    ¬Str.Generates (Str.ofOrdinals {0}) (Str.ofOrdinals {0, 1}) := by
  intro d
  obtain ⟨p, hp, hle⟩ := d.continuous.2.1 1 (by simp [Str.ofOrdinals])
  rw [Finset.mem_singleton.mp hp] at hle
  exact (not_le_of_gt (by exact zero_lt_one : (0 : Ordinal.{0}) < 1)) hle

/-- The isominimality hypothesis cannot be removed: a positive singleton
has a bounded extension, but a downward covering obstructs generation. -/
theorem positive_singleton_bounded_extension_rejected (a : Ordinal.{0}) (ha : 0 < a) :
    (∀ z ∈ ({0, a} : Finset Ordinal.{0}), ∃ p ∈ ({a} : Finset Ordinal.{0}), z ≤ p) ∧
      ¬Str.Generates (Str.ofOrdinals {a}) (Str.ofOrdinals {0, a}) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact ⟨a, Finset.mem_singleton_self a, zero_le⟩
    · exact ⟨z, hz, le_rfl⟩
  · have hcov : (Str.ofOrdinals {a}).Covered :=
      ⟨id, fun _ _ _ _ h => h, fun _ _ _ _ h => h, fun _ _ _ _ h => h⟩
    have hc : Str.CoversInto (Str.ofOrdinals {a}) (Str.ofOrdinals {0, a}) (fun _ => 0) := by
      refine ⟨fun _ _ => by simp [Str.ofOrdinals], ?_, fun _ _ _ _ _ => R1_refl 0,
        fun _ _ _ _ _ => R2_refl 0⟩
      intro x hx y hy hxy
      rw [Finset.mem_singleton.mp hx, Finset.mem_singleton.mp hy] at hxy
      exact (lt_irrefl a hxy).elim
    exact Str.not_generates_of_coversInto_lt hcov hc (Finset.mem_singleton_self a) ha

/-- A least strict two-point second-relation chain really generates an
extension with a new point. This is a positive nonidentity control. -/
theorem exists_least_chain_generating_new_zero :
    ∃ (U : Finset Ordinal.{0}) (a b : Ordinal.{0}),
      IsominimalOrdinalSet U ∧ a ∈ U ∧ b ∈ U ∧ 0 < a ∧ a < b ∧ R2 a b ∧
      0 ∉ U ∧ Str.Generates (Str.ofOrdinals U) (Str.ofOrdinals (insert 0 U)) := by
  let P := rationalFullChain 2
  obtain ⟨h, e, _, hm, _, _⟩ := exists_complete_minimal_ordinal_copy P
    (rationalFullChain_isPattern 2)
  let U := P.U.image h
  let a := h 0
  let b := h 1
  have hzero : (0 : ℚ) ∈ P.U := rationalFullChain_mem (by omega : 0 < 2)
  have hone : (1 : ℚ) ∈ P.U := rationalFullChain_mem (by omega : 1 < 2)
  have hlt : a < b := e.2.1 0 hzero 1 hone (by norm_num)
  have hsecond : R2 a b := (e.2.2 0 hzero 1 hone).2.mp (by
    change (0 : ℚ) ≤ 1
    norm_num)
  have hpos : 0 < a := positive_of_strict_first (R2_R1 hsecond) hlt
  have ha : a ∈ U := Finset.mem_image_of_mem h hzero
  have hb : b ∈ U := Finset.mem_image_of_mem h hone
  have hcarrier : U = {a, b} := by
    have hP : P.U = {0, 1} := by
      norm_num [P, rationalFullChain, Finset.range_add_one]
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton, or_comm]
    simp only [U, hP, Finset.image_insert, Finset.image_singleton, a, b]
  have hnot : 0 ∉ U := by
    rw [hcarrier]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hpos.ne, (hpos.trans hlt).ne⟩
  refine ⟨U, a, b, hm, ha, hb, hpos, hlt, hsecond, hnot,
    hm.generates (Finset.subset_insert 0 U) ?_⟩
  intro z hz
  rcases Finset.mem_insert.mp hz with rfl | hz
  · exact ⟨a, ha, zero_le⟩
  · exact ⟨z, hz, le_rfl⟩

end Alexander313.Carlson
