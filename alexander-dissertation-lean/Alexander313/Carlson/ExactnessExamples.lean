import Alexander313.Carlson.IsominimalCuts
import Alexander313.Carlson.CoreTallness

/-! Empty-carrier and boundary controls for exactness and isominimal cuts. -/

noncomputable section

namespace Alexander313.Carlson

theorem empty_exact_in_pattern {α : Type*} [LinearOrder α]
    (Q : Str α) (hQ : Q.IsPattern) : Str.Exact (Q.restrict ∅) Q := by
  refine ⟨hQ, ?_, ?_⟩
  · simpa only [Str.restrict, Str.initialSpan_empty] using
      Str.Generates.refl (hQ.restrict (Finset.empty_subset _))
  · intro p x y _ _ hp
    have hempty : p ∈ (∅ : Finset α) := by
      simpa only [Str.restrict, Str.initialSpan_empty] using hp.1
    exact (Finset.notMem_empty p hempty).elim

theorem empty_ordinal_set_isominimal : IsominimalOrdinalSet ∅ := by
  apply IsominimalOrdinalSet.iff_le_covering.mpr
  simp

theorem singleton_isominimal_iff_zero (a : Ordinal.{0}) :
    IsominimalOrdinalSet {a} ↔ a = 0 := by
  constructor
  · intro h
    have hc : (Str.ofOrdinals {a}).CoveringR (fun _ => 0) := by
      refine ⟨?_, ?_, ?_⟩
      · intro x hx y hy hxy
        have hx' : x = a := Finset.mem_singleton.mp hx
        have hy' : y = a := Finset.mem_singleton.mp hy
        rw [hx', hy'] at hxy
        exact (lt_irrefl a hxy).elim
      · intro _ _ _ _ _
        exact R1_refl 0
      · intro _ _ _ _ _
        exact R2_refl 0
    exact le_antisymm (h.le_covering hc (Finset.mem_singleton_self a)) zero_le
  · rintro rfl
    apply IsominimalOrdinalSet.iff_le_covering.mpr
    intro g _ z hz
    rw [Finset.mem_singleton.mp hz]
    exact zero_le

/-- A strict first-relation edge has a positive lower endpoint. -/
theorem positive_of_strict_first {a b : Ordinal.{0}} (hab : R1 a b) (hlt : a < b) :
    0 < a := by
  obtain ⟨f, hf⟩ := R1_copy' hab {a} (by
    intro z hz
    rw [Finset.mem_singleton.mp hz]
    exact hlt)
  exact zero_le.trans_lt (hf.1 a (Finset.mem_singleton_self a))

/-- Omitting 1-correctness would make the restriction theorem false.
The lower singleton cut of a least strict two-point chain is not
isominimal and its actual first edge crosses the cut. -/
theorem exists_isominimal_uncorrect_cut :
    ∃ (U : Finset Ordinal.{0}) (a : Ordinal.{0}),
      IsominimalOrdinalSet U ∧ a ∈ U ∧
      ¬IsominimalOrdinalSet (U.filter (fun x => x ≤ a)) ∧
      ¬Str.KCorrect ((Str.ofOrdinals U).initialCut a) (Str.ofOrdinals U) .one := by
  let P := rationalFullChain 2
  let A := PatternRealization.ofPattern P (rationalFullChain_isPattern 2)
  let U := P.U.image A.label
  let a := A.label 0
  let b := A.label 1
  have hzero : (0 : ℚ) ∈ P.U := rationalFullChain_mem (by omega : 0 < 2)
  have hone : (1 : ℚ) ∈ P.U := rationalFullChain_mem (by omega : 1 < 2)
  have hlt : a < b := A.seed_isIso.2.1 0 hzero 1 hone (by norm_num)
  have hab : R1 a b := (A.seed_isIso.2.2 0 hzero 1 hone).1.mp (by
    change (0 : ℚ) ≤ 1
    norm_num)
  have ha : a ∈ U := Finset.mem_image_of_mem A.label hzero
  have hb : b ∈ U := Finset.mem_image_of_mem A.label hone
  have hU : IsominimalOrdinalSet U := by
    intro T f ef hle
    have ef' : Str.IsIso (A.ordinal.stagePattern 0) (Str.ofOrdinals T) f := by
      simpa only [GeneratingSequence.OrdinalRealization.stagePattern, A.seed, U] using ef
    have hle' : ∀ z ∈ (A.ordinal.stagePattern 0).U, f z ≤ z := by
      simpa only [GeneratingSequence.OrdinalRealization.stagePattern, A.seed,
        Str.ofOrdinals, U] using hle
    simpa only [GeneratingSequence.OrdinalRealization.stagePattern, A.seed,
      Str.ofOrdinals, U] using
      A.ordinal.stage_isominimal 0 ef' hle'
  have hcarrier : U = {a, b} := by
    ext z
    constructor
    · intro hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      have hi' : i = 0 ∨ i = 1 := by
        have := Finset.mem_range.mp hi
        omega
      rcases hi' with rfl | rfl <;> simp [a, b]
    · intro hz
      rcases Finset.mem_insert.mp hz with hz | hz
      · exact hz ▸ ha
      · exact (Finset.mem_singleton.mp hz) ▸ hb
  have hcut : U.filter (fun x => x ≤ a) = {a} := by
    rw [hcarrier]
    ext z
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | rfl, hle⟩
      · rfl
      · exact ((not_le_of_gt hlt) hle).elim
    · rintro rfl
      exact ⟨Or.inl rfl, le_rfl⟩
  have hnon : ¬IsominimalOrdinalSet (U.filter (fun x => x ≤ a)) := by
    rw [hcut, singleton_isominimal_iff_zero]
    exact (positive_of_strict_first hab hlt).ne'
  refine ⟨U, a, hU, ha, hnon, ?_⟩
  intro hc
  exact (not_le_of_gt hlt)
    ((Str.initialCut_correct_iff (Str.ofOrdinals U) a).mp hc a ha le_rfl b hb hab)

end Alexander313.Carlson
