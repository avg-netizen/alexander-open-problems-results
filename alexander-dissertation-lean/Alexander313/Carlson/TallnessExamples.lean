import Alexander313.Carlson.Tallness

/-! Boundary cases and an order-violating negative control for coveredness. -/

noncomputable section

namespace Alexander313.Carlson

def completeFiniteChain (n : ℕ) : Str (Fin n) := ⟨Finset.univ, (· ≤ ·), (· ≤ ·)⟩

theorem completeFiniteChain_isPattern (n : ℕ) : (completeFiniteChain n).IsPattern := by
  exact ⟨fun _ _ _ _ h => h, fun _ _ _ _ h => h, fun _ _ => le_rfl,
    fun _ _ => le_rfl, fun _ _ _ _ _ _ h₁ h₂ => h₁.trans h₂,
    fun _ _ _ _ _ _ h₁ h₂ => h₁.trans h₂, fun _ _ _ _ _ _ h _ _ => h,
    fun _ _ _ _ _ _ h _ _ _ => h⟩

theorem completeFiniteChain_covered (n : ℕ) : (completeFiniteChain n).Covered :=
  every_pattern_covered _ (completeFiniteChain_isPattern n)

theorem empty_second_chain :
    ∃ xs : List Ordinal.{0}, xs.length = 0 ∧ xs.Pairwise (· < ·) ∧ xs.Pairwise R2 :=
  exists_finite_second_chain 0

theorem zero_rank_ordinal_guard :
    ∃ top : Ordinal.{0}, ∃ tail : List Ordinal.{0}, tail.length = 0 ∧
      (top :: tail).Pairwise (· < ·) ∧ (top :: tail).Pairwise R2 :=
  exists_ordinal_guard 0

def reversedFirstStructure : Str (Fin 2) := ⟨Finset.univ, fun x y => y ≤ x, (· = ·)⟩

/-- Coveredness is not asserted for structures with an edge against the
linear order: increasing images and `R1_le` exclude this two-point example. -/
theorem reversedFirstStructure_not_covered : ¬reversedFirstStructure.Covered := by
  rintro ⟨h, mono, first, _⟩
  have hlt : h 0 < h 1 := mono 0 (Finset.mem_univ _) 1 (Finset.mem_univ _) (by decide)
  have hrel : R1 (h 1) (h 0) := first 1 (Finset.mem_univ _) 0 (Finset.mem_univ _)
    (by change (0 : Fin 2) ≤ 1; decide)
  exact hlt.not_ge (R1_le hrel)

end Alexander313.Carlson
