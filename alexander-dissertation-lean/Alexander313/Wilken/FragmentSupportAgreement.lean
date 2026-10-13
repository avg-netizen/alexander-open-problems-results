import Alexander313.Wilken.HullSupportTransfer

/-!
# Adjacent fragment fidelity from proved higher calls

The helpers below propagate equality of actual higher collapsing calls
through the finite grammar and through the already well-founded P
recursion. Finite coverage proves that every old grammar call meets the
smaller fragment's true argument bound. The end-extension module supplies
the higher equalities by descending finite-level induction; no final
theorem assumes an end-extension package. Candidate terms, uncompiled.
-/

namespace Alexander313.Wilken

theorem finiteBoundary_next_lt_sort (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) :
    finiteBoundary τ n (m + 1) < omegaSequence τ (m + 2) := by
  by_cases hnext : m + 1 < n
  · exact finiteBoundary_lt_cardinal τ hτ n (m + 1) hnext
  · have hn : n = m + 1 := by omega
    subst n
    rw [finiteBoundary_terminal τ (m + 1) (Nat.succ_pos m), Nat.add_sub_cancel]
    exact (finiteBoundary_lt_cardinal τ hτ (m + 1) m (Nat.lt_succ_self m)).trans
      (omegaSequence_step τ (m + 1))

/-- The cutoff is an actual initial part of Tⁿₘ₊₁, including its
duplicated terminal convention; it is never treated as Ωₘ₊₂ itself. -/
theorem source_nextNotation_of_lt_finiteBoundary (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) {ξ : Ordinal.{0}}
    (hξ : ξ < finiteBoundary τ n (m + 1)) : sourceNotation τ n (m + 1) ξ := by
  by_cases hnext : m + 1 < n
  · exact ((source_finite_notation_low_iff_lt_boundary τ hτ n (m + 1) hnext ξ).2 hξ).1
  · have hn : n = m + 1 := by omega
    subst n
    rw [finiteBoundary_terminal τ (m + 1) (Nat.succ_pos m), Nat.add_sub_cancel] at hξ
    rw [sourceNotation, if_neg (lt_irrefl (m + 1))]
    exact hξ.trans (finiteBoundary_lt_cardinal τ hτ (m + 1) m (Nat.lt_succ_self m))

/-- Every constructor bound needed for this grammar embedding is proved
by finite coverage. The final corollary discharges `agreement`. -/
theorem sourceNotation_next_fragment_of_agreement (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n r : Nat) (hrn : r ≤ n)
    (agreement : ∀ k, r ≤ k → k < n → ∀ η,
      η < finiteBoundary τ n (k + 1) →
      sourceFiniteCollapse τ n k η = sourceFiniteCollapse τ (n + 1) k η)
    {ξ : Ordinal.{0}} (hξ : sourceNotation τ n r ξ) :
    sourceNotation τ (n + 1) r ξ := by
  have hrnew : r < n + 1 := by omega
  by_cases hr : r < n
  · rw [sourceNotation, if_pos hr] at hξ
    rw [sourceNotation, if_pos hrnew]
    induction hξ with
    | parameter hp => exact .parameter hp
    | add _ _ iha ihb => exact .add iha ihb
    | @collapse k η hrk hkn hsort hη ih =>
      have hηNotation : sourceNotation τ n r η := by
        simpa only [sourceNotation, if_pos hr] using hη
      have hbound := source_finite_collapse_argument_lt_boundary τ hτ n r k hrk hkn
        hηNotation hsort
      rw [agreement k hrk hkn η hbound]
      exact .collapse hrk (by omega) hsort ih
  · have hr : r = n := by omega
    subst r
    rw [sourceNotation, if_neg (lt_irrefl n)] at hξ
    rw [sourceNotation, if_pos (Nat.lt_succ_self n)]
    exact .parameter hξ

/-- Actual P support is preserved when all higher constructor calls
agree. Recursion decreases the old fragment's proved finite presentation
size, not the ordinal value of a collapsing argument. -/
theorem sourceP_next_fragment_of_higher_agreement (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n)
    (higher : ∀ k, m < k → k < n → ∀ η,
      η < finiteBoundary τ n (k + 1) →
      sourceFiniteCollapse τ n k η = sourceFiniteCollapse τ (n + 1) k η)
    (ξ : SourceNotationOrdinal τ n (m + 1))
    (ξ' : SourceNotationOrdinal τ (n + 1) (m + 1)) (heq : ξ.val = ξ'.val) :
    sourceP τ hτ n m hm ξ = sourceP τ hτ (n + 1) m (by omega) ξ' := by
  classical
  revert ξ'
  refine (presentationOrder_wf τ n (m + 1) (Nat.succ_pos m)
    (Nat.succ_le_of_lt hm)).induction ξ
    (C := fun ξ => ∀ ξ' : SourceNotationOrdinal τ (n + 1) (m + 1), ξ.val = ξ'.val →
      sourceP τ hτ n m hm ξ = sourceP τ hτ (n + 1) m (by omega) ξ') ?_
  intro ξ ih ξ' heq
  have embed : ∀ η, sourceNotation τ n (m + 1) η →
      sourceNotation τ (n + 1) (m + 1) η := by
    intro η hη
    exact sourceNotation_next_fragment_of_agreement τ hτ n (m + 1)
      (Nat.succ_le_of_lt hm)
      (fun k hmk hkn γ hγ => higher k (by omega) hkn γ hγ) hη
  by_cases hlow : ξ.val < omegaSequence τ (m + 1)
  · rw [sourceP_low τ hτ n m hm ξ hlow,
      sourceP_low τ hτ (n + 1) m (by omega) ξ' (by simpa only [← heq] using hlow), heq]
  · by_cases hp : Ordinal.IsPrincipal (· + ·) ξ.val
    · let q := sourceHigherPresentation τ hτ n m hm ξ (le_of_not_gt hlow) hp
      let γ' : SourceNotationOrdinal τ (n + 1) (m + 1) :=
        ⟨q.argument.val, embed q.argument.val q.argument.property⟩
      have hmq : m < q.level := by have h := q.lower; omega
      have hbound := source_finite_collapse_argument_lt_boundary τ hτ n (m + 1) q.level
        q.lower q.upper q.argument.property q.sort
      have hdenote : ξ'.val = sourceFiniteCollapse τ (n + 1) q.level γ'.val :=
        heq.symm.trans (q.denote.trans (higher q.level hmq q.upper q.argument.val hbound))
      calc
        sourceP τ hτ n m hm ξ = sourceP τ hτ n m hm q.argument :=
          sourceP_principal τ hτ n m hm ξ (le_of_not_gt hlow) hp
        _ = sourceP τ hτ (n + 1) m (by omega) γ' :=
          ih q.argument (sourceHigherPresentation_order τ hτ n m hm ξ q) γ' rfl
        _ = sourceP τ hτ (n + 1) m (by omega) ξ' :=
          (sourceP_theta τ hτ (n + 1) m (by omega) ξ' γ' q.level hmq
            (by have h := q.upper; omega) q.sort hdenote).symm
    · ext p
      constructor
      · intro hmem
        obtain ⟨a, ha, hpa⟩ := (sourceP_mem_anf τ hτ n m hm ξ p).1 hmem
        have ha' : a ∈ canonicalANF ξ'.val := by simpa only [← heq] using ha
        have hsame := ih (sourceComponent τ hτ n m hm ξ a ha)
          (sourceComponent_order τ hτ n m hm ξ (le_of_not_gt hlow) hp a ha)
          (sourceComponent τ hτ (n + 1) m (by omega) ξ' a ha') rfl
        exact (sourceP_mem_anf τ hτ (n + 1) m (by omega) ξ' p).2
          ⟨a, ha', by simpa only [hsame] using hpa⟩
      · intro hmem
        obtain ⟨a, ha', hpa⟩ := (sourceP_mem_anf τ hτ (n + 1) m (by omega) ξ' p).1 hmem
        have ha : a ∈ canonicalANF ξ.val := by simpa only [heq] using ha'
        have hsame := ih (sourceComponent τ hτ n m hm ξ a ha)
          (sourceComponent_order τ hτ n m hm ξ (le_of_not_gt hlow) hp a ha)
          (sourceComponent τ hτ (n + 1) m (by omega) ξ' a ha') rfl
        exact (sourceP_mem_anf τ hτ n m hm ξ p).2
          ⟨a, ha, by simpa only [← hsame] using hpa⟩

end Alexander313.Wilken
