import Alexander313.Wilken.FiniteEndExtension
import Alexander313.Wilken.TerminalExtension

/-!
# Strict growth of the actual finite endpoints

The old endpoint is bounded by the first descending approximant of the
next fragment. At the terminal level this is the already proved exact
boundary identity. At each lower level actual empty-support comparison,
adjacent support fidelity and adjacent function agreement bound every
old approximant. Its genuine supremum is therefore below the next
fragment's endpoint. This is the remaining clause of source Lemma 2.15,
for n>0 and all m≤n. All proof terms are uncompiled candidates.
-/

namespace Alexander313.Wilken

theorem finiteApproximant_support_empty (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n r : Nat) (hr : r < n) (m : Nat) (hm : m < r) (k : Nat) :
    sourceP τ hτ n m (by omega)
      ⟨finiteApproximant τ n r k,
        finiteApproximant_lower_notation τ hτ n r hr (m + 1) (by omega) k⟩ = ∅ := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  have hd : N.succ - (r + 1) ≤ N := by omega
  have hlevel : N - (N.succ - (r + 1)) = r := by omega
  simpa only [finiteApproximant, Nat.succ_sub_one] using
    descendingApproximant_support_empty τ hτ N (N.succ - (r + 1)) hd m (by omega) k

theorem finiteApproximant_terminal_one (τ : Ordinal.{0}) (n : Nat) (hn : 0 < n) :
    finiteApproximant τ (n + 1) n 1 = omegaSequence τ n := by
  rw [finiteApproximant_top, terminalApproximant_succ, terminalApproximant_zero]
  exact sourceFiniteCollapse_zero_positiveLevel τ (n + 1) n (Nat.lt_succ_self n) hn

/-- A concrete new finite term bounds the whole old supremum. -/
theorem finiteBoundary_le_next_firstApproximant (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) :
    finiteBoundary τ n m ≤ finiteApproximant τ (n + 1) m 1 := by
  have all : ∀ m : Fin n,
      finiteBoundary τ n m.val ≤ finiteApproximant τ (n + 1) m.val 1 := by
    intro m
    refine (InvImage.wf (fun k : Fin n => n - k.val) Nat.lt_wfRel.wf).induction m
      (C := fun m => finiteBoundary τ n m.val ≤ finiteApproximant τ (n + 1) m.val 1) ?_
    intro m ih
    by_cases hnext : m.val + 1 < n
    · have hnextBound := ih ⟨m.val + 1, hnext⟩
        (by change n - (m.val + 1) < n - m.val; have h := m.isLt; omega)
      rw [finiteBoundary, if_pos m.isLt.le]
      apply Ordinal.iSup_le
      intro k
      let a : SourceNotationOrdinal τ n (m.val + 1) :=
        ⟨finiteApproximant τ n (m.val + 1) k,
          finiteApproximant_lower_notation τ hτ n (m.val + 1) hnext (m.val + 1) le_rfl k⟩
      let a' : SourceNotationOrdinal τ (n + 1) (m.val + 1) :=
        ⟨a.val, sourceNotation_finite_end_extension τ hτ n (m.val + 1) hnext.le a.property⟩
      let b : SourceNotationOrdinal τ (n + 1) (m.val + 1) :=
        ⟨finiteApproximant τ (n + 1) (m.val + 1) 1,
          finiteApproximant_lower_notation τ hτ (n + 1) (m.val + 1) (by omega)
            (m.val + 1) le_rfl 1⟩
      have hsorta : a.val < omegaSequence τ (m.val + 2) :=
        finiteApproximant_lt_cardinal τ hτ n (m.val + 1) hnext k
      have hsortb : b.val < omegaSequence τ (m.val + 2) :=
        finiteApproximant_lt_cardinal τ hτ (n + 1) (m.val + 1) (by omega) 1
      have hab : a'.val < b.val :=
        (finiteApproximant_lt_boundary τ hτ n (m.val + 1) hnext k).trans_le hnextBound
      have hempty : sourceP τ hτ (n + 1) m.val (by omega) a' = ∅ := by
        rw [← sourceP_finite_end_extension τ hτ n m.val m.isLt a a' rfl]
        exact finiteApproximant_support_empty τ hτ n (m.val + 1) hnext m.val
          (Nat.lt_succ_self m.val) k
      have hvalues := sourceFiniteCollapse_lt_of_empty_support τ hτ (n + 1) m.val
        (by have h := m.isLt; omega) a' b hsorta hsortb hab hempty
      have hagree := sourceFiniteCollapse_finite_end_extension τ hτ n m.val m.isLt a.val
        (finiteApproximant_lt_boundary τ hτ n (m.val + 1) hnext k)
      rw [finiteApproximant_next τ n m.val k hnext,
        finiteApproximant_next τ (n + 1) m.val 1 (by have h := m.isLt; omega), hagree]
      exact hvalues.le
    · have hn : n = m.val + 1 := by have h := m.isLt; omega
      have hb : finiteBoundary τ n m.val =
          sourceFiniteCollapse τ (n + 1) m.val (omegaSequence τ n) := by
        simpa only [hn, finiteBoundary_top] using
          terminalBoundary_eq_next_collapse τ hτ m.val
      have ha : finiteApproximant τ (n + 1) m.val 1 =
          sourceFiniteCollapse τ (n + 1) m.val (omegaSequence τ n) := by
        rw [finiteApproximant_next τ (n + 1) m.val 1 (by have h := m.isLt; omega)]
        rw [← hn, finiteApproximant_terminal_one τ n (by have h := m.isLt; omega)]
      exact (hb.trans ha.symm).le
  exact all ⟨m, hm⟩

/-- Full strict endpoint growth from source Lemma 2.15, including the
duplicated terminal endpoint. n>0 is Definition 2.12's source domain. -/
theorem finiteBoundary_strict_end_extension (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n : Nat) (hn : 0 < n) (m : Nat) (hm : m ≤ n) :
    finiteBoundary τ n m < finiteBoundary τ (n + 1) m := by
  rcases hm.eq_or_lt with hterminal | hproper
  · subst m
    rw [finiteBoundary_terminal τ n hn]
    have hcard : finiteBoundary τ n (n - 1) < omegaSequence τ n := by
      have hindex : n - 1 + 1 = n := by omega
      simpa only [hindex] using
        finiteBoundary_lt_cardinal τ hτ n (n - 1) (by omega)
    exact hcard.trans (finiteBoundary_base_lt τ hτ (n + 1) n (Nat.lt_succ_self n))
  · exact (finiteBoundary_le_next_firstApproximant τ hτ n m hproper).trans_lt
      (finiteApproximant_lt_boundary τ hτ (n + 1) m (by omega) 1)

end Alexander313.Wilken
