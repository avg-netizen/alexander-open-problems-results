import Alexander313.Wilken.DirectLimitNotations

/-!
# The genuine global descending cofinal chain

Global collapsing functions are iterated literally, from ϑₙ(0) down to
the desired level. Every iterate is proved equal to an actual finite
first approximant, using real finite argument domains and global/finite
function fidelity. The endpoint-growth bound then proves the supremum
identity in Theorem 2.18. The separate exact finite-boundary identity in
Corollary 2.19 is not claimed here. All terms await compilation.
-/

namespace Alexander313.Wilken

noncomputable def globalTower (τ : Ordinal.{0}) (top : Nat) : Nat → Ordinal.{0}
  | 0 => globalCollapse τ top 0
  | d + 1 => globalCollapse τ (top - (d + 1)) (globalTower τ top d)

/-- The actual global iteration denotes the actual finite first tower. -/
theorem globalTower_eq_descending_first (τ : Ordinal.{0}) (hτ : 0 < τ)
    (top d : Nat) (hd : d ≤ top) :
    globalTower τ top d = descendingApproximant τ top d 1 := by
  revert hd
  induction d with
  | zero =>
    intro hd
    have hbase : 0 < omegaSequence τ top :=
      hτ.trans_le ((omegaSequence_strictMono τ).monotone (Nat.zero_le top))
    have hzero : sourceNotation τ (top + 1) top 0 := by
      rw [sourceNotation, if_pos (Nat.lt_succ_self top)]
      exact .parameter hbase
    have hsort : (0 : Ordinal.{0}) < omegaSequence τ (top + 2) :=
      (omegaSequence_isSuccLimit τ (top + 1)).bot_lt
    have hbound := source_finite_collapse_argument_lt_boundary τ hτ (top + 1) top top
      le_rfl (Nat.lt_succ_self top) hzero hsort
    change globalCollapse τ top 0 = sourceFiniteCollapse τ (top + 1) top 0
    exact globalCollapse_finite_agreement τ hτ (top + 1) top (Nat.lt_succ_self top) 0 hbound
  | succ d ih =>
    intro hd
    have hdprev : d ≤ top := by omega
    have hindex : top - d = top - (d + 1) + 1 := by omega
    have hsort : descendingApproximant τ top d 1 <
        omegaSequence τ (top - (d + 1) + 2) := by
      simpa only [hindex] using (descendingApproximant_properties τ hτ top d hdprev 1).2
    have hnotation : sourceNotation τ (top + 1) (top - (d + 1))
        (descendingApproximant τ top d 1) :=
      (descendingApproximant_properties τ hτ top d hdprev 1).1 (top - (d + 1)) (by omega)
    have hbound := source_finite_collapse_argument_lt_boundary τ hτ (top + 1)
      (top - (d + 1)) (top - (d + 1)) le_rfl (by omega) hnotation hsort
    change globalCollapse τ (top - (d + 1)) (globalTower τ top d) =
      sourceFiniteCollapse τ (top + 1) (top - (d + 1)) (descendingApproximant τ top d 1)
    rw [ih hdprev]
    exact globalCollapse_finite_agreement τ hτ (top + 1) (top - (d + 1)) (by omega)
      (descendingApproximant τ top d 1) hbound

/-- Literally ϑₘ(...ϑₙ(0)...), for m≤n. Irrelevant m>n values are
auxiliary and have no source correspondence theorem. -/
noncomputable def globalDescendingTerm (τ : Ordinal.{0}) (n m : Nat) : Ordinal.{0} :=
  globalTower τ n (n - m)

theorem globalDescendingTerm_eq_firstApproximant (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m ≤ n) :
    globalDescendingTerm τ n m = finiteApproximant τ (n + 1) m 1 := by
  have hdepth : n + 1 - (m + 1) = n - m := by omega
  rw [globalDescendingTerm, finiteApproximant, Nat.add_sub_cancel, hdepth]
  exact globalTower_eq_descending_first τ hτ n (n - m) (Nat.sub_le n m)

/-- The displayed global descending-chain supremum in Theorem 2.18.
The index j enumerates exactly the source heights n≥m. -/
theorem globalBoundary_eq_iSup_descending (τ : Ordinal.{0}) (hτ : 0 < τ) (m : Nat) :
    globalBoundary τ m = ⨆ j : Nat, globalDescendingTerm τ (m + j) m := by
  apply le_antisymm
  · unfold globalBoundary
    apply Ordinal.iSup_le
    intro j
    have hm : m < m + 1 + j := by omega
    have hterm : finiteApproximant τ (m + 1 + j + 1) m 1 ≤
        ⨆ i : Nat, globalDescendingTerm τ (m + i) m := by
      have heq : m + (j + 1) = m + 1 + j := by omega
      have hi := Ordinal.le_iSup (fun i : Nat => globalDescendingTerm τ (m + i) m) (j + 1)
      rw [globalDescendingTerm_eq_firstApproximant τ hτ (m + (j + 1)) m (by omega), heq] at hi
      exact hi
    exact (finiteBoundary_le_next_firstApproximant τ hτ (m + 1 + j) m hm).trans hterm
  · apply Ordinal.iSup_le
    intro j
    rw [globalDescendingTerm_eq_firstApproximant τ hτ (m + j) m (by omega)]
    exact (finiteApproximant_lt_boundary τ hτ (m + j + 1) m (by omega) 1).le.trans
      (finiteBoundary_le_globalBoundary τ (m + j + 1) m (by omega))

end Alexander313.Wilken
