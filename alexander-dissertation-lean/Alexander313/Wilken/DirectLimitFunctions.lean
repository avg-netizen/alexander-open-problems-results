import Alexander313.Wilken.FragmentMonotonicity

/-!
# Actual semantic direct-limit endpoints and collapsing functions

The source endpoint θₘ is the genuine countable supremum of finite
endpoints. A finite fragment containing an argument is selected by
Nat.find. Actual finite coherence proves independence from that choice,
and actual finite coverage supplies its domain and proper range. The
total extension by zero outside the source domain is auxiliary and is
never identified with a legitimate source call. These functions remain
noncomputable; no effective public code is constructed. Uncompiled.
-/

namespace Alexander313.Wilken

noncomputable def globalBoundary (τ : Ordinal.{0}) (m : Nat) : Ordinal.{0} :=
  ⨆ j : Nat, finiteBoundary τ (m + 1 + j) m

theorem globalBoundary_cofinal (τ : Ordinal.{0}) (m : Nat) (α : Ordinal.{0}) :
    α < globalBoundary τ m ↔ ∃ j, α < finiteBoundary τ (m + 1 + j) m := by
  unfold globalBoundary
  exact Ordinal.lt_iSup_iff

theorem finiteBoundary_le_globalBoundary (τ : Ordinal.{0}) (n m : Nat) (hm : m < n) :
    finiteBoundary τ n m ≤ globalBoundary τ m := by
  have heq : m + 1 + (n - (m + 1)) = n := by omega
  simpa only [heq, globalBoundary] using
    Ordinal.le_iSup (fun j : Nat => finiteBoundary τ (m + 1 + j) m) (n - (m + 1))

/-- This also covers the duplicated old terminal level m=n. -/
theorem finiteBoundary_lt_globalBoundary (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n : Nat) (hn : 0 < n) (m : Nat) (hm : m ≤ n) :
    finiteBoundary τ n m < globalBoundary τ m :=
  (finiteBoundary_strict_end_extension τ hτ n hn m hm).trans_le
    (finiteBoundary_le_globalBoundary τ (n + 1) m (by omega))

theorem globalBoundary_lt_cardinal (τ : Ordinal.{0}) (hτ : 0 < τ) (m : Nat) :
    globalBoundary τ m < omegaSequence τ (m + 1) := by
  unfold globalBoundary
  apply Ordinal.lift_iSup_lt_of_lt_cof
  · simpa only [Cardinal.mk_nat, Cardinal.lift_aleph0, Ordinal.lift_id, omegaSequence,
      (omegaSequence_regular τ m).cof_ord] using
        (levelCardinal_infinite τ m).trans_lt (levelCardinal_step τ m)
  · intro j
    exact finiteBoundary_lt_cardinal τ hτ (m + 1 + j) m (by omega)

theorem globalBoundary_base_lt (τ : Ordinal.{0}) (hτ : 0 < τ) (m : Nat) :
    omegaSequence τ m < globalBoundary τ m :=
  (finiteBoundary_base_lt τ hτ (m + 1) m (Nat.lt_succ_self m)).trans_le
    (finiteBoundary_le_globalBoundary τ (m + 1) m (Nat.lt_succ_self m))

/-- The selected fragment is strictly above m+1, as required by the
cofinal representation of the next global endpoint. -/
noncomputable def globalFragment (τ : Ordinal.{0}) (m : Nat) (α : Ordinal.{0})
    (hα : α < globalBoundary τ (m + 1)) : Nat :=
  m + 2 + Nat.find ((globalBoundary_cofinal τ (m + 1) α).1 hα)

theorem globalFragment_gt (τ : Ordinal.{0}) (m : Nat) (α : Ordinal.{0})
    (hα : α < globalBoundary τ (m + 1)) : m + 1 < globalFragment τ m α hα := by
  unfold globalFragment
  omega

theorem globalFragment_bound (τ : Ordinal.{0}) (m : Nat) (α : Ordinal.{0})
    (hα : α < globalBoundary τ (m + 1)) :
    α < finiteBoundary τ (globalFragment τ m α hα) (m + 1) := by
  simpa only [globalFragment] using
    Nat.find_spec ((globalBoundary_cofinal τ (m + 1) α).1 hα)

/-- ϑₘ on θₘ₊₁; the zero value outside that domain is auxiliary. -/
noncomputable def globalCollapse (τ : Ordinal.{0}) (m : Nat) (α : Ordinal.{0}) : Ordinal.{0} :=
  if hα : α < globalBoundary τ (m + 1) then
    sourceFiniteCollapse τ (globalFragment τ m α hα) m α else 0

/-- Every eligible finite fragment gives the same actual global value.
The endpoint inequality supplies the global input domain even in the
old duplicated-terminal case. -/
theorem globalCollapse_finite_agreement (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (α : Ordinal.{0})
    (hα : α < finiteBoundary τ n (m + 1)) :
    globalCollapse τ m α = sourceFiniteCollapse τ n m α := by
  have hglobal : α < globalBoundary τ (m + 1) :=
    hα.trans (finiteBoundary_lt_globalBoundary τ hτ n (by omega) (m + 1) (by omega))
  rw [globalCollapse, dif_pos hglobal]
  let p := globalFragment τ m α hglobal
  have hp : m < p := (Nat.lt_succ_self m).trans (globalFragment_gt τ m α hglobal)
  have hbound : α < finiteBoundary τ p (m + 1) := globalFragment_bound τ m α hglobal
  exact (sourceFiniteCollapse_fragment_agreement τ hτ p m (max n p) hp (le_max_right n p)
    α hbound).trans
    (sourceFiniteCollapse_fragment_agreement τ hτ n m (max n p) hm (le_max_left n p) α hα).symm

theorem globalCollapse_bounds (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) (α : Ordinal.{0}) (hα : α < globalBoundary τ (m + 1)) :
    omegaSequence τ m ≤ globalCollapse τ m α ∧
      globalCollapse τ m α < omegaSequence τ (m + 1) := by
  let n := globalFragment τ m α hα
  have hm : m < n := (Nat.lt_succ_self m).trans (globalFragment_gt τ m α hα)
  have hb : α < finiteBoundary τ n (m + 1) := globalFragment_bound τ m α hα
  rw [globalCollapse_finite_agreement τ hτ n m hm α hb]
  exact ⟨(sourceFiniteCollapse_bounds τ n m hm α).1,
    sourceFiniteCollapse_proper_notation τ n m hm α
      (hb.trans (finiteBoundary_next_lt_sort τ hτ n m hm))
      (source_nextNotation_of_lt_finiteBoundary τ hτ n m hm hb)⟩

/-- The literal typed function θₘ₊₁ → Ωₘ₊₁ in Definition 2.17.
This is a semantic ordinal function, not a public-code algorithm. -/
noncomputable def globalCollapseOnDomain (τ : Ordinal.{0}) (hτ : 0 < τ) (m : Nat) :
    {α : Ordinal.{0} // α < globalBoundary τ (m + 1)} →
      {β : Ordinal.{0} // β < omegaSequence τ (m + 1)} :=
  fun α => ⟨globalCollapse τ m α.val, (globalCollapse_bounds τ hτ m α.val α.property).2⟩

end Alexander313.Wilken
