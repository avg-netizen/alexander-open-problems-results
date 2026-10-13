import Alexander313.Wilken.TerminalCoverage
import Alexander313.Wilken.LowFragmentAgreement

/-!
# Actual terminal end-extension and the next-fragment boundary term

At the terminal level, the extra higher constructor in fragment m+2 has
values at or above Ωₘ₊₁. It cannot occur in the small part of a hull.
Restricted hull induction and ordinal induction therefore prove agreement
of the two actual collapsing functions on every argument below Ωₘ₊₁.

This gives the terminal hull/function clauses of Lemma 2.15 and the
terminal inclusion clause of Corollary 2.16. The actual
terminal boundary is then identified with ϑ^{m+2}_m(Ωₘ₊₁), supplying a
finite adjacent-fragment identity needed by Corollary 2.19. General
lower-level end-extension and the direct limit are not asserted.
Every proof term is an uncompiled candidate.
-/

namespace Alexander313.Wilken

/-- Restricted hull agreement from already proved local agreement. The
new higher level has no values below the cardinal cutoff. -/
theorem source_terminal_hull_congr_of_local (τ : Ordinal.{0}) (m : Nat)
    (α β : Ordinal.{0}) (hα : α ≤ omegaSequence τ (m + 1))
    («local» : ∀ γ < α, sourceFiniteCollapse τ (m + 1) m γ =
      sourceFiniteCollapse τ (m + 2) m γ)
    (ξ : Ordinal.{0}) (hξ : ξ < omegaSequence τ (m + 1)) :
    Hull (omegaSequence τ) (sourceFiniteCollapse τ (m + 1)) (m + 1) m α β ξ ↔
      Hull (omegaSequence τ) (sourceFiniteCollapse τ (m + 2)) (m + 2) m α β ξ :=
  source_low_hull_congr_of_local τ (m + 1) (m + 2) m α β hα «local» ξ hξ

/-- The minimum candidates agree because both their small closure test
and their actual argument-membership test see only the restricted hull. -/
theorem source_terminal_candidate_congr_of_local (τ : Ordinal.{0}) (m : Nat)
    (α β : Ordinal.{0}) (hα : α < omegaSequence τ (m + 1))
    («local» : ∀ γ < α, sourceFiniteCollapse τ (m + 1) m γ =
      sourceFiniteCollapse τ (m + 2) m γ) :
    CollapseCandidate (omegaSequence τ) (sourceFiniteCollapse τ (m + 1))
        (m + 1) m α β ↔
      CollapseCandidate (omegaSequence τ) (sourceFiniteCollapse τ (m + 2))
        (m + 2) m α β :=
  source_low_candidate_congr_of_local τ (m + 1) (m + 2) m α β hα «local»

/-- Actual terminal collapsing functions agree on the whole low argument
segment, a larger domain than the terminal instance of Lemma 2.15 asks. -/
theorem source_terminal_collapse_end_extension (τ : Ordinal.{0}) (m : Nat)
    (α : Ordinal.{0}) (hα : α < omegaSequence τ (m + 1)) :
    sourceFiniteCollapse τ (m + 1) m α = sourceFiniteCollapse τ (m + 2) m α :=
  sourceFiniteCollapse_low_fragment_agreement τ (m + 1) (m + 2) m
    (Nat.lt_succ_self m) (by omega) α hα

/-- Terminal hulls agree below Ωₘ₊₁ for every bounded local argument.
This includes the smaller cutoff θ^{m+1}_m used in source Lemma 2.15. -/
theorem source_terminal_hull_end_extension (τ : Ordinal.{0}) (m : Nat)
    (α β ξ : Ordinal.{0}) (hα : α ≤ omegaSequence τ (m + 1))
    (hξ : ξ < omegaSequence τ (m + 1)) :
    Hull (omegaSequence τ) (sourceFiniteCollapse τ (m + 1)) (m + 1) m α β ξ ↔
      Hull (omegaSequence τ) (sourceFiniteCollapse τ (m + 2)) (m + 2) m α β ξ :=
  source_terminal_hull_congr_of_local τ m α β hα
    (fun γ hγ => source_terminal_collapse_end_extension τ m γ (hγ.trans_le hα)) ξ hξ

/-- The terminal finite fragment really embeds in the next fragment. -/
theorem source_terminal_notation_end_extension (τ : Ordinal.{0}) (m : Nat)
    {ξ : Ordinal.{0}} (hξ : sourceNotation τ (m + 1) m ξ) :
    sourceNotation τ (m + 2) m ξ := by
  rw [sourceNotation, if_pos (by omega : m < m + 2)]
  rw [sourceNotation, if_pos (Nat.lt_succ_self m)] at hξ
  induction hξ with
  | parameter h => exact .parameter h
  | add _ _ ihξ ihη => exact .add ihξ ihη
  | @collapse k α hmk hkn hsort hα ih =>
    have hk : k = m := by omega
    subst k
    have hnotation : sourceNotation τ (m + 1) m α := by
      rw [sourceNotation, if_pos (Nat.lt_succ_self m)]
      exact hα
    have hsmall := (source_terminal_notation_lt_boundary τ m hnotation).trans
      (terminalBoundary_lt_cardinal τ m)
    rw [source_terminal_collapse_end_extension τ m α hsmall]
    exact .collapse le_rfl (by omega) hsort ih

/-- The newly available next-cardinal argument has the terminal boundary
as a genuine non-fallback minimum candidate. -/
theorem terminalBoundary_next_candidate (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) :
    CollapseCandidate (omegaSequence τ) (sourceFiniteCollapse τ (m + 2))
      (m + 2) m (omegaSequence τ (m + 1)) (terminalBoundary τ m) := by
  have hbase : 0 < omegaSequence τ m :=
    hτ.trans_le ((omegaSequence_strictMono τ).monotone (Nat.zero_le m))
  refine ⟨terminalBoundary_lt_cardinal τ m, ?_, ?_⟩
  · intro ξ hin hsmall
    revert hsmall
    induction hin with
    | below_base h => intro _; exact h.trans (terminalBoundary_base_lt τ m)
    | below_parameter h => intro _; exact h
    | @add x y hx hy ihx ihy =>
      intro hsmall
      exact terminalBoundary_add_closed τ m
        (ihx (le_self_add.trans_lt hsmall)) (ihy (le_add_self.trans_lt hsmall))
    | @higher k γ hmk hkn hsort harg ih =>
      intro hsmall
      have hlevel : omegaSequence τ (m + 1) ≤ omegaSequence τ k :=
        (omegaSequence_strictMono τ).monotone (Nat.succ_le_of_lt hmk)
      exact False.elim (hsmall.not_ge
        (hlevel.trans (sourceFiniteCollapse_bounds τ (m + 2) k hkn γ).1))
    | @«local» γ hγ harg ih =>
      intro _
      rw [← source_terminal_collapse_end_extension τ m γ hγ]
      exact terminalBoundary_collapse_closed τ m (ih hγ)
  · have hzero : sourceFiniteCollapse τ (m + 2) (m + 1) 0 =
        omegaSequence τ (m + 1) :=
      sourceFiniteCollapse_zero_positiveLevel τ (m + 2) (m + 1) (by omega) (by omega)
    rw [← hzero]
    exact .higher (Nat.lt_succ_self m) (by omega)
      ((omegaSequence_isSuccLimit τ (m + 2)).bot_lt) (.below_base hbase)

/-- Each old terminal iterate is below the new collapse at the next
cardinal. This is a real hull calculation for the actual new fragment. -/
theorem terminalApproximant_lt_next_collapse (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m k : Nat) :
    terminalApproximant τ m k <
      sourceFiniteCollapse τ (m + 2) m (omegaSequence τ (m + 1)) := by
  induction k with
  | zero => exact sourceFiniteCollapse_pos τ hτ (m + 2) m (by omega) _
  | succ k ih =>
    rw [terminalApproximant_succ,
      source_terminal_collapse_end_extension τ m _ (terminalApproximant_lt_cardinal τ m k)]
    exact (finiteCollapse_hull_initial (by omega : m < m + 2)
      (omegaSequence τ (m + 1)) _).1
      ⟨.«local» (terminalApproximant_lt_cardinal τ m k) (.below_parameter ih),
        by
          rw [← source_terminal_collapse_end_extension τ m _
            (terminalApproximant_lt_cardinal τ m k)]
          exact terminalApproximant_lt_cardinal τ m (k + 1)⟩

/-- The terminal boundary is represented by an actual next-fragment
term. This is a finite identity needed by Corollary 2.19; the global
direct-limit function in that corollary has not yet been constructed. -/
theorem terminalBoundary_eq_next_collapse (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) :
    terminalBoundary τ m =
      sourceFiniteCollapse τ (m + 2) m (omegaSequence τ (m + 1)) := by
  apply le_antisymm
  · exact Ordinal.iSup_le (fun k => (terminalApproximant_lt_next_collapse τ hτ m k).le)
  · exact finiteCollapse_minimal (by omega : m < m + 2)
      (terminalBoundary_next_candidate τ hτ m)

theorem terminalBoundary_next_notation (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) :
    sourceNotation τ (m + 2) m (terminalBoundary τ m) := by
  rw [terminalBoundary_eq_next_collapse τ hτ m,
    sourceNotation, if_pos (by omega : m < m + 2)]
  have hbase : 0 < omegaSequence τ m :=
    hτ.trans_le ((omegaSequence_strictMono τ).monotone (Nat.zero_le m))
  have hzero := sourceFiniteCollapse_zero_positiveLevel τ (m + 2) (m + 1) (by omega) (by omega)
  have hargument : FiniteNotation (omegaSequence τ) (sourceFiniteCollapse τ (m + 2))
      (m + 2) m (omegaSequence τ (m + 1)) := by
    rw [← hzero]
    exact .collapse (Nat.le_succ m) (by omega)
      ((omegaSequence_isSuccLimit τ (m + 2)).bot_lt) (.parameter hbase)
  exact .collapse le_rfl (by omega) (omegaSequence_step τ (m + 1)) hargument

/-- Actual strict extension, witnessed by the first ordinal missing from
the old terminal fragment, rather than an assumed boundary inequality. -/
theorem source_terminal_notation_strict_extension (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) :
    ∃ ξ, sourceNotation τ (m + 2) m ξ ∧ ¬ sourceNotation τ (m + 1) m ξ :=
  ⟨terminalBoundary τ m, terminalBoundary_next_notation τ hτ m,
    source_terminal_notation_boundary_absent τ m⟩

end Alexander313.Wilken
