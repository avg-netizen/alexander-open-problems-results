import Alexander313.Wilken.LowLimitArithmetic

/-!
# The genuine terminal boundary and its next principal value

The actual terminal iteration from zero has the same argument and image
suprema. Countable low-limit arithmetic therefore computes the collapse at
its boundary as the next additive principal. An independent iteration proof
shows that this boundary is the least positive ordinal whose initial segment
is closed under the actual terminal collapsing function.

This is an actual source boundary statement, not an identification with a
named epsilon number or with the prescribed υ bases. The boundary itself is
outside its terminal notation grammar; its low next-level argument sort still
licenses the displayed function evaluation. Uncompiled proof terms.
-/

namespace Alexander313.Wilken

theorem terminal_lowCollapseSup_eq_boundary (τ : Ordinal.{0}) (m : Nat) :
    lowCollapseSup τ (m + 1) m (terminalApproximant τ m) = terminalBoundary τ m := by
  apply le_antisymm
  · apply Ordinal.iSup_le
    intro j
    exact Ordinal.le_iSup (terminalApproximant τ m) (j + 1)
  · apply Ordinal.iSup_le
    intro j
    exact ((terminalApproximant_strictMono τ m).monotone (Nat.le_succ j)).trans
      (Ordinal.le_iSup
        (fun k => sourceFiniteCollapse τ (m + 1) m (terminalApproximant τ m k)) j)

theorem sourceFiniteCollapse_terminalBoundary_eq_nextAdditivePrincipal
    (τ : Ordinal.{0}) (m : Nat) :
    sourceFiniteCollapse τ (m + 1) m (terminalBoundary τ m) =
      nextAdditivePrincipal (terminalBoundary τ m) := by
  have h := sourceFiniteCollapse_limit_eq_next_of_eq τ (m + 1) m (Nat.lt_succ_self m)
    (terminalApproximant τ m) (terminalApproximant_strictMono τ m)
    (terminalApproximant_lt_cardinal τ m) (terminal_lowCollapseSup_eq_boundary τ m).symm
  rw [terminal_lowCollapseSup_eq_boundary] at h
  exact h

theorem terminalBoundary_le_of_positive_collapse_closed (τ : Ordinal.{0}) (m : Nat)
    (β : Ordinal.{0}) (hβ : 0 < β)
    (hclosed : ∀ ξ < β, sourceFiniteCollapse τ (m + 1) m ξ < β) :
    terminalBoundary τ m ≤ β := by
  have hiter : ∀ j, terminalApproximant τ m j < β := by
    intro j
    induction j with
    | zero => exact hβ
    | succ j ih => exact hclosed _ ih
  exact Ordinal.iSup_le (fun j => (hiter j).le)

theorem terminalBoundary_pos (τ : Ordinal.{0}) (m : Nat) :
    0 < terminalBoundary τ m :=
  (zero_le : 0 ≤ omegaSequence τ m).trans_lt (terminalBoundary_base_lt τ m)

/-- Exact least positive initial-segment closure, derived from the actual
iteration and its already proved below-boundary collapse closure. -/
theorem terminalBoundary_is_least_positive_collapse_closed (τ : Ordinal.{0}) (m : Nat) :
    0 < terminalBoundary τ m ∧
      (∀ ξ < terminalBoundary τ m,
        sourceFiniteCollapse τ (m + 1) m ξ < terminalBoundary τ m) ∧
      ∀ β : Ordinal.{0}, 0 < β →
        (∀ ξ < β, sourceFiniteCollapse τ (m + 1) m ξ < β) → terminalBoundary τ m ≤ β :=
  ⟨terminalBoundary_pos τ m,
    fun ξ hξ => terminalBoundary_collapse_closed τ m hξ,
    terminalBoundary_le_of_positive_collapse_closed τ m⟩

theorem terminalBoundary_lt_its_collapse (τ : Ordinal.{0}) (m : Nat) :
    terminalBoundary τ m < sourceFiniteCollapse τ (m + 1) m (terminalBoundary τ m) := by
  rw [sourceFiniteCollapse_terminalBoundary_eq_nextAdditivePrincipal]
  exact (nextAdditivePrincipal_spec _).1

/-- Every low global call agrees with every finite fragment containing its
level, even when the low argument lies above that fragment's own boundary. -/
theorem globalCollapse_low_finite_agreement (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (α : Ordinal.{0})
    (hα : α < omegaSequence τ (m + 1)) :
    globalCollapse τ m α = sourceFiniteCollapse τ n m α := by
  have hglobal : α < globalBoundary τ (m + 1) :=
    hα.trans (globalBoundary_base_lt τ hτ (m + 1))
  rw [globalCollapse, dif_pos hglobal]
  have hfragment : m < globalFragment τ m α hglobal := by
    have h := globalFragment_gt τ m α hglobal
    omega
  exact sourceFiniteCollapse_low_fragment_agreement τ (globalFragment τ m α hglobal)
    n m hfragment hm α hα

theorem globalCollapse_low_argument_lt (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) (α : Ordinal.{0}) (hα : α < omegaSequence τ (m + 1)) :
    α < globalCollapse τ m α := by
  rw [globalCollapse_low_finite_agreement τ hτ (m + 1) m (Nat.lt_succ_self m) α hα]
  exact sourceFiniteCollapse_low_argument_lt τ (m + 1) m (Nat.lt_succ_self m) hα

theorem globalCollapse_strictMono_low (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) {α β : Ordinal.{0}} (hαβ : α < β)
    (hβ : β < omegaSequence τ (m + 1)) :
    globalCollapse τ m α < globalCollapse τ m β := by
  rw [globalCollapse_low_finite_agreement τ hτ (m + 1) m (Nat.lt_succ_self m)
    α (hαβ.trans hβ),
    globalCollapse_low_finite_agreement τ hτ (m + 1) m (Nat.lt_succ_self m) β hβ]
  exact sourceFiniteCollapse_strictMono_low τ (m + 1) m (Nat.lt_succ_self m) hαβ hβ

theorem globalCollapse_terminalBoundary_eq_nextAdditivePrincipal
    (τ : Ordinal.{0}) (hτ : 0 < τ) (m : Nat) :
    globalCollapse τ m (terminalBoundary τ m) =
      nextAdditivePrincipal (terminalBoundary τ m) := by
  rw [globalCollapse_low_finite_agreement τ hτ (m + 1) m (Nat.lt_succ_self m)
    _ (terminalBoundary_lt_cardinal τ m)]
  exact sourceFiniteCollapse_terminalBoundary_eq_nextAdditivePrincipal τ m

/-- Every actual global low initial segment is closed under its real
collapsing function, not merely under addition. -/
theorem globalBoundary_collapse_closed (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) {ξ : Ordinal.{0}} (hξ : ξ < globalBoundary τ m) :
    globalCollapse τ m ξ < globalBoundary τ m := by
  have hnotation := (globalNotation_low_iff_lt_boundary τ hτ m ξ).mpr hξ
  have hsort : ξ < omegaSequence τ (m + 2) :=
    hnotation.2.trans (omegaSequence_step τ (m + 1))
  have hdomain : ξ < globalBoundary τ (m + 1) :=
    hnotation.2.trans (globalBoundary_base_lt τ hτ (m + 1))
  exact (globalNotation_low_iff_lt_boundary τ hτ m (globalCollapse τ m ξ)).mp
    ⟨.collapse le_rfl hsort hnotation.1, (globalCollapse_bounds τ hτ m ξ hdomain).2⟩

theorem globalBoundary_finite_low_collapse_closed (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) {ξ : Ordinal.{0}} (hξ : ξ < globalBoundary τ m) :
    sourceFiniteCollapse τ n m ξ < globalBoundary τ m := by
  rw [← globalCollapse_low_finite_agreement τ hτ n m hm ξ
    (hξ.trans (globalBoundary_lt_cardinal τ hτ m))]
  exact globalBoundary_collapse_closed τ hτ m hξ

namespace RelativeTerm.Hereditary

theorem finiteBase_low_collapse_closed (r n : Nat) (hn : 0 < n)
    {ξ : Ordinal.{0}} (hξ : ξ < finiteBase (r + 1)) :
    sourceFiniteCollapse (finiteBase r) n 0 ξ < finiteBase (r + 1) :=
  globalBoundary_finite_low_collapse_closed (finiteBase r) (finiteBase_pos r) n 0 hn hξ

end RelativeTerm.Hereditary

end Alexander313.Wilken
