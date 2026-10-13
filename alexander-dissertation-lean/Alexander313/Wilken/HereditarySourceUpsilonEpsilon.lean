import Alexander313.Wilken.HereditarySourceUpsilonSupport
import Alexander313.Wilken.SuccessorEpsilonBases

/-!
# Genuine epsilon bases throughout the source upsilon iteration

Every successor extension is epsilon by the actual source-grammar boundary
theorem, valid for every positive starting grammar base. At a genuine limit,
successor indices are cofinal below that limit; their real epsilon values
bound ordinary omega powers of every earlier value. Continuity of the actual
power function therefore proves epsilon status at the limit as well. Every
positive upsilon index consequently supplies the source's actual base class.
No transfinite code, tracking assignment or cross-context mu is asserted.
Uncompiled source candidate.
-/

namespace Alexander313.Wilken

theorem sourceBaseExtension_epsilon (tau : Ordinal.{0}) :
    Ordinal.omega0 ^ sourceBaseExtension tau = sourceBaseExtension tau := by
  rw [sourceBaseExtension_eq_globalBoundary]
  exact globalBoundary_omegaPower_eq_self (sourceStartingBase tau)
    (sourceStartingBase_pos tau) 0

theorem sourceUpsilon_succ_epsilon (i : Ordinal.{0}) :
    Ordinal.omega0 ^ sourceUpsilon (i + 1) = sourceUpsilon (i + 1) := by
  simpa only [sourceUpsilon_succ] using sourceBaseExtension_epsilon (sourceUpsilon i)

/-- Actual successor indices below a limit supply all power bounds; no
epsilon assertion about an arbitrary earlier index is used as a premise. -/
theorem sourceUpsilon_limit_epsilon (i : Ordinal.{0}) (hi : Order.IsSuccLimit i) :
    Ordinal.omega0 ^ sourceUpsilon i = sourceUpsilon i := by
  have := hi.nonempty_Iio.to_subtype
  rw [sourceUpsilon_limit i hi,
    (Ordinal.isNormal_opow Ordinal.one_lt_omega0).map_iSup Ordinal.bddAbove_of_small]
  apply le_antisymm
  · apply Ordinal.iSup_le
    intro j
    calc
      Ordinal.omega0 ^ sourceUpsilon j.1 ≤ Ordinal.omega0 ^ sourceUpsilon (j.1 + 1) :=
        Ordinal.opow_le_opow_right Ordinal.omega0_pos (sourceUpsilon_step j.1).le
      _ = sourceUpsilon (j.1 + 1) := sourceUpsilon_succ_epsilon j.1
      _ ≤ ⨆ k : Set.Iio i, sourceUpsilon k.1 :=
        Ordinal.le_iSup (fun k : Set.Iio i => sourceUpsilon k.1) ⟨j.1 + 1, hi.add_one_lt j.2⟩
  · apply Ordinal.iSup_le
    intro j
    exact (Ordinal.right_le_opow (sourceUpsilon j.1) Ordinal.one_lt_omega0).trans
      (Ordinal.le_iSup _ j)

theorem sourceUpsilon_positive_epsilon (i : Ordinal.{0}) (hi : 0 < i) :
    Ordinal.omega0 ^ sourceUpsilon i = sourceUpsilon i := by
  revert hi
  induction i using Ordinal.limitRecOn with
  | zero => intro hi; exact False.elim ((lt_irrefl (0 : Ordinal.{0})) hi)
  | add_one i _ => intro hi; exact sourceUpsilon_succ_epsilon i
  | limit i hi _ => intro hp; exact sourceUpsilon_limit_epsilon i hi

theorem sourceUpsilon_positive (i : Ordinal.{0}) (hi : 0 < i) : 0 < sourceUpsilon i := by
  simpa only [sourceUpsilon_zero] using sourceUpsilon_strictMono hi

/-- At every positive index the actual source grammar starts at precisely
the preceding upsilon value and satisfies the source's epsilon condition. -/
theorem sourceUpsilon_positive_grammar (i : Ordinal.{0}) (hi : 0 < i) :
    Ordinal.omega0 ^ sourceUpsilon i = sourceUpsilon i ∧
      sourceUpsilon (i + 1) = globalBoundary (sourceUpsilon i) 0 := by
  refine ⟨sourceUpsilon_positive_epsilon i hi, ?_⟩
  rw [sourceUpsilon_succ]
  exact sourceBaseExtension_eq_of_pos _ (sourceUpsilon_positive i hi)

end Alexander313.Wilken
