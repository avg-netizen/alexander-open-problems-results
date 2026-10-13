import Alexander313.Wilken.HereditaryGlobalAdditiveTracking

/-!
# Exact original global tracking source clauses

Every printed finite-stage Definition3.24 clause conversely runs the actual
global producer. The large branch forces strict separation from its genuine
epsilon endpoint; the source clauses do not supply branch flags. This is
execution fidelity and mathematical termination, not yet a global TS/evaluation
or order-isomorphism theorem. Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.GlobalAdditiveTracking

open Source Return

theorem endpoint_epsilon (alpha : Nat) (hl : level alpha ≠ 0) :
    Ordinal.omega0 ^ unionInterpretation (endpointCode (level alpha)) =
      unionInterpretation (endpointCode (level alpha)) := by
  cases hm : level alpha with
  | zero => exact False.elim (hl hm)
  | succ s => simpa only [PublicEpsilonSourceDictionary.endpointCode_value, hm] using
      finiteBase_succ_omegaPower_eq_self s

theorem endpoint_lt_cutoff (alpha : Nat) (hl : level alpha ≠ 0) :
    unionInterpretation (endpointCode (level alpha)) <
      unionInterpretation (endpointCode (level alpha)) ^ Ordinal.omega0 :=
  Ordinal.left_lt_opow (EpsilonOffsets.epsilon_one_lt (endpoint_epsilon alpha hl)) Ordinal.one_lt_omega0

theorem endpoint_false_of_strict (alpha : Nat) (hi : inputCheck alpha = true)
    (hlt : unionInterpretation (endpointCode (level alpha)) < unionInterpretation alpha) :
    endpointCheck alpha = false := by
  cases he : endpointCheck alpha with
  | false => rfl
  | true =>
    have hv := (endpointCheck_exact alpha hi).mp he
    have heq : unionInterpretation alpha = unionInterpretation (endpointCode (level alpha)) :=
      hv.trans (PublicEpsilonSourceDictionary.endpointCode_value _).symm
    exact False.elim ((ne_of_gt hlt) heq)

/-- Each actual source clause executes the producer at its real semantic
branch. Relative words and quotients are genuine independent executions. -/
theorem clauses_execute (alpha : Nat) (codes : List Nat) (hi : inputCheck alpha = true)
    (hc : SourceClauses alpha codes) : codes ∈ execute alpha := by
  rcases hc with ⟨hl, ho⟩ | ⟨hl, he, rfl⟩ |
    ⟨hl, hlt, hb, quotient, hq, rfl⟩ | ⟨hl, hb, tail, ht, rfl⟩
  · have hz : (level alpha == 0) = true := beq_iff_eq.mpr hl
    simpa only [execute, hi, hz, Bool.cond_true] using ho
  · have hz : (level alpha == 0) = false := by
      cases hz : level alpha == 0 with
      | false => rfl
      | true => exact False.elim (hl (beq_iff_eq.mp hz))
    have hp : endpointCheck alpha = true := (endpointCheck_exact alpha hi).mpr he
    simp only [execute, hi, hz, hp, Bool.cond_true, Bool.cond_false]
    exact Part.mem_some _
  · have hz : (level alpha == 0) = false := by
      cases hz : level alpha == 0 with
      | false => rfl
      | true => exact False.elim (hl (beq_iff_eq.mp hz))
    have hp := endpoint_false_of_strict alpha hi hlt
    have hs : smallCheck alpha = true := (smallCheck_exact alpha hi).mpr
      (by rw [← endpoint_context alpha hl]; exact hb)
    simpa only [execute, hi, hz, hp, hs, Bool.cond_true, Bool.cond_false] using
      Part.mem_map (fun out => baseWord (level alpha) ++ [out]) hq
  · have hz : (level alpha == 0) = false := by
      cases hz : level alpha == 0 with
      | false => rfl
      | true => exact False.elim (hl (beq_iff_eq.mp hz))
    have hp := endpoint_false_of_strict alpha hi ((endpoint_lt_cutoff alpha hl).trans_le hb)
    have hs : smallCheck alpha = false := by
      cases hs : smallCheck alpha with
      | false => rfl
      | true =>
        have hv := (smallCheck_exact alpha hi).mp hs
        rw [← endpoint_context alpha hl] at hv
        exact False.elim ((not_lt_of_ge hb) hv)
    simpa only [execute, hi, hz, hp, hs, Bool.cond_true, Bool.cond_false] using
      Part.mem_map (fun word => baseWord (level alpha) ++ word) ht

theorem execute_iff_clauses (alpha : Nat) (codes : List Nat) : codes ∈ execute alpha ↔
    inputCheck alpha = true ∧ SourceClauses alpha codes :=
  ⟨execute_clauses alpha codes, fun h => clauses_execute alpha codes h.1 h.2⟩

/-- The complete printed source assignment has an actual finite executing
word on every canonical positive additive-principal input. -/
theorem source_clauses_exist (alpha : Nat) (hi : inputCheck alpha = true) :
    ∃ codes, SourceClauses alpha codes ∧ codes ∈ execute alpha ∧
      (∀ c ∈ codes, Canonical.check c = true) := by
  obtain ⟨codes, ho⟩ := execute_returns alpha hi
  exact ⟨codes, (execute_clauses alpha codes ho).2, ho, execute_canonical alpha codes ho⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.GlobalAdditiveTracking
