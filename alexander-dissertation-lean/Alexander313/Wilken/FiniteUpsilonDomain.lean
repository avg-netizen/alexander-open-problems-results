import Alexander313.Wilken.TerminalPrincipalArithmetic
import Alexander313.Effective.HereditaryUnionProgram

/-!
# The actual zero-started finite/omega υ domain

Definition 1.5 has υ₀=0, the source sets T₀:=T₁=T for convenience and
explicitly uses υ₁=1∞. Zero is the indexing endpoint; the first term grammar
has base one. We implement this
convention by taking the low actual global grammar at max(1,τ), and define
its extension independently as the supremum of that literal grammar.

The source initial-segment theorem proves this extension equals the previously
constructed global boundary. Thus the zero-started finite sequence agrees
with finiteBase at every positive index, and their omega suprema agree. The
actual uniform hereditary recognizer consequently has exactly this ordinal
image. Successor bases have not yet been proved to belong to the source's
epsilon-or-one parameter class: this is alignment of the literal finite/omega
closure definitions, not a completed source-base-class interpretation. This
does not prove epsilon status, canonical syntax, source tracking or
resemblance/reflection. No transfinite segment above omega is constructed.
All proof terms await external compilation and source-correspondence review.
-/

namespace Alexander313.Wilken

noncomputable def sourceStartingBase (τ : Ordinal.{0}) : Ordinal.{0} := max 1 τ

theorem sourceStartingBase_pos (τ : Ordinal.{0}) : 0 < sourceStartingBase τ :=
  zero_lt_one.trans_le (le_max_left 1 τ)

@[simp] theorem sourceStartingBase_zero : sourceStartingBase 0 = 1 := by
  simp [sourceStartingBase]

theorem sourceStartingBase_of_pos (τ : Ordinal.{0}) (hτ : 0 < τ) :
    sourceStartingBase τ = τ := by
  have hone : (1 : Ordinal.{0}) ≤ τ := by
    simpa only [zero_add] using Order.add_one_le_of_lt hτ
  exact max_eq_right hone

/-- The actual low source term grammar, rather than an alias for a boundary. -/
noncomputable def sourceBaseExtension (τ : Ordinal.{0}) : Ordinal.{0} :=
  sSup {ξ : Ordinal.{0} | GlobalNotation (sourceStartingBase τ) 0 ξ ∧
    ξ < omegaSequence (sourceStartingBase τ) 1}

theorem sourceBaseExtension_eq_globalBoundary (τ : Ordinal.{0}) :
    sourceBaseExtension τ = globalBoundary (sourceStartingBase τ) 0 := by
  let σ := sourceStartingBase τ
  have hσ : 0 < σ := sourceStartingBase_pos τ
  let S : Set Ordinal.{0} := {ξ | GlobalNotation σ 0 ξ ∧ ξ < omegaSequence σ 1}
  have hS : S.Nonempty :=
    ⟨0, .parameter (by simpa only [omegaSequence_zero] using hσ),
      (omegaSequence_isSuccLimit σ 0).bot_lt⟩
  have hbdd : BddAbove S := ⟨omegaSequence σ 1, fun _ h => h.2.le⟩
  change sSup S = globalBoundary σ 0
  apply le_antisymm
  · exact csSup_le hS (fun ξ hξ =>
      ((globalNotation_low_iff_lt_boundary σ hσ 0 ξ).mp hξ).le)
  · unfold globalBoundary
    apply Ordinal.iSup_le
    intro j
    change finiteBoundary σ (0 + 1 + j) 0 ≤ sSup S
    unfold finiteBoundary
    simp only [if_pos (Nat.zero_le (0 + 1 + j))]
    apply Ordinal.iSup_le
    intro k
    apply le_csSup hbdd
    exact ⟨sourceNotation_to_globalNotation σ hσ (0 + 1 + j) 0 (by omega)
      (finiteApproximant_lower_notation σ hσ (0 + 1 + j) 0 (by omega) 0 le_rfl k),
      finiteApproximant_lt_cardinal σ hσ (0 + 1 + j) 0 (by omega) k⟩

theorem sourceBaseExtension_eq_of_pos (τ : Ordinal.{0}) (hτ : 0 < τ) :
    sourceBaseExtension τ = globalBoundary τ 0 := by
  rw [sourceBaseExtension_eq_globalBoundary, sourceStartingBase_of_pos τ hτ]

@[simp] theorem sourceBaseExtension_zero : sourceBaseExtension 0 = globalBoundary 1 0 := by
  rw [sourceBaseExtension_eq_globalBoundary, sourceStartingBase_zero]

theorem sourceBaseExtension_gt (τ : Ordinal.{0}) : τ < sourceBaseExtension τ := by
  rw [sourceBaseExtension_eq_globalBoundary]
  exact (le_max_right 1 τ).trans_lt
    (by simpa only [omegaSequence_zero, sourceStartingBase] using
      globalBoundary_base_lt (sourceStartingBase τ) (sourceStartingBase_pos τ) 0)

noncomputable def sourceUpsilonFinite : Nat → Ordinal.{0}
  | 0 => 0
  | r + 1 => sourceBaseExtension (sourceUpsilonFinite r)

@[simp] theorem sourceUpsilonFinite_zero : sourceUpsilonFinite 0 = 0 := rfl

@[simp] theorem sourceUpsilonFinite_succ (r : Nat) :
    sourceUpsilonFinite (r + 1) = sourceBaseExtension (sourceUpsilonFinite r) := rfl

theorem sourceUpsilonFinite_one : sourceUpsilonFinite 1 = globalBoundary 1 0 := by
  simp only [sourceUpsilonFinite, sourceBaseExtension_zero]

theorem sourceUpsilonFinite_step (r : Nat) :
    sourceUpsilonFinite r < sourceUpsilonFinite (r + 1) :=
  sourceBaseExtension_gt _

theorem sourceUpsilonFinite_strictMono : StrictMono sourceUpsilonFinite :=
  strictMono_nat_of_lt_succ sourceUpsilonFinite_step

theorem sourceUpsilonFinite_pos (r : Nat) : 0 < sourceUpsilonFinite (r + 1) := by
  simpa only [sourceUpsilonFinite_zero] using
    sourceUpsilonFinite_strictMono (Nat.zero_lt_succ r)

/-- The literal zero-start source sequence and the actual one-start base
sequence have the same values at every positive index. -/
theorem sourceUpsilonFinite_eq_finiteBase_succ (r : Nat) :
    sourceUpsilonFinite (r + 1) = RelativeTerm.Hereditary.finiteBase (r + 1) := by
  induction r with
  | zero => exact sourceUpsilonFinite_one
  | succ r ih =>
    rw [sourceUpsilonFinite_succ, ih,
      sourceBaseExtension_eq_of_pos _ (RelativeTerm.Hereditary.finiteBase_pos (r + 1))]
    rfl

noncomputable def sourceUpsilonOmega : Ordinal.{0} := ⨆ r, sourceUpsilonFinite r

theorem sourceUpsilonOmega_eq_finiteBaseLimit :
    sourceUpsilonOmega = RelativeTerm.Hereditary.finiteBaseLimit := by
  apply le_antisymm
  · apply Ordinal.iSup_le
    intro r
    cases r with
    | zero => exact zero_le
    | succ r =>
      rw [sourceUpsilonFinite_eq_finiteBase_succ]
      exact Ordinal.le_iSup RelativeTerm.Hereditary.finiteBase (r + 1)
  · apply Ordinal.iSup_le
    intro r
    cases r with
    | zero =>
      have h : RelativeTerm.Hereditary.finiteBase 0 ≤ sourceUpsilonFinite 1 := by
        rw [sourceUpsilonFinite_eq_finiteBase_succ 0]
        exact (RelativeTerm.Hereditary.finiteBase_step 0).le
      exact h.trans (Ordinal.le_iSup sourceUpsilonFinite 1)
    | succ r =>
      rw [← sourceUpsilonFinite_eq_finiteBase_succ]
      exact Ordinal.le_iSup sourceUpsilonFinite (r + 1)

theorem sourceUpsilonFinite_lt_omega (r : Nat) : sourceUpsilonFinite r < sourceUpsilonOmega :=
  (sourceUpsilonFinite_step r).trans_le (Ordinal.le_iSup sourceUpsilonFinite (r + 1))

/-- Exact ordinal image of the genuine uniform executing recognizer. -/
theorem sourceUpsilonOmega_iff_recognizer (ξ : Ordinal.{0}) :
    ξ < sourceUpsilonOmega ↔ ∃ query : Nat,
      HereditaryUnionProgram.recognizer.domain query ∧
        RelativeTerm.Hereditary.unionInterpretation query = ξ := by
  rw [sourceUpsilonOmega_eq_finiteBaseLimit]
  exact HereditaryUnionProgram.recognizer_covers ξ

end Alexander313.Wilken
