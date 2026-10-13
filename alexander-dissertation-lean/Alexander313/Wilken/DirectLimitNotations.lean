import Alexander313.Wilken.DirectLimitFunctions

/-!
# Actual direct-limit notation grammar and finite union

The literal source grammar has arbitrary finite collapsing levels and
only the source cardinal-sort restriction on each argument. Actual
finite witnesses prove that every call lies in the global function's
domain, so the auxiliary total extension never contributes. Conversely,
every finite source term denotes the same ordinal in this grammar.
The finite union and low initial-segment identity are proved, rather
than assumed. Semantic, noncomputable functions; uncompiled proof terms.
-/

namespace Alexander313.Wilken

/-- Tₘ from Definition 2.17, with no assumed finite-fragment witness. -/
inductive GlobalNotation (τ : Ordinal.{0}) (m : Nat) : Ordinal.{0} → Prop where
  | parameter {ξ} : ξ < omegaSequence τ m → GlobalNotation τ m ξ
  | add {ξ η} : GlobalNotation τ m ξ → GlobalNotation τ m η → GlobalNotation τ m (ξ + η)
  | collapse {k ξ} : m ≤ k → ξ < omegaSequence τ (k + 2) →
      GlobalNotation τ m ξ → GlobalNotation τ m (globalCollapse τ k ξ)

theorem sourceNotation_to_globalNotation (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) {ξ : Ordinal.{0}} (hξ : sourceNotation τ n m ξ) :
    GlobalNotation τ m ξ := by
  rw [sourceNotation, if_pos hm] at hξ
  induction hξ with
  | parameter h => exact .parameter h
  | add _ _ iha ihb => exact .add iha ihb
  | @collapse k η hmk hkn hsort hη ih =>
    have hηNotation : sourceNotation τ n m η := by
      simpa only [sourceNotation, if_pos hm] using hη
    have hbound := source_finite_collapse_argument_lt_boundary τ hτ n m k hmk hkn
      hηNotation hsort
    rw [← globalCollapse_finite_agreement τ hτ n k hkn η hbound]
    exact .collapse hmk hsort ih

/-- Every actual global derivation has a finite source witness. -/
theorem globalNotation_finite_witness (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) {ξ : Ordinal.{0}} (hξ : GlobalNotation τ m ξ) :
    ∃ n, m < n ∧ sourceNotation τ n m ξ := by
  induction hξ with
  | parameter h =>
    refine ⟨m + 1, Nat.lt_succ_self m, ?_⟩
    rw [sourceNotation, if_pos (Nat.lt_succ_self m)]
    exact .parameter h
  | @add a b ha hb iha ihb =>
    obtain ⟨n, hmn, han⟩ := iha
    obtain ⟨n', hmn', hbn'⟩ := ihb
    let p := max n n'
    have hmp : m < p := hmn.trans_le (le_max_left n n')
    have hap := sourceNotation_fragment_mono τ hτ n m p hmn.le (le_max_left n n') han
    have hbp := sourceNotation_fragment_mono τ hτ n' m p hmn'.le (le_max_right n n') hbn'
    refine ⟨p, hmp, ?_⟩
    rw [sourceNotation, if_pos hmp] at hap hbp ⊢
    exact .add hap hbp
  | @collapse k η hmk hsort hη ih =>
    obtain ⟨n, hmn, hηn⟩ := ih
    let p := max n (k + 1)
    have hkp : k < p := (Nat.lt_succ_self k).trans_le (le_max_right n (k + 1))
    have hmp : m < p := hmk.trans_lt hkp
    have hηp := sourceNotation_fragment_mono τ hτ n m p hmn.le (le_max_left n (k + 1)) hηn
    have hbound := source_finite_collapse_argument_lt_boundary τ hτ p m k hmk hkp hηp hsort
    refine ⟨p, hmp, ?_⟩
    rw [globalCollapse_finite_agreement τ hτ p k hkp η hbound,
      sourceNotation, if_pos hmp]
    exact .collapse hmk hkp hsort (by simpa only [sourceNotation, if_pos hmp] using hηp)

/-- The finite union clause of Theorem 2.18. -/
theorem globalNotation_iff_finite (τ : Ordinal.{0}) (hτ : 0 < τ) (m : Nat) (ξ : Ordinal.{0}) :
    GlobalNotation τ m ξ ↔ ∃ n, m < n ∧ sourceNotation τ n m ξ :=
  ⟨globalNotation_finite_witness τ hτ m,
    fun ⟨n, hm, hξ⟩ => sourceNotation_to_globalNotation τ hτ n m hm hξ⟩

/-- Every actual sorted argument of the global grammar belongs to the
source domain θₖ₊₁. No extra domain premise is imposed on its constructor. -/
theorem globalNotation_sorted_lt_boundary (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m k : Nat) (hmk : m ≤ k) {η : Ordinal.{0}}
    (hη : GlobalNotation τ m η) (hsort : η < omegaSequence τ (k + 2)) :
    η < globalBoundary τ (k + 1) := by
  obtain ⟨n, hmn, hηn⟩ := globalNotation_finite_witness τ hτ m hη
  let p := max n (k + 1)
  have hkp : k < p := (Nat.lt_succ_self k).trans_le (le_max_right n (k + 1))
  have hηp := sourceNotation_fragment_mono τ hτ n m p hmn.le (le_max_left n (k + 1)) hηn
  exact (source_finite_collapse_argument_lt_boundary τ hτ p m k hmk hkp hηp hsort).trans
    (finiteBoundary_lt_globalBoundary τ hτ p (by omega) (k + 1) (by omega))

/-- The low initial-segment identity in Theorem 2.18. -/
theorem globalNotation_low_iff_lt_boundary (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) (ξ : Ordinal.{0}) :
    (GlobalNotation τ m ξ ∧ ξ < omegaSequence τ (m + 1)) ↔ ξ < globalBoundary τ m := by
  constructor
  · rintro ⟨hξ, hsmall⟩
    obtain ⟨n, hm, hn⟩ := globalNotation_finite_witness τ hτ m hξ
    exact ((source_finite_notation_low_iff_lt_boundary τ hτ n m hm ξ).1 ⟨hn, hsmall⟩).trans
      (finiteBoundary_lt_globalBoundary τ hτ n (by omega) m hm.le)
  · intro hξ
    obtain ⟨j, hj⟩ := (globalBoundary_cofinal τ m ξ).1 hξ
    have hm : m < m + 1 + j := by omega
    obtain ⟨hnotation, hsmall⟩ :=
      (source_finite_notation_low_iff_lt_boundary τ hτ (m + 1 + j) m hm ξ).2 hj
    exact ⟨sourceNotation_to_globalNotation τ hτ (m + 1 + j) m hm hnotation, hsmall⟩

/-- The first supremum identity in Corollary 2.19, proved using actual
cofinal finite approximants in every lower grammar. -/
theorem globalNotation_sorted_sup (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m k : Nat) (hmk : m ≤ k) :
    sSup {ξ : Ordinal.{0} | GlobalNotation τ m ξ ∧ ξ < omegaSequence τ (k + 2)} =
      globalBoundary τ (k + 1) := by
  let S : Set Ordinal.{0} := {ξ | GlobalNotation τ m ξ ∧ ξ < omegaSequence τ (k + 2)}
  have hbase : 0 < omegaSequence τ m :=
    hτ.trans_le ((omegaSequence_strictMono τ).monotone (Nat.zero_le m))
  have hS : S.Nonempty := ⟨0, GlobalNotation.parameter hbase,
    (omegaSequence_isSuccLimit τ (k + 1)).bot_lt⟩
  have hbdd : BddAbove S := ⟨omegaSequence τ (k + 2), fun _ h => h.2.le⟩
  apply le_antisymm
  · exact csSup_le hS (fun ξ hξ => (globalNotation_sorted_lt_boundary τ hτ m k hmk hξ.1 hξ.2).le)
  · unfold globalBoundary
    apply Ordinal.iSup_le
    intro j
    have hn : k + 1 < k + 1 + 1 + j := by omega
    rw [finiteBoundary, if_pos hn.le]
    apply Ordinal.iSup_le
    intro i
    apply le_csSup hbdd
    refine ⟨?_, finiteApproximant_lt_cardinal τ hτ (k + 1 + 1 + j) (k + 1) hn i⟩
    exact sourceNotation_to_globalNotation τ hτ (k + 1 + 1 + j) m (by omega)
      (finiteApproximant_lower_notation τ hτ (k + 1 + 1 + j) (k + 1) hn m (by omega) i)

end Alexander313.Wilken
