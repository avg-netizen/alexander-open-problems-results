import Alexander313.Wilken.DirectLimitComparison

/-!
# Actual low-input principal arithmetic

The least larger additive principal ordinal is constructed independently by a
minimum, with a concrete regular-cardinal witness. Restricted hull induction
characterizes the source minimum below the next cardinal. Its successor-input
value is exactly that independent principal successor of its preceding value.

This derives a genuine arithmetic clause from the actual source construction.
It does not identify the full non-epsilon enumeration in Lemma 2.4, prove
epsilon status of the global bases, or provide a general ordinal-code algorithm.
All proof terms await external compilation.
-/

namespace Alexander313.Wilken

open Order

private theorem larger_principal_exists (α : Ordinal.{0}) :
    ∃ β : Ordinal.{0}, α < β ∧ Ordinal.IsPrincipal (· + ·) β :=
  ⟨omegaSequence α 1, omegaSequence_base_lt α, omegaSequence_add_closed α 0⟩

noncomputable def nextAdditivePrincipal (α : Ordinal.{0}) : Ordinal.{0} :=
  sInf {β : Ordinal.{0} | α < β ∧ Ordinal.IsPrincipal (· + ·) β}

theorem nextAdditivePrincipal_spec (α : Ordinal.{0}) :
    α < nextAdditivePrincipal α ∧
      Ordinal.IsPrincipal (· + ·) (nextAdditivePrincipal α) :=
  csInf_mem (larger_principal_exists α)

theorem nextAdditivePrincipal_le (α β : Ordinal.{0}) (hαβ : α < β)
    (hβ : Ordinal.IsPrincipal (· + ·) β) : nextAdditivePrincipal α ≤ β :=
  csInf_le' ⟨hαβ, hβ⟩

theorem nextAdditivePrincipal_le_iff (α β : Ordinal.{0})
    (hβ : Ordinal.IsPrincipal (· + ·) β) :
    nextAdditivePrincipal α ≤ β ↔ α < β :=
  ⟨fun h => (nextAdditivePrincipal_spec α).1.trans_le h,
    fun h => nextAdditivePrincipal_le α β h hβ⟩

theorem nextAdditivePrincipal_mono : Monotone nextAdditivePrincipal := by
  intro α β hαβ
  exact nextAdditivePrincipal_le α (nextAdditivePrincipal β)
    (hαβ.trans_lt (nextAdditivePrincipal_spec β).1)
    (nextAdditivePrincipal_spec β).2

/-- In a low hull, higher calls cannot be small. Bounding every local
call therefore bounds the whole small hull by an actual principal ordinal. -/
theorem source_low_hull_below_principal (τ : Ordinal.{0}) (n m : Nat)
    (α β : Ordinal.{0}) (hbase : omegaSequence τ m ≤ β)
    (hβ : Ordinal.IsPrincipal (· + ·) β)
    («local» : ∀ γ < α, sourceFiniteCollapse τ n m γ < β)
    {ξ : Ordinal.{0}}
    (hξ : Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α β ξ)
    (hsmall : ξ < omegaSequence τ (m + 1)) : ξ < β := by
  revert hsmall
  induction hξ with
  | below_base h => intro _; exact h.trans_le hbase
  | below_parameter h => intro _; exact h
  | @add a b ha hb iha ihb =>
    intro hsmall
    exact hβ (iha (le_self_add.trans_lt hsmall))
      (ihb (le_add_self.trans_lt hsmall))
  | @higher k γ hmk hkn hsort hγ ih =>
    intro hsmall
    have hlarge : omegaSequence τ (m + 1) ≤ sourceFiniteCollapse τ n k γ :=
      ((omegaSequence_strictMono τ).monotone (Nat.succ_le_of_lt hmk)).trans
        (sourceFiniteCollapse_bounds τ n k hkn γ).1
    exact False.elim (hsmall.not_ge hlarge)
  | @«local» γ hγα hγ ih => intro _; exact «local» γ hγα

/-- Exact low-source minimum test against an actual principal bound.
The finite candidate and all its local-call bounds are derived. -/
theorem sourceFiniteCollapse_low_le_iff_principal (τ : Ordinal.{0})
    (n m : Nat) (hm : m < n) (α β : Ordinal.{0})
    (hα : α < omegaSequence τ (m + 1))
    (hβsmall : β < omegaSequence τ (m + 1))
    (hβ : Ordinal.IsPrincipal (· + ·) β) :
    sourceFiniteCollapse τ n m α ≤ β ↔
      omegaSequence τ m ≤ β ∧ α < β ∧
        ∀ γ < α, sourceFiniteCollapse τ n m γ < β := by
  constructor
  · intro h
    refine ⟨(sourceFiniteCollapse_bounds τ n m hm α).1.trans h,
      (sourceFiniteCollapse_low_argument_lt τ n m hm hα).trans_le h, ?_⟩
    intro γ hγα
    exact (sourceFiniteCollapse_strictMono_low τ n m hm hγα hα).trans_le h
  · rintro ⟨hbase, hαβ, hlocal⟩
    have hc : CollapseCandidate (omegaSequence τ) (sourceFiniteCollapse τ n)
        n m α β :=
      ⟨hβsmall, fun ξ hξ hsmall =>
        source_low_hull_below_principal τ n m α β hbase hβ hlocal hξ hsmall,
        .below_parameter hαβ⟩
    exact finiteCollapse_minimal hm hc

/-- Source successor inputs enumerate the next additive principal value.
Only the low input sort is needed; no enumeration package is supplied. -/
theorem sourceFiniteCollapse_succ_eq_nextAdditivePrincipal (τ : Ordinal.{0})
    (n m : Nat) (hm : m < n) (α : Ordinal.{0})
    (hα : α < omegaSequence τ (m + 1)) :
    sourceFiniteCollapse τ n m (α + 1) =
      nextAdditivePrincipal (sourceFiniteCollapse τ n m α) := by
  have hsucc : α + 1 < omegaSequence τ (m + 1) :=
    (omegaSequence_isSuccLimit τ m).add_one_lt hα
  have hproper := sourceFiniteCollapse_proper_notation τ n m hm (α + 1)
    (hsucc.trans (omegaSequence_step τ (m + 1)))
    (sourceNotation_next_of_low τ n m hm hsucc)
  let δ := nextAdditivePrincipal (sourceFiniteCollapse τ n m α)
  have hδ := nextAdditivePrincipal_spec (sourceFiniteCollapse τ n m α)
  have hδle : δ ≤ sourceFiniteCollapse τ n m (α + 1) :=
    nextAdditivePrincipal_le _ _
      (sourceFiniteCollapse_strictMono_low τ n m hm (lt_add_one α) hsucc)
      (sourceFiniteCollapse_add_closed τ n m hm (α + 1))
  have hδsmall : δ < omegaSequence τ (m + 1) := hδle.trans_lt hproper
  have hbaseδ : omegaSequence τ m ≤ δ :=
    (sourceFiniteCollapse_bounds τ n m hm α).1.trans hδ.1.le
  have hαδ : α < δ :=
    (sourceFiniteCollapse_low_argument_lt τ n m hm hα).trans hδ.1
  have hαsuccδ : α + 1 < δ := by
    by_cases hαzero : α = 0
    · subst α
      have hzero : 0 < sourceFiniteCollapse τ n m 0 :=
        sourceFiniteCollapse_low_argument_lt τ n m hm hα
      have hone : (1 : Ordinal.{0}) ≤ sourceFiniteCollapse τ n m 0 := by
        simpa only [zero_add] using add_one_le_of_lt hzero
      simpa only [zero_add] using hone.trans_lt hδ.1
    · have honeα : (1 : Ordinal.{0}) ≤ α := by
        simpa only [zero_add] using
          add_one_le_of_lt (lt_of_le_of_ne ((zero_le : 0 ≤ α)) (Ne.symm hαzero))
      exact hδ.2 hαδ (honeα.trans_lt hαδ)
  apply le_antisymm
  · apply (sourceFiniteCollapse_low_le_iff_principal τ n m hm (α + 1) δ
      hsucc hδsmall hδ.2).mpr
    refine ⟨hbaseδ, hαsuccδ, ?_⟩
    intro γ hγ
    have hγα : γ ≤ α := lt_add_one_iff.mp hγ
    rcases hγα.eq_or_lt with hγα | hγα
    · simpa only [hγα] using hδ.1
    · exact (sourceFiniteCollapse_strictMono_low τ n m hm hγα hα).trans hδ.1
  · exact hδle

end Alexander313.Wilken
