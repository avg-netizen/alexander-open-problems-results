import Alexander313.Wilken.InitialHulls

/-!
# Actual coverage at the terminal finite collapsing level

The terminal branch of Wilken Definition 2.12 is iteration of ϑⁿₙ₋₁
from zero. We construct this sequence and prove that its supremum is
exactly Tⁿₙ₋₁. This is the terminal case of Theorem 2.13, including
cofinality, the proper cardinal bound and closure under the terminal
collapsing function. No coverage theorem is assumed.

Ordinal universe zero is inherited from the actual initial-hull theorem.
The hypothesis 0<τ covers the source bases; no effective syntax or
lower-level coverage is asserted. All proofs await external compilation.
-/

namespace Alexander313.Wilken

/-- Every low ordinal is in the actual next-level argument domain. -/
theorem sourceNotation_next_of_low (τ : Ordinal) (n m : Nat) (hm : m < n)
    {α : Ordinal} (hα : α < omegaSequence τ (m + 1)) :
    sourceNotation τ n (m + 1) α :=
  (source_nextNotation_iff_hull τ n m hm α).2 (.below_parameter hα)

/-- On low arguments the source minimum strictly exceeds its argument.
This uses membership in its own hull, rather than an assumed monotonicity
or arithmetic description of the collapsing function. -/
theorem sourceFiniteCollapse_low_argument_lt (τ : Ordinal) (n m : Nat)
    (hm : m < n) {α : Ordinal} (hα : α < omegaSequence τ (m + 1)) :
    α < sourceFiniteCollapse τ n m α := by
  have hnotation := sourceNotation_next_of_low τ n m hm hα
  have hsort := hα.trans (omegaSequence_step τ (m + 1))
  have hin := sourceFiniteCollapse_argument_notation τ n m hm α hsort hnotation
  exact (finiteCollapse_hull_initial hm α α).1 ⟨hin, hα⟩

/-- The actual collapsing function is strictly increasing on its low
argument segment. General collapsing arguments need the star test. -/
theorem sourceFiniteCollapse_strictMono_low (τ : Ordinal) (n m : Nat)
    (hm : m < n) {α γ : Ordinal} (hαγ : α < γ)
    (hγ : γ < omegaSequence τ (m + 1)) :
    sourceFiniteCollapse τ n m α < sourceFiniteCollapse τ n m γ := by
  have hα := hαγ.trans hγ
  have hproper := sourceFiniteCollapse_proper_notation τ n m hm α
    (hα.trans (omegaSequence_step τ (m + 1)))
    (sourceNotation_next_of_low τ n m hm hα)
  have harg : α < sourceFiniteCollapse τ n m γ :=
    hαγ.trans (sourceFiniteCollapse_low_argument_lt τ n m hm hγ)
  exact (finiteCollapse_hull_initial hm γ _).1
    ⟨.«local» hαγ (.below_parameter harg), hproper⟩

/-- Above level zero the base is an actual infinite initial ordinal, so
the zero value needs no closure or positivity assumption on τ. -/
theorem sourceFiniteCollapse_zero_positiveLevel (τ : Ordinal) (n m : Nat)
    (hm : m < n) (hmpos : 0 < m) :
    sourceFiniteCollapse τ n m 0 = omegaSequence τ m := by
  have hbase : Ordinal.IsPrincipal (· + ·) (omegaSequence τ m) := by
    cases m with
    | zero => omega
    | succ m => exact omegaSequence_add_closed τ m
  have hpositive : 0 < omegaSequence τ m := by
    cases m with
    | zero => omega
    | succ m => exact (omegaSequence_isSuccLimit τ m).bot_lt
  have hc : CollapseCandidate (omegaSequence τ) (sourceFiniteCollapse τ n)
      n m 0 (omegaSequence τ m) :=
    ⟨omegaSequence_step τ m,
      fun ξ hξ hsort => source_hull_zero_small τ n m hbase hξ hsort,
      .below_base hpositive⟩
  exact le_antisymm (finiteCollapse_minimal hm hc)
    (sourceFiniteCollapse_bounds τ n m hm 0).1

/-- The literal Θ^{m+1}_m(k) in the terminal branch of Definition 2.12. -/
noncomputable def terminalApproximant (τ : Ordinal.{0}) (m : Nat) : Nat → Ordinal.{0}
  | 0 => 0
  | k + 1 => sourceFiniteCollapse τ (m + 1) m (terminalApproximant τ m k)

theorem terminalApproximant_zero (τ : Ordinal.{0}) (m : Nat) :
    terminalApproximant τ m 0 = 0 := rfl

theorem terminalApproximant_succ (τ : Ordinal.{0}) (m k : Nat) :
    terminalApproximant τ m (k + 1) =
      sourceFiniteCollapse τ (m + 1) m (terminalApproximant τ m k) := rfl

theorem terminalApproximant_lt_cardinal (τ : Ordinal.{0}) (m k : Nat) :
    terminalApproximant τ m k < omegaSequence τ (m + 1) := by
  induction k with
  | zero => exact (omegaSequence_isSuccLimit τ m).bot_lt
  | succ k ih =>
    exact sourceFiniteCollapse_proper_notation τ (m + 1) m (Nat.lt_succ_self m) _
      (ih.trans (omegaSequence_step τ (m + 1)))
      (sourceNotation_next_of_low τ (m + 1) m (Nat.lt_succ_self m) ih)

theorem terminalApproximant_strictMono (τ : Ordinal.{0}) (m : Nat) :
    StrictMono (terminalApproximant τ m) := by
  apply strictMono_nat_of_lt_succ
  intro k
  exact sourceFiniteCollapse_low_argument_lt τ (m + 1) m (Nat.lt_succ_self m)
    (terminalApproximant_lt_cardinal τ m k)

theorem terminalApproximant_succ_principal (τ : Ordinal.{0}) (m k : Nat) :
    Ordinal.IsPrincipal (· + ·) (terminalApproximant τ m (k + 1)) :=
  sourceFiniteCollapse_add_closed τ (m + 1) m (Nat.lt_succ_self m) _

theorem terminalApproximant_notation (τ : Ordinal.{0}) (hτ : 0 < τ) (m k : Nat) :
    sourceNotation τ (m + 1) m (terminalApproximant τ m k) := by
  rw [sourceNotation, if_pos (Nat.lt_succ_self m)]
  have hbase : 0 < omegaSequence τ m :=
    hτ.trans_le ((omegaSequence_strictMono τ).monotone (Nat.zero_le m))
  induction k with
  | zero => exact .parameter hbase
  | succ k ih =>
    exact .collapse le_rfl (Nat.lt_succ_self m)
      ((terminalApproximant_lt_cardinal τ m k).trans (omegaSequence_step τ (m + 1))) ih

/-- The literal terminal θ^{m+1}_m in Definition 2.12. -/
noncomputable def terminalBoundary (τ : Ordinal.{0}) (m : Nat) : Ordinal.{0} :=
  ⨆ k, terminalApproximant τ m k

theorem terminalBoundary_lt_cardinal (τ : Ordinal.{0}) (m : Nat) :
    terminalBoundary τ m < omegaSequence τ (m + 1) := by
  apply Ordinal.lift_iSup_lt_of_lt_cof
  · simpa only [Cardinal.mk_nat, Cardinal.lift_aleph0, Ordinal.lift_id, omegaSequence,
      (omegaSequence_regular τ m).cof_ord] using
        (levelCardinal_infinite τ m).trans_lt (levelCardinal_step τ m)
  · exact terminalApproximant_lt_cardinal τ m

theorem terminalApproximant_lt_boundary (τ : Ordinal.{0}) (m k : Nat) :
    terminalApproximant τ m k < terminalBoundary τ m :=
  (terminalApproximant_strictMono τ m (Nat.lt_succ_self k)).trans_le
    (Ordinal.le_iSup (terminalApproximant τ m) (k + 1))

theorem terminalBoundary_cofinal (τ : Ordinal.{0}) (m : Nat) (ξ : Ordinal.{0}) :
    ξ < terminalBoundary τ m ↔ ∃ k, ξ < terminalApproximant τ m k :=
  Ordinal.lt_iSup_iff

theorem terminalBoundary_base_lt (τ : Ordinal.{0}) (m : Nat) :
    omegaSequence τ m < terminalBoundary τ m :=
  (sourceFiniteCollapse_bounds τ (m + 1) m (Nat.lt_succ_self m) 0).1.trans_lt
    (terminalApproximant_lt_boundary τ m 1)

/-- The inequality for the duplicated terminal endpoint in the source
convention θⁿₙ=θⁿₙ₋₁, when passing from fragment n to fragment n+1. -/
theorem terminalBoundary_lt_next_terminalBoundary (τ : Ordinal.{0}) (m : Nat) :
    terminalBoundary τ m < terminalBoundary τ (m + 1) :=
  (terminalBoundary_lt_cardinal τ m).trans (terminalBoundary_base_lt τ (m + 1))

theorem terminalBoundary_add_closed (τ : Ordinal.{0}) (m : Nat) :
    Ordinal.IsPrincipal (· + ·) (terminalBoundary τ m) := by
  intro ξ η hξ hη
  obtain ⟨i, hi⟩ := (terminalBoundary_cofinal τ m ξ).1 hξ
  obtain ⟨j, hj⟩ := (terminalBoundary_cofinal τ m η).1 hη
  have hξ' : ξ < terminalApproximant τ m (max i j + 1) :=
    hi.trans_le ((terminalApproximant_strictMono τ m).monotone
      ((le_max_left i j).trans (Nat.le_succ _)))
  have hη' : η < terminalApproximant τ m (max i j + 1) :=
    hj.trans_le ((terminalApproximant_strictMono τ m).monotone
      ((le_max_right i j).trans (Nat.le_succ _)))
  exact ((terminalApproximant_succ_principal τ m (max i j)) hξ' hη').trans
    (terminalApproximant_lt_boundary τ m (max i j + 1))

/-- The terminal sequence is closed under its collapsing function below
its supremum; the bound is proved by comparison with a later iterate. -/
theorem terminalBoundary_collapse_closed (τ : Ordinal.{0}) (m : Nat)
    {ξ : Ordinal.{0}} (hξ : ξ < terminalBoundary τ m) :
    sourceFiniteCollapse τ (m + 1) m ξ < terminalBoundary τ m := by
  obtain ⟨k, hk⟩ := (terminalBoundary_cofinal τ m ξ).1 hξ
  have hc := sourceFiniteCollapse_strictMono_low τ (m + 1) m (Nat.lt_succ_self m)
    hk (terminalApproximant_lt_cardinal τ m k)
  exact hc.trans (terminalApproximant_lt_boundary τ m (k + 1))

/-- The finite terminal grammar stays strictly below the actual iteration
supremum, including every collapsing argument admitted by the grammar. -/
theorem source_terminal_notation_lt_boundary (τ : Ordinal.{0}) (m : Nat)
    {ξ : Ordinal.{0}} (hξ : sourceNotation τ (m + 1) m ξ) :
    ξ < terminalBoundary τ m := by
  rw [sourceNotation, if_pos (Nat.lt_succ_self m)] at hξ
  induction hξ with
  | parameter h => exact h.trans (terminalBoundary_base_lt τ m)
  | add _ _ ihξ ihη => exact terminalBoundary_add_closed τ m ihξ ihη
  | @collapse k α hmk hkn hsort hα ih =>
    have hk : k = m := by omega
    subst k
    exact terminalBoundary_collapse_closed τ m ih

/-- The terminal case of source Theorem 2.13, with the whole notation
domain identified with its actual proper initial segment. -/
theorem source_terminal_notation_iff_lt_boundary (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) (ξ : Ordinal.{0}) :
    sourceNotation τ (m + 1) m ξ ↔ ξ < terminalBoundary τ m := by
  constructor
  · exact source_terminal_notation_lt_boundary τ m
  · intro hξ
    obtain ⟨k, hk⟩ := (terminalBoundary_cofinal τ m ξ).1 hξ
    apply (sourceNotation_iff_hull τ (m + 1) m (Nat.lt_succ_self m) ξ).2
    exact source_hull_initial_segment τ hτ (m + 1) m (Nat.lt_succ_self m)
      (omegaSequence τ (m + 2)) 0 le_rfl (omegaSequence_isSuccLimit τ m).bot_lt
      ((sourceNotation_iff_hull τ (m + 1) m (Nat.lt_succ_self m) _).1
        (terminalApproximant_notation τ hτ m k))
      (terminalApproximant_lt_cardinal τ m k) hk

theorem source_terminal_notation_boundary_absent (τ : Ordinal.{0}) (m : Nat) :
    ¬ sourceNotation τ (m + 1) m (terminalBoundary τ m) := by
  intro h
  exact lt_irrefl _ (source_terminal_notation_lt_boundary τ m h)

end Alexander313.Wilken
