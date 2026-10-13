import Alexander313.Wilken.TerminalCoverage

/-!
# The actual descending finite approximants

Definition 2.12 is constructed by finite Nat recursion from the terminal
iterates. The values have actual finite-domain presentations at every
lower level and proper cardinal bounds. Their support at a strictly lower
level is empty, so actual hull comparison proves strict increase.

The suprema here are the source θⁿₘ, including θⁿₙ=θⁿₙ₋₁ and θⁿₙ₊₁=0.
Their identification with notation coverage is proved separately. No
coverage or end-extension hypothesis is used. All terms are uncompiled
candidates, specialized to Ordinal universe zero and positive τ.
-/

namespace Alexander313.Wilken

/-- Start at level `top` and apply exactly `d` descending constructors. -/
noncomputable def descendingApproximant (τ : Ordinal.{0}) (top : Nat) :
    Nat → Nat → Ordinal.{0}
  | 0, k => terminalApproximant τ top k
  | d + 1, k => sourceFiniteCollapse τ (top + 1) (top - (d + 1))
      (descendingApproximant τ top d k)

theorem terminalApproximant_lower_notation (τ : Ordinal.{0}) (hτ : 0 < τ)
    (top r : Nat) (hr : r ≤ top) (k : Nat) :
    sourceNotation τ (top + 1) r (terminalApproximant τ top k) := by
  have hrn : r < top + 1 := by omega
  rw [sourceNotation, if_pos hrn]
  have hbase : 0 < omegaSequence τ r :=
    hτ.trans_le ((omegaSequence_strictMono τ).monotone (Nat.zero_le r))
  induction k with
  | zero => exact .parameter hbase
  | succ k ih =>
    exact .collapse hr (Nat.lt_succ_self top)
      ((terminalApproximant_lt_cardinal τ top k).trans (omegaSequence_step τ (top + 1))) ih

/-- All lower presentations and the proper output sort are proved
together, with a strictly smaller finite descending depth. -/
theorem descendingApproximant_properties (τ : Ordinal.{0}) (hτ : 0 < τ)
    (top d : Nat) (hd : d ≤ top) (k : Nat) :
    (∀ r ≤ top - d, sourceNotation τ (top + 1) r (descendingApproximant τ top d k)) ∧
      descendingApproximant τ top d k < omegaSequence τ (top - d + 1) := by
  revert hd
  induction d with
  | zero =>
    intro _
    exact ⟨fun r hr => terminalApproximant_lower_notation τ hτ top r hr k,
      terminalApproximant_lt_cardinal τ top k⟩
  | succ d ih =>
    intro hd
    have hprev := ih (by omega : d ≤ top)
    have hindex : top - d = top - (d + 1) + 1 := by omega
    have hsort : descendingApproximant τ top d k <
        omegaSequence τ (top - (d + 1) + 2) := by
      simpa only [hindex] using hprev.2
    have hkn : top - (d + 1) < top + 1 := by omega
    have harg := hprev.1 (top - (d + 1)) (by omega)
    refine ⟨?_, ?_⟩
    · intro r hr
      have hrn : r < top + 1 := by omega
      have harg_r := hprev.1 r (by omega : r ≤ top - d)
      rw [sourceNotation, if_pos hrn]
      rw [sourceNotation, if_pos hrn] at harg_r
      exact .collapse hr hkn hsort harg_r
    · exact (sourceFiniteCollapse_typed_range τ (top + 1) (top - (d + 1))
        (top - (d + 1)) le_rfl hkn _ harg hsort).2

/-- The source Θⁿₘ(k), with irrelevant n=0/m>n values unused. -/
noncomputable def finiteApproximant (τ : Ordinal.{0}) (n m k : Nat) : Ordinal.{0} :=
  descendingApproximant τ (n - 1) (n - (m + 1)) k

theorem finiteApproximant_top (τ : Ordinal.{0}) (m k : Nat) :
    finiteApproximant τ (m + 1) m k = terminalApproximant τ m k := by
  have htop : m + 1 - 1 = m := by omega
  have hdepth : m + 1 - (m + 1) = 0 := by omega
  rw [finiteApproximant, htop, hdepth]
  rfl

theorem finiteApproximant_next (τ : Ordinal.{0}) (n m k : Nat) (hm : m + 1 < n) :
    finiteApproximant τ n m k = sourceFiniteCollapse τ n m (finiteApproximant τ n (m + 1) k) := by
  have hdepth : n - (m + 1) = n - (m + 2) + 1 := by omega
  have hlevel : n - 1 - (n - (m + 2) + 1) = m := by omega
  have hfragment : n - 1 + 1 = n := by omega
  rw [finiteApproximant, hdepth, descendingApproximant, hlevel, hfragment]
  rfl

theorem finiteApproximant_lower_notation (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (r : Nat) (hr : r ≤ m) (k : Nat) :
    sourceNotation τ n r (finiteApproximant τ n m k) := by
  have hd : n - (m + 1) ≤ n - 1 := by omega
  have hlevel : n - 1 - (n - (m + 1)) = m := by omega
  have hfragment : n - 1 + 1 = n := by omega
  simpa only [finiteApproximant, hlevel, hfragment] using
    (descendingApproximant_properties τ hτ (n - 1) (n - (m + 1)) hd k).1 r
      (by omega : r ≤ n - 1 - (n - (m + 1)))

theorem finiteApproximant_lt_cardinal (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (k : Nat) :
    finiteApproximant τ n m k < omegaSequence τ (m + 1) := by
  have hd : n - (m + 1) ≤ n - 1 := by omega
  have hlevel : n - 1 - (n - (m + 1)) = m := by omega
  simpa only [finiteApproximant, hlevel] using
    (descendingApproximant_properties τ hτ (n - 1) (n - (m + 1)) hd k).2

theorem terminalApproximant_support_empty (τ : Ordinal.{0}) (hτ : 0 < τ)
    (top r : Nat) (hr : r < top) (k : Nat) :
    sourceP τ hτ (top + 1) r (by omega)
      ⟨terminalApproximant τ top k,
        terminalApproximant_lower_notation τ hτ top (r + 1) (by omega) k⟩ = ∅ := by
  induction k with
  | zero =>
    rw [sourceP_low τ hτ (top + 1) r (by omega)
      ⟨terminalApproximant τ top 0,
        terminalApproximant_lower_notation τ hτ top (r + 1) (by omega) 0⟩
      (omegaSequence_isSuccLimit τ r).bot_lt]
    simp only [terminalApproximant_zero, canonicalANF_zero, List.toFinset_nil]
  | succ k ih =>
    rw [sourceP_theta τ hτ (top + 1) r (by omega)
      ⟨terminalApproximant τ top (k + 1),
        terminalApproximant_lower_notation τ hτ top (r + 1) (by omega) (k + 1)⟩
      ⟨terminalApproximant τ top k,
        terminalApproximant_lower_notation τ hτ top (r + 1) (by omega) k⟩
      top hr (Nat.lt_succ_self top)
      ((terminalApproximant_lt_cardinal τ top k).trans (omegaSequence_step τ (top + 1))) rfl]
    exact ih

theorem descendingApproximant_support_empty (τ : Ordinal.{0}) (hτ : 0 < τ)
    (top d : Nat) (hd : d ≤ top) (r : Nat) (hr : r < top - d) (k : Nat) :
    sourceP τ hτ (top + 1) r (by omega)
      ⟨descendingApproximant τ top d k,
        (descendingApproximant_properties τ hτ top d hd k).1 (r + 1) (by omega)⟩ = ∅ := by
  revert hd r hr
  induction d with
  | zero =>
    intro hd r hr
    exact terminalApproximant_support_empty τ hτ top r hr k
  | succ d ih =>
    intro hd r hr
    have hdprev : d ≤ top := by omega
    have hindex : top - d = top - (d + 1) + 1 := by omega
    have hsort : descendingApproximant τ top d k <
        omegaSequence τ (top - (d + 1) + 2) := by
      simpa only [hindex] using (descendingApproximant_properties τ hτ top d hdprev k).2
    rw [sourceP_theta τ hτ (top + 1) r (by omega)
      ⟨descendingApproximant τ top (d + 1) k,
        (descendingApproximant_properties τ hτ top (d + 1) hd k).1 (r + 1) (by omega)⟩
      ⟨descendingApproximant τ top d k,
        (descendingApproximant_properties τ hτ top d hdprev k).1 (r + 1) (by omega)⟩
      (top - (d + 1)) hr (by omega) hsort rfl]
    exact ih hdprev r (by omega)

theorem sourceFiniteCollapse_lt_of_empty_support (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (α γ : SourceNotationOrdinal τ n (m + 1))
    (hα : α.val < omegaSequence τ (m + 2)) (hγ : γ.val < omegaSequence τ (m + 2))
    (hαγ : α.val < γ.val) (hempty : sourceP τ hτ n m hm α = ∅) :
    sourceFiniteCollapse τ n m α.val < sourceFiniteCollapse τ n m γ.val := by
  apply (sourceFiniteCollapse_lt_iff_later_hull τ n m hm
    ⟨α.property, hα⟩ ⟨γ.property, hγ⟩ hαγ).2
  apply (source_hull_iff_sourceP τ hτ n m hm γ.val (sourceFiniteCollapse τ n m γ.val)
    hγ.le (sourceFiniteCollapse_bounds τ n m hm γ.val).2 α).2
  rw [hempty]
  simp

theorem descendingApproximant_strictMono (τ : Ordinal.{0}) (hτ : 0 < τ)
    (top d : Nat) (hd : d ≤ top) : StrictMono (descendingApproximant τ top d) := by
  revert hd
  induction d with
  | zero => intro _; exact terminalApproximant_strictMono τ top
  | succ d ih =>
    intro hd i j hij
    have hdprev : d ≤ top := by omega
    have hindex : top - d = top - (d + 1) + 1 := by omega
    have hsort : ∀ k, descendingApproximant τ top d k <
        omegaSequence τ (top - (d + 1) + 2) := by
      intro k
      simpa only [hindex] using (descendingApproximant_properties τ hτ top d hdprev k).2
    exact sourceFiniteCollapse_lt_of_empty_support τ hτ (top + 1) (top - (d + 1))
      (by omega)
      ⟨descendingApproximant τ top d i,
        (descendingApproximant_properties τ hτ top d hdprev i).1
          (top - (d + 1) + 1) (by omega)⟩
      ⟨descendingApproximant τ top d j,
        (descendingApproximant_properties τ hτ top d hdprev j).1
          (top - (d + 1) + 1) (by omega)⟩
      (hsort i) (hsort j) (ih hdprev hij)
      (descendingApproximant_support_empty τ hτ top d hdprev (top - (d + 1)) (by omega) i)

theorem finiteApproximant_strictMono (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) : StrictMono (finiteApproximant τ n m) :=
  descendingApproximant_strictMono τ hτ (n - 1) (n - (m + 1)) (by omega)

/-- The source θⁿₘ, with the two explicit endpoint conventions. -/
noncomputable def finiteBoundary (τ : Ordinal.{0}) (n m : Nat) : Ordinal.{0} :=
  if m ≤ n then ⨆ k, finiteApproximant τ n m k else 0

theorem finiteBoundary_top (τ : Ordinal.{0}) (m : Nat) :
    finiteBoundary τ (m + 1) m = terminalBoundary τ m := by
  simp only [finiteBoundary, if_pos (Nat.le_succ m), finiteApproximant_top, terminalBoundary]

theorem finiteBoundary_terminal (τ : Ordinal.{0}) (n : Nat) (hn : 0 < n) :
    finiteBoundary τ n n = finiteBoundary τ n (n - 1) := by
  have hdepth : n - (n - 1 + 1) = 0 := by omega
  simp only [finiteBoundary, if_pos le_rfl, if_pos (Nat.sub_le n 1),
    finiteApproximant, Nat.sub_eq_zero_of_le (Nat.le_succ n), hdepth]

theorem finiteBoundary_above_terminal (τ : Ordinal.{0}) (n : Nat) :
    finiteBoundary τ n (n + 1) = 0 := by
  rw [finiteBoundary, if_neg (by omega)]

theorem finiteBoundary_lt_cardinal (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) : finiteBoundary τ n m < omegaSequence τ (m + 1) := by
  rw [finiteBoundary, if_pos hm.le]
  apply Ordinal.lift_iSup_lt_of_lt_cof
  · simpa only [Cardinal.mk_nat, Cardinal.lift_aleph0, Ordinal.lift_id, omegaSequence,
      (omegaSequence_regular τ m).cof_ord] using
        (levelCardinal_infinite τ m).trans_lt (levelCardinal_step τ m)
  · exact finiteApproximant_lt_cardinal τ hτ n m hm

theorem finiteApproximant_lt_boundary (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (k : Nat) : finiteApproximant τ n m k < finiteBoundary τ n m := by
  rw [finiteBoundary, if_pos hm.le]
  exact (finiteApproximant_strictMono τ hτ n m hm (Nat.lt_succ_self k)).trans_le
    (Ordinal.le_iSup (finiteApproximant τ n m) (k + 1))

theorem finiteBoundary_cofinal (τ : Ordinal.{0}) (n m : Nat) (hm : m < n) (ξ : Ordinal.{0}) :
    ξ < finiteBoundary τ n m ↔ ∃ k, ξ < finiteApproximant τ n m k := by
  rw [finiteBoundary, if_pos hm.le]
  exact Ordinal.lt_iSup_iff

theorem finiteBoundary_base_lt (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) : omegaSequence τ m < finiteBoundary τ n m := by
  have hbase : omegaSequence τ m ≤ finiteApproximant τ n m 1 := by
    by_cases hnext : m + 1 < n
    · rw [finiteApproximant_next τ n m 1 hnext]
      exact (sourceFiniteCollapse_bounds τ n m hm _).1
    · have htop : n = m + 1 := by omega
      subst n
      rw [finiteApproximant_top]
      exact (sourceFiniteCollapse_bounds τ (m + 1) m (Nat.lt_succ_self m) 0).1
  exact hbase.trans_lt (finiteApproximant_lt_boundary τ hτ n m hm 1)

theorem finiteApproximant_succ_principal (τ : Ordinal.{0}) (n m : Nat)
    (hm : m < n) (k : Nat) : Ordinal.IsPrincipal (· + ·) (finiteApproximant τ n m (k + 1)) := by
  by_cases hnext : m + 1 < n
  · rw [finiteApproximant_next τ n m (k + 1) hnext]
    exact sourceFiniteCollapse_add_closed τ n m hm _
  · have htop : n = m + 1 := by omega
    subst n
    rw [finiteApproximant_top]
    exact terminalApproximant_succ_principal τ m k

theorem finiteBoundary_add_closed (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) : Ordinal.IsPrincipal (· + ·) (finiteBoundary τ n m) := by
  intro ξ η hξ hη
  obtain ⟨i, hi⟩ := (finiteBoundary_cofinal τ n m hm ξ).1 hξ
  obtain ⟨j, hj⟩ := (finiteBoundary_cofinal τ n m hm η).1 hη
  have hξ' : ξ < finiteApproximant τ n m (max i j + 1) :=
    hi.trans_le ((finiteApproximant_strictMono τ hτ n m hm).monotone
      ((le_max_left i j).trans (Nat.le_succ _)))
  have hη' : η < finiteApproximant τ n m (max i j + 1) :=
    hj.trans_le ((finiteApproximant_strictMono τ hτ n m hm).monotone
      ((le_max_right i j).trans (Nat.le_succ _)))
  exact ((finiteApproximant_succ_principal τ n m hm (max i j)) hξ' hη').trans
    (finiteApproximant_lt_boundary τ hτ n m hm (max i j + 1))

end Alexander313.Wilken
