import Alexander313.Wilken.DirectLimitTowers

/-!
# Actual finite-boundary representation in the global system

Descending level induction turns the endpoint-growth bound into an
equality with the new fragment's first approximant. At a nonterminal
level the next-level equality licenses every local call in a genuine
minimum candidate. Actual hull support transfer proves its closure; the
first argument is an actual pure higher tower with empty support. The
terminal identity was proved independently. This gives the exact finite
identity of Corollary 2.19, with literal global collapsing functions.
No source representation contract is an input. Uncompiled candidates.
-/

namespace Alexander313.Wilken

/-- The next-level equality is a descending-induction hypothesis,
discharged by `finiteBoundary_eq_next_firstApproximant` below. -/
theorem finiteBoundary_next_first_candidate (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m + 1 < n)
    (hnext : finiteBoundary τ n (m + 1) = finiteApproximant τ (n + 1) (m + 1) 1) :
    CollapseCandidate (omegaSequence τ) (sourceFiniteCollapse τ (n + 1)) (n + 1) m
      (finiteApproximant τ (n + 1) (m + 1) 1) (finiteBoundary τ n m) := by
  classical
  let α := finiteApproximant τ (n + 1) (m + 1) 1
  let β := finiteBoundary τ n m
  have hmn : m < n := by omega
  have hnew : m < n + 1 := by omega
  have hαsort : α < omegaSequence τ (m + 2) :=
    finiteApproximant_lt_cardinal τ hτ (n + 1) (m + 1) (by omega) 1
  have hβsort : β < omegaSequence τ (m + 1) := finiteBoundary_lt_cardinal τ hτ n m hmn
  let Q := Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m (omegaSequence τ (m + 2)) 0
  refine ⟨hβsort, ?_, ?_⟩
  · intro ξ hin hsmall
    let x : SourceNotationOrdinal τ (n + 1) (m + 1) :=
      ⟨ξ, source_hull_next_notation τ (n + 1) m hnew hαsort.le hβsort.le hin⟩
    have hs := source_hull_support_transfer τ hτ (n + 1) m hnew α β hαsort.le hβsort.le Q
      (fun p hp => Hull.below_base hp)
      (fun p hp => by
        have hnotation := ((source_finite_notation_low_iff_lt_boundary τ hτ n m hmn p).2 hp).1
        exact (sourceNotation_iff_hull τ n m hmn p).1 hnotation)
      (fun γ hγα hsupport => by
        have hγbound : γ.val < finiteBoundary τ n (m + 1) := by
          rw [hnext]
          exact hγα
        let γold : SourceNotationOrdinal τ n (m + 1) :=
          ⟨γ.val, source_nextNotation_of_lt_finiteBoundary τ hτ n m hmn hγbound⟩
        have hP := sourceP_finite_end_extension τ hτ n m hmn γold γ rfl
        have harg := (source_hull_iff_sourceP τ hτ n m hmn (omegaSequence τ (m + 2)) 0
          le_rfl (zero_le) γold).2 (fun p hp => hsupport p (by simpa only [hP] using hp))
        rw [← sourceFiniteCollapse_finite_end_extension τ hτ n m hmn γ.val hγbound]
        exact Hull.«local» (hγα.trans hαsort) harg) hin x rfl
    have hcomponents : ∀ p ∈ canonicalANF ξ, Q p := by
      intro p hp
      apply hs p
      rw [sourceP_low τ hτ (n + 1) m hnew x hsmall]
      exact List.mem_toFinset.2 hp
    have hQξ := (source_hull_iff_canonicalANF τ hτ n m hmn
      (omegaSequence τ (m + 2)) 0 ξ).2 hcomponents
    exact (source_finite_notation_low_iff_lt_boundary τ hτ n m hmn ξ).1
      ⟨(sourceNotation_iff_hull τ n m hmn ξ).2 hQξ, hsmall⟩
  · let a : SourceNotationOrdinal τ (n + 1) (m + 1) :=
      ⟨α, finiteApproximant_lower_notation τ hτ (n + 1) (m + 1) (by omega)
        (m + 1) le_rfl 1⟩
    have hempty : sourceP τ hτ (n + 1) m hnew a = ∅ :=
      finiteApproximant_support_empty τ hτ (n + 1) (m + 1) (by omega) m
        (Nat.lt_succ_self m) 1
    apply (source_hull_iff_sourceP τ hτ (n + 1) m hnew α β hαsort.le hβsort.le a).2
    rw [hempty]
    simp

/-- The old finite endpoint is exactly the next first descending term. -/
theorem finiteBoundary_eq_next_firstApproximant (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) :
    finiteBoundary τ n m = finiteApproximant τ (n + 1) m 1 := by
  have all : ∀ m : Fin n,
      finiteBoundary τ n m.val = finiteApproximant τ (n + 1) m.val 1 := by
    intro m
    refine (InvImage.wf (fun k : Fin n => n - k.val) Nat.lt_wfRel.wf).induction
      (C := fun k : Fin n =>
        finiteBoundary τ n k.val = finiteApproximant τ (n + 1) k.val 1) m ?_
    intro m ih
    by_cases hnext : m.val + 1 < n
    · have hnextEq := ih ⟨m.val + 1, hnext⟩
        (by change n - (m.val + 1) < n - m.val; have h := m.isLt; omega)
      apply le_antisymm (finiteBoundary_le_next_firstApproximant τ hτ n m.val m.isLt)
      rw [finiteApproximant_next τ (n + 1) m.val 1 (by have h := m.isLt; omega)]
      exact finiteCollapse_minimal (by have h := m.isLt; omega)
        (finiteBoundary_next_first_candidate τ hτ n m.val hnext hnextEq)
    · have hn : n = m.val + 1 := by have h := m.isLt; omega
      have hb : finiteBoundary τ n m.val =
          sourceFiniteCollapse τ (n + 1) m.val (omegaSequence τ n) := by
        simpa only [hn, finiteBoundary_top] using terminalBoundary_eq_next_collapse τ hτ m.val
      have ha : finiteApproximant τ (n + 1) m.val 1 =
          sourceFiniteCollapse τ (n + 1) m.val (omegaSequence τ n) := by
        rw [finiteApproximant_next τ (n + 1) m.val 1 (by have h := m.isLt; omega)]
        rw [← hn, finiteApproximant_terminal_one τ n (by have h := m.isLt; omega)]
      exact hb.trans ha.symm
  exact all ⟨m, hm⟩

/-- The exact finite endpoint identity in Corollary 2.19. Its right
side is the literal global term ϑₘ(...ϑₙ(0)...). -/
theorem finiteBoundary_eq_globalDescendingTerm (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) :
    finiteBoundary τ n m = globalDescendingTerm τ n m :=
  (finiteBoundary_eq_next_firstApproximant τ hτ n m hm).trans
    (globalDescendingTerm_eq_firstApproximant τ hτ n m hm.le).symm

theorem finiteBoundary_next_notation (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) : sourceNotation τ (n + 1) m (finiteBoundary τ n m) := by
  rw [finiteBoundary_eq_next_firstApproximant τ hτ n m hm]
  exact finiteApproximant_lower_notation τ hτ (n + 1) m (by omega) m le_rfl 1

theorem sourceNotation_strict_finite_end_extension (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) :
    ∃ ξ, sourceNotation τ (n + 1) m ξ ∧ ¬ sourceNotation τ n m ξ :=
  ⟨finiteBoundary τ n m, finiteBoundary_next_notation τ hτ n m hm,
    source_finite_boundary_absent τ hτ n m hm⟩

end Alexander313.Wilken
