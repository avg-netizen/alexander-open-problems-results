import Alexander313.Wilken.FragmentSupportAgreement
import Alexander313.Wilken.LowFragmentAgreement

/-!
# Actual general finite end-extension

The comparison interval is the source θⁿₘ₊₁, rather than the smaller
Ωₘ₊₁ fragment. Canonical support transfers hull derivations across the
new highest constructor. Actual finite coverage and presentation-size
recursion preserve the support of old terms. Descending level induction
and local ordinal induction discharge all equality premises below.

This constructs the hull and function clauses of Lemma 2.15 and the
inclusion and function clauses of Corollary 2.16. Strict growth of the
general endpoints and direct limits remain separate. No unrestricted
terminal-hull argument bound is used. All proofs await compilation.
-/

namespace Alexander313.Wilken

/-- Support transfer turns proved higher/local call equalities into
agreement of actual hulls on the full source interval. -/
theorem source_finite_hull_congr_of_agreement (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (α β : Ordinal.{0})
    (hα : α < finiteBoundary τ n (m + 1)) (hβ : β < omegaSequence τ (m + 1))
    (higher : ∀ k, m < k → k < n → ∀ η,
      η < finiteBoundary τ n (k + 1) →
      sourceFiniteCollapse τ n k η = sourceFiniteCollapse τ (n + 1) k η)
    («local» : ∀ γ < α, sourceFiniteCollapse τ n m γ = sourceFiniteCollapse τ (n + 1) m γ)
    (ξ : Ordinal.{0}) (hξ : ξ < finiteBoundary τ n (m + 1)) :
    Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α β ξ ↔
      Hull (omegaSequence τ) (sourceFiniteCollapse τ (n + 1)) (n + 1) m α β ξ := by
  have hαsort : α ≤ omegaSequence τ (m + 2) :=
    (hα.trans (finiteBoundary_next_lt_sort τ hτ n m hm)).le
  have embed : ∀ η, sourceNotation τ n (m + 1) η →
      sourceNotation τ (n + 1) (m + 1) η := by
    intro η hη
    exact sourceNotation_next_fragment_of_agreement τ hτ n (m + 1)
      (Nat.succ_le_of_lt hm)
      (fun k hmk hkn γ hγ => higher k (by omega) hkn γ hγ) hη
  let x : SourceNotationOrdinal τ n (m + 1) :=
    ⟨ξ, source_nextNotation_of_lt_finiteBoundary τ hτ n m hm hξ⟩
  let x' : SourceNotationOrdinal τ (n + 1) (m + 1) := ⟨ξ, embed ξ x.property⟩
  have hxP := sourceP_next_fragment_of_higher_agreement τ hτ n m hm higher x x' rfl
  constructor
  · intro hin
    have hs := source_hull_support_transfer τ hτ n m hm α β hαsort hβ.le
      (Hull (omegaSequence τ) (sourceFiniteCollapse τ (n + 1)) (n + 1) m α β)
      (fun p hp => Hull.below_base hp) (fun p hp => Hull.below_parameter hp)
      (fun γ hγα hsupport => by
        let γ' : SourceNotationOrdinal τ (n + 1) (m + 1) :=
          ⟨γ.val, embed γ.val γ.property⟩
        have hP := sourceP_next_fragment_of_higher_agreement τ hτ n m hm higher γ γ' rfl
        have harg := (source_hull_iff_sourceP τ hτ (n + 1) m (by omega) α β
          hαsort hβ.le γ').2 (fun p hp => hsupport p (by simpa only [hP] using hp))
        rw [«local» γ.val hγα]
        exact Hull.«local» hγα harg) hin x rfl
    exact (source_hull_iff_sourceP τ hτ (n + 1) m (by omega) α β hαsort hβ.le x').2
      (fun p hp => hs p (by simpa only [hxP] using hp))
  · intro hin
    have hs := source_hull_support_transfer τ hτ (n + 1) m (by omega) α β hαsort hβ.le
      (Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α β)
      (fun p hp => Hull.below_base hp) (fun p hp => Hull.below_parameter hp)
      (fun γ' hγα hsupport => by
        let γ : SourceNotationOrdinal τ n (m + 1) :=
          ⟨γ'.val, source_nextNotation_of_lt_finiteBoundary τ hτ n m hm (hγα.trans hα)⟩
        have hP := sourceP_next_fragment_of_higher_agreement τ hτ n m hm higher γ γ' rfl
        have harg := (source_hull_iff_sourceP τ hτ n m hm α β hαsort hβ.le γ).2
          (fun p hp => hsupport p (by simpa only [← hP] using hp))
        rw [← «local» γ'.val hγα]
        exact Hull.«local» hγα harg) hin x' rfl
    exact (source_hull_iff_sourceP τ hτ n m hm α β hαsort hβ.le x).2
      (fun p hp => hs p (by simpa only [← hxP] using hp))

/-- At a nonterminal level the comparison interval contains the whole
low closure segment, so actual minimum candidates agree. The terminal
case uses the independently proved low-fragment theorem instead. -/
theorem source_finite_candidate_congr_of_agreement (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m + 1 < n) (α β : Ordinal.{0})
    (hα : α < finiteBoundary τ n (m + 1))
    (higher : ∀ k, m < k → k < n → ∀ η,
      η < finiteBoundary τ n (k + 1) →
      sourceFiniteCollapse τ n k η = sourceFiniteCollapse τ (n + 1) k η)
    («local» : ∀ γ < α, sourceFiniteCollapse τ n m γ = sourceFiniteCollapse τ (n + 1) m γ) :
    CollapseCandidate (omegaSequence τ) (sourceFiniteCollapse τ n) n m α β ↔
      CollapseCandidate (omegaSequence τ) (sourceFiniteCollapse τ (n + 1)) (n + 1) m α β := by
  have hbase := finiteBoundary_base_lt τ hτ n (m + 1) hm
  constructor
  · rintro ⟨hβ, hclosed, harg⟩
    have hh := source_finite_hull_congr_of_agreement τ hτ n m (by omega)
      α β hα hβ higher «local»
    refine ⟨hβ, ?_, (hh α hα).1 harg⟩
    intro ξ hin hsmall
    exact hclosed ξ ((hh ξ (hsmall.trans hbase)).2 hin) hsmall
  · rintro ⟨hβ, hclosed, harg⟩
    have hh := source_finite_hull_congr_of_agreement τ hτ n m (by omega)
      α β hα hβ higher «local»
    refine ⟨hβ, ?_, (hh α hα).2 harg⟩
    intro ξ hin hsmall
    exact hclosed ξ ((hh ξ (hsmall.trans hbase)).1 hin) hsmall

/-- The full source collapsing-function interval in Lemma 2.15. Higher
calls decrease n−m; local calls decrease their ordinal argument. -/
theorem sourceFiniteCollapse_finite_end_extension (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (α : Ordinal.{0})
    (hα : α < finiteBoundary τ n (m + 1)) :
    sourceFiniteCollapse τ n m α = sourceFiniteCollapse τ (n + 1) m α := by
  have all : ∀ m : Fin n, ∀ α : Ordinal.{0}, α < finiteBoundary τ n (m.val + 1) →
      sourceFiniteCollapse τ n m.val α = sourceFiniteCollapse τ (n + 1) m.val α := by
    intro m
    refine (InvImage.wf (fun k : Fin n => n - k.val) Nat.lt_wfRel.wf).induction m
      (C := fun m => ∀ α : Ordinal.{0}, α < finiteBoundary τ n (m.val + 1) →
        sourceFiniteCollapse τ n m.val α = sourceFiniteCollapse τ (n + 1) m.val α) ?_
    intro m ih α
    have higher : ∀ k, m.val < k → k < n → ∀ η,
        η < finiteBoundary τ n (k + 1) →
        sourceFiniteCollapse τ n k η = sourceFiniteCollapse τ (n + 1) k η := by
      intro k hmk hkn η hη
      exact ih ⟨k, hkn⟩ (by change n - k < n - m.val; have h := m.isLt; omega) η hη
    by_cases hnext : m.val + 1 < n
    · refine WellFoundedLT.induction α
        (motive := fun α => α < finiteBoundary τ n (m.val + 1) →
          sourceFiniteCollapse τ n m.val α = sourceFiniteCollapse τ (n + 1) m.val α) ?_
      intro α localih hα
      have «local» : ∀ γ < α,
          sourceFiniteCollapse τ n m.val γ = sourceFiniteCollapse τ (n + 1) m.val γ := by
        intro γ hγ
        exact localih γ hγ (hγ.trans hα)
      have hc : collapseCandidates (omegaSequence τ) (sourceFiniteCollapse τ n) n m.val α =
          collapseCandidates (omegaSequence τ) (sourceFiniteCollapse τ (n + 1))
            (n + 1) m.val α := by
        ext β
        change (CollapseCandidate _ _ _ _ _ β ∨ β = omegaSequence τ (m.val + 1)) ↔
          (CollapseCandidate _ _ _ _ _ β ∨ β = omegaSequence τ (m.val + 1))
        rw [source_finite_candidate_congr_of_agreement τ hτ n m.val hnext α β hα higher «local»]
      change finiteCollapse (omegaSequence τ) n m.val α =
        finiteCollapse (omegaSequence τ) (n + 1) m.val α
      rw [finiteCollapse_eq _ _ _ m.isLt, finiteCollapse_eq _ _ _ (by have h := m.isLt; omega)]
      exact congrArg sInf hc
    · intro hα
      have hn : n = m.val + 1 := by have h := m.isLt; omega
      have hsmall : α < omegaSequence τ (m.val + 1) := by
        have hb : finiteBoundary τ n (m.val + 1) = finiteBoundary τ n m.val := by
          simpa only [hn, Nat.add_sub_cancel] using
            finiteBoundary_terminal τ n (by have h := m.isLt; omega)
        exact hα.trans (by rw [hb]; exact finiteBoundary_lt_cardinal τ hτ n m.val m.isLt)
      exact sourceFiniteCollapse_low_fragment_agreement τ n (n + 1) m.val m.isLt
        (by have h := m.isLt; omega) α hsmall
  exact all ⟨m, hm⟩ α hα

/-- The actual hull intersection identity from Lemma 2.15, pointwise. -/
theorem source_finite_hull_end_extension (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (α β ξ : Ordinal.{0})
    (hα : α < finiteBoundary τ n (m + 1)) (hβ : β < omegaSequence τ (m + 1))
    (hξ : ξ < finiteBoundary τ n (m + 1)) :
    Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α β ξ ↔
      Hull (omegaSequence τ) (sourceFiniteCollapse τ (n + 1)) (n + 1) m α β ξ :=
  source_finite_hull_congr_of_agreement τ hτ n m hm α β hα hβ
    (fun k _ hk η hη => sourceFiniteCollapse_finite_end_extension τ hτ n k hk η hη)
    (fun γ hγ => sourceFiniteCollapse_finite_end_extension τ hτ n m hm γ (hγ.trans hα)) ξ hξ

/-- The notation inclusion of Corollary 2.16, also allowing Tⁿₙ. -/
theorem sourceNotation_finite_end_extension (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m ≤ n) {ξ : Ordinal.{0}} (hξ : sourceNotation τ n m ξ) :
    sourceNotation τ (n + 1) m ξ :=
  sourceNotation_next_fragment_of_agreement τ hτ n m hm
    (fun k _ hk η hη => sourceFiniteCollapse_finite_end_extension τ hτ n k hk η hη) hξ

/-- The exact old-notation agreement domain from Corollary 2.16. -/
theorem sourceFiniteCollapse_finite_notation_agreement (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m k : Nat) (hmk : m ≤ k) (hk : k < n) {η : Ordinal.{0}}
    (hη : sourceNotation τ n m η) (hsort : η < omegaSequence τ (k + 2)) :
    sourceFiniteCollapse τ n k η = sourceFiniteCollapse τ (n + 1) k η :=
  sourceFiniteCollapse_finite_end_extension τ hτ n k hk η
    (source_finite_collapse_argument_lt_boundary τ hτ n m k hmk hk hη hsort)

/-- Actual canonical support agrees for every old next-level notation. -/
theorem sourceP_finite_end_extension (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (ξ : SourceNotationOrdinal τ n (m + 1))
    (ξ' : SourceNotationOrdinal τ (n + 1) (m + 1)) (heq : ξ.val = ξ'.val) :
    sourceP τ hτ n m hm ξ = sourceP τ hτ (n + 1) m (by omega) ξ' :=
  sourceP_next_fragment_of_higher_agreement τ hτ n m hm
    (fun k _ hk η hη => sourceFiniteCollapse_finite_end_extension τ hτ n k hk η hη) ξ ξ' heq

end Alexander313.Wilken
