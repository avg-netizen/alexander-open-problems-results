import Alexander313.Wilken.DirectLimitSupport

/-!
# Actual direct-limit star comparison and injectivity

Two genuine global arguments have a common finite source witness. Finite
coverage gives the true argument bounds at that witness, and proved support
coherence transports the finite star law. Thus both equality and strict order
laws concern the actual global collapsing functions, with no assumed global
comparison package. They remain semantic laws; executable comparisons of
canonical public codes and the edge/tracking operations are separate work.
-/

namespace Alexander313.Wilken

theorem globalStar_lt_globalCollapse (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) (α : GlobalNotationOrdinal τ (m + 1))
    (hsort : α.val < omegaSequence τ (m + 2)) :
    globalStar τ hτ m α < globalCollapse τ m α.val := by
  let n := globalSupportFragment τ hτ m α
  have hmn : m + 1 < n := (globalSupportFragment_spec τ hτ m α).1
  have hm : m < n := by omega
  let αn : SourceNotationOrdinal τ n (m + 1) :=
    ⟨α.val, (globalSupportFragment_spec τ hτ m α).2⟩
  have hb : α.val < finiteBoundary τ n (m + 1) :=
    source_finite_notation_sorted_lt_boundary τ hτ n (m + 1) (m + 1)
      le_rfl hmn αn.property hsort
  rw [globalStar_finite_agreement τ hτ m α n hm αn rfl,
    globalCollapse_finite_agreement τ hτ n m hm α.val hb]
  exact sourceStar_lt_sourceFiniteCollapse τ hτ n m hm αn hsort

/-- The displayed star law of Lemma 2.10(d), now for the real unbounded
global grammar and its actual direct-limit collapsing functions. -/
theorem globalCollapse_lt_iff_globalStar (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) (α γ : GlobalNotationOrdinal τ (m + 1))
    (hsortα : α.val < omegaSequence τ (m + 2))
    (hsortγ : γ.val < omegaSequence τ (m + 2)) :
    globalCollapse τ m α.val < globalCollapse τ m γ.val ↔
      (α.val < γ.val ∧ globalStar τ hτ m α < globalCollapse τ m γ.val) ∨
        globalCollapse τ m α.val ≤ globalStar τ hτ m γ := by
  obtain ⟨n, hmn, hα, hγ⟩ := globalNotation_common_fragment τ hτ (m + 1) α γ
  have hm : m < n := by omega
  let αn : SourceNotationOrdinal τ n (m + 1) := ⟨α.val, hα⟩
  let γn : SourceNotationOrdinal τ n (m + 1) := ⟨γ.val, hγ⟩
  have hbα := source_finite_notation_sorted_lt_boundary τ hτ n (m + 1) (m + 1)
    le_rfl hmn hα hsortα
  have hbγ := source_finite_notation_sorted_lt_boundary τ hτ n (m + 1) (m + 1)
    le_rfl hmn hγ hsortγ
  rw [globalStar_finite_agreement τ hτ m α n hm αn rfl,
    globalStar_finite_agreement τ hτ m γ n hm γn rfl,
    globalCollapse_finite_agreement τ hτ n m hm α.val hbα,
    globalCollapse_finite_agreement τ hτ n m hm γ.val hbγ]
  exact sourceFiniteCollapse_lt_iff_sourceStar τ hτ n m hm αn γn hsortα hsortγ

theorem globalCollapse_eq_iff (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) (α γ : GlobalNotationOrdinal τ (m + 1))
    (hsortα : α.val < omegaSequence τ (m + 2))
    (hsortγ : γ.val < omegaSequence τ (m + 2)) :
    globalCollapse τ m α.val = globalCollapse τ m γ.val ↔ α.val = γ.val := by
  obtain ⟨n, hmn, hα, hγ⟩ := globalNotation_common_fragment τ hτ (m + 1) α γ
  have hm : m < n := by omega
  have hbα := source_finite_notation_sorted_lt_boundary τ hτ n (m + 1) (m + 1)
    le_rfl hmn hα hsortα
  have hbγ := source_finite_notation_sorted_lt_boundary τ hτ n (m + 1) (m + 1)
    le_rfl hmn hγ hsortγ
  rw [globalCollapse_finite_agreement τ hτ n m hm α.val hbα,
    globalCollapse_finite_agreement τ hτ n m hm γ.val hbγ]
  exact sourceFiniteCollapse_eq_iff τ n m hm ⟨hα, hsortα⟩ ⟨hγ, hsortγ⟩

/-- Injectivity on the whole prescribed ordinal input interval, using
the proved low initial-segment identity rather than a notation premise. -/
theorem globalCollapse_injective_on (τ : Ordinal.{0}) (hτ : 0 < τ) (m : Nat) :
    Set.InjOn (globalCollapse τ m) (Set.Iio (globalBoundary τ (m + 1))) := by
  intro α hα γ hγ heq
  let α' : GlobalNotationOrdinal τ (m + 1) :=
    ⟨α, ((globalNotation_low_iff_lt_boundary τ hτ (m + 1) α).mpr hα).1⟩
  let γ' : GlobalNotationOrdinal τ (m + 1) :=
    ⟨γ, ((globalNotation_low_iff_lt_boundary τ hτ (m + 1) γ).mpr hγ).1⟩
  exact (globalCollapse_eq_iff τ hτ m α' γ'
    (hα.trans (globalBoundary_lt_cardinal τ hτ (m + 1)))
    (hγ.trans (globalBoundary_lt_cardinal τ hτ (m + 1)))).mp heq

theorem globalCollapse_add_closed (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) (α : Ordinal.{0}) (hα : α < globalBoundary τ (m + 1)) :
    Ordinal.IsPrincipal (· + ·) (globalCollapse τ m α) := by
  let n := globalFragment τ m α hα
  have hm : m < n := by
    have h := globalFragment_gt τ m α hα
    omega
  rw [globalCollapse_finite_agreement τ hτ n m hm α
    (globalFragment_bound τ m α hα)]
  exact sourceFiniteCollapse_add_closed τ n m hm α

theorem globalCollapse_pos (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) (α : Ordinal.{0}) (hα : α < globalBoundary τ (m + 1)) :
    0 < globalCollapse τ m α :=
  (hτ.trans_le ((omegaSequence_strictMono τ).monotone (Nat.zero_le m))).trans_le
    (globalCollapse_bounds τ hτ m α hα).1

end Alexander313.Wilken
