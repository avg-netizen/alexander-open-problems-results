import Alexander313.Wilken.SourceSupport

/-!
# Full finite-source support, star bounds and comparison

Wilken Lemma 2.10(b,c,d) is derived for the constructed P and the actual
finite collapsing family. Induction follows the proved finite-presentation
measure. The principal branch uses actual higher-hull inverse closure;
the nonprincipal branch uses canonical ANF components. No support or star
comparison theorem is supplied as a field of an input package.

The theorem domain is exactly Tⁿₘ₊₁∩Ωₘ₊₂, specialized to Ordinal universe
zero to match the presentation syntax. The construction remains semantic
and noncomputable; primitive-recursive public-code comparison, tracking
and direct limits are separate unfinished work. All terms are candidates
awaiting external compilation.
-/

namespace Alexander313.Wilken

/-- The actual support equivalence of Lemma 2.10(b), including endpoint
hulls. Its strict source bounds are special cases of these ≤ bounds. -/
theorem source_hull_iff_sourceP (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (α β : Ordinal.{0})
    (hα : α ≤ omegaSequence τ (m + 2)) (hβ : β ≤ omegaSequence τ (m + 1))
    (ξ : SourceNotationOrdinal τ n (m + 1)) :
    Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α β ξ.val ↔
      ∀ p ∈ sourceP τ hτ n m hm ξ,
        Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α β p := by
  classical
  refine (presentationOrder_wf τ n (m + 1) (Nat.succ_pos m) (Nat.succ_le_of_lt hm)).induction ξ
    (C := fun ξ => Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α β ξ.val ↔
      ∀ p ∈ sourceP τ hτ n m hm ξ,
        Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α β p) ?_
  intro ξ ih
  by_cases hlow : ξ.val < omegaSequence τ (m + 1)
  · rw [sourceP_low τ hτ n m hm ξ hlow]
    simpa only [List.mem_toFinset] using
      source_hull_iff_canonicalANF τ hτ n m hm α β ξ.val
  · by_cases hprincipal : Ordinal.IsPrincipal (· + ·) ξ.val
    · let q := sourceHigherPresentation τ hτ n m hm ξ (le_of_not_gt hlow) hprincipal
      have hmq : m < q.level := by have h := q.lower; omega
      calc
        Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α β ξ.val ↔
            Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α β
              (sourceFiniteCollapse τ n q.level q.argument.val) := by rw [q.denote]
        _ ↔ Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α β q.argument.val :=
          source_hull_higher_iff_argument τ hτ n m hm α β hα hβ q.level hmq q.upper
            q.argument.val q.argument.property q.sort
        _ ↔ ∀ p ∈ sourceP τ hτ n m hm q.argument,
            Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α β p :=
          ih q.argument (sourceHigherPresentation_order τ hτ n m hm ξ q)
        _ ↔ ∀ p ∈ sourceP τ hτ n m hm ξ,
            Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α β p := by
          rw [sourceP_principal τ hτ n m hm ξ (le_of_not_gt hlow) hprincipal]
    · constructor
      · intro hx p hp
        obtain ⟨a, ha, hp⟩ := (sourceP_mem_anf τ hτ n m hm ξ p).1 hp
        have hin := source_hull_canonicalANF τ hτ n m hm α β hx a ha
        exact (ih (sourceComponent τ hτ n m hm ξ a ha)
          (sourceComponent_order τ hτ n m hm ξ (le_of_not_gt hlow) hprincipal a ha)).1 hin p hp
      · intro hsupport
        apply (source_hull_iff_canonicalANF τ hτ n m hm α β ξ.val).2
        intro a ha
        apply (ih (sourceComponent τ hτ n m hm ξ a ha)
          (sourceComponent_order τ hτ n m hm ξ (le_of_not_gt hlow) hprincipal a ha)).2
        intro p hp
        exact hsupport p ((sourceP_mem_anf τ hτ n m hm ξ p).2 ⟨a, ha, hp⟩)

/-- The actual `max((Pⁿₘ(ξ) \ Ωₘ) ∪ {0})` of Definition 2.9. -/
noncomputable def sourceStar (τ : Ordinal.{0}) (hτ : 0 < τ) (n m : Nat) (hm : m < n)
    (ξ : SourceNotationOrdinal τ n (m + 1)) : Ordinal.{0} := by
  classical
  exact ((sourceP τ hτ n m hm ξ).filter (fun p => omegaSequence τ m ≤ p)).sup id

theorem sourceStar_eq_lowStar (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (ξ : SourceNotationOrdinal τ n (m + 1))
    (hlow : ξ.val < omegaSequence τ (m + 1)) :
    sourceStar τ hτ n m hm ξ = lowStar τ m ξ.val := by
  classical
  rw [sourceStar, sourceP_low τ hτ n m hm ξ hlow, lowStar]

/-- A positive bound at or above Ωₘ bounds star exactly when it bounds
all actual support components, including those found below higher θs. -/
theorem sourceStar_lt_iff (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (ξ : SourceNotationOrdinal τ n (m + 1)) (β : Ordinal.{0})
    (hβ : 0 < β) (hbase : omegaSequence τ m ≤ β) :
    sourceStar τ hτ n m hm ξ < β ↔ ∀ p ∈ sourceP τ hτ n m hm ξ, p < β := by
  classical
  unfold sourceStar
  constructor
  · intro h p hp
    by_cases hlarge : omegaSequence τ m ≤ p
    · have hmem : p ∈ (sourceP τ hτ n m hm ξ).filter (fun p => omegaSequence τ m ≤ p) :=
        Finset.mem_filter.2 ⟨hp, hlarge⟩
      exact (Finset.sup_lt_iff hβ).1 h p hmem
    · exact (lt_of_not_ge hlarge).trans_le hbase
  · intro h
    apply (Finset.sup_lt_iff hβ).2
    intro p hp
    exact h p (Finset.mem_filter.1 hp).1

/-- Full Lemma 2.10(c), using the actual support equivalence, the actual
argument hull and the initial segment of the constructed minimum. -/
theorem sourceStar_lt_sourceFiniteCollapse (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (α : SourceNotationOrdinal τ n (m + 1))
    (hsort : α.val < omegaSequence τ (m + 2)) :
    sourceStar τ hτ n m hm α < sourceFiniteCollapse τ n m α.val := by
  apply (sourceStar_lt_iff τ hτ n m hm α (sourceFiniteCollapse τ n m α.val)
    (sourceFiniteCollapse_pos τ hτ n m hm α.val)
    (sourceFiniteCollapse_bounds τ n m hm α.val).1).2
  have harg := sourceFiniteCollapse_argument_notation τ n m hm α.val hsort α.property
  have hsupport := (source_hull_iff_sourceP τ hτ n m hm α.val
    (sourceFiniteCollapse τ n m α.val) hsort.le
    (sourceFiniteCollapse_bounds τ n m hm α.val).2 α).1 harg
  intro p hp
  exact (finiteCollapse_hull_initial hm α.val p).1
    ⟨hsupport p hp, sourceP_below τ hτ n m hm α p hp⟩

/-- The full star test in any source collapse hull; no low-input premise
on ξ is present. Higher support recursion is already constructed. -/
theorem source_collapse_hull_iff_sourceStar (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (γ : Ordinal.{0})
    (hsortγ : γ ≤ omegaSequence τ (m + 2))
    (ξ : SourceNotationOrdinal τ n (m + 1)) :
    Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m γ
        (sourceFiniteCollapse τ n m γ) ξ.val ↔
      sourceStar τ hτ n m hm ξ < sourceFiniteCollapse τ n m γ := by
  rw [source_hull_iff_sourceP τ hτ n m hm γ (sourceFiniteCollapse τ n m γ) hsortγ
    (sourceFiniteCollapse_bounds τ n m hm γ).2 ξ,
    sourceStar_lt_iff τ hτ n m hm ξ (sourceFiniteCollapse τ n m γ)
      (sourceFiniteCollapse_pos τ hτ n m hm γ)
      (sourceFiniteCollapse_bounds τ n m hm γ).1]
  constructor
  · intro h p hp
    exact (finiteCollapse_hull_initial hm γ p).1
      ⟨h p hp, sourceP_below τ hτ n m hm ξ p hp⟩
  · intro h p hp
    exact .below_parameter (h p hp)

/-- Full displayed Lemma 2.10(d) on its literal source domain. The earlier
injectivity theorem and this star formula use the same constructed θs. -/
theorem sourceFiniteCollapse_lt_iff_sourceStar (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (α γ : SourceNotationOrdinal τ n (m + 1))
    (hsortα : α.val < omegaSequence τ (m + 2))
    (hsortγ : γ.val < omegaSequence τ (m + 2)) :
    sourceFiniteCollapse τ n m α.val < sourceFiniteCollapse τ n m γ.val ↔
      (α.val < γ.val ∧ sourceStar τ hτ n m hm α < sourceFiniteCollapse τ n m γ.val) ∨
        sourceFiniteCollapse τ n m α.val ≤ sourceStar τ hτ n m hm γ := by
  have hα : α.val ∈ sourceCollapseDomain τ n m := ⟨α.property, hsortα⟩
  have hγ : γ.val ∈ sourceCollapseDomain τ n m := ⟨γ.property, hsortγ⟩
  constructor
  · intro hvalues
    rcases (sourceFiniteCollapse_lt_iff_hulls τ n m hm hα hγ).1 hvalues with
      ⟨hαγ, hinα⟩ | ⟨hγα, hnotγ⟩
    · exact Or.inl ⟨hαγ,
        (source_collapse_hull_iff_sourceStar τ hτ n m hm γ.val hsortγ.le α).1 hinα⟩
    · apply Or.inr
      apply le_of_not_gt
      intro hstar
      exact hnotγ ((source_collapse_hull_iff_sourceStar τ hτ n m hm α.val hsortα.le γ).2 hstar)
  · rintro (⟨hαγ, hstar⟩ | hstar)
    · exact (sourceFiniteCollapse_lt_iff_hulls τ n m hm hα hγ).2
        (Or.inl ⟨hαγ,
          (source_collapse_hull_iff_sourceStar τ hτ n m hm γ.val hsortγ.le α).2 hstar⟩)
    · exact hstar.trans_lt (sourceStar_lt_sourceFiniteCollapse τ hτ n m hm γ hsortγ)

end Alexander313.Wilken
