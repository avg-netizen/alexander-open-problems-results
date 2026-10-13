import Alexander313.Wilken.HullInversion

/-!
# The actual star maximum and comparison on the low-argument fragment

For ξ<Ωₘ₊₁, Wilken Definition 2.9 sets Pⁿₘ(ξ) equal to the canonical
principal components of ξ. Its star is therefore the maximum of those
components at or above Ωₘ, with zero added. We construct exactly that
finite maximum and derive Lemma 2.10(c,d) on this fragment.

The bound ξ<Ωₘ₊₁ is an explicit theorem hypothesis. The total `lowStar`
definition outside that fragment is auxiliary; it is not identified with
the source star there. Full P/star recursion through higher θ arguments
and hereditary effective syntax remain unfinished. These semantic proof
terms are candidates awaiting external compilation.
-/

namespace Alexander313.Wilken

/-- The maximum `max((ANF(ξ) \ Ωₘ) ∪ {0})`, represented as a finite
supremum with bottom zero. It is the source star when ξ<Ωₘ₊₁. -/
noncomputable def lowStar (τ : Ordinal) (m : Nat) (ξ : Ordinal) : Ordinal := by
  classical
  exact ((canonicalANF ξ).toFinset.filter (fun a => omegaSequence τ m ≤ a)).sup id

/-- A positive bound at or above Ωₘ bounds the star iff it bounds every
canonical atom. Atoms below Ωₘ automatically satisfy that bound. -/
theorem lowStar_lt_iff (τ : Ordinal) (m : Nat) (ξ β : Ordinal)
    (hβ : 0 < β) (hbase : omegaSequence τ m ≤ β) :
    lowStar τ m ξ < β ↔ ∀ a ∈ canonicalANF ξ, a < β := by
  classical
  unfold lowStar
  constructor
  · intro h a ha
    by_cases hlarge : omegaSequence τ m ≤ a
    · have hmem : a ∈ (canonicalANF ξ).toFinset.filter
          (fun a => omegaSequence τ m ≤ a) :=
        Finset.mem_filter.2 ⟨List.mem_toFinset.2 ha, hlarge⟩
      exact (Finset.sup_lt_iff hβ).1 h a hmem
    · exact (lt_of_not_ge hlarge).trans_le hbase
  · intro h
    apply (Finset.sup_lt_iff hβ).2
    intro a ha
    exact h a (List.mem_toFinset.1 (Finset.mem_filter.1 ha).1)

/-- Lemma 2.10(c) on its literal low-argument fragment. Every ANF atom
is below the next cardinal, so the constructed hull initial segment
turns argument membership into the required strict star bound. -/
theorem lowStar_lt_sourceFiniteCollapse (τ : Ordinal) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) {α : Ordinal}
    (hα : α ∈ sourceCollapseDomain τ n m)
    (hlow : α < omegaSequence τ (m + 1)) :
    lowStar τ m α < sourceFiniteCollapse τ n m α := by
  apply (lowStar_lt_iff τ m α (sourceFiniteCollapse τ n m α)
    (sourceFiniteCollapse_pos τ hτ n m hm α)
    (sourceFiniteCollapse_bounds τ n m hm α).1).2
  intro a ha
  have harg := sourceFiniteCollapse_argument_notation τ n m hm α hα.2 hα.1
  have hin := source_hull_canonicalANF τ hτ n m hm α
    (sourceFiniteCollapse τ n m α) harg a ha
  exact (finiteCollapse_hull_initial hm α a).1
    ⟨hin, (canonicalANF_mem_le ha).trans_lt hlow⟩

/-- The source star test for a low ξ in a constructed collapse hull. -/
theorem source_collapse_hull_iff_lowStar (τ : Ordinal) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (γ ξ : Ordinal)
    (hlow : ξ < omegaSequence τ (m + 1)) :
    Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m γ
        (sourceFiniteCollapse τ n m γ) ξ ↔
      lowStar τ m ξ < sourceFiniteCollapse τ n m γ := by
  rw [source_hull_iff_canonicalANF τ hτ n m hm γ
    (sourceFiniteCollapse τ n m γ) ξ,
    lowStar_lt_iff τ m ξ (sourceFiniteCollapse τ n m γ)
      (sourceFiniteCollapse_pos τ hτ n m hm γ)
      (sourceFiniteCollapse_bounds τ n m hm γ).1]
  constructor
  · intro h a ha
    exact (finiteCollapse_hull_initial hm γ a).1
      ⟨h a ha, (canonicalANF_mem_le ha).trans_lt hlow⟩
  · intro h a ha
    exact .below_parameter (h a ha)

/-- The displayed Lemma 2.10(d) formula, proved on the explicit fragment
where Definition 2.9 identifies the source support with ANF. Its second
disjunct needs no argument-order condition because γ's star is strictly
below its own collapsing value. -/
theorem sourceFiniteCollapse_lt_iff_lowStar (τ : Ordinal) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) {α γ : Ordinal}
    (hα : α ∈ sourceCollapseDomain τ n m)
    (hγ : γ ∈ sourceCollapseDomain τ n m)
    (hlowα : α < omegaSequence τ (m + 1))
    (hlowγ : γ < omegaSequence τ (m + 1)) :
    sourceFiniteCollapse τ n m α < sourceFiniteCollapse τ n m γ ↔
      (α < γ ∧ lowStar τ m α < sourceFiniteCollapse τ n m γ) ∨
        sourceFiniteCollapse τ n m α ≤ lowStar τ m γ := by
  constructor
  · intro hvalues
    rcases (sourceFiniteCollapse_lt_iff_hulls τ n m hm hα hγ).1 hvalues with
      ⟨hαγ, hinα⟩ | ⟨hγα, hnotγ⟩
    · exact Or.inl ⟨hαγ,
        (source_collapse_hull_iff_lowStar τ hτ n m hm γ α hlowα).1 hinα⟩
    · apply Or.inr
      apply le_of_not_gt
      intro hstar
      exact hnotγ ((source_collapse_hull_iff_lowStar τ hτ n m hm α γ hlowγ).2 hstar)
  · rintro (⟨hαγ, hstar⟩ | hstar)
    · exact (sourceFiniteCollapse_lt_iff_hulls τ n m hm hα hγ).2
        (Or.inl ⟨hαγ,
          (source_collapse_hull_iff_lowStar τ hτ n m hm γ α hlowα).2 hstar⟩)
    · exact hstar.trans_lt (lowStar_lt_sourceFiniteCollapse τ hτ n m hm hγ hlowγ)

/-- At the last finite level the source argument domain is Tⁿₙ=Ωₙ,
so the low-star formula already covers the entire source restriction of
ϑⁿₙ₋₁. Higher-level support recursion is unnecessary at this level. -/
theorem sourceFiniteCollapse_top_lt_iff_lowStar (τ : Ordinal) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (htop : m + 1 = n) {α γ : Ordinal}
    (hα : α ∈ sourceCollapseDomain τ n m)
    (hγ : γ ∈ sourceCollapseDomain τ n m) :
    sourceFiniteCollapse τ n m α < sourceFiniteCollapse τ n m γ ↔
      (α < γ ∧ lowStar τ m α < sourceFiniteCollapse τ n m γ) ∨
        sourceFiniteCollapse τ n m α ≤ lowStar τ m γ := by
  apply sourceFiniteCollapse_lt_iff_lowStar τ hτ n m hm hα hγ
  · have h := hα.1
    rw [htop, sourceNotation, if_neg (lt_irrefl n)] at h
    simpa only [htop] using h
  · have h := hγ.1
    rw [htop, sourceNotation, if_neg (lt_irrefl n)] at h
    simpa only [htop] using h

end Alexander313.Wilken
