import Alexander313.Wilken.LowStarComparison

/-!
# A concrete finite-presentation measure for source support recursion

A collapsing argument may be larger than its value as an ordinal. The
recursion in Wilken Definition 2.9 therefore cannot be justified by
ordinary ordinal descent. We use the least size of an actual admissible
finite relative term denoting the ordinal. Such a term is constructed by
the already proved finite grammar, including the terminal convention.

Surviving canonical components of a high nonprincipal value have smaller
presentations. The unique argument of a higher principal θ value also has
a smaller presentation, even when its ordinal value is larger. Both facts
are proved by structural induction on actual admissible raw terms and
the canonical absorption law; raw leaf collection is never used.

This measure is semantic and noncomputable. It is not an effective public
code domain. Ordinal universe zero matches the existing relative-term
syntax. Every proof term is a candidate awaiting external compilation.
-/

namespace Alexander313.Wilken

theorem finiteNotation_terminal_lt (τ : Ordinal) (n : Nat) (hn : 0 < n)
    {ξ : Ordinal}
    (hξ : FiniteNotation (omegaSequence τ) (sourceFiniteCollapse τ n) n n ξ) :
    ξ < omegaSequence τ n := by
  have hclosed : Ordinal.IsPrincipal (· + ·) (omegaSequence τ n) := by
    cases n with
    | zero => omega
    | succ n => exact omegaSequence_add_closed τ n
  induction hξ with
  | parameter h => exact h
  | add _ _ ihξ ihη => exact hclosed ihξ ihη
  | collapse hnk hkn hsort _ ih => omega

/-- Actual presentations also exist at the terminal source level. -/
theorem sourceNotation_iff_relativeTerm_le (τ : Ordinal.{0}) (n r : Nat)
    (hr : 0 < r) (hrn : r ≤ n) (ξ : Ordinal.{0}) : sourceNotation τ n r ξ ↔
    ∃ t : SourceRelativeTerm τ r,
      RelativeTerm.Admissible (sourceParameters τ r) (omegaSequence τ)
        (sourceFiniteCollapse τ n) n r t ∧
      t.eval (sourceParameters τ r) (sourceFiniteCollapse τ n) = ξ := by
  by_cases hproper : r < n
  · exact sourceNotation_iff_relativeTerm τ n r hproper ξ
  · have hterminal : r = n := by omega
    subst r
    rw [sourceNotation, if_neg (lt_irrefl n)]
    constructor
    · intro hξ
      refine ⟨.parameter (Ordinal.ToType.mk ⟨ξ, hξ⟩), .parameter ?_, ?_⟩
      · exact sourceParameters_below τ n _
      · exact sourceParameters_mk τ n ξ hξ
    · rintro ⟨t, ht, rfl⟩
      exact finiteNotation_terminal_lt τ n hr ht.denote

theorem source_admissible_denote_le (τ : Ordinal.{0}) (n r : Nat)
    (hr : 0 < r) (hrn : r ≤ n) (t : SourceRelativeTerm τ r)
    (ht : RelativeTerm.Admissible (sourceParameters τ r) (omegaSequence τ)
      (sourceFiniteCollapse τ n) n r t) :
    sourceNotation τ n r (t.eval (sourceParameters τ r) (sourceFiniteCollapse τ n)) :=
  (sourceNotation_iff_relativeTerm_le τ n r hr hrn _).2 ⟨t, ht, rfl⟩

theorem sourceNotation_canonicalANF_le (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n r : Nat) (hrn : r ≤ n) {ξ a : Ordinal.{0}}
    (hξ : sourceNotation τ n r ξ) (ha : a ∈ canonicalANF ξ) :
    sourceNotation τ n r a := by
  by_cases hr : r < n
  · exact sourceNotation_canonicalANF τ hτ n r hr hξ ha
  · have hterminal : r = n := by omega
    subst r
    exact sourceNotation_terminal_canonicalANF τ n hξ ha

/-- A canonical surviving component has a presentation no larger than
the original tree. This does not preserve absorbed leaves. -/
theorem sourceRelativeTerm_component_witness (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n r : Nat) (t : SourceRelativeTerm τ r)
    (ht : RelativeTerm.Admissible (sourceParameters τ r) (omegaSequence τ)
      (sourceFiniteCollapse τ n) n r t) :
    ∀ a ∈ canonicalANF (t.eval (sourceParameters τ r) (sourceFiniteCollapse τ n)),
      ∃ s : SourceRelativeTerm τ r,
        RelativeTerm.Admissible (sourceParameters τ r) (omegaSequence τ)
          (sourceFiniteCollapse τ n) n r s ∧
        s.eval (sourceParameters τ r) (sourceFiniteCollapse τ n) = a ∧ s.size ≤ t.size := by
  induction ht with
  | @parameter p hp =>
    intro a ha
    have hbound := (canonicalANF_mem_le ha).trans_lt hp
    refine ⟨.parameter (Ordinal.ToType.mk ⟨a, hbound⟩),
      .parameter (sourceParameters_below τ r _), sourceParameters_mk τ r a hbound, ?_⟩
    exact le_rfl
  | @sum a b ha hb iha ihb =>
    intro p hp
    rcases canonicalANF_add_mem hp with hp | hp
    · obtain ⟨s, hs, hval, hsize⟩ := iha p hp
      exact ⟨s, hs, hval, hsize.trans (RelativeTerm.sum_left_size_lt a b).le⟩
    · obtain ⟨s, hs, hval, hsize⟩ := ihb p hp
      exact ⟨s, hs, hval, hsize.trans (RelativeTerm.sum_right_size_lt a b).le⟩
  | @theta k a hrk hkn hsort ha ih =>
    intro p hp
    have hanf := canonicalANF_principal
      (sourceFiniteCollapse_pos τ hτ n k hkn
        (a.eval (sourceParameters τ r) (sourceFiniteCollapse τ n)))
      (sourceFiniteCollapse_add_closed τ n k hkn
        (a.eval (sourceParameters τ r) (sourceFiniteCollapse τ n)))
    simp only [RelativeTerm.eval] at hp
    rw [hanf, List.mem_singleton] at hp
    refine ⟨.theta k a, .theta hrk hkn hsort ha, ?_, le_rfl⟩
    exact hp.symm

/-- A proper component of a value outside the parameter segment has a
strictly smaller finite presentation. -/
theorem sourceRelativeTerm_proper_component_witness (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n r : Nat) (t : SourceRelativeTerm τ r)
    (ht : RelativeTerm.Admissible (sourceParameters τ r) (omegaSequence τ)
      (sourceFiniteCollapse τ n) n r t)
    (hhigh : omegaSequence τ r ≤ t.eval (sourceParameters τ r) (sourceFiniteCollapse τ n))
    {a : Ordinal.{0}}
    (ha : a ∈ canonicalANF (t.eval (sourceParameters τ r) (sourceFiniteCollapse τ n)))
    (hne : a ≠ t.eval (sourceParameters τ r) (sourceFiniteCollapse τ n)) :
    ∃ s : SourceRelativeTerm τ r,
      RelativeTerm.Admissible (sourceParameters τ r) (omegaSequence τ)
        (sourceFiniteCollapse τ n) n r s ∧
      s.eval (sourceParameters τ r) (sourceFiniteCollapse τ n) = a ∧ s.size < t.size := by
  cases ht with
  | parameter hp => exact False.elim (hp.not_ge hhigh)
  | @sum x y hx hy =>
    rcases canonicalANF_add_mem ha with ha | ha
    · obtain ⟨s, hs, hval, hsize⟩ := sourceRelativeTerm_component_witness τ hτ n r x hx a ha
      exact ⟨s, hs, hval, hsize.trans_lt (RelativeTerm.sum_left_size_lt x y)⟩
    · obtain ⟨s, hs, hval, hsize⟩ := sourceRelativeTerm_component_witness τ hτ n r y hy a ha
      exact ⟨s, hs, hval, hsize.trans_lt (RelativeTerm.sum_right_size_lt x y)⟩
  | @theta k x hrk hkn hsort hx =>
    have hanf := canonicalANF_principal
      (sourceFiniteCollapse_pos τ hτ n k hkn
        (x.eval (sourceParameters τ r) (sourceFiniteCollapse τ n)))
      (sourceFiniteCollapse_add_closed τ n k hkn
        (x.eval (sourceParameters τ r) (sourceFiniteCollapse τ n)))
    simp only [RelativeTerm.eval] at ha
    rw [hanf, List.mem_singleton] at ha
    exact False.elim (hne ha)

/-- A higher θ component determines an actual smaller argument tree,
using level/argument uniqueness on the source-admissible domain. -/
theorem sourceRelativeTerm_higher_argument_witness (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n r : Nat) (hr : 0 < r) (hrn : r ≤ n) (t : SourceRelativeTerm τ r)
    (ht : RelativeTerm.Admissible (sourceParameters τ r) (omegaSequence τ)
      (sourceFiniteCollapse τ n) n r t) :
    ∀ k γ, r ≤ k → k < n → sourceNotation τ n r γ →
      γ < omegaSequence τ (k + 2) →
      sourceFiniteCollapse τ n k γ ∈
        canonicalANF (t.eval (sourceParameters τ r) (sourceFiniteCollapse τ n)) →
      ∃ s : SourceRelativeTerm τ r,
        RelativeTerm.Admissible (sourceParameters τ r) (omegaSequence τ)
          (sourceFiniteCollapse τ n) n r s ∧
        s.eval (sourceParameters τ r) (sourceFiniteCollapse τ n) = γ ∧ s.size < t.size := by
  induction ht with
  | @parameter p hp =>
    intro k γ hrk hkn hγ hsort hc
    have hsmall := (canonicalANF_mem_le hc).trans_lt hp
    have hlarge : omegaSequence τ r ≤ sourceFiniteCollapse τ n k γ :=
      ((omegaSequence_strictMono τ).monotone hrk).trans
        (sourceFiniteCollapse_bounds τ n k hkn γ).1
    exact False.elim (hsmall.not_ge hlarge)
  | @sum a b ha hb iha ihb =>
    intro k γ hrk hkn hγ hsort hc
    rcases canonicalANF_add_mem hc with hc | hc
    · obtain ⟨s, hs, hval, hsize⟩ := iha k γ hrk hkn hγ hsort hc
      exact ⟨s, hs, hval, hsize.trans (RelativeTerm.sum_left_size_lt a b)⟩
    · obtain ⟨s, hs, hval, hsize⟩ := ihb k γ hrk hkn hγ hsort hc
      exact ⟨s, hs, hval, hsize.trans (RelativeTerm.sum_right_size_lt a b)⟩
  | @theta l a hrl hln hsorta ha ih =>
    intro k γ hrk hkn hγ hsortγ hc
    have hanf := canonicalANF_principal
      (sourceFiniteCollapse_pos τ hτ n l hln
        (a.eval (sourceParameters τ r) (sourceFiniteCollapse τ n)))
      (sourceFiniteCollapse_add_closed τ n l hln
        (a.eval (sourceParameters τ r) (sourceFiniteCollapse τ n)))
    simp only [RelativeTerm.eval] at hc
    rw [hanf, List.mem_singleton] at hc
    have hsame := sourceFiniteCollapse_presentation_unique τ n r k l hrk hrl hkn hln
      hγ (source_admissible_denote_le τ n r hr hrn a ha) hsortγ hsorta hc
    exact ⟨a, ha, hsame.2.symm, RelativeTerm.theta_arg_size_lt l a⟩

abbrev SourceNotationOrdinal (τ : Ordinal.{0}) (n r : Nat) :=
  {ξ : Ordinal.{0} // sourceNotation τ n r ξ}

theorem source_presentation_size_exists (τ : Ordinal.{0}) (n r : Nat)
    (hr : 0 < r) (hrn : r ≤ n) (ξ : SourceNotationOrdinal τ n r) :
    ∃ j : Nat, ∃ t : SourceRelativeTerm τ r,
      RelativeTerm.Admissible (sourceParameters τ r) (omegaSequence τ)
        (sourceFiniteCollapse τ n) n r t ∧
      t.eval (sourceParameters τ r) (sourceFiniteCollapse τ n) = ξ.val ∧ t.size = j := by
  obtain ⟨t, ht, hval⟩ := (sourceNotation_iff_relativeTerm_le τ n r hr hrn ξ.val).1 ξ.property
  exact ⟨t.size, t, ht, hval, rfl⟩

noncomputable def leastPresentationSize (τ : Ordinal.{0}) (n r : Nat)
    (hr : 0 < r) (hrn : r ≤ n) (ξ : SourceNotationOrdinal τ n r) : Nat := by
  classical
  exact Nat.find (source_presentation_size_exists τ n r hr hrn ξ)

theorem leastPresentationSize_witness (τ : Ordinal.{0}) (n r : Nat)
    (hr : 0 < r) (hrn : r ≤ n) (ξ : SourceNotationOrdinal τ n r) :
    ∃ t : SourceRelativeTerm τ r,
      RelativeTerm.Admissible (sourceParameters τ r) (omegaSequence τ)
        (sourceFiniteCollapse τ n) n r t ∧
      t.eval (sourceParameters τ r) (sourceFiniteCollapse τ n) = ξ.val ∧
      t.size = leastPresentationSize τ n r hr hrn ξ := by
  classical
  exact Nat.find_spec (source_presentation_size_exists τ n r hr hrn ξ)

theorem leastPresentationSize_le (τ : Ordinal.{0}) (n r : Nat)
    (hr : 0 < r) (hrn : r ≤ n) (ξ : SourceNotationOrdinal τ n r)
    (t : SourceRelativeTerm τ r)
    (ht : RelativeTerm.Admissible (sourceParameters τ r) (omegaSequence τ)
      (sourceFiniteCollapse τ n) n r t)
    (hval : t.eval (sourceParameters τ r) (sourceFiniteCollapse τ n) = ξ.val) :
    leastPresentationSize τ n r hr hrn ξ ≤ t.size := by
  classical
  exact Nat.find_min' (source_presentation_size_exists τ n r hr hrn ξ) ⟨t, ht, hval, rfl⟩

theorem leastPresentationSize_component_lt (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n r : Nat) (hr : 0 < r) (hrn : r ≤ n)
    (ξ a : SourceNotationOrdinal τ n r) (hhigh : omegaSequence τ r ≤ ξ.val)
    (ha : a.val ∈ canonicalANF ξ.val) (hne : a.val ≠ ξ.val) :
    leastPresentationSize τ n r hr hrn a < leastPresentationSize τ n r hr hrn ξ := by
  obtain ⟨t, ht, hval, hsize⟩ := leastPresentationSize_witness τ n r hr hrn ξ
  obtain ⟨s, hs, hsval, hssize⟩ := sourceRelativeTerm_proper_component_witness τ hτ n r t ht
    (by simpa only [hval] using hhigh) (by simpa only [hval] using ha)
    (by simpa only [hval] using hne)
  exact (leastPresentationSize_le τ n r hr hrn a s hs hsval).trans_lt (hssize.trans_eq hsize)

theorem leastPresentationSize_theta_argument_lt (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n r : Nat) (hr : 0 < r) (hrn : r ≤ n) (k : Nat) (hrk : r ≤ k) (hkn : k < n)
    (ξ γ : SourceNotationOrdinal τ n r) (hsort : γ.val < omegaSequence τ (k + 2))
    (heq : ξ.val = sourceFiniteCollapse τ n k γ.val) :
    leastPresentationSize τ n r hr hrn γ < leastPresentationSize τ n r hr hrn ξ := by
  obtain ⟨t, ht, hval, hsize⟩ := leastPresentationSize_witness τ n r hr hrn ξ
  have hcomponent : sourceFiniteCollapse τ n k γ.val ∈
      canonicalANF (t.eval (sourceParameters τ r) (sourceFiniteCollapse τ n)) := by
    rw [hval, heq, canonicalANF_principal (sourceFiniteCollapse_pos τ hτ n k hkn γ.val)
      (sourceFiniteCollapse_add_closed τ n k hkn γ.val)]
    exact List.mem_singleton_self _
  obtain ⟨s, hs, hsval, hssize⟩ := sourceRelativeTerm_higher_argument_witness τ hτ n r hr hrn
    t ht k γ.val hrk hkn γ.property hsort hcomponent
  exact (leastPresentationSize_le τ n r hr hrn γ s hs hsval).trans_lt (hssize.trans_eq hsize)

/-- The actual support recursion order, justified by finite witnesses. -/
def presentationOrder (τ : Ordinal.{0}) (n r : Nat) (hr : 0 < r) (hrn : r ≤ n)
    (ξ η : SourceNotationOrdinal τ n r) : Prop :=
  leastPresentationSize τ n r hr hrn ξ < leastPresentationSize τ n r hr hrn η

theorem presentationOrder_wf (τ : Ordinal.{0}) (n r : Nat) (hr : 0 < r) (hrn : r ≤ n) :
    WellFounded (presentationOrder τ n r hr hrn) :=
  InvImage.wf (leastPresentationSize τ n r hr hrn) Nat.lt_wfRel.wf

end Alexander313.Wilken
