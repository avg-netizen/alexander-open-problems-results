import Alexander313.Wilken.FinitePresentationMeasure

/-!
# Actual finite source principal support

Wilken Definition 2.9 is constructed on Tⁿₘ₊₁, using the proved least
finite-presentation order. Low values stop at their canonical ANF. High
principal values recurse through their unique actual θ argument. High
nonprincipal values recurse through their canonical principal summands.

The θ presentation data below are constructed from the finite source
grammar, not supplied as a comparison or termination contract. The source
equations and independence from any admissible raw presentation are then
proved. This semantic construction is restricted to Ordinal universe zero
to match the existing raw syntax; it is noncomputable and does not yet
provide hereditary public codes. All proof terms await compilation.
-/

namespace Alexander313.Wilken

/-- A literal higher constructor together with its actual admissible
argument. Every instance used below is derived from the source grammar. -/
structure SourceHigherPresentation (τ : Ordinal.{0}) (n m : Nat)
    (ξ : SourceNotationOrdinal τ n (m + 1)) where
  level : Nat
  argument : SourceNotationOrdinal τ n (m + 1)
  lower : m + 1 ≤ level
  upper : level < n
  sort : argument.val < omegaSequence τ (level + 2)
  denote : ξ.val = sourceFiniteCollapse τ n level argument.val

theorem sourceHigherPresentation_nonempty (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (ξ : SourceNotationOrdinal τ n (m + 1))
    (hhigh : omegaSequence τ (m + 1) ≤ ξ.val)
    (hp : Ordinal.IsPrincipal (· + ·) ξ.val) :
    Nonempty (SourceHigherPresentation τ n m ξ) := by
  by_cases hr : m + 1 < n
  · have hpos : 0 < ξ.val :=
      (hτ.trans_le ((omegaSequence_strictMono τ).monotone (Nat.zero_le (m + 1)))).trans_le hhigh
    rcases sourceNotation_principal_cases τ hτ n (m + 1) hr ξ.property hpos hp with
      hsmall | ⟨k, γ, hmk, hkn, hγ, hsort, heq⟩
    · exact False.elim (hsmall.not_ge hhigh)
    · exact ⟨⟨k, ⟨γ, hγ⟩, hmk, hkn, hsort, heq⟩⟩
  · have hterminal : m + 1 = n := by omega
    have hsmall := ξ.property
    simp only [sourceNotation, if_neg hr] at hsmall
    exact False.elim (hsmall.not_ge hhigh)

noncomputable def sourceHigherPresentation (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (ξ : SourceNotationOrdinal τ n (m + 1))
    (hhigh : omegaSequence τ (m + 1) ≤ ξ.val)
    (hp : Ordinal.IsPrincipal (· + ·) ξ.val) : SourceHigherPresentation τ n m ξ :=
  Classical.choice (sourceHigherPresentation_nonempty τ hτ n m hm ξ hhigh hp)

theorem sourceHigherPresentation_order (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (ξ : SourceNotationOrdinal τ n (m + 1))
    (p : SourceHigherPresentation τ n m ξ) :
    presentationOrder τ n (m + 1) (Nat.succ_pos m) (Nat.succ_le_of_lt hm) p.argument ξ :=
  leastPresentationSize_theta_argument_lt τ hτ n (m + 1) (Nat.succ_pos m)
    (Nat.succ_le_of_lt hm) p.level p.lower p.upper ξ p.argument p.sort p.denote

theorem sourceHigherPresentation_unique (τ : Ordinal.{0}) (n m : Nat)
    (ξ : SourceNotationOrdinal τ n (m + 1))
    (p q : SourceHigherPresentation τ n m ξ) : p.level = q.level ∧ p.argument = q.argument := by
  have hsame := sourceFiniteCollapse_presentation_unique τ n (m + 1) p.level q.level
    p.lower q.lower p.upper q.upper p.argument.property q.argument.property p.sort q.sort
    (p.denote.symm.trans q.denote)
  exact ⟨hsame.1, Subtype.ext hsame.2⟩

/-- The actual source-domain element represented by a canonical atom. -/
def sourceComponent (τ : Ordinal.{0}) (hτ : 0 < τ) (n m : Nat) (hm : m < n)
    (ξ : SourceNotationOrdinal τ n (m + 1)) (a : Ordinal.{0})
    (ha : a ∈ canonicalANF ξ.val) : SourceNotationOrdinal τ n (m + 1) :=
  ⟨a, sourceNotation_canonicalANF_le τ hτ n (m + 1) (Nat.succ_le_of_lt hm) ξ.property ha⟩

theorem sourceComponent_order (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (ξ : SourceNotationOrdinal τ n (m + 1))
    (hhigh : omegaSequence τ (m + 1) ≤ ξ.val)
    (hnp : ¬ Ordinal.IsPrincipal (· + ·) ξ.val) (a : Ordinal.{0})
    (ha : a ∈ canonicalANF ξ.val) :
    presentationOrder τ n (m + 1) (Nat.succ_pos m) (Nat.succ_le_of_lt hm)
      (sourceComponent τ hτ n m hm ξ a ha) ξ := by
  apply leastPresentationSize_component_lt τ hτ n (m + 1) (Nat.succ_pos m)
    (Nat.succ_le_of_lt hm) ξ (sourceComponent τ hτ n m hm ξ a ha) hhigh ha
  intro heq
  change a = ξ.val at heq
  have hatom := (canonicalANF_normal ξ.val).1 a ha
  have hp : Ordinal.IsPrincipal (· + ·) ξ.val := by simpa only [heq] using hatom.2
  exact hnp hp

noncomputable def sourceSupportStep (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (ξ : SourceNotationOrdinal τ n (m + 1))
    (ih : ∀ η, presentationOrder τ n (m + 1) (Nat.succ_pos m)
      (Nat.succ_le_of_lt hm) η ξ → Finset Ordinal.{0}) : Finset Ordinal.{0} := by
  classical
  exact if hlow : ξ.val < omegaSequence τ (m + 1) then (canonicalANF ξ.val).toFinset
    else if hp : Ordinal.IsPrincipal (· + ·) ξ.val then
      let p := sourceHigherPresentation τ hτ n m hm ξ (le_of_not_gt hlow) hp
      ih p.argument (sourceHigherPresentation_order τ hτ n m hm ξ p)
    else
      (canonicalANF ξ.val).toFinset.attach.biUnion (fun a =>
        ih (sourceComponent τ hτ n m hm ξ a.val (List.mem_toFinset.1 a.property))
          (sourceComponent_order τ hτ n m hm ξ (le_of_not_gt hlow) hp
            a.val (List.mem_toFinset.1 a.property)))

/-- Pⁿₘ is an actual function on the semantic finite source domain. -/
noncomputable def sourceP (τ : Ordinal.{0}) (hτ : 0 < τ) (n m : Nat) (hm : m < n)
    (ξ : SourceNotationOrdinal τ n (m + 1)) : Finset Ordinal.{0} :=
  (presentationOrder_wf τ n (m + 1) (Nat.succ_pos m) (Nat.succ_le_of_lt hm)).fix
    (sourceSupportStep τ hτ n m hm) ξ

theorem sourceP_eq (τ : Ordinal.{0}) (hτ : 0 < τ) (n m : Nat) (hm : m < n)
    (ξ : SourceNotationOrdinal τ n (m + 1)) :
    sourceP τ hτ n m hm ξ = sourceSupportStep τ hτ n m hm ξ
      (fun η _ => sourceP τ hτ n m hm η) := by
  unfold sourceP
  rw [WellFounded.fix_eq]

/-- The literal low clause of Definition 2.9. -/
theorem sourceP_low (τ : Ordinal.{0}) (hτ : 0 < τ) (n m : Nat) (hm : m < n)
    (ξ : SourceNotationOrdinal τ n (m + 1)) (hlow : ξ.val < omegaSequence τ (m + 1)) :
    sourceP τ hτ n m hm ξ = (canonicalANF ξ.val).toFinset := by
  classical
  rw [sourceP_eq, sourceSupportStep, dif_pos hlow]

theorem sourceP_principal (τ : Ordinal.{0}) (hτ : 0 < τ) (n m : Nat) (hm : m < n)
    (ξ : SourceNotationOrdinal τ n (m + 1)) (hhigh : omegaSequence τ (m + 1) ≤ ξ.val)
    (hp : Ordinal.IsPrincipal (· + ·) ξ.val) :
    sourceP τ hτ n m hm ξ = sourceP τ hτ n m hm
      (sourceHigherPresentation τ hτ n m hm ξ hhigh hp).argument := by
  classical
  rw [sourceP_eq, sourceSupportStep, dif_neg (not_lt_of_ge hhigh), dif_pos hp]

theorem sourceP_nonprincipal (τ : Ordinal.{0}) (hτ : 0 < τ) (n m : Nat) (hm : m < n)
    (ξ : SourceNotationOrdinal τ n (m + 1)) (hhigh : omegaSequence τ (m + 1) ≤ ξ.val)
    (hnp : ¬ Ordinal.IsPrincipal (· + ·) ξ.val) :
    sourceP τ hτ n m hm ξ = (canonicalANF ξ.val).toFinset.attach.biUnion (fun a =>
      sourceP τ hτ n m hm
        (sourceComponent τ hτ n m hm ξ a.val (List.mem_toFinset.1 a.property))) := by
  classical
  rw [sourceP_eq, sourceSupportStep, dif_neg (not_lt_of_ge hhigh), dif_neg hnp]

/-- The higher-θ clause is independent of the selected presentation,
because both its level and actual admissible argument are unique. -/
theorem sourceP_theta (τ : Ordinal.{0}) (hτ : 0 < τ) (n m : Nat) (hm : m < n)
    (ξ γ : SourceNotationOrdinal τ n (m + 1)) (k : Nat)
    (hmk : m < k) (hkn : k < n) (hsort : γ.val < omegaSequence τ (k + 2))
    (heq : ξ.val = sourceFiniteCollapse τ n k γ.val) :
    sourceP τ hτ n m hm ξ = sourceP τ hτ n m hm γ := by
  have hhigh : omegaSequence τ (m + 1) ≤ ξ.val := by
    rw [heq]
    exact ((omegaSequence_strictMono τ).monotone (Nat.succ_le_of_lt hmk)).trans
      (sourceFiniteCollapse_bounds τ n k hkn γ.val).1
  have hp : Ordinal.IsPrincipal (· + ·) ξ.val := by
    rw [heq]
    exact sourceFiniteCollapse_add_closed τ n k hkn γ.val
  let p := sourceHigherPresentation τ hτ n m hm ξ hhigh hp
  let q : SourceHigherPresentation τ n m ξ :=
    ⟨k, γ, Nat.succ_le_of_lt hmk, hkn, hsort, heq⟩
  have hsame := (sourceHigherPresentation_unique τ n m ξ p q).2
  rw [sourceP_principal τ hτ n m hm ξ hhigh hp]
  exact congrArg (sourceP τ hτ n m hm) hsame

/-- Support is the union of the supports of its canonical principal
atoms. This also proves the boundary case ξ=Ωₘ₊₁ without a raw spelling. -/
theorem sourceP_mem_anf (τ : Ordinal.{0}) (hτ : 0 < τ) (n m : Nat) (hm : m < n)
    (ξ : SourceNotationOrdinal τ n (m + 1)) (p : Ordinal.{0}) :
    p ∈ sourceP τ hτ n m hm ξ ↔
      ∃ a, ∃ ha : a ∈ canonicalANF ξ.val,
        p ∈ sourceP τ hτ n m hm (sourceComponent τ hτ n m hm ξ a ha) := by
  classical
  by_cases hlow : ξ.val < omegaSequence τ (m + 1)
  · rw [sourceP_low τ hτ n m hm ξ hlow, List.mem_toFinset]
    constructor
    · intro hp
      refine ⟨p, hp, ?_⟩
      have hsmall : (sourceComponent τ hτ n m hm ξ p hp).val < omegaSequence τ (m + 1) :=
        (canonicalANF_mem_le hp).trans_lt hlow
      have hatom := (canonicalANF_normal ξ.val).1 p hp
      rw [sourceP_low τ hτ n m hm _ hsmall, sourceComponent, canonicalANF_principal hatom.1 hatom.2]
      exact List.mem_toFinset.2 (List.mem_singleton_self _)
    · rintro ⟨a, ha, hp⟩
      have hsmall : (sourceComponent τ hτ n m hm ξ a ha).val < omegaSequence τ (m + 1) :=
        (canonicalANF_mem_le ha).trans_lt hlow
      have hatom := (canonicalANF_normal ξ.val).1 a ha
      rw [sourceP_low τ hτ n m hm _ hsmall, sourceComponent, canonicalANF_principal hatom.1 hatom.2,
        List.mem_toFinset, List.mem_singleton] at hp
      simpa only [hp] using ha
  · by_cases hprincipal : Ordinal.IsPrincipal (· + ·) ξ.val
    · have hpos : 0 < ξ.val :=
        (hτ.trans_le ((omegaSequence_strictMono τ).monotone (Nat.zero_le (m + 1)))).trans_le
          (le_of_not_gt hlow)
      have hanf := canonicalANF_principal hpos hprincipal
      constructor
      · intro hp
        refine ⟨ξ.val, ?_, ?_⟩
        · rw [hanf]; exact List.mem_singleton_self _
        · exact hp
      · rintro ⟨a, ha, hp⟩
        rw [hanf, List.mem_singleton] at ha
        subst a
        exact hp
    · rw [sourceP_nonprincipal τ hτ n m hm ξ (le_of_not_gt hlow) hprincipal,
        Finset.mem_biUnion]
      constructor
      · rintro ⟨a, ha, hp⟩
        exact ⟨a.val, List.mem_toFinset.1 a.property, hp⟩
      · rintro ⟨a, ha, hp⟩
        exact ⟨⟨a, List.mem_toFinset.2 ha⟩, Finset.mem_attach _ _, hp⟩

/-- The normal-addition clause of Definition 2.9. The hypothesis is the
literal ANF condition, whose arithmetic meaning was proved previously. -/
theorem sourceP_add_normal (τ : Ordinal.{0}) (hτ : 0 < τ) (n m : Nat) (hm : m < n)
    (ξ α β : SourceNotationOrdinal τ n (m + 1))
    (heq : ξ.val = α.val + β.val)
    (hnormal : IsAdditiveNormalForm (canonicalANF α.val ++ canonicalANF β.val)) :
    sourceP τ hτ n m hm ξ = sourceP τ hτ n m hm α ∪ sourceP τ hτ n m hm β := by
  classical
  have hanf : canonicalANF ξ.val = canonicalANF α.val ++ canonicalANF β.val := by
    apply canonicalANF_eq_of_normal hnormal
    rw [principalSum_append, principalSum_canonicalANF, principalSum_canonicalANF]
    exact heq.symm
  ext p
  constructor
  · intro hp
    obtain ⟨a, ha, hp⟩ := (sourceP_mem_anf τ hτ n m hm ξ p).1 hp
    have hmem : a ∈ canonicalANF α.val ∨ a ∈ canonicalANF β.val := by
      rw [hanf] at ha
      exact List.mem_append.1 ha
    rcases hmem with hα | hβ
    · exact Finset.mem_union.2 (Or.inl ((sourceP_mem_anf τ hτ n m hm α p).2 ⟨a, hα, hp⟩))
    · exact Finset.mem_union.2 (Or.inr ((sourceP_mem_anf τ hτ n m hm β p).2 ⟨a, hβ, hp⟩))
  · intro hp
    rcases Finset.mem_union.1 hp with hp | hp
    · obtain ⟨a, ha, hp⟩ := (sourceP_mem_anf τ hτ n m hm α p).1 hp
      have hmem : a ∈ canonicalANF ξ.val := by rw [hanf]; exact List.mem_append_left _ ha
      exact (sourceP_mem_anf τ hτ n m hm ξ p).2 ⟨a, hmem, hp⟩
    · obtain ⟨a, ha, hp⟩ := (sourceP_mem_anf τ hτ n m hm β p).1 hp
      have hmem : a ∈ canonicalANF ξ.val := by rw [hanf]; exact List.mem_append_right _ ha
      exact (sourceP_mem_anf τ hτ n m hm ξ p).2 ⟨a, hmem, hp⟩

/-- The paper's `ξ =NF α + β` means that β is the final principal
summand, and α is the sum of the preceding ANF list (p. 7). It includes
the stipulated ξ=α=β=0 case. This is stricter than arbitrary absorption
free binary addition and records the exact source convention. -/
def SourceNormalSum (ξ α β : Ordinal.{0}) : Prop :=
  (ξ = 0 ∧ α = 0 ∧ β = 0) ∨
    ∃ xs : List Ordinal.{0}, IsAdditiveNormalForm (xs ++ [β]) ∧
      principalSum xs = α ∧ principalSum (xs ++ [β]) = ξ

theorem sourceNormalSum_eq_add {ξ α β : Ordinal.{0}} (h : SourceNormalSum ξ α β) :
    ξ = α + β := by
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨xs, hxs, hα, hξ⟩
  · simp
  · rw [← hξ, principalSum_append, hα]
    simp [principalSum]

theorem sourceNormalSum_canonical_concat {ξ α β : Ordinal.{0}}
    (h : SourceNormalSum ξ α β) :
    IsAdditiveNormalForm (canonicalANF α ++ canonicalANF β) := by
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨xs, hxs, hα, hξ⟩
  · simpa only [canonicalANF_zero, List.nil_append] using additiveNormalForm_nil
  · have hprefix : IsAdditiveNormalForm xs :=
      ⟨fun a ha => hxs.1 a (List.mem_append_left _ ha),
        (List.pairwise_append.1 hxs.2).1⟩
    have hlast := hxs.1 β (List.mem_append_right _ (List.mem_singleton_self _))
    rw [canonicalANF_eq_of_normal hprefix hα, canonicalANF_principal hlast.1 hlast.2]
    exact hxs

/-- The literal normal-addition clause in Definition 2.9, using the
paper's final-principal-summand convention rather than a raw sum tree. -/
theorem sourceP_source_normal_add (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (ξ α β : SourceNotationOrdinal τ n (m + 1))
    (h : SourceNormalSum ξ.val α.val β.val) :
    sourceP τ hτ n m hm ξ = sourceP τ hτ n m hm α ∪ sourceP τ hτ n m hm β :=
  sourceP_add_normal τ hτ n m hm ξ α β (sourceNormalSum_eq_add h)
    (sourceNormalSum_canonical_concat h)

/-- The constructed P is a finite subset of the next parameter segment,
as required by Definition 2.9. -/
theorem sourceP_below (τ : Ordinal.{0}) (hτ : 0 < τ) (n m : Nat) (hm : m < n)
    (ξ : SourceNotationOrdinal τ n (m + 1)) :
    ∀ p ∈ sourceP τ hτ n m hm ξ, p < omegaSequence τ (m + 1) := by
  classical
  refine (presentationOrder_wf τ n (m + 1) (Nat.succ_pos m) (Nat.succ_le_of_lt hm)).induction ξ
    (C := fun ξ => ∀ p ∈ sourceP τ hτ n m hm ξ, p < omegaSequence τ (m + 1)) ?_
  intro ξ ih p hp
  by_cases hlow : ξ.val < omegaSequence τ (m + 1)
  · rw [sourceP_low τ hτ n m hm ξ hlow, List.mem_toFinset] at hp
    exact (canonicalANF_mem_le hp).trans_lt hlow
  · by_cases hprincipal : Ordinal.IsPrincipal (· + ·) ξ.val
    · let q := sourceHigherPresentation τ hτ n m hm ξ (le_of_not_gt hlow) hprincipal
      rw [sourceP_principal τ hτ n m hm ξ (le_of_not_gt hlow) hprincipal] at hp
      exact ih q.argument (sourceHigherPresentation_order τ hτ n m hm ξ q) p hp
    · rw [sourceP_nonprincipal τ hτ n m hm ξ (le_of_not_gt hlow) hprincipal,
        Finset.mem_biUnion] at hp
      obtain ⟨a, ha, hp⟩ := hp
      exact ih (sourceComponent τ hτ n m hm ξ a.val (List.mem_toFinset.1 a.property))
        (sourceComponent_order τ hτ n m hm ξ (le_of_not_gt hlow) hprincipal
          a.val (List.mem_toFinset.1 a.property)) p hp

/-- Equality of denoted ordinals makes support equal, independently of
the size or spelling of the two admissible raw presentations. -/
theorem sourceP_presentation_independent (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (s t : SourceRelativeTerm τ (m + 1))
    (hs : RelativeTerm.Admissible (sourceParameters τ (m + 1)) (omegaSequence τ)
      (sourceFiniteCollapse τ n) n (m + 1) s)
    (ht : RelativeTerm.Admissible (sourceParameters τ (m + 1)) (omegaSequence τ)
      (sourceFiniteCollapse τ n) n (m + 1) t)
    (heq : s.eval (sourceParameters τ (m + 1)) (sourceFiniteCollapse τ n) =
      t.eval (sourceParameters τ (m + 1)) (sourceFiniteCollapse τ n)) :
    sourceP τ hτ n m hm
        ⟨_, source_admissible_denote_le τ n (m + 1) (Nat.succ_pos m) (Nat.succ_le_of_lt hm) s hs⟩ =
      sourceP τ hτ n m hm
        ⟨_, source_admissible_denote_le τ n (m + 1) (Nat.succ_pos m) (Nat.succ_le_of_lt hm) t ht⟩ :=
  congrArg (sourceP τ hτ n m hm) (Subtype.ext heq)

end Alexander313.Wilken
