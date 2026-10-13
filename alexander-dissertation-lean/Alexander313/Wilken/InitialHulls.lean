import Alexander313.Wilken.SourceStarComparison

/-!
# Actual initial-segment hulls and star parameters

Wilken Lemma 2.11(b) is proved using a first missing ordinal q and the
least included ordinal ζ at or above q. Addition makes q principal.
Canonical decomposition makes ζ principal, and the actual hull grammar
makes ζ a local θ value. Its support belongs to the hull and is strictly
below ζ. Minimality therefore puts all support below q, producing a
genuine collapse candidate q and contradicting q<ζ.

The initial-segment endpoint is the already constructed cardinal-bounded
hull closure supremum. It then supplies the candidate needed to prove
Lemma 2.11(a): the star-successor hull equals the collapse-parameter hull.
No initial-segment or hull-equality contract is assumed. All terms are
uncompiled candidates; effective syntax and direct limits remain separate.
-/

namespace Alexander313.Wilken

open Order

/-- The first missing ordinal of any addition-closed hull is additive
principal. This uses actual ordinal subtraction to split a proposed sum
crossing the gap, and does not assume decomposition closure. -/
theorem hull_first_gap_principal {omega : Nat → Ordinal}
    {theta : Nat → Ordinal → Ordinal} {n m : Nat} {α β q : Ordinal}
    (hsmall : ∀ a < q, Hull omega theta n m α β a)
    (hgap : ¬ Hull omega theta n m α β q) : Ordinal.IsPrincipal (· + ·) q := by
  intro a b ha hb
  apply lt_of_not_ge
  intro hsum
  have hdiff : q - a < q := (Ordinal.sub_le.2 hsum).trans_lt hb
  have hq := Hull.add (hsmall a ha) (hsmall (q - a) hdiff)
  have heq := Ordinal.add_sub_cancel_of_le ha.le
  exact hgap (by simpa only [heq] using hq)

/-- A small canonical principal component of an actual source hull is
a seed or an actual local collapsing call. Higher outputs cannot be
small, by their constructed cardinal bounds. -/
theorem source_hull_small_atom_cases (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (α β : Ordinal.{0}) {ξ : Ordinal.{0}}
    (hξ : Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α β ξ) :
    ∀ a ∈ canonicalANF ξ, a < omegaSequence τ (m + 1) →
      a < omegaSequence τ m ∨ a < β ∨
        ∃ γ, γ < α ∧ Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α β γ ∧
          a = sourceFiniteCollapse τ n m γ := by
  induction hξ with
  | below_base hξ =>
    intro a ha hsmall
    exact Or.inl ((canonicalANF_mem_le ha).trans_lt hξ)
  | below_parameter hξ =>
    intro a ha hsmall
    exact Or.inr (Or.inl ((canonicalANF_mem_le ha).trans_lt hξ))
  | add hξ hη ihξ ihη =>
    intro a ha hsmall
    exact (canonicalANF_add_mem ha).elim (fun ha => ihξ a ha hsmall) (fun ha => ihη a ha hsmall)
  | @higher k γ hmk hkn hsort hγ ih =>
    intro a ha hsmall
    have hanf := canonicalANF_principal
      (sourceFiniteCollapse_pos τ hτ n k hkn γ)
      (sourceFiniteCollapse_add_closed τ n k hkn γ)
    rw [hanf, List.mem_singleton] at ha
    subst a
    have hlarge : omegaSequence τ (m + 1) ≤ sourceFiniteCollapse τ n k γ :=
      ((omegaSequence_strictMono τ).monotone (Nat.succ_le_of_lt hmk)).trans
        (sourceFiniteCollapse_bounds τ n k hkn γ).1
    exact False.elim (hsmall.not_ge hlarge)
  | @«local» γ hγα hγ ih =>
    intro a ha hsmall
    have hanf := canonicalANF_principal
      (sourceFiniteCollapse_pos τ hτ n m hm γ)
      (sourceFiniteCollapse_add_closed τ n m hm γ)
    rw [hanf, List.mem_singleton] at ha
    exact Or.inr (Or.inr ⟨γ, hγα, hγ, ha⟩)

/-- Lemma 2.11(b), expressed as actual downward closure below Ωₘ₊₁. -/
theorem source_hull_initial_segment (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (α β : Ordinal.{0})
    (hα : α ≤ omegaSequence τ (m + 2)) (hβ : β < omegaSequence τ (m + 1))
    {ξ η : Ordinal.{0}}
    (hξ : Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α β ξ)
    (hξsmall : ξ < omegaSequence τ (m + 1)) (hηξ : η < ξ) :
    Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α β η := by
  classical
  by_contra hη
  let missing : Set Ordinal.{0} :=
    {q | q < ξ ∧ ¬ Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α β q}
  have hmissing : missing.Nonempty := ⟨η, hηξ, hη⟩
  let q := sInf missing
  have hq : q < ξ ∧ ¬ Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α β q :=
    csInf_mem hmissing
  have hqsmall : q < omegaSequence τ (m + 1) := hq.1.trans hξsmall
  have hbelowq : ∀ a < q,
      Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α β a := by
    intro a haq
    by_contra ha
    have hqa : q ≤ a := csInf_le' (show a ∈ missing from ⟨haq.trans hq.1, ha⟩)
    exact haq.not_ge hqa
  have hbaseq : omegaSequence τ m ≤ q := by
    apply le_of_not_gt
    intro h
    exact hq.2 (.below_base h)
  have hβq : β ≤ q := by
    apply le_of_not_gt
    intro h
    exact hq.2 (.below_parameter h)
  have hqpos : 0 < q :=
    (hτ.trans_le ((omegaSequence_strictMono τ).monotone (Nat.zero_le m))).trans_le hbaseq
  have hqprincipal := hull_first_gap_principal hbelowq hq.2
  let included : Set Ordinal.{0} :=
    {ζ | q ≤ ζ ∧ Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α β ζ ∧
      ζ < omegaSequence τ (m + 1)}
  have hincluded : included.Nonempty := ⟨ξ, hq.1.le, hξ, hξsmall⟩
  let ζ := sInf included
  have hζ : q ≤ ζ ∧ Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α β ζ ∧
      ζ < omegaSequence τ (m + 1) := csInf_mem hincluded
  have hqne : q ≠ ζ := by
    intro heq
    exact hq.2 (by simpa only [← heq] using hζ.2.1)
  have hqζ : q < ζ := lt_of_le_of_ne hζ.1 hqne
  have hζpos : 0 < ζ := hqpos.trans_le hζ.1
  have hhighatom : ∃ a ∈ canonicalANF ζ, q ≤ a := by
    by_contra hnone
    have hatoms : ∀ a ∈ canonicalANF ζ, a < q := by
      intro a ha
      apply lt_of_not_ge
      intro hqa
      exact hnone ⟨a, ha, hqa⟩
    have hsum := principalSum_lt hqpos hqprincipal (canonicalANF ζ) hatoms
    rw [principalSum_canonicalANF] at hsum
    exact hsum.not_ge hζ.1
  obtain ⟨a, ha, hqa⟩ := hhighatom
  have haHull := source_hull_canonicalANF τ hτ n m hm α β hζ.2.1 a ha
  have hasmall : a < omegaSequence τ (m + 1) := (canonicalANF_mem_le ha).trans_lt hζ.2.2
  have hζa : ζ ≤ a := csInf_le' (show a ∈ included from ⟨hqa, haHull, hasmall⟩)
  have hae : a = ζ := le_antisymm (canonicalANF_mem_le ha) hζa
  have hζprincipal : Ordinal.IsPrincipal (· + ·) ζ := by
    simpa only [hae] using ((canonicalANF_normal ζ).1 a ha).2
  have hself : ζ ∈ canonicalANF ζ := by
    rw [canonicalANF_principal hζpos hζprincipal]
    exact List.mem_singleton_self _
  rcases source_hull_small_atom_cases τ hτ n m hm α β hζ.2.1 ζ hself hζ.2.2 with
    hseed | hseed | ⟨γ, hγα, hγHull, hζθ⟩
  · exact hseed.not_ge (hbaseq.trans hζ.1)
  · exact hseed.not_ge (hβq.trans hζ.1)
  · have hγnotation : sourceNotation τ n (m + 1) γ :=
      (source_nextNotation_iff_hull τ n m hm γ).2
        (source_hull_to_admissible τ n m hm hα hβ.le hγHull)
    let γdomain : SourceNotationOrdinal τ n (m + 1) := ⟨γ, hγnotation⟩
    have hγsort : γ < omegaSequence τ (m + 2) := hγα.trans_le hα
    have hsupportHull := (source_hull_iff_sourceP τ hτ n m hm α β hα hβ.le γdomain).1 hγHull
    have hsupportζ : ∀ p ∈ sourceP τ hτ n m hm γdomain, p < ζ := by
      have hstar := sourceStar_lt_sourceFiniteCollapse τ hτ n m hm γdomain hγsort
      have hall := (sourceStar_lt_iff τ hτ n m hm γdomain
        (sourceFiniteCollapse τ n m γ) (sourceFiniteCollapse_pos τ hτ n m hm γ)
        (sourceFiniteCollapse_bounds τ n m hm γ).1).1 hstar
      intro p hp
      simpa only [← hζθ] using hall p hp
    have hsupportq : ∀ p ∈ sourceP τ hτ n m hm γdomain, p < q := by
      intro p hp
      apply lt_of_not_ge
      intro hqp
      have hζp : ζ ≤ p := csInf_le'
        (show p ∈ included from ⟨hqp, hsupportHull p hp, sourceP_below τ hτ n m hm γdomain p hp⟩)
      exact (hsupportζ p hp).not_ge hζp
    have hγOwn : Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m γ q γ :=
      (source_hull_iff_sourceP τ hτ n m hm γ q hγsort.le hqsmall.le γdomain).2
        (fun p hp => .below_parameter (hsupportq p hp))
    have hqθ : q ≤ sourceFiniteCollapse τ n m γ := by rw [← hζθ]; exact hζ.1
    have hcandidate : CollapseCandidate (omegaSequence τ) (sourceFiniteCollapse τ n) n m γ q := by
      refine ⟨hqsmall, ?_, hγOwn⟩
      intro x hx hxsmall
      have hin := hull_absorb hbelowq (hull_mono hγα.le le_rfl hx)
      have hxθ := (finiteCollapse_hull_initial hm γ x).1
        ⟨hull_mono le_rfl hqθ hx, hxsmall⟩
      have hxζ : x < ζ := by
        change x < sourceFiniteCollapse τ n m γ at hxθ
        simpa only [← hζθ] using hxθ
      apply lt_of_not_ge
      intro hqx
      have hζx : ζ ≤ x := csInf_le' (show x ∈ included from ⟨hqx, hin, hxsmall⟩)
      exact hxζ.not_ge hζx
    have hminimum : sourceFiniteCollapse τ n m γ ≤ q := finiteCollapse_minimal hm hcandidate
    have hζq : ζ ≤ q := by simpa only [← hζθ] using hminimum
    exact hqζ.not_ge hζq

/-- The actual ordinal endpoint of the low part of each hull is the
cardinal-bounded closure supremum already constructed in ProperCollapse. -/
theorem source_hull_initial_bound_iff (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (α β : Ordinal.{0})
    (hα : α ≤ omegaSequence τ (m + 2)) (hβ : β < omegaSequence τ (m + 1))
    (ξ : Ordinal.{0}) :
    (Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α β ξ ∧
        ξ < omegaSequence τ (m + 1)) ↔
      ξ < hullClosureBound τ (sourceFiniteCollapse τ n) n m α β := by
  classical
  constructor
  · rintro ⟨hξ, hsmall⟩
    exact add_one_le_iff.1 (hullClosureBound_contains τ (sourceFiniteCollapse τ n)
      n m α β ξ hξ hsmall)
  · intro hξ
    have hbound := hullClosureBound_lt τ (sourceFiniteCollapse τ n) n m α β hβ
    have hsmall := hξ.trans hbound
    have hz := source_hull_zero τ hτ n m α β
    have hzsmall : (0 : Ordinal.{0}) < omegaSequence τ (m + 1) :=
      (omegaSequence_isSuccLimit τ m).bot_lt
    have hnonempty : ((fun x : Ordinal.{0} => x + 1) ''
        smallHull τ (sourceFiniteCollapse τ n) n m α β).Nonempty :=
      ⟨0 + 1, 0, ⟨hz, hzsmall⟩, rfl⟩
    have hex : ∃ η, Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α β η ∧
        η < omegaSequence τ (m + 1) ∧ ξ ≤ η := by
      by_contra hnone
      have hsup : hullClosureBound τ (sourceFiniteCollapse τ n) n m α β ≤ ξ := by
        apply csSup_le hnonempty
        rintro x ⟨η, hη, rfl⟩
        apply add_one_le_of_lt
        apply lt_of_not_ge
        intro hξη
        exact hnone ⟨η, hη.1, hη.2, hξη⟩
      exact hξ.not_ge hsup
    obtain ⟨η, hη, hηsmall, hξη⟩ := hex
    refine ⟨?_, hsmall⟩
    rcases hξη.eq_or_lt with heq | hlt
    · simpa only [heq] using hη
    · exact source_hull_initial_segment τ hτ n m hm α β hα hβ hη hηsmall hlt

/-- The low part of the source hull is an actual ordinal below the next
cardinal, not merely a set stipulated to be an initial segment. -/
theorem source_hull_has_ordinal_segment (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (α β : Ordinal.{0})
    (hα : α ≤ omegaSequence τ (m + 2)) (hβ : β < omegaSequence τ (m + 1)) :
    ∃ δ < omegaSequence τ (m + 1), ∀ ξ,
      (Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α β ξ ∧
        ξ < omegaSequence τ (m + 1)) ↔ ξ < δ :=
  ⟨hullClosureBound τ (sourceFiniteCollapse τ n) n m α β,
    hullClosureBound_lt τ (sourceFiniteCollapse τ n) n m α β hβ,
    source_hull_initial_bound_iff τ hτ n m hm α β hα hβ⟩

/-- Full Lemma 2.11(a): the actual star-successor parameter gives exactly
the same hull as the constructed collapsing value. -/
theorem source_hull_star_successor_iff_collapse (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (α : SourceNotationOrdinal τ n (m + 1))
    (hsort : α.val < omegaSequence τ (m + 2)) (ξ : Ordinal.{0}) :
    Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α.val
        (sourceStar τ hτ n m hm α + 1) ξ ↔
      Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α.val
        (sourceFiniteCollapse τ n m α.val) ξ := by
  classical
  let σ := sourceStar τ hτ n m hm α
  let δ := hullClosureBound τ (sourceFiniteCollapse τ n) n m α.val (σ + 1)
  have hstarθ : σ < sourceFiniteCollapse τ n m α.val :=
    sourceStar_lt_sourceFiniteCollapse τ hτ n m hm α hsort
  have hproper := sourceFiniteCollapse_proper_notation τ n m hm α.val hsort α.property
  have hstarSmall : σ < omegaSequence τ (m + 1) := hstarθ.trans hproper
  have hparameterSmall : σ + 1 < omegaSequence τ (m + 1) :=
    (omegaSequence_isSuccLimit τ m).add_one_lt hstarSmall
  have hparameterθ : σ + 1 ≤ sourceFiniteCollapse τ n m α.val := add_one_le_of_lt hstarθ
  have harg : Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α.val (σ + 1) α.val := by
    apply (source_hull_iff_sourceP τ hτ n m hm α.val (σ + 1) hsort.le hparameterSmall.le α).2
    intro p hp
    by_cases hlarge : omegaSequence τ m ≤ p
    · have hpσ : p ≤ σ := by
        change p ≤ (sourceP τ hτ n m hm α |>.filter (omegaSequence τ m ≤ ·)).sup id
        exact Finset.le_sup (f := id) (Finset.mem_filter.2 ⟨hp, hlarge⟩)
      exact .below_parameter (lt_add_one_iff.2 hpσ)
    · exact .below_base (lt_of_not_ge hlarge)
  have hδSmall : δ < omegaSequence τ (m + 1) :=
    hullClosureBound_lt τ (sourceFiniteCollapse τ n) n m α.val (σ + 1) hparameterSmall
  have hbelowδ : ∀ η < δ,
      Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α.val (σ + 1) η := by
    intro η hη
    exact ((source_hull_initial_bound_iff τ hτ n m hm α.val (σ + 1)
      hsort.le hparameterSmall η).2 hη).1
  have hparameterδ : σ + 1 ≤ δ :=
    hullClosureBound_contains τ (sourceFiniteCollapse τ n) n m α.val (σ + 1) σ
      (.below_parameter (lt_add_one_iff.2 le_rfl)) hstarSmall
  have hcandidate : CollapseCandidate (omegaSequence τ) (sourceFiniteCollapse τ n) n m α.val δ := by
    refine ⟨hδSmall, ?_, hull_mono le_rfl hparameterδ harg⟩
    intro η hη hsmall
    have hin := hull_absorb hbelowδ hη
    exact (source_hull_initial_bound_iff τ hτ n m hm α.val (σ + 1)
      hsort.le hparameterSmall η).1 ⟨hin, hsmall⟩
  have hminimum : sourceFiniteCollapse τ n m α.val ≤ δ := finiteCollapse_minimal hm hcandidate
  constructor
  · exact hull_mono le_rfl hparameterθ
  · intro h
    exact hull_absorb (fun η hη => hbelowδ η (hη.trans_le hminimum)) h

end Alexander313.Wilken
