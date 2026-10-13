import Alexander313.Wilken.HullSupportTransfer
import Alexander313.Wilken.GlobalBaseArithmetic

/-!
# Actual successor-argument barriers for source collapse

The actual source support of A+1 is bounded by theta(A). This follows from
canonical support transfer under addition, including absorption, and the real
argument-star bound. Thus a genuine theta value strictly between theta(A)
and theta(A+1) must have argument strictly below A. Finite and direct-limit
statements keep the original source domains and actual cardinal sorts.

This is a necessary precursor to Lemma 2.31. It does not identify the high
Omega-multiple part of a smaller argument or prove the full fixed-point-level
exclusion. The printed Lemma 2.30 also needs a boundary convention: at base 1,
the actual images of arguments below 1 have least upper bound 1, but 1 has no
positive-argument theta presentation. These are statements about that literal
source criterion, not about the separate thesis targets. All terms are
uncompiled proof candidates.
-/

namespace Alexander313.Wilken.SourceCollapseSuccessors

private theorem one_le_of_pos {a : Ordinal.{0}} (ha : 0 < a) : 1 ≤ a := by
  simpa only [zero_add] using Order.add_one_le_of_lt ha

theorem one_lt_next_cardinal (τ : Ordinal.{0}) (hτ : 0 < τ) (m : Nat) :
    (1 : Ordinal.{0}) < omegaSequence τ (m + 1) :=
  (one_le_of_pos hτ).trans_lt
    ((omegaSequence_base_lt τ).trans_le
      ((omegaSequence_strictMono τ).monotone (Nat.succ_le_succ (Nat.zero_le m))))

/-- Addition in the actual next-level notation domain, including its terminal
parameter-segment case. -/
def addArgument (τ : Ordinal.{0}) (n m : Nat) (hm : m < n)
    (a b : SourceNotationOrdinal τ n (m + 1)) : SourceNotationOrdinal τ n (m + 1) :=
  ⟨a.val + b.val, (source_nextNotation_iff_hull τ n m hm _).mpr
    (.add ((source_nextNotation_iff_hull τ n m hm _).mp a.property)
      ((source_nextNotation_iff_hull τ n m hm _).mp b.property))⟩

def oneArgument (τ : Ordinal.{0}) (hτ : 0 < τ) (n m : Nat) (hm : m < n) :
    SourceNotationOrdinal τ n (m + 1) :=
  ⟨1, (source_nextNotation_iff_hull τ n m hm _).mpr
    (.below_parameter (one_lt_next_cardinal τ hτ m))⟩

def succArgument (τ : Ordinal.{0}) (hτ : 0 < τ) (n m : Nat) (hm : m < n)
    (a : SourceNotationOrdinal τ n (m + 1)) : SourceNotationOrdinal τ n (m + 1) :=
  addArgument τ n m hm a (oneArgument τ hτ n m hm)

@[simp] theorem succArgument_val (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (a : SourceNotationOrdinal τ n (m + 1)) :
    (succArgument τ hτ n m hm a).val = a.val + 1 := rfl

/-- A low argument's real canonical star is bounded by that argument. -/
theorem star_le_argument_of_low (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (a : SourceNotationOrdinal τ n (m + 1))
    (ha : a.val < omegaSequence τ (m + 1)) : sourceStar τ hτ n m hm a ≤ a.val := by
  classical
  rw [sourceStar_eq_lowStar τ hτ n m hm a ha]
  unfold lowStar
  apply Finset.sup_le
  intro p hp
  exact canonicalANF_mem_le (List.mem_toFinset.mp (Finset.mem_filter.mp hp).1)

/-- Actual support addition gives an inequality even when atoms are absorbed.
No raw-leaf union or supplied support law is used. -/
theorem star_add_le (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (a b : SourceNotationOrdinal τ n (m + 1)) :
    sourceStar τ hτ n m hm (addArgument τ n m hm a b) ≤
      max (sourceStar τ hτ n m hm a) (sourceStar τ hτ n m hm b) := by
  classical
  unfold sourceStar
  apply Finset.sup_le
  intro p hp
  obtain ⟨hp, hlarge⟩ := Finset.mem_filter.mp hp
  rcases Finset.mem_union.mp (sourceP_add_subset τ hτ n m hm
      (addArgument τ n m hm a b) a b rfl hp) with hp | hp
  · exact (Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨hp, hlarge⟩)).trans (le_max_left _ _)
  · exact (Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨hp, hlarge⟩)).trans (le_max_right _ _)

theorem successor_star_le (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (a : SourceNotationOrdinal τ n (m + 1))
    (ha : a.val < omegaSequence τ (m + 2)) :
    sourceStar τ hτ n m hm (succArgument τ hτ n m hm a) ≤ sourceFiniteCollapse τ n m a.val := by
  apply (star_add_le τ hτ n m hm a (oneArgument τ hτ n m hm)).trans
  apply max_le
  · exact (sourceStar_lt_sourceFiniteCollapse τ hτ n m hm a ha).le
  · exact (star_le_argument_of_low τ hτ n m hm (oneArgument τ hτ n m hm)
      (one_lt_next_cardinal τ hτ m)).trans
      (one_le_of_pos (sourceFiniteCollapse_pos τ hτ n m hm a.val))

private theorem canonicalANF_add_one_normal (a : Ordinal.{0}) :
    IsAdditiveNormalForm (canonicalANF a ++ canonicalANF 1) := by
  rw [canonicalANF_principal zero_lt_one Ordinal.isPrincipal_add_one]
  have hn := canonicalANF_normal a
  constructor
  · intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact hn.1 b hb
    · have he := List.mem_singleton.mp hb
      subst b
      exact ⟨zero_lt_one, Ordinal.isPrincipal_add_one⟩
  · apply List.pairwise_append.mpr
    refine ⟨hn.2, by simp only [List.pairwise_singleton], ?_⟩
    intro b hb c hc
    have he := List.mem_singleton.mp hc
    subst c
    exact one_le_of_pos (hn.1 b hb).1

/-- Adding a final 1 absorbs no canonical atom, so the earlier star is
also bounded by the successor argument's actual star. -/
theorem star_le_successor_star (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (a : SourceNotationOrdinal τ n (m + 1)) :
    sourceStar τ hτ n m hm a ≤ sourceStar τ hτ n m hm (succArgument τ hτ n m hm a) := by
  classical
  have hp := sourceP_add_normal τ hτ n m hm (succArgument τ hτ n m hm a)
    a (oneArgument τ hτ n m hm) rfl (canonicalANF_add_one_normal a.val)
  unfold sourceStar
  apply Finset.sup_le
  intro p hmem
  obtain ⟨hmem, hlarge⟩ := Finset.mem_filter.mp hmem
  apply Finset.le_sup (f := id)
  apply Finset.mem_filter.mpr
  refine ⟨?_, hlarge⟩
  rw [hp]
  exact Finset.mem_union.mpr (Or.inl hmem)

/-- The actual source minimum and argument-star test make successor
arguments strictly increase the collapsing value, even for high arguments. -/
theorem collapse_lt_successor (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (a : SourceNotationOrdinal τ n (m + 1))
    (ha : a.val < omegaSequence τ (m + 2)) :
    sourceFiniteCollapse τ n m a.val < sourceFiniteCollapse τ n m (a.val + 1) := by
  have hs : (succArgument τ hτ n m hm a).val < omegaSequence τ (m + 2) :=
    (omegaSequence_isSuccLimit τ (m + 1)).add_one_lt ha
  by_contra! hv
  rcases hv.eq_or_lt with he | he
  · have harg := sourceFiniteCollapse_injective_on τ n m hm
      ⟨(succArgument τ hτ n m hm a).property, hs⟩ ⟨a.property, ha⟩ he
    exact (ne_of_gt (lt_add_one a.val)) harg
  · rcases (sourceFiniteCollapse_lt_iff_sourceStar τ hτ n m hm
      (succArgument τ hτ n m hm a) a hs ha).mp he with ⟨harg, _⟩ | hstar
    · exact (not_lt_of_ge (lt_add_one a.val).le) harg
    · have hbad := (hstar.trans (star_le_successor_star τ hτ n m hm a)).trans_lt
        (sourceStar_lt_sourceFiniteCollapse τ hτ n m hm (succArgument τ hτ n m hm a) hs)
      exact lt_irrefl _ hbad

/-- Necessary adjacent-interval barrier. The conclusion is argument descent;
the stronger high-part conclusion of Lemma 2.31 is not substituted for it. -/
theorem adjacent_argument_lt (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (a b : SourceNotationOrdinal τ n (m + 1))
    (ha : a.val < omegaSequence τ (m + 2)) (hb : b.val < omegaSequence τ (m + 2))
    (hab : sourceFiniteCollapse τ n m a.val < sourceFiniteCollapse τ n m b.val)
    (hbs : sourceFiniteCollapse τ n m b.val < sourceFiniteCollapse τ n m (a.val + 1)) :
    b.val < a.val := by
  have hs : (succArgument τ hτ n m hm a).val < omegaSequence τ (m + 2) :=
    (omegaSequence_isSuccLimit τ (m + 1)).add_one_lt ha
  rcases (sourceFiniteCollapse_lt_iff_sourceStar τ hτ n m hm b
      (succArgument τ hτ n m hm a) hb hs).mp hbs with ⟨harg, _⟩ | hstar
  · have hle : b.val ≤ a.val := Order.lt_add_one_iff.mp harg
    rcases hle.eq_or_lt with he | he
    · exact False.elim ((ne_of_lt hab) (congrArg (sourceFiniteCollapse τ n m) he).symm)
    · exact he
  · exact False.elim (hab.not_ge (hstar.trans (successor_star_le τ hτ n m hm a ha)))

/-- On the zero-high-part fragment, no genuine theta value lies in the
adjacent interval. This is the actual low case of Lemma 2.31. -/
theorem no_adjacent_value_of_low (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (a b : SourceNotationOrdinal τ n (m + 1))
    (ha : a.val < omegaSequence τ (m + 1)) (hb : b.val < omegaSequence τ (m + 2)) :
    ¬ (sourceFiniteCollapse τ n m a.val < sourceFiniteCollapse τ n m b.val ∧
      sourceFiniteCollapse τ n m b.val < sourceFiniteCollapse τ n m (a.val + 1)) := by
  rintro ⟨hab, hbs⟩
  have hba := adjacent_argument_lt τ hτ n m hm a b
    (ha.trans (omegaSequence_step τ (m + 1))) hb hab hbs
  exact lt_asymm hab (sourceFiniteCollapse_strictMono_low τ n m hm hba ha)

def globalAddArgument (τ : Ordinal.{0}) (m : Nat)
    (a b : GlobalNotationOrdinal τ (m + 1)) : GlobalNotationOrdinal τ (m + 1) :=
  ⟨a.val + b.val, .add a.property b.property⟩

def globalOneArgument (τ : Ordinal.{0}) (hτ : 0 < τ) (m : Nat) :
    GlobalNotationOrdinal τ (m + 1) := ⟨1, .parameter (one_lt_next_cardinal τ hτ m)⟩

def globalSuccArgument (τ : Ordinal.{0}) (hτ : 0 < τ) (m : Nat)
    (a : GlobalNotationOrdinal τ (m + 1)) : GlobalNotationOrdinal τ (m + 1) :=
  globalAddArgument τ m a (globalOneArgument τ hτ m)

@[simp] theorem globalSuccArgument_val (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) (a : GlobalNotationOrdinal τ (m + 1)) :
    (globalSuccArgument τ hτ m a).val = a.val + 1 := rfl

theorem global_star_add_le (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) (a b : GlobalNotationOrdinal τ (m + 1)) :
    globalStar τ hτ m (globalAddArgument τ m a b) ≤
      max (globalStar τ hτ m a) (globalStar τ hτ m b) := by
  obtain ⟨n, hmn, ha, hb⟩ := globalNotation_common_fragment τ hτ (m + 1) a b
  have hm : m < n := by omega
  let an : SourceNotationOrdinal τ n (m + 1) := ⟨a.val, ha⟩
  let bn : SourceNotationOrdinal τ n (m + 1) := ⟨b.val, hb⟩
  rw [globalStar_finite_agreement τ hτ m (globalAddArgument τ m a b) n hm
      (addArgument τ n m hm an bn) rfl,
    globalStar_finite_agreement τ hτ m a n hm an rfl,
    globalStar_finite_agreement τ hτ m b n hm bn rfl]
  exact star_add_le τ hτ n m hm an bn

theorem global_star_le_argument_of_low (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) (a : GlobalNotationOrdinal τ (m + 1))
    (ha : a.val < omegaSequence τ (m + 1)) : globalStar τ hτ m a ≤ a.val := by
  classical
  rw [globalStar_eq_lowStar τ hτ m a ha]
  unfold lowStar
  apply Finset.sup_le
  intro p hp
  exact canonicalANF_mem_le (List.mem_toFinset.mp (Finset.mem_filter.mp hp).1)

theorem global_successor_star_le (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) (a : GlobalNotationOrdinal τ (m + 1))
    (ha : a.val < omegaSequence τ (m + 2)) :
    globalStar τ hτ m (globalSuccArgument τ hτ m a) ≤ globalCollapse τ m a.val := by
  apply (global_star_add_le τ hτ m a (globalOneArgument τ hτ m)).trans
  apply max_le
  · exact (globalStar_lt_globalCollapse τ hτ m a ha).le
  · have hbound : a.val < globalBoundary τ (m + 1) :=
      (globalNotation_low_iff_lt_boundary τ hτ (m + 1) a.val).mp
        ⟨a.property, by simpa only [Nat.add_assoc] using ha⟩
    exact (global_star_le_argument_of_low τ hτ m (globalOneArgument τ hτ m)
      (one_lt_next_cardinal τ hτ m)).trans
      (one_le_of_pos (globalCollapse_pos τ hτ m a.val hbound))

theorem global_collapse_lt_successor (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) (a : GlobalNotationOrdinal τ (m + 1))
    (ha : a.val < omegaSequence τ (m + 2)) :
    globalCollapse τ m a.val < globalCollapse τ m (a.val + 1) := by
  let s := globalSuccArgument τ hτ m a
  have hs : s.val < omegaSequence τ (m + 2) :=
    (omegaSequence_isSuccLimit τ (m + 1)).add_one_lt ha
  obtain ⟨n, hmn, han, hsn⟩ := globalNotation_common_fragment τ hτ (m + 1) a s
  have hm : m < n := by omega
  let an : SourceNotationOrdinal τ n (m + 1) := ⟨a.val, han⟩
  have hba := source_finite_notation_sorted_lt_boundary τ hτ n (m + 1) (m + 1)
    le_rfl hmn han ha
  have hbs := source_finite_notation_sorted_lt_boundary τ hτ n (m + 1) (m + 1)
    le_rfl hmn hsn hs
  rw [globalCollapse_finite_agreement τ hτ n m hm a.val hba,
    globalCollapse_finite_agreement τ hτ n m hm (a.val + 1) hbs]
  exact collapse_lt_successor τ hτ n m hm an ha

/-- The same barrier for the genuine unbounded global source family. -/
theorem global_adjacent_argument_lt (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) (a b : GlobalNotationOrdinal τ (m + 1))
    (ha : a.val < omegaSequence τ (m + 2)) (hb : b.val < omegaSequence τ (m + 2))
    (hab : globalCollapse τ m a.val < globalCollapse τ m b.val)
    (hbs : globalCollapse τ m b.val < globalCollapse τ m (a.val + 1)) : b.val < a.val := by
  have hs : (globalSuccArgument τ hτ m a).val < omegaSequence τ (m + 2) :=
    (omegaSequence_isSuccLimit τ (m + 1)).add_one_lt ha
  rcases (globalCollapse_lt_iff_globalStar τ hτ m b (globalSuccArgument τ hτ m a) hb hs).mp hbs with
    ⟨harg, _⟩ | hstar
  · have hle : b.val ≤ a.val := Order.lt_add_one_iff.mp harg
    rcases hle.eq_or_lt with he | he
    · exact False.elim ((ne_of_lt hab) (congrArg (globalCollapse τ m) he).symm)
    · exact he
  · exact False.elim (hab.not_ge (hstar.trans (global_successor_star_le τ hτ m a ha)))

theorem global_no_adjacent_value_of_low (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) (a b : GlobalNotationOrdinal τ (m + 1))
    (ha : a.val < omegaSequence τ (m + 1)) (hb : b.val < omegaSequence τ (m + 2)) :
    ¬ (globalCollapse τ m a.val < globalCollapse τ m b.val ∧
      globalCollapse τ m b.val < globalCollapse τ m (a.val + 1)) := by
  rintro ⟨hab, hbs⟩
  have hbound : b.val < globalBoundary τ (m + 1) :=
    (globalNotation_low_iff_lt_boundary τ hτ (m + 1) b.val).mp
      ⟨b.property, by simpa only [Nat.add_assoc] using hb⟩
  have hnext := nextAdditivePrincipal_le (globalCollapse τ m a.val) (globalCollapse τ m b.val)
    hab (globalCollapse_add_closed τ hτ m b.val hbound)
  rw [globalCollapse_succ_eq_nextAdditivePrincipal τ hτ m a.val ha] at hbs
  exact hbs.not_ge hnext

/-- The other literal boundary is an empty set of earlier arguments. This
does not assert a corrected version of Lemma 2.30. -/
theorem zero_images_isLUB (τ : Ordinal.{0}) (n m : Nat) (Δ : Ordinal.{0}) :
    IsLUB {v : Ordinal.{0} | ∃ σ : Ordinal.{0}, σ < 0 ∧ v = sourceFiniteCollapse τ n m (Δ + σ)} 0 := by
  constructor
  · rintro v ⟨σ, hσ, _⟩
    exact False.elim ((not_lt_of_ge ((zero_le : 0 ≤ σ))) hσ)
  · intro b _
    exact (zero_le : 0 ≤ b)

theorem zero_not_collapse (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (a : Ordinal.{0}) : sourceFiniteCollapse τ n m a ≠ 0 :=
  ne_of_gt (sourceFiniteCollapse_pos τ hτ n m hm a)

/-- Literal base-1 boundary of the displayed supremum criterion. IsLUB keeps
the ordinal-indexed set at its original universe. -/
theorem base_one_images_isLUB (n : Nat) (hn : 0 < n) :
    IsLUB {v : Ordinal.{0} | ∃ σ : Ordinal.{0}, σ < 1 ∧ v = sourceFiniteCollapse 1 n 0 σ} 1 := by
  have hzero : sourceFiniteCollapse 1 n 0 0 = 1 := by
    simpa only [omegaSequence_zero] using
      sourceFiniteCollapse_zero 1 zero_lt_one Ordinal.isPrincipal_add_one n 0 hn
  constructor
  · rintro v ⟨σ, hσ, rfl⟩
    have hσzero : σ = 0 := by simpa only [Ordinal.lt_one_iff_zero] using hσ
    rw [hσzero, hzero]
  · intro b hb
    exact hb ⟨0, zero_lt_one, hzero.symm⟩

theorem base_one_no_positive_argument (n : Nat) (hn : 0 < n)
    (b : SourceNotationOrdinal 1 n 1) (hb : b.val < omegaSequence 1 2) (hpos : 0 < b.val) :
    sourceFiniteCollapse 1 n 0 b.val ≠ 1 := by
  have hzero : sourceFiniteCollapse 1 n 0 0 = 1 := by
    simpa only [omegaSequence_zero] using
      sourceFiniteCollapse_zero 1 zero_lt_one Ordinal.isPrincipal_add_one n 0 hn
  have hz : sourceNotation 1 n 1 0 := sourceNotation_next_of_low 1 n 0 hn
    (zero_lt_one.trans (one_lt_next_cardinal 1 zero_lt_one 0))
  intro h
  have he := sourceFiniteCollapse_injective_on 1 n 0 hn
    ⟨b.property, hb⟩ ⟨hz, zero_lt_one.trans (one_lt_next_cardinal 1 zero_lt_one 1)⟩
    (h.trans hzero.symm)
  exact (ne_of_gt hpos) he

theorem base_one_no_higher_level (n : Nat) (hn : 0 < n)
    (b : SourceNotationOrdinal 1 n 1) (hb : b.val < omegaSequence 1 2)
    (Γ ρ : Ordinal.{0}) (hΓ : 0 < Γ) (he : b.val = Γ + ρ) :
    sourceFiniteCollapse 1 n 0 b.val ≠ 1 :=
  base_one_no_positive_argument n hn b hb (by rw [he]; exact hΓ.trans_le le_self_add)

theorem global_base_one_images_isLUB :
    IsLUB {v : Ordinal.{0} | ∃ σ : Ordinal.{0}, σ < 1 ∧ v = globalCollapse 1 0 σ} 1 := by
  have hzero : globalCollapse 1 0 0 = 1 := by
    simpa only [omegaSequence_zero] using globalCollapse_zero 1 zero_lt_one Ordinal.isPrincipal_add_one 0
  constructor
  · rintro v ⟨σ, hσ, rfl⟩
    have hσzero : σ = 0 := by simpa only [Ordinal.lt_one_iff_zero] using hσ
    rw [hσzero, hzero]
  · intro b hb
    exact hb ⟨0, zero_lt_one, hzero.symm⟩

theorem global_base_one_no_positive_argument (b : GlobalNotationOrdinal 1 1)
    (hb : b.val < omegaSequence 1 2) (hpos : 0 < b.val) : globalCollapse 1 0 b.val ≠ 1 := by
  let z : GlobalNotationOrdinal 1 1 :=
    ⟨0, .parameter (zero_lt_one.trans (one_lt_next_cardinal 1 zero_lt_one 0))⟩
  have hzero : globalCollapse 1 0 z.val = 1 := by
    simpa only [z, omegaSequence_zero] using globalCollapse_zero 1 zero_lt_one Ordinal.isPrincipal_add_one 0
  intro h
  have he := (globalCollapse_eq_iff 1 zero_lt_one 0 b z hb
    (zero_lt_one.trans (one_lt_next_cardinal 1 zero_lt_one 1))).mp (h.trans hzero.symm)
  exact (ne_of_gt hpos) he

theorem global_base_one_no_higher_level (b : GlobalNotationOrdinal 1 1)
    (hb : b.val < omegaSequence 1 2) (Γ ρ : Ordinal.{0}) (hΓ : 0 < Γ)
    (he : b.val = Γ + ρ) : globalCollapse 1 0 b.val ≠ 1 :=
  global_base_one_no_positive_argument b hb (by rw [he]; exact hΓ.trans_le le_self_add)

end Alexander313.Wilken.SourceCollapseSuccessors
