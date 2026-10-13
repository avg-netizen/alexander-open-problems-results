import Alexander313.Wilken.SourceCollapseSuccessors
import Alexander313.Wilken.MultiplicativePrincipalArithmetic

/-!
# Actual residual image suprema and fixed-point boundary repair

Divisibility of the high part by the next cardinal is used arithmetically:
its genuine ANF consists of atoms at or above that cardinal. A low residual
therefore survives as a literal ANF suffix. Actual hull inversion gives the
strict residual bound below its collapsing value, with every shifted argument
admitted and sorted by the original source construction.

The bounded supremum below a successor residual is equal to that residual
exactly in the base-1, level-zero, zero-high-part, residual-1 case. Zero is a
separate empty-supremum case. Other fixed residuals are positive successor
limits. On that proper-limit domain the actual higher-presentation criterion
is proved in both directions. Original same-level constructor admission
extracts the residual admission, and genuine common fragments transport the
whole bounded supremum family to the direct-limit source functions. The
complete criterion retains both boundary exceptions explicitly. No
fixed-point, support or effectivity contract is supplied. All terms are
uncompiled proof candidates.
-/

namespace Alexander313.Wilken.SourceFixedPointLimits

private theorem one_le_of_pos {a : Ordinal.{0}} (ha : 0 < a) : 1 ≤ a :=
  Order.one_le_iff_pos.mpr ha

noncomputable def scaledANF (Ω δ : Ordinal.{0}) : List Ordinal.{0} :=
  (canonicalANF δ).map (fun a => Ω * a)

theorem scaledANF_normal (Ω δ : Ordinal.{0}) (hΩ : 0 < Ω)
    (hp : Ordinal.IsPrincipal (· + ·) Ω) : IsAdditiveNormalForm (scaledANF Ω δ) := by
  have hn := canonicalANF_normal δ
  constructor
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    have hbp := hn.1 b hb
    refine ⟨?_, ?_⟩
    · simpa only [mul_zero] using (Ordinal.isNormal_mul_right hΩ).strictMono hbp.1
    · by_cases hb1 : b = 1
      · simpa only [hb1, mul_one] using hp
      · exact Ordinal.isPrincipal_add_mul_of_isPrincipal_add Ω hb1 hbp.2
  · change ((canonicalANF δ).map (fun a => Ω * a)).Pairwise (fun a b => b ≤ a)
    rw [List.pairwise_map]
    exact hn.2.imp (fun {_ _} hab => mul_le_mul' le_rfl hab)

theorem canonicalANF_multiple (Ω δ : Ordinal.{0}) (hΩ : 0 < Ω)
    (hp : Ordinal.IsPrincipal (· + ·) Ω) : canonicalANF (Ω * δ) = scaledANF Ω δ := by
  apply canonicalANF_eq_of_normal (scaledANF_normal Ω δ hΩ hp)
  rw [scaledANF, ← MultiplicativePrincipalArithmetic.mul_principalSum, principalSum_canonicalANF]

theorem canonicalANF_multiple_ge (Ω Δ : Ordinal.{0}) (hΩ : 0 < Ω)
    (hp : Ordinal.IsPrincipal (· + ·) Ω) (hΔ : Ω ∣ Δ) :
    ∀ a ∈ canonicalANF Δ, Ω ≤ a := by
  rcases hΔ with ⟨δ, rfl⟩
  rw [canonicalANF_multiple Ω δ hΩ hp]
  intro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  simpa only [mul_one] using
    (mul_le_mul' (le_rfl : Ω ≤ Ω) (one_le_of_pos ((canonicalANF_normal δ).1 b hb).1))

/-- The genuine low residual cannot absorb any atom of the divisible high part. -/
theorem canonicalANF_multiple_add_low (Ω Δ η : Ordinal.{0}) (hΩ : 0 < Ω)
    (hp : Ordinal.IsPrincipal (· + ·) Ω) (hΔ : Ω ∣ Δ) (hη : η < Ω) :
    canonicalANF (Δ + η) = canonicalANF Δ ++ canonicalANF η := by
  have hdn := canonicalANF_normal Δ
  have hen := canonicalANF_normal η
  have hn : IsAdditiveNormalForm (canonicalANF Δ ++ canonicalANF η) := by
    constructor
    · intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hdn.1 a ha
      · exact hen.1 a ha
    · apply List.pairwise_append.mpr
      refine ⟨hdn.2, hen.2, ?_⟩
      intro a ha b hb
      exact ((canonicalANF_mem_le hb).trans_lt hη).le.trans
        (canonicalANF_multiple_ge Ω Δ hΩ hp hΔ a ha)
  apply canonicalANF_eq_of_normal hn
  rw [principalSum_append, principalSum_canonicalANF, principalSum_canonicalANF]

/-- Distinct divisible high parts are separated by every low residual. -/
theorem multiple_add_low_lt_of_lt (Ω Δ Γ η : Ordinal.{0}) (hΩ : 0 < Ω)
    (hΔ : Ω ∣ Δ) (hΓ : Ω ∣ Γ) (hΔΓ : Δ < Γ) (hη : η < Ω) : Δ + η < Γ := by
  rcases hΔ with ⟨δ, rfl⟩
  rcases hΓ with ⟨γ, rfl⟩
  have hδγ : δ < γ := (Ordinal.isNormal_mul_right hΩ).strictMono.lt_iff_lt.mp hΔΓ
  calc
    Ω * δ + η < Ω * δ + Ω := add_lt_add_right hη _
    _ = Ω * (δ + 1) := by rw [mul_add_one]
    _ ≤ Ω * γ := mul_le_mul' le_rfl (Order.add_one_le_of_lt hδγ)

theorem next_cardinal_pos (τ : Ordinal.{0}) (hτ : 0 < τ) (m : Nat) :
    0 < omegaSequence τ (m + 1) :=
  hτ.trans_le ((omegaSequence_strictMono τ).monotone (Nat.zero_le (m + 1)))

/-- Actual source hull inversion extracts both unabsorbed pieces. -/
theorem source_hull_multiple_add_low_iff (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (α β Δ η : Ordinal.{0})
    (hΔ : omegaSequence τ (m + 1) ∣ Δ) (hη : η < omegaSequence τ (m + 1)) :
    Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α β (Δ + η) ↔
      Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α β Δ ∧
        Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α β η := by
  rw [source_hull_iff_canonicalANF τ hτ n m hm α β (Δ + η),
    source_hull_iff_canonicalANF τ hτ n m hm α β Δ,
    source_hull_iff_canonicalANF τ hτ n m hm α β η,
    canonicalANF_multiple_add_low _ Δ η (next_cardinal_pos τ hτ m)
      (omegaSequence_add_closed τ m) hΔ hη]
  constructor
  · intro h
    exact ⟨fun a ha => h a (List.mem_append_left _ ha),
      fun a ha => h a (List.mem_append_right _ ha)⟩
  · rintro ⟨hd, he⟩ a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hd a ha
    · exact he a ha

def lowArgument (τ : Ordinal.{0}) (n m : Nat) (hm : m < n)
    (η : Ordinal.{0}) (hη : η < omegaSequence τ (m + 1)) : SourceNotationOrdinal τ n (m + 1) :=
  ⟨η, sourceNotation_next_of_low τ n m hm hη⟩

def shiftArgument (τ : Ordinal.{0}) (n m : Nat) (hm : m < n)
    (Δ : SourceNotationOrdinal τ n (m + 1)) (η : Ordinal.{0})
    (hη : η < omegaSequence τ (m + 1)) : SourceNotationOrdinal τ n (m + 1) :=
  SourceCollapseSuccessors.addArgument τ n m hm Δ (lowArgument τ n m hm η hη)

@[simp] theorem shiftArgument_val (τ : Ordinal.{0}) (n m : Nat) (hm : m < n)
    (Δ : SourceNotationOrdinal τ n (m + 1)) (η : Ordinal.{0})
    (hη : η < omegaSequence τ (m + 1)) :
    (shiftArgument τ n m hm Δ η hη).val = Δ.val + η := rfl

theorem shiftArgument_sort (τ : Ordinal.{0}) (n m : Nat) (hm : m < n)
    (Δ : SourceNotationOrdinal τ n (m + 1)) (hΔ : Δ.val < omegaSequence τ (m + 2))
    (η : Ordinal.{0}) (hη : η < omegaSequence τ (m + 1)) :
    (shiftArgument τ n m hm Δ η hη).val < omegaSequence τ (m + 2) :=
  omegaSequence_add_closed τ (m + 1) hΔ (hη.trans (omegaSequence_step τ (m + 1)))

/-- The low residual is strictly below the actual collapse of its genuine
shifted source argument. Neither this bound nor its admission is assumed. -/
theorem tail_lt_collapse (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (Δ : SourceNotationOrdinal τ n (m + 1))
    (hΔsort : Δ.val < omegaSequence τ (m + 2))
    (hΔdvd : omegaSequence τ (m + 1) ∣ Δ.val)
    (η : Ordinal.{0}) (hη : η < omegaSequence τ (m + 1)) :
    η < sourceFiniteCollapse τ n m (Δ.val + η) := by
  let a := shiftArgument τ n m hm Δ η hη
  have ha := shiftArgument_sort τ n m hm Δ hΔsort η hη
  have harg := sourceFiniteCollapse_argument_notation τ n m hm a.val ha a.property
  have htail := (source_hull_multiple_add_low_iff τ hτ n m hm a.val
    (sourceFiniteCollapse τ n m a.val) Δ.val η hΔdvd hη).mp harg
  exact (finiteCollapse_hull_initial hm a.val η).mp ⟨htail.2, hη⟩

/-- Every actual divided high part inherits the original next-level domain. -/
theorem high_part_notation (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (a : SourceNotationOrdinal τ n (m + 1))
    (ha : a.val < omegaSequence τ (m + 2)) :
    sourceNotation τ n (m + 1)
      (omegaSequence τ (m + 1) * (a.val / omegaSequence τ (m + 1))) := by
  let Ω := omegaSequence τ (m + 1)
  have hΩ := next_cardinal_pos τ hτ m
  have harg := sourceFiniteCollapse_argument_notation τ n m hm a.val ha a.property
  have hsplit : Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m a.val
      (sourceFiniteCollapse τ n m a.val) (Ω * (a.val / Ω) + a.val % Ω) := by
    rw [Ordinal.div_add_mod]
    exact harg
  have hhead := (source_hull_multiple_add_low_iff τ hτ n m hm a.val
      (sourceFiniteCollapse τ n m a.val) (Ω * (a.val / Ω)) (a.val % Ω)
      ⟨a.val / Ω, rfl⟩ (Ordinal.mod_lt _ (ne_of_gt hΩ))).mp hsplit
  exact source_hull_next_notation τ n m hm ha.le (sourceFiniteCollapse_bounds τ n m hm a.val).2 hhead.1

theorem star_shift_eq_max (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (Δ : SourceNotationOrdinal τ n (m + 1))
    (hΔdvd : omegaSequence τ (m + 1) ∣ Δ.val)
    (η : Ordinal.{0}) (hη : η < omegaSequence τ (m + 1)) :
    sourceStar τ hτ n m hm (shiftArgument τ n m hm Δ η hη) =
      max (sourceStar τ hτ n m hm Δ) (sourceStar τ hτ n m hm (lowArgument τ n m hm η hη)) := by
  classical
  have hn : IsAdditiveNormalForm (canonicalANF Δ.val ++ canonicalANF η) := by
    rw [← canonicalANF_multiple_add_low _ Δ.val η (next_cardinal_pos τ hτ m)
      (omegaSequence_add_closed τ m) hΔdvd hη]
    exact canonicalANF_normal _
  have hp := sourceP_add_normal τ hτ n m hm (shiftArgument τ n m hm Δ η hη)
    Δ (lowArgument τ n m hm η hη) rfl hn
  unfold sourceStar
  rw [hp, Finset.filter_union, Finset.sup_union]

noncomputable def residualImageSup (τ : Ordinal.{0}) (n m : Nat) (Δ η : Ordinal.{0}) : Ordinal.{0} :=
  Ordinal.bsup η (fun σ _ => sourceFiniteCollapse τ n m (Δ + σ))

theorem residualImageSup_zero (τ : Ordinal.{0}) (n m : Nat) (Δ : Ordinal.{0}) :
    residualImageSup τ n m Δ 0 = 0 := Ordinal.bsup_zero _

theorem residualImageSup_one (τ : Ordinal.{0}) (n m : Nat) (Δ : Ordinal.{0}) :
    residualImageSup τ n m Δ 1 = sourceFiniteCollapse τ n m Δ := by
  simpa only [residualImageSup, add_zero] using
    Ordinal.bsup_one (fun σ _ => sourceFiniteCollapse τ n m (Δ + σ))

theorem image_le_sup (τ : Ordinal.{0}) (n m : Nat) (Δ η σ : Ordinal.{0}) (hσ : σ < η) :
    sourceFiniteCollapse τ n m (Δ + σ) ≤ residualImageSup τ n m Δ η :=
  Ordinal.le_bsup _ σ hσ

/-- Domination is proved on the actual divisible-high-part domain. It
justifies turning a strict supremum test into failure of equality there. -/
theorem residual_le_imageSup (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (Δ : SourceNotationOrdinal τ n (m + 1))
    (hΔsort : Δ.val < omegaSequence τ (m + 2))
    (hΔdvd : omegaSequence τ (m + 1) ∣ Δ.val)
    (η : Ordinal.{0}) (hη : η < omegaSequence τ (m + 1)) :
    η ≤ residualImageSup τ n m Δ.val η := by
  by_contra! hsmall
  have ht := tail_lt_collapse τ hτ n m hm Δ hΔsort hΔdvd
    (residualImageSup τ n m Δ.val η) (hsmall.trans hη)
  exact ht.not_ge (image_le_sup τ n m Δ.val η _ hsmall)

theorem strict_sup_iff_not_fixed (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (Δ : SourceNotationOrdinal τ n (m + 1))
    (hΔsort : Δ.val < omegaSequence τ (m + 2))
    (hΔdvd : omegaSequence τ (m + 1) ∣ Δ.val)
    (η : Ordinal.{0}) (hη : η < omegaSequence τ (m + 1)) :
    η < residualImageSup τ n m Δ.val η ↔ residualImageSup τ n m Δ.val η ≠ η := by
  have hle := residual_le_imageSup τ hτ n m hm Δ hΔsort hΔdvd η hη
  exact ⟨fun h => ne_of_gt h, fun h => lt_of_le_of_ne hle h.symm⟩

private theorem principal_successor_eq_zero {σ : Ordinal.{0}}
    (hp : Ordinal.IsPrincipal (· + ·) (σ + 1)) : σ = 0 := by
  by_contra hσ
  have hs : 0 < σ := pos_iff_ne_zero.mpr hσ
  have h1 : 1 < σ + 1 := (one_le_of_pos hs).trans_lt (lt_add_one σ)
  exact lt_irrefl _ (hp (lt_add_one σ) h1)

/-- Every successor equality is classified, including all higher levels and
all positive bases. No limit or source-presentation test is assumed. -/
theorem fixed_successor_iff (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (Δ : SourceNotationOrdinal τ n (m + 1))
    (hΔsort : Δ.val < omegaSequence τ (m + 2))
    (hΔdvd : omegaSequence τ (m + 1) ∣ Δ.val)
    (σ : Ordinal.{0}) (hσ : σ + 1 < omegaSequence τ (m + 1)) :
    residualImageSup τ n m Δ.val (σ + 1) = σ + 1 ↔
      σ = 0 ∧ m = 0 ∧ τ = 1 ∧ Δ.val = 0 := by
  constructor
  · intro he
    have ht := tail_lt_collapse τ hτ n m hm Δ hΔsort hΔdvd σ
      ((lt_add_one σ).trans hσ)
    have hv : sourceFiniteCollapse τ n m (Δ.val + σ) = σ + 1 :=
      le_antisymm ((image_le_sup τ n m Δ.val (σ + 1) σ (lt_add_one σ)).trans_eq he)
        (Order.add_one_le_of_lt ht)
    have hs0 : σ = 0 := principal_successor_eq_zero
      (hv ▸ sourceFiniteCollapse_add_closed τ n m hm (Δ.val + σ))
    have hv1 : sourceFiniteCollapse τ n m Δ.val = 1 := by
      simpa only [hs0, zero_add, add_zero] using hv
    have hb : omegaSequence τ m ≤ 1 := (sourceFiniteCollapse_bounds τ n m hm Δ.val).1.trans_eq hv1
    have hτ1 : τ = 1 := le_antisymm
      (((omegaSequence_strictMono τ).monotone (Nat.zero_le m)).trans hb) (one_le_of_pos hτ)
    have hm0 : m = 0 := by
      by_contra hm0
      have h1m : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
      have hbad := (SourceCollapseSuccessors.one_lt_next_cardinal τ hτ 0).trans_le
        (((omegaSequence_strictMono τ).monotone h1m).trans hb)
      exact lt_irrefl _ hbad
    have hz : sourceNotation τ n (m + 1) 0 := sourceNotation_next_of_low τ n m hm
      (next_cardinal_pos τ hτ m)
    have hτp : Ordinal.IsPrincipal (· + ·) τ := hτ1.symm ▸ Ordinal.isPrincipal_add_one
    have hv0 : sourceFiniteCollapse τ n m 0 = 1 := by
      simpa only [hm0, omegaSequence_zero, hτ1] using sourceFiniteCollapse_zero τ hτ hτp n m hm
    have hd0 := sourceFiniteCollapse_injective_on τ n m hm ⟨Δ.property, hΔsort⟩
      ⟨hz, (next_cardinal_pos τ hτ (m + 1))⟩ (hv1.trans hv0.symm)
    exact ⟨hs0, hm0, hτ1, hd0⟩
  · rintro ⟨rfl, rfl, rfl, hΔ⟩
    simp only [zero_add, residualImageSup_one, hΔ, sourceFiniteCollapse_zero 1 zero_lt_one
      Ordinal.isPrincipal_add_one n 0 hm, omegaSequence_zero]

/-- The only non-limit fixed residuals are the empty case and the literal
base-1 zero-high-part exception. -/
theorem fixed_residual_cases (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (Δ : SourceNotationOrdinal τ n (m + 1))
    (hΔsort : Δ.val < omegaSequence τ (m + 2))
    (hΔdvd : omegaSequence τ (m + 1) ∣ Δ.val)
    (η : Ordinal.{0}) (hη : η < omegaSequence τ (m + 1))
    (he : residualImageSup τ n m Δ.val η = η) :
    η = 0 ∨ (η = 1 ∧ m = 0 ∧ τ = 1 ∧ Δ.val = 0) ∨ Order.IsSuccLimit η := by
  rcases Ordinal.zero_or_succ_or_isSuccLimit η with hz | hs | hl
  · exact Or.inl hz
  · obtain ⟨σ, rfl⟩ := hs
    rw [Order.succ_eq_add_one] at hη he ⊢
    obtain ⟨hs0, hm0, hτ1, hd0⟩ := (fixed_successor_iff τ hτ n m hm Δ hΔsort hΔdvd σ hη).mp he
    exact Or.inr (Or.inl ⟨by rw [hs0, zero_add], hm0, hτ1, hd0⟩)
  · exact Or.inr (Or.inr hl)

theorem fixed_above_one_isSuccLimit (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (Δ : SourceNotationOrdinal τ n (m + 1))
    (hΔsort : Δ.val < omegaSequence τ (m + 2))
    (hΔdvd : omegaSequence τ (m + 1) ∣ Δ.val)
    (η : Ordinal.{0}) (hη : η < omegaSequence τ (m + 1)) (h1 : 1 < η)
    (he : residualImageSup τ n m Δ.val η = η) : Order.IsSuccLimit η := by
  rcases fixed_residual_cases τ hτ n m hm Δ hΔsort hΔdvd η hη he with hz | hb | hl
  · exact False.elim (((zero_le : (0 : Ordinal.{0}) ≤ 1)).not_gt (h1.trans_eq hz))
  · exact False.elim (h1.ne' hb.1)
  · exact hl

/-- A supremum of actual additive-principal collapsing values is again
additive principal. The proof uses two real cofinal images, not monotonicity
of collapse in an arbitrary argument. -/
theorem residualImageSup_add_closed (τ : Ordinal.{0}) (n m : Nat) (hm : m < n)
    (Δ η : Ordinal.{0}) : Ordinal.IsPrincipal (· + ·) (residualImageSup τ n m Δ η) := by
  intro a b ha hb
  obtain ⟨σ, hσ, has⟩ := (Ordinal.lt_bsup (fun σ _ => sourceFiniteCollapse τ n m (Δ + σ))).mp ha
  obtain ⟨ρ, hρ, hbr⟩ := (Ordinal.lt_bsup (fun σ _ => sourceFiniteCollapse τ n m (Δ + σ))).mp hb
  rcases le_total (sourceFiniteCollapse τ n m (Δ + σ)) (sourceFiniteCollapse τ n m (Δ + ρ)) with h | h
  · exact (sourceFiniteCollapse_add_closed τ n m hm (Δ + ρ) (has.trans_le h) hbr).trans_le
      (image_le_sup τ n m Δ η ρ hρ)
  · exact (sourceFiniteCollapse_add_closed τ n m hm (Δ + σ) has (hbr.trans_le h)).trans_le
      (image_le_sup τ n m Δ η σ hσ)

/-- At a proper-limit equality every individual image is strictly below
the fixed residual: the next residual is still in the supremum domain. -/
theorem image_lt_fixed_limit (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (Δ : SourceNotationOrdinal τ n (m + 1))
    (hΔsort : Δ.val < omegaSequence τ (m + 2))
    (η : Ordinal.{0}) (hη : η < omegaSequence τ (m + 1)) (hl : Order.IsSuccLimit η)
    (he : residualImageSup τ n m Δ.val η = η) (σ : Ordinal.{0}) (hσ : σ < η) :
    sourceFiniteCollapse τ n m (Δ.val + σ) < η := by
  have hs1 := hl.add_one_lt hσ
  have hsΩ := hσ.trans hη
  have ht := SourceCollapseSuccessors.collapse_lt_successor τ hτ n m hm
    (shiftArgument τ n m hm Δ σ hsΩ) (shiftArgument_sort τ n m hm Δ hΔsort σ hsΩ)
  have hstep : sourceFiniteCollapse τ n m (Δ.val + σ) <
      sourceFiniteCollapse τ n m (Δ.val + (σ + 1)) := by
    simpa only [shiftArgument_val, add_assoc] using ht
  exact hstep.trans_le
    ((image_le_sup τ n m Δ.val η (σ + 1) hs1).trans_eq he)

theorem base_lt_fixed_limit (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (Δ : SourceNotationOrdinal τ n (m + 1))
    (hΔsort : Δ.val < omegaSequence τ (m + 2))
    (η : Ordinal.{0}) (hη : η < omegaSequence τ (m + 1)) (hl : Order.IsSuccLimit η)
    (he : residualImageSup τ n m Δ.val η = η) : omegaSequence τ m < η := by
  have hz : 0 < η := zero_lt_one.trans (Ordinal.one_lt_of_isSuccLimit hl)
  exact (sourceFiniteCollapse_bounds τ n m hm Δ.val).1.trans_lt
    (by simpa only [add_zero] using image_lt_fixed_limit τ hτ n m hm Δ hΔsort η hη hl he 0 hz)

/-- The higher presentation retains its original same-level source argument,
its next-level domain and its sort. Its high part, low tail and collapse are
literal ordinal operations. -/
def HigherPresentation (τ : Ordinal.{0}) (hτ : 0 < τ) (n m : Nat) (hm : m < n)
    (Δ : SourceNotationOrdinal τ n (m + 1)) (η : Ordinal.{0}) : Prop :=
  ∃ b : SourceNotationOrdinal τ n (m + 1), ∃ Γ ρ : Ordinal.{0},
    sourceNotation τ n m b.val ∧ b.val < omegaSequence τ (m + 2) ∧ omegaSequence τ (m + 1) ∣ Γ ∧
      ρ < omegaSequence τ (m + 1) ∧ b.val = Γ + ρ ∧ Δ.val < Γ ∧
        η = sourceFiniteCollapse τ n m b.val ∧ sourceStar τ hτ n m hm Δ < η

theorem higherPresentation_fixed (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (Δ : SourceNotationOrdinal τ n (m + 1))
    (hΔsort : Δ.val < omegaSequence τ (m + 2))
    (hΔdvd : omegaSequence τ (m + 1) ∣ Δ.val)
    (η : Ordinal.{0}) (hη : η < omegaSequence τ (m + 1))
    (hp : HigherPresentation τ hτ n m hm Δ η) : residualImageSup τ n m Δ.val η = η := by
  obtain ⟨b, Γ, ρ, hbm, hb, hΓ, hρ, hbe, hΔΓ, hηb, hsΔ⟩ := hp
  apply le_antisymm
  · apply Ordinal.bsup_le
    intro σ hσ
    have hσΩ := hσ.trans hη
    let a := shiftArgument τ n m hm Δ σ hσΩ
    have ha := shiftArgument_sort τ n m hm Δ hΔsort σ hσΩ
    have hab : a.val < b.val := (multiple_add_low_lt_of_lt _ Δ.val Γ σ
      (next_cardinal_pos τ hτ m) hΔdvd hΓ hΔΓ hσΩ).trans_le
        (by rw [hbe]; exact le_self_add)
    have hs : sourceStar τ hτ n m hm a < η := by
      rw [star_shift_eq_max τ hτ n m hm Δ hΔdvd σ hσΩ]
      exact max_lt_iff.mpr ⟨hsΔ, (SourceCollapseSuccessors.star_le_argument_of_low τ hτ n m hm
        (lowArgument τ n m hm σ hσΩ) hσΩ).trans_lt hσ⟩
    exact ((sourceFiniteCollapse_lt_iff_sourceStar τ hτ n m hm a b ha hb).mpr
      (Or.inl ⟨hab, hηb ▸ hs⟩)).le.trans_eq hηb.symm
  · exact residual_le_imageSup τ hτ n m hm Δ hΔsort hΔdvd η hη

/-- Necessity of the actual higher presentation. The source grammar produces
the collapsing constructor; division, unabsorbed ANF and hull inversion
produce its high part and tail. The high-part inequality follows by comparing
with a low residual beyond both the real tail and the actual argument star. -/
theorem fixed_limit_higherPresentation (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (Δ : SourceNotationOrdinal τ n (m + 1))
    (hΔsort : Δ.val < omegaSequence τ (m + 2))
    (hΔdvd : omegaSequence τ (m + 1) ∣ Δ.val)
    (η : Ordinal.{0}) (hη : η < omegaSequence τ (m + 1))
    (hηsource : sourceNotation τ n m η) (hl : Order.IsSuccLimit η)
    (he : residualImageSup τ n m Δ.val η = η) : HigherPresentation τ hτ n m hm Δ η := by
  have hz : 0 < η := zero_lt_one.trans (Ordinal.one_lt_of_isSuccLimit hl)
  have hp : Ordinal.IsPrincipal (· + ·) η := he ▸ residualImageSup_add_closed τ n m hm Δ.val η
  have hbη := base_lt_fixed_limit τ hτ n m hm Δ hΔsort η hη hl he
  have hcases := sourceNotation_principal_cases τ hτ n m hm hηsource hz hp
  rcases hcases with hlow | ⟨k, ξ, hmk, hk, hξ, hξsort, hηξ⟩
  · exact False.elim (lt_asymm hlow hbη)
  · have hkm : k = m := by
      by_contra hkm
      have hmklt : m < k := lt_of_le_of_ne hmk (Ne.symm hkm)
      have hΩk : omegaSequence τ (m + 1) ≤ omegaSequence τ k :=
        (omegaSequence_strictMono τ).monotone (Nat.succ_le_of_lt hmklt)
      have hbad : omegaSequence τ (m + 1) ≤ η := hΩk.trans
        ((sourceFiniteCollapse_bounds τ n k hk ξ).1.trans_eq hηξ.symm)
      exact hη.not_ge hbad
    subst k
    let b : SourceNotationOrdinal τ n (m + 1) :=
      ⟨ξ, sourceNotation_upward τ n m (m + 1) (Nat.le_succ m) (Nat.succ_le_of_lt hm) hξ⟩
    let Ω := omegaSequence τ (m + 1)
    let Γ := Ω * (b.val / Ω)
    let ρ := b.val % Ω
    have hΩ := next_cardinal_pos τ hτ m
    have hΓdvd : Ω ∣ Γ := ⟨b.val / Ω, rfl⟩
    have hρΩ : ρ < Ω := Ordinal.mod_lt _ (ne_of_gt hΩ)
    have hdecomp : Γ + ρ = b.val := Ordinal.div_add_mod _ _
    have hΓsort : Γ < omegaSequence τ (m + 2) :=
      (Ordinal.mul_div_le _ _).trans_lt hξsort
    let g : SourceNotationOrdinal τ n (m + 1) := ⟨Γ, high_part_notation τ hτ n m hm b hξsort⟩
    have hρ : ρ < η := by
      have ht := tail_lt_collapse τ hτ n m hm g hΓsort hΓdvd ρ hρΩ
      rw [hdecomp] at ht
      exact ht.trans_eq hηξ.symm
    have hsb : sourceStar τ hτ n m hm b < η :=
      (sourceStar_lt_sourceFiniteCollapse τ hτ n m hm b hξsort).trans_eq hηξ.symm
    have hΔΓ : Δ.val < Γ := by
      by_contra! hΓΔ
      let σ := max ρ (sourceStar τ hτ n m hm b) + 1
      have hmax : max ρ (sourceStar τ hτ n m hm b) < η := max_lt_iff.mpr ⟨hρ, hsb⟩
      have hση : σ < η := hl.add_one_lt hmax
      have hσΩ := hση.trans hη
      have hρσ : ρ < σ := (le_max_left _ _).trans_lt (lt_add_one _)
      have hbsσ : sourceStar τ hτ n m hm b < σ := (le_max_right _ _).trans_lt (lt_add_one _)
      let a := shiftArgument τ n m hm Δ σ hσΩ
      have ha := shiftArgument_sort τ n m hm Δ hΔsort σ hσΩ
      have hba : b.val < a.val := by
        rw [← hdecomp]
        exact (add_le_add_left hΓΔ ρ).trans_lt (add_lt_add_right hρσ Δ.val)
      have hstar : sourceStar τ hτ n m hm b < sourceFiniteCollapse τ n m a.val :=
        hbsσ.trans (tail_lt_collapse τ hτ n m hm Δ hΔsort hΔdvd σ hσΩ)
      have hv := (sourceFiniteCollapse_lt_iff_sourceStar τ hτ n m hm b a hξsort ha).mpr
        (Or.inl ⟨hba, hstar⟩)
      have hvη : η < sourceFiniteCollapse τ n m (Δ.val + σ) := hηξ.trans_lt hv
      exact hvη.not_ge ((image_le_sup τ n m Δ.val η σ hση).trans_eq he)
    have hsΔ : sourceStar τ hτ n m hm Δ < η :=
      (sourceStar_lt_sourceFiniteCollapse τ hτ n m hm Δ hΔsort).trans
        (by simpa only [add_zero] using image_lt_fixed_limit τ hτ n m hm Δ hΔsort η hη hl he 0 hz)
    exact ⟨b, Γ, ρ, hξ, hξsort, hΓdvd, hρΩ, hdecomp.symm, hΔΓ, hηξ, hsΔ⟩

/-- The proper-limit reading of Lemma 2.30 on the genuine finite source
domain. All constructor, sort, tail and star facts are derived from the
actual source minimum and comparison. -/
theorem proper_limit_fixed_iff (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (Δ : SourceNotationOrdinal τ n (m + 1))
    (hΔsort : Δ.val < omegaSequence τ (m + 2))
    (hΔdvd : omegaSequence τ (m + 1) ∣ Δ.val)
    (η : Ordinal.{0}) (hη : η < omegaSequence τ (m + 1))
    (hηsource : sourceNotation τ n m η) (hl : Order.IsSuccLimit η) :
    residualImageSup τ n m Δ.val η = η ↔ HigherPresentation τ hτ n m hm Δ η :=
  ⟨fixed_limit_higherPresentation τ hτ n m hm Δ hΔsort hΔdvd η hη hηsource hl,
    higherPresentation_fixed τ hτ n m hm Δ hΔsort hΔdvd η hη⟩

/-- A repaired complete criterion, with both ordinary-supremum boundary
cases retained explicitly rather than silently discarded. -/
theorem fixed_iff_boundary_or_higher (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (Δ : SourceNotationOrdinal τ n (m + 1))
    (hΔsort : Δ.val < omegaSequence τ (m + 2))
    (hΔdvd : omegaSequence τ (m + 1) ∣ Δ.val)
    (η : Ordinal.{0}) (hη : η < omegaSequence τ (m + 1))
    (hηsource : sourceNotation τ n m η) :
    residualImageSup τ n m Δ.val η = η ↔
      η = 0 ∨ (η = 1 ∧ m = 0 ∧ τ = 1 ∧ Δ.val = 0) ∨
        (Order.IsSuccLimit η ∧ HigherPresentation τ hτ n m hm Δ η) := by
  constructor
  · intro he
    rcases fixed_residual_cases τ hτ n m hm Δ hΔsort hΔdvd η hη he with hz | hb | hl
    · exact Or.inl hz
    · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr ⟨hl, fixed_limit_higherPresentation τ hτ n m hm Δ hΔsort hΔdvd η hη hηsource hl he⟩)
  · rintro (rfl | ⟨rfl, hm0, hτ1, hd0⟩ | ⟨hl, hp⟩)
    · exact residualImageSup_zero τ n m Δ.val
    · simpa only [zero_add] using (fixed_successor_iff τ hτ n m hm Δ hΔsort hΔdvd 0
        (by simpa only [zero_add] using hη)).mpr ⟨rfl, hm0, hτ1, hd0⟩
    · exact higherPresentation_fixed τ hτ n m hm Δ hΔsort hΔdvd η hη hp

theorem source_notation_multiple_add_low_iff (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (Δ η : Ordinal.{0})
    (hΔdvd : omegaSequence τ (m + 1) ∣ Δ) (hη : η < omegaSequence τ (m + 1)) :
    sourceNotation τ n m (Δ + η) ↔ sourceNotation τ n m Δ ∧ sourceNotation τ n m η := by
  rw [sourceNotation_iff_hull τ n m hm (Δ + η), sourceNotation_iff_hull τ n m hm Δ,
    sourceNotation_iff_hull τ n m hm η]
  exact source_hull_multiple_add_low_iff τ hτ n m hm (omegaSequence τ (m + 2)) 0 Δ η hΔdvd hη

/-- The literal Convention 2.28 caller supplies its original same-level
constructor argument. The residual admission required for the grammar proof
is extracted from that argument's actual hull, not imposed separately. -/
theorem source_argument_fixed_iff (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (Δ : SourceNotationOrdinal τ n (m + 1))
    (hΔsort : Δ.val < omegaSequence τ (m + 2))
    (hΔdvd : omegaSequence τ (m + 1) ∣ Δ.val)
    (η : Ordinal.{0}) (hη : η < omegaSequence τ (m + 1))
    (harg : sourceNotation τ n m (Δ.val + η)) :
    residualImageSup τ n m Δ.val η = η ↔
      η = 0 ∨ (η = 1 ∧ m = 0 ∧ τ = 1 ∧ Δ.val = 0) ∨
        (Order.IsSuccLimit η ∧ HigherPresentation τ hτ n m hm Δ η) :=
  fixed_iff_boundary_or_higher τ hτ n m hm Δ hΔsort hΔdvd η hη
    ((source_notation_multiple_add_low_iff τ hτ n m hm Δ.val η hΔdvd hη).mp harg).2

/-- In the fine-predecessor normal decomposition, a unit prefix forces
the final principal summand to be a unit too. The separate printed unit
branch therefore includes this exceptional prefix. -/
theorem sourceNormalSum_prefix_one_last_eq_one {ξ β : Ordinal.{0}}
    (h : SourceNormalSum ξ 1 β) : β = 1 := by
  rcases h with hz | ⟨xs, hxs, hprefix, hvalue⟩
  · exact False.elim (zero_ne_one hz.2.1.symm)
  · have hβ := hxs.1 β (List.mem_append_right _ (List.mem_singleton_self _))
    have hn := sourceNormalSum_canonical_concat (Or.inr ⟨xs, hxs, hprefix, hvalue⟩ : SourceNormalSum ξ 1 β)
    rw [canonicalANF_principal zero_lt_one Ordinal.isPrincipal_add_one,
      canonicalANF_principal hβ.1 hβ.2] at hn
    have hβ1 : β ≤ 1 := (List.pairwise_append.mp hn.2).2.2 1 (List.mem_singleton_self _)
      β (List.mem_singleton_self _)
    exact le_antisymm hβ1 (one_le_of_pos hβ.1)

noncomputable def globalResidualImageSup (τ : Ordinal.{0}) (m : Nat) (Δ η : Ordinal.{0}) : Ordinal.{0} :=
  Ordinal.bsup η (fun σ _ => globalCollapse τ m (Δ + σ))

/-- The entire bounded family has one genuine finite fragment: each low
residual is a parameter in the same next-level grammar. -/
theorem globalResidualImageSup_finite_agreement (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hmn : m + 1 < n) (Δ : SourceNotationOrdinal τ n (m + 1))
    (hΔsort : Δ.val < omegaSequence τ (m + 2))
    (η : Ordinal.{0}) (hη : η < omegaSequence τ (m + 1)) :
    globalResidualImageSup τ m Δ.val η = residualImageSup τ n m Δ.val η := by
  unfold globalResidualImageSup residualImageSup
  congr 1
  funext σ hσ
  have hm : m < n := by omega
  have hσΩ := hσ.trans hη
  have hb := source_finite_notation_sorted_lt_boundary τ hτ n (m + 1) (m + 1)
    le_rfl hmn (shiftArgument τ n m hm Δ σ hσΩ).property
      (shiftArgument_sort τ n m hm Δ hΔsort σ hσΩ)
  exact globalCollapse_finite_agreement τ hτ n m hm (Δ.val + σ) hb

private theorem commonResidualFragment (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) (Δ : GlobalNotationOrdinal τ (m + 1)) {η : Ordinal.{0}}
    (hηsource : GlobalNotation τ m η) :
    ∃ n, m + 1 < n ∧ sourceNotation τ n (m + 1) Δ.val ∧ sourceNotation τ n m η := by
  obtain ⟨nd, hmd, hd⟩ := globalNotation_finite_witness τ hτ (m + 1) Δ.property
  obtain ⟨ne, hme, he⟩ := globalNotation_finite_witness τ hτ m hηsource
  refine ⟨max nd ne, hmd.trans_le (le_max_left nd ne), ?_, ?_⟩
  · exact sourceNotation_fragment_mono τ hτ nd (m + 1) (max nd ne) hmd.le (le_max_left nd ne) hd
  · exact sourceNotation_fragment_mono τ hτ ne m (max nd ne) hme.le (le_max_right nd ne) he

def GlobalHigherPresentation (τ : Ordinal.{0}) (hτ : 0 < τ) (m : Nat)
    (Δ : GlobalNotationOrdinal τ (m + 1)) (η : Ordinal.{0}) : Prop :=
  ∃ b : GlobalNotationOrdinal τ (m + 1), ∃ Γ ρ : Ordinal.{0},
    GlobalNotation τ m b.val ∧ b.val < omegaSequence τ (m + 2) ∧ omegaSequence τ (m + 1) ∣ Γ ∧
      ρ < omegaSequence τ (m + 1) ∧ b.val = Γ + ρ ∧ Δ.val < Γ ∧
        η = globalCollapse τ m b.val ∧ globalStar τ hτ m Δ < η

theorem global_higherPresentation_fixed (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) (Δ : GlobalNotationOrdinal τ (m + 1))
    (hΔsort : Δ.val < omegaSequence τ (m + 2))
    (hΔdvd : omegaSequence τ (m + 1) ∣ Δ.val)
    (η : Ordinal.{0}) (hη : η < omegaSequence τ (m + 1))
    (hp : GlobalHigherPresentation τ hτ m Δ η) : globalResidualImageSup τ m Δ.val η = η := by
  obtain ⟨b, Γ, ρ, hbm, hb, hΓ, hρ, hbe, hΔΓ, hηb, hsΔ⟩ := hp
  obtain ⟨n, hmn, hd, hbnm⟩ := commonResidualFragment τ hτ m Δ hbm
  have hm : m < n := by omega
  have hbn := sourceNotation_upward τ n m (m + 1) (Nat.le_succ m) hmn.le hbnm
  let dn : SourceNotationOrdinal τ n (m + 1) := ⟨Δ.val, hd⟩
  let bn : SourceNotationOrdinal τ n (m + 1) := ⟨b.val, hbn⟩
  have hbnd := source_finite_notation_sorted_lt_boundary τ hτ n (m + 1) (m + 1) le_rfl hmn hbn hb
  have hηbn : η = sourceFiniteCollapse τ n m bn.val :=
    hηb.trans (globalCollapse_finite_agreement τ hτ n m hm b.val hbnd)
  have hs : sourceStar τ hτ n m hm dn < η := by
    rwa [globalStar_finite_agreement τ hτ m Δ n hm dn rfl] at hsΔ
  rw [globalResidualImageSup_finite_agreement τ hτ n m hmn dn hΔsort η hη]
  exact higherPresentation_fixed τ hτ n m hm dn hΔsort hΔdvd η hη
    ⟨bn, Γ, ρ, hbnm, hb, hΓ, hρ, hbe, hΔΓ, hηbn, hs⟩

theorem global_fixed_limit_higherPresentation (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) (Δ : GlobalNotationOrdinal τ (m + 1))
    (hΔsort : Δ.val < omegaSequence τ (m + 2))
    (hΔdvd : omegaSequence τ (m + 1) ∣ Δ.val)
    (η : Ordinal.{0}) (hη : η < omegaSequence τ (m + 1))
    (hηsource : GlobalNotation τ m η) (hl : Order.IsSuccLimit η)
    (he : globalResidualImageSup τ m Δ.val η = η) : GlobalHigherPresentation τ hτ m Δ η := by
  obtain ⟨n, hmn, hd, hen⟩ := commonResidualFragment τ hτ m Δ hηsource
  have hm : m < n := by omega
  let dn : SourceNotationOrdinal τ n (m + 1) := ⟨Δ.val, hd⟩
  have hsup := globalResidualImageSup_finite_agreement τ hτ n m hmn dn hΔsort η hη
  have hfixed := hsup.symm.trans he
  obtain ⟨b, Γ, ρ, hbm, hb, hΓ, hρ, hbe, hΔΓ, hηb, hsΔ⟩ :=
    fixed_limit_higherPresentation τ hτ n m hm dn hΔsort hΔdvd η hη hen hl hfixed
  let bg : GlobalNotationOrdinal τ (m + 1) :=
    ⟨b.val, sourceNotation_to_globalNotation τ hτ n (m + 1) hmn b.property⟩
  have hbnd := source_finite_notation_sorted_lt_boundary τ hτ n (m + 1) (m + 1)
    le_rfl hmn b.property hb
  have hηbg : η = globalCollapse τ m bg.val :=
    hηb.trans (globalCollapse_finite_agreement τ hτ n m hm b.val hbnd).symm
  have hs : globalStar τ hτ m Δ < η := by
    rw [globalStar_finite_agreement τ hτ m Δ n hm dn rfl]
    exact hsΔ
  exact ⟨bg, Γ, ρ, sourceNotation_to_globalNotation τ hτ n m hm hbm,
    hb, hΓ, hρ, hbe, hΔΓ, hηbg, hs⟩

theorem global_proper_limit_fixed_iff (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) (Δ : GlobalNotationOrdinal τ (m + 1))
    (hΔsort : Δ.val < omegaSequence τ (m + 2))
    (hΔdvd : omegaSequence τ (m + 1) ∣ Δ.val)
    (η : Ordinal.{0}) (hη : η < omegaSequence τ (m + 1))
    (hηsource : GlobalNotation τ m η) (hl : Order.IsSuccLimit η) :
    globalResidualImageSup τ m Δ.val η = η ↔ GlobalHigherPresentation τ hτ m Δ η :=
  ⟨global_fixed_limit_higherPresentation τ hτ m Δ hΔsort hΔdvd η hη hηsource hl,
    global_higherPresentation_fixed τ hτ m Δ hΔsort hΔdvd η hη⟩

theorem global_fixed_iff_boundary_or_higher (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) (Δ : GlobalNotationOrdinal τ (m + 1))
    (hΔsort : Δ.val < omegaSequence τ (m + 2))
    (hΔdvd : omegaSequence τ (m + 1) ∣ Δ.val)
    (η : Ordinal.{0}) (hη : η < omegaSequence τ (m + 1))
    (hηsource : GlobalNotation τ m η) :
    globalResidualImageSup τ m Δ.val η = η ↔
      η = 0 ∨ (η = 1 ∧ m = 0 ∧ τ = 1 ∧ Δ.val = 0) ∨
        (Order.IsSuccLimit η ∧ GlobalHigherPresentation τ hτ m Δ η) := by
  obtain ⟨n, hmn, hd, hen⟩ := commonResidualFragment τ hτ m Δ hηsource
  have hm : m < n := by omega
  let dn : SourceNotationOrdinal τ n (m + 1) := ⟨Δ.val, hd⟩
  have hsup := globalResidualImageSup_finite_agreement τ hτ n m hmn dn hΔsort η hη
  constructor
  · intro he
    rcases fixed_residual_cases τ hτ n m hm dn hΔsort hΔdvd η hη (hsup.symm.trans he) with hz | hb | hl
    · exact Or.inl hz
    · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr ⟨hl, global_fixed_limit_higherPresentation τ hτ m Δ hΔsort hΔdvd η hη hηsource hl he⟩)
  · rintro (hz | hb | ⟨hl, hp⟩)
    · rw [hsup, hz, residualImageSup_zero]
    · rw [hsup]
      exact (fixed_iff_boundary_or_higher τ hτ n m hm dn hΔsort hΔdvd η hη hen).mpr (Or.inr (Or.inl hb))
    · exact global_higherPresentation_fixed τ hτ m Δ hΔsort hΔdvd η hη hp

theorem global_notation_multiple_add_low_iff (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) (Δ η : Ordinal.{0}) (hΔdvd : omegaSequence τ (m + 1) ∣ Δ)
    (hη : η < omegaSequence τ (m + 1)) :
    GlobalNotation τ m (Δ + η) ↔ GlobalNotation τ m Δ ∧ GlobalNotation τ m η := by
  constructor
  · intro harg
    obtain ⟨n, hm, hn⟩ := globalNotation_finite_witness τ hτ m harg
    obtain ⟨hd, he⟩ := (source_notation_multiple_add_low_iff τ hτ n m hm Δ η hΔdvd hη).mp hn
    exact ⟨sourceNotation_to_globalNotation τ hτ n m hm hd, sourceNotation_to_globalNotation τ hτ n m hm he⟩
  · rintro ⟨hd, he⟩
    exact .add hd he

/-- The repaired literal source criterion on the direct-limit family. Its
only source admission premise is the original same-level argument, alongside
the genuine high-part domain and cardinal sort used by source collapse. -/
theorem global_source_argument_fixed_iff (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) (Δ : GlobalNotationOrdinal τ (m + 1))
    (hΔsort : Δ.val < omegaSequence τ (m + 2))
    (hΔdvd : omegaSequence τ (m + 1) ∣ Δ.val)
    (η : Ordinal.{0}) (hη : η < omegaSequence τ (m + 1))
    (harg : GlobalNotation τ m (Δ.val + η)) :
    globalResidualImageSup τ m Δ.val η = η ↔
      η = 0 ∨ (η = 1 ∧ m = 0 ∧ τ = 1 ∧ Δ.val = 0) ∨
        (Order.IsSuccLimit η ∧ GlobalHigherPresentation τ hτ m Δ η) :=
  global_fixed_iff_boundary_or_higher τ hτ m Δ hΔsort hΔdvd η hη
    ((global_notation_multiple_add_low_iff τ hτ m Δ.val η hΔdvd hη).mp harg).2

theorem global_strict_sup_iff_not_fixed (τ : Ordinal.{0}) (hτ : 0 < τ)
    (m : Nat) (Δ : GlobalNotationOrdinal τ (m + 1))
    (hΔsort : Δ.val < omegaSequence τ (m + 2))
    (hΔdvd : omegaSequence τ (m + 1) ∣ Δ.val)
    (η : Ordinal.{0}) (hη : η < omegaSequence τ (m + 1)) :
    η < globalResidualImageSup τ m Δ.val η ↔ globalResidualImageSup τ m Δ.val η ≠ η := by
  obtain ⟨n, hmn, hd⟩ := globalNotation_finite_witness τ hτ (m + 1) Δ.property
  have hm : m < n := by omega
  let dn : SourceNotationOrdinal τ n (m + 1) := ⟨Δ.val, hd⟩
  rw [globalResidualImageSup_finite_agreement τ hτ n m hmn dn hΔsort η hη]
  exact strict_sup_iff_not_fixed τ hτ n m hm dn hΔsort hΔdvd η hη

end Alexander313.Wilken.SourceFixedPointLimits
