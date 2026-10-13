import Alexander313.Wilken.MultiplicativePrincipalArithmetic

/-!
# Genuine reduced multiplicative normal forms

For an actual positive additive principal alpha=omega^delta, the actual ANF
of delta gives the ordered factors omega^a. Their product is alpha by real
ordinal exponent addition. Each factor belongs to Wilken's displayed class M
and is greater than one. Real omega logarithms turn any other reduced word
into an ANF of delta; genuine ANF uniqueness therefore proves word uniqueness.

The source's weakly decreasing M words permit unit factors. IsMNF retains that
convention; IsReducedMNF explicitly excludes units. Only reduced words are
claimed unique. The unit ordinal has the empty reduced word and last factor
one, in accordance with the source's complete prefix/last convention. No
factorization, logarithm, arithmetic, semantic chooser or effectivity oracle
is supplied. This module is ordinal mathematics, not a coded algorithm.
All proof terms remain uncompiled candidates.
-/

namespace Alexander313.Wilken.MultiplicativeNormalForm

universe u

open MultiplicativePrincipalArithmetic

/-- The actual ordered ordinal product, with empty product one. -/
def factorProduct : List Ordinal.{u} → Ordinal.{u}
  | [] => 1
  | a :: xs => a * factorProduct xs

theorem factorProduct_foldr (xs : List Ordinal.{u}) : factorProduct xs = xs.foldr (· * ·) 1 := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [factorProduct, List.foldr_cons, ih]

theorem factorProduct_append (xs ys : List Ordinal.{u}) :
    factorProduct (xs ++ ys) = factorProduct xs * factorProduct ys := by
  induction xs with
  | nil => simp only [List.nil_append, factorProduct, one_mul]
  | cons a xs ih => simp only [List.cons_append, factorProduct, ih, mul_assoc]

/-- Source words allow one: this predicate alone does not give uniqueness. -/
def IsMNF (xs : List Ordinal.{u}) : Prop :=
  (∀ a ∈ xs, IsMultiplicativePrincipal a) ∧ xs.Pairwise (fun a b => b ≤ a)

/-- The unique convention removes all unit factors. -/
def IsReducedMNF (xs : List Ordinal.{u}) : Prop :=
  IsMNF xs ∧ ∀ a ∈ xs, 1 < a

theorem isMNF_nil : IsMNF ([] : List Ordinal.{u}) := by simp [IsMNF]

theorem isReducedMNF_nil : IsReducedMNF ([] : List Ordinal.{u}) := by simp [IsReducedMNF, IsMNF]

theorem isReducedMNF_singleton {a : Ordinal.{u}} (hm : IsMultiplicativePrincipal a) (ha : 1 < a) :
    IsReducedMNF [a] := by simp [IsReducedMNF, IsMNF, hm, ha]

theorem isMNF_tail {a : Ordinal.{u}} {xs : List Ordinal.{u}} (h : IsMNF (a :: xs)) : IsMNF xs :=
  ⟨fun b hb => h.1 b (List.mem_cons_of_mem _ hb), (List.pairwise_cons.mp h.2).2⟩

theorem isReducedMNF_tail {a : Ordinal.{u}} {xs : List Ordinal.{u}}
    (h : IsReducedMNF (a :: xs)) : IsReducedMNF xs :=
  ⟨isMNF_tail h.1, fun b hb => h.2 b (List.mem_cons_of_mem _ hb)⟩

/-- This explicitly records the ambiguity excluded by the reduced convention. -/
theorem source_unit_ambiguity : IsMNF ([] : List Ordinal.{u}) ∧ IsMNF [1] ∧
    factorProduct ([] : List Ordinal.{u}) = factorProduct [1] ∧ ([] : List Ordinal.{u}) ≠ [1] := by
  simp [IsMNF, factorProduct]
  exact ⟨zero_lt_one, Ordinal.isPrincipal_add_one, Ordinal.isPrincipal_mul_one⟩

private theorem pairwise_map_monotone (xs : List Ordinal.{u}) (f : Ordinal.{u} → Ordinal.{u})
    (hf : Monotone f) (hx : xs.Pairwise (fun a b => b ≤ a)) :
    (xs.map f).Pairwise (fun a b => b ≤ a) := by
  revert hx
  induction xs with
  | nil => intro _; exact List.Pairwise.nil
  | cons a xs ih =>
    intro hx
    have ht := List.pairwise_cons.mp hx
    apply List.pairwise_cons.mpr
    refine ⟨?_, ih ht.2⟩
    intro b hb
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
    exact hf (ht.1 c hc)

/-- Actual exponent addition computes the value of every power-factor word. -/
theorem factorProduct_omega_map (xs : List Ordinal.{u}) :
    factorProduct (xs.map (fun a => Ordinal.omega0 ^ a)) = Ordinal.omega0 ^ principalSum xs := by
  induction xs with
  | nil => simp only [List.map_nil, factorProduct, principalSum, Ordinal.opow_zero]
  | cons a xs ih => simp only [List.map_cons, factorProduct, principalSum, ih, Ordinal.opow_add]

noncomputable def omegaFactors (δ : Ordinal.{u}) : List Ordinal.{u} :=
  (canonicalANF δ).map (fun a => Ordinal.omega0 ^ a)

theorem factorProduct_omegaFactors (δ : Ordinal.{u}) :
    factorProduct (omegaFactors δ) = Ordinal.omega0 ^ δ := by
  rw [omegaFactors, factorProduct_omega_map, principalSum_canonicalANF]

theorem omegaFactors_reduced (δ : Ordinal.{u}) : IsReducedMNF (omegaFactors δ) := by
  have hn := canonicalANF_normal δ
  refine ⟨⟨?_, pairwise_map_monotone _ _
    (Ordinal.isNormal_opow Ordinal.one_lt_omega0).strictMono.monotone hn.2⟩, ?_⟩
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    have hp := hn.1 b hb
    exact ⟨Ordinal.opow_pos _ Ordinal.omega0_pos, Ordinal.isPrincipal_add_omega0_opow _,
      (omegaPower_multiplicative_iff b).mpr (Or.inr hp)⟩
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    have h := (Ordinal.isNormal_opow Ordinal.one_lt_omega0).strictMono (hn.1 b hb).1
    simpa only [Ordinal.opow_zero] using h

/-- The real library logarithm is used only in the ordinal proof. -/
noncomputable def factorLogs (xs : List Ordinal.{u}) : List Ordinal.{u} :=
  xs.map (Ordinal.log Ordinal.omega0)

theorem positivePrincipal_eq_omegaLog {a : Ordinal.{u}} (ha : 0 < a)
    (hp : Ordinal.IsPrincipal (· + ·) a) : Ordinal.omega0 ^ Ordinal.log Ordinal.omega0 a = a := by
  rcases Ordinal.isPrincipal_add_iff_zero_or_omega0_opow.mp hp with hz | ⟨δ, hδ⟩
  · exact False.elim ((ne_of_gt ha) hz)
  · rw [← hδ, Ordinal.log_opow Ordinal.one_lt_omega0]

theorem multiplicative_log_spec {a : Ordinal.{u}} (hm : IsMultiplicativePrincipal a) (ha : 1 < a) :
    0 < Ordinal.log Ordinal.omega0 a ∧ Ordinal.IsPrincipal (· + ·) (Ordinal.log Ordinal.omega0 a) := by
  have he := positivePrincipal_eq_omegaLog hm.1 hm.2.1
  have hn : Ordinal.log Ordinal.omega0 a ≠ 0 := by
    intro hz
    have hu : (1 : Ordinal.{u}) = a := by simpa only [hz, Ordinal.opow_zero] using he
    exact (ne_of_gt ha) hu.symm
  have hmul := hm.2.2
  rw [← he] at hmul
  exact ⟨pos_iff_ne_zero.mpr hn,
    Ordinal.isPrincipal_add_of_isPrincipal_mul_opow Ordinal.one_lt_omega0 hmul⟩

theorem factorLogs_normal {xs : List Ordinal.{u}} (hx : IsReducedMNF xs) :
    IsAdditiveNormalForm (factorLogs xs) := by
  constructor
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact multiplicative_log_spec (hx.1.1 b hb) (hx.2 b hb)
  · exact pairwise_map_monotone _ _ (fun _ _ h => Ordinal.log_mono_right Ordinal.omega0 h) hx.1.2

theorem factorLogs_product (xs : List Ordinal.{u}) (hx : ∀ a ∈ xs, IsMultiplicativePrincipal a) :
    Ordinal.omega0 ^ principalSum (factorLogs xs) = factorProduct xs := by
  revert hx
  induction xs with
  | nil => intro _; simp only [factorLogs, List.map_nil, principalSum, Ordinal.opow_zero, factorProduct]
  | cons a xs ih =>
    intro hx
    have ha := hx a List.mem_cons_self
    have ht := fun b hb => hx b (List.mem_cons_of_mem _ hb)
    change Ordinal.omega0 ^ (Ordinal.log Ordinal.omega0 a + principalSum (factorLogs xs)) = a * factorProduct xs
    rw [Ordinal.opow_add, positivePrincipal_eq_omegaLog ha.1 ha.2.1, ih ht]

theorem factorLogs_recovery (xs : List Ordinal.{u}) (hx : ∀ a ∈ xs, IsMultiplicativePrincipal a) :
    (factorLogs xs).map (fun a => Ordinal.omega0 ^ a) = xs := by
  rw [factorLogs, List.map_map]
  calc
    xs.map ((fun a => Ordinal.omega0 ^ a) ∘ Ordinal.log Ordinal.omega0) = xs.map id := by
      apply List.map_congr_left
      intro a ha
      exact positivePrincipal_eq_omegaLog (hx a ha).1 (hx a ha).2.1
    _ = xs := by simp only [List.map_id]

theorem factorLogs_omegaFactors (δ : Ordinal.{u}) : factorLogs (omegaFactors δ) = canonicalANF δ := by
  simp only [factorLogs, omegaFactors, List.map_map]
  have hfun : (Ordinal.log Ordinal.omega0) ∘ (fun a : Ordinal.{u} => Ordinal.omega0 ^ a) = id := by
    funext a
    exact Ordinal.log_opow Ordinal.one_lt_omega0 a
  rw [hfun, List.map_id]

theorem reducedMNF_exponent {xs : List Ordinal.{u}} (hx : IsReducedMNF xs) :
    canonicalANF (principalSum (factorLogs xs)) = factorLogs xs :=
  canonicalANF_eq_of_normal (factorLogs_normal hx) rfl

theorem reducedMNF_unique {xs ys : List Ordinal.{u}} (hx : IsReducedMNF xs)
    (hy : IsReducedMNF ys) (he : factorProduct xs = factorProduct ys) : xs = ys := by
  have hs : principalSum (factorLogs xs) = principalSum (factorLogs ys) :=
    (Ordinal.isNormal_opow Ordinal.one_lt_omega0).strictMono.injective
      ((factorLogs_product xs hx.1.1).trans (he.trans (factorLogs_product ys hy.1.1).symm))
  have hl := additiveNormalForm_unique (factorLogs_normal hx) (factorLogs_normal hy) hs
  rw [← factorLogs_recovery xs hx.1.1, ← factorLogs_recovery ys hy.1.1, hl]

theorem reducedMNF_eq_omegaFactors {xs : List Ordinal.{u}} {δ : Ordinal.{u}}
    (hx : IsReducedMNF xs) (he : factorProduct xs = Ordinal.omega0 ^ δ) : xs = omegaFactors δ :=
  reducedMNF_unique hx (omegaFactors_reduced δ) (he.trans (factorProduct_omegaFactors δ).symm)

theorem reducedMNF_product_one_iff {xs : List Ordinal.{u}} (hx : IsReducedMNF xs) :
    factorProduct xs = 1 ↔ xs = [] := by
  constructor
  · intro he
    exact reducedMNF_unique hx isReducedMNF_nil he
  · intro he
    rw [he, factorProduct]

noncomputable def canonicalMNF (α : Ordinal.{u}) : List Ordinal.{u} := omegaFactors (Ordinal.log Ordinal.omega0 α)

theorem canonicalMNF_reduced (α : Ordinal.{u}) : IsReducedMNF (canonicalMNF α) := omegaFactors_reduced _

theorem factorProduct_canonicalMNF {α : Ordinal.{u}} (hα : 0 < α)
    (hp : Ordinal.IsPrincipal (· + ·) α) : factorProduct (canonicalMNF α) = α :=
  (factorProduct_omegaFactors _).trans (positivePrincipal_eq_omegaLog hα hp)

theorem canonicalMNF_omegaPower (δ : Ordinal.{u}) : canonicalMNF (Ordinal.omega0 ^ δ) = omegaFactors δ := by
  rw [canonicalMNF, Ordinal.log_opow Ordinal.one_lt_omega0]

theorem reducedMNF_exists {α : Ordinal.{u}} (hα : 0 < α) (hp : Ordinal.IsPrincipal (· + ·) α) :
    ∃ xs : List Ordinal.{u}, IsReducedMNF xs ∧ factorProduct xs = α :=
  ⟨canonicalMNF α, canonicalMNF_reduced α, factorProduct_canonicalMNF hα hp⟩

theorem reducedMNF_exists_unique {α : Ordinal.{u}} (hα : 0 < α) (hp : Ordinal.IsPrincipal (· + ·) α) :
    ∃! xs : List Ordinal.{u}, IsReducedMNF xs ∧ factorProduct xs = α := by
  obtain ⟨xs, hx, hv⟩ := reducedMNF_exists hα hp
  exact ⟨xs, ⟨hx, hv⟩, fun ys hy => reducedMNF_unique hy.1 hx (hy.2.trans hv.symm)⟩

theorem isMNF_product_principal {xs : List Ordinal.{u}} (hx : IsMNF xs) :
    0 < factorProduct xs ∧ Ordinal.IsPrincipal (· + ·) (factorProduct xs) := by
  rw [← factorLogs_product xs hx.1]
  exact ⟨Ordinal.opow_pos _ Ordinal.omega0_pos, Ordinal.isPrincipal_add_omega0_opow _⟩

theorem reducedMNF_exists_iff (α : Ordinal.{u}) :
    (∃ xs : List Ordinal.{u}, IsReducedMNF xs ∧ factorProduct xs = α) ↔
      0 < α ∧ Ordinal.IsPrincipal (· + ·) α := by
  constructor
  · rintro ⟨xs, hx, rfl⟩
    exact isMNF_product_principal hx.1
  · rintro ⟨hα, hp⟩
    exact reducedMNF_exists hα hp

theorem omegaFactors_zero : omegaFactors (0 : Ordinal.{u}) = [] := by
  simp only [omegaFactors, canonicalANF_zero, List.map_nil]

theorem canonicalMNF_one : canonicalMNF (1 : Ordinal.{u}) = [] := by
  have h := canonicalMNF_omegaPower (0 : Ordinal.{u})
  simpa only [Ordinal.opow_zero, omegaFactors_zero] using h

theorem canonicalANF_nil_iff (δ : Ordinal.{u}) : canonicalANF δ = [] ↔ δ = 0 := by
  constructor
  · intro h
    have hv := principalSum_canonicalANF δ
    rw [h] at hv
    exact hv.symm
  · intro h
    rw [h, canonicalANF_zero]

theorem omegaFactors_nil_iff (δ : Ordinal.{u}) : omegaFactors δ = [] ↔ δ = 0 := by
  simp only [omegaFactors, List.map_eq_nil_iff, canonicalANF_nil_iff]

theorem omegaFactors_nonempty {δ : Ordinal.{u}} (hδ : 0 < δ) : omegaFactors δ ≠ [] :=
  fun h => (ne_of_gt hδ) ((omegaFactors_nil_iff δ).mp h)

theorem canonicalMNF_nil_iff {α : Ordinal.{u}} (hα : 0 < α)
    (hp : Ordinal.IsPrincipal (· + ·) α) : canonicalMNF α = [] ↔ α = 1 := by
  constructor
  · intro h
    have hv := factorProduct_canonicalMNF hα hp
    rw [h] at hv
    exact hv.symm
  · intro h
    rw [h, canonicalMNF_one]

/-- Component fallbacks are one for products and zero for exponent sums. -/
def firstFactor (xs : List Ordinal.{u}) : Ordinal.{u} := xs[0]?.getD 1

def lastFactor (xs : List Ordinal.{u}) : Ordinal.{u} := xs.reverse[0]?.getD 1

noncomputable def firstExponent (δ : Ordinal.{u}) : Ordinal.{u} := (canonicalANF δ)[0]?.getD 0

noncomputable def endExponent (δ : Ordinal.{u}) : Ordinal.{u} := (canonicalANF δ).reverse[0]?.getD 0

theorem firstExponent_of_anf {δ : Ordinal.{u}} {xs : List Ordinal.{u}}
    (hn : IsAdditiveNormalForm xs) (hv : principalSum xs = δ) : firstExponent δ = xs[0]?.getD 0 := by
  rw [firstExponent, canonicalANF_eq_of_normal hn hv]

theorem endExponent_of_anf {δ : Ordinal.{u}} {xs : List Ordinal.{u}}
    (hn : IsAdditiveNormalForm xs) (hv : principalSum xs = δ) : endExponent δ = xs.reverse[0]?.getD 0 := by
  rw [endExponent, canonicalANF_eq_of_normal hn hv]

private theorem first_map (f : Ordinal.{u} → Ordinal.{u}) (xs : List Ordinal.{u}) (z : Ordinal.{u}) :
    f (xs[0]?.getD z) = (xs.map f)[0]?.getD (f z) := by
  cases xs <;> rfl

theorem firstFactor_omega_map (xs : List Ordinal.{u}) :
    firstFactor (xs.map (fun a => Ordinal.omega0 ^ a)) = Ordinal.omega0 ^ (xs[0]?.getD (0 : Ordinal.{u})) := by
  simpa only [firstFactor, Ordinal.opow_zero] using
    (first_map (fun a => Ordinal.omega0 ^ a) xs 0).symm

theorem lastFactor_omega_map (xs : List Ordinal.{u}) :
    lastFactor (xs.map (fun a => Ordinal.omega0 ^ a)) = Ordinal.omega0 ^ (xs.reverse[0]?.getD (0 : Ordinal.{u})) := by
  simpa only [lastFactor, List.map_reverse, Ordinal.opow_zero] using
    (first_map (fun a => Ordinal.omega0 ^ a) xs.reverse 0).symm

theorem firstFactor_omegaFactors (δ : Ordinal.{u}) :
    firstFactor (omegaFactors δ) = Ordinal.omega0 ^ firstExponent δ := firstFactor_omega_map _

/-- This holds also at delta=0: the empty product has last factor one. -/
theorem lastFactor_omegaFactors (δ : Ordinal.{u}) :
    lastFactor (omegaFactors δ) = Ordinal.omega0 ^ endExponent δ := lastFactor_omega_map _

theorem firstFactor_mem (xs : List Ordinal.{u}) (hne : xs ≠ []) : firstFactor xs ∈ xs := by
  cases xs with
  | nil => exact False.elim (hne rfl)
  | cons a xs => exact List.mem_cons_self

theorem lastFactor_mem (xs : List Ordinal.{u}) (hne : xs ≠ []) : lastFactor xs ∈ xs := by
  have hr : xs.reverse ≠ [] := fun h => hne (List.reverse_eq_nil_iff.mp h)
  have hm := firstFactor_mem xs.reverse hr
  simpa only [firstFactor, lastFactor, List.mem_reverse] using hm

theorem firstFactor_spec {xs : List Ordinal.{u}} (hx : IsReducedMNF xs) (hne : xs ≠ []) :
    IsMultiplicativePrincipal (firstFactor xs) ∧ 1 < firstFactor xs :=
  ⟨hx.1.1 _ (firstFactor_mem xs hne), hx.2 _ (firstFactor_mem xs hne)⟩

theorem lastFactor_spec {xs : List Ordinal.{u}} (hx : IsReducedMNF xs) (hne : xs ≠ []) :
    IsMultiplicativePrincipal (lastFactor xs) ∧ 1 < lastFactor xs :=
  ⟨hx.1.1 _ (lastFactor_mem xs hne), hx.2 _ (lastFactor_mem xs hne)⟩

/-- The entire empty/unit case is explicit in these source component functions. -/
noncomputable def leadingFactor (α : Ordinal.{u}) : Ordinal.{u} := firstFactor (canonicalMNF α)

noncomputable def lf (α : Ordinal.{u}) : Ordinal.{u} := lastFactor (canonicalMNF α)

theorem leadingFactor_one : leadingFactor (1 : Ordinal.{u}) = 1 := by
  exact congrArg firstFactor canonicalMNF_one

theorem lf_one : lf (1 : Ordinal.{u}) = 1 := by
  exact congrArg lastFactor canonicalMNF_one

theorem leadingFactor_omegaPower (δ : Ordinal.{u}) :
    leadingFactor (Ordinal.omega0 ^ δ) = Ordinal.omega0 ^ firstExponent δ := by
  rw [leadingFactor, canonicalMNF_omegaPower, firstFactor_omegaFactors]

/-- Literal source last-factor law: lf(omega^delta)=omega^(end(delta)). -/
theorem lf_omegaPower (δ : Ordinal.{u}) : lf (Ordinal.omega0 ^ δ) = Ordinal.omega0 ^ endExponent δ := by
  rw [lf, canonicalMNF_omegaPower, lastFactor_omegaFactors]

theorem lf_omegaPower_of_anf {δ : Ordinal.{u}} {xs : List Ordinal.{u}}
    (hn : IsAdditiveNormalForm xs) (hv : principalSum xs = δ) :
    lf (Ordinal.omega0 ^ δ) = Ordinal.omega0 ^ (xs.reverse[0]?.getD (0 : Ordinal.{u})) := by
  rw [lf_omegaPower, endExponent_of_anf hn hv]

theorem reducedMNF_last {α : Ordinal.{u}} {xs : List Ordinal.{u}} (hα : 0 < α)
    (hp : Ordinal.IsPrincipal (· + ·) α) (hx : IsReducedMNF xs) (hv : factorProduct xs = α) :
    lastFactor xs = lf α := by
  have he : xs = canonicalMNF α := reducedMNF_unique hx (canonicalMNF_reduced α)
    (hv.trans (factorProduct_canonicalMNF hα hp).symm)
  simpa only [lf, he]

theorem reducedMNF_first {α : Ordinal.{u}} {xs : List Ordinal.{u}} (hα : 0 < α)
    (hp : Ordinal.IsPrincipal (· + ·) α) (hx : IsReducedMNF xs) (hv : factorProduct xs = α) :
    firstFactor xs = leadingFactor α := by
  have he : xs = canonicalMNF α := reducedMNF_unique hx (canonicalMNF_reduced α)
    (hv.trans (factorProduct_canonicalMNF hα hp).symm)
  simpa only [leadingFactor, he]

theorem canonicalMNF_multiplicative {α : Ordinal.{u}} (hm : IsMultiplicativePrincipal α)
    (hα : 1 < α) : canonicalMNF α = [α] := by
  have hl := multiplicative_log_spec hm hα
  have he := positivePrincipal_eq_omegaLog hm.1 hm.2.1
  simp only [canonicalMNF, omegaFactors, canonicalANF_principal hl.1 hl.2, List.map_cons,
    List.map_nil, he]

theorem lf_multiplicative {α : Ordinal.{u}} (hm : IsMultiplicativePrincipal α) : lf α = α := by
  by_cases hα : α = 1
  · subst α; exact lf_one
  · have hpos : 1 < α := (lt_or_eq_of_le (Order.one_le_iff_pos.mpr hm.1)).resolve_right
      (fun h => hα h.symm)
    exact congrArg lastFactor (canonicalMNF_multiplicative hm hpos)

/-- Remove the last factor; the empty and singleton prefixes both have product one. -/
def factorPrefix (xs : List Ordinal.{u}) : List Ordinal.{u} := xs.reverse.tail.reverse

theorem factorProduct_prefix_last (xs : List Ordinal.{u}) :
    factorProduct xs = factorProduct (factorPrefix xs) * lastFactor xs := by
  cases hr : xs.reverse with
  | nil =>
    have hz : xs = [] := List.reverse_eq_nil_iff.mp hr
    subst xs
    simp [factorProduct, factorPrefix, lastFactor]
  | cons a as =>
    have he : xs = as.reverse ++ [a] := by
      have h := congrArg List.reverse hr
      simpa only [List.reverse_reverse, List.reverse_cons] using h
    have hp : factorPrefix xs = as.reverse := congrArg (fun ys : List Ordinal.{u} => ys.tail.reverse) hr
    have hl : lastFactor xs = a := congrArg (fun ys : List Ordinal.{u} => ys[0]?.getD 1) hr
    calc
      factorProduct xs = factorProduct (as.reverse ++ [a]) := congrArg factorProduct he
      _ = factorProduct as.reverse * a := by simp only [factorProduct_append, factorProduct, mul_one]
      _ = factorProduct (factorPrefix xs) * lastFactor xs := by rw [hp, hl]

theorem source_prefix_last {α : Ordinal.{u}} (hα : 0 < α)
    (hp : Ordinal.IsPrincipal (· + ·) α) :
    α = factorProduct (factorPrefix (canonicalMNF α)) * lf α := by
  calc
    α = factorProduct (canonicalMNF α) := (factorProduct_canonicalMNF hα hp).symm
    _ = factorProduct (factorPrefix (canonicalMNF α)) * lastFactor (canonicalMNF α) :=
      factorProduct_prefix_last _
    _ = factorProduct (factorPrefix (canonicalMNF α)) * lf α := rfl

theorem source_prefix_last_one : factorProduct (factorPrefix (canonicalMNF (1 : Ordinal.{u}))) = 1 ∧
    lf (1 : Ordinal.{u}) = 1 := by
  constructor
  · simp only [canonicalMNF_one, factorPrefix, List.reverse_nil, List.tail_nil, factorProduct]
  · exact lf_one

theorem source_prefix_last_multiplicative {α : Ordinal.{u}} (hm : IsMultiplicativePrincipal α) :
    factorProduct (factorPrefix (canonicalMNF α)) = 1 ∧ lf α = α := by
  refine ⟨?_, lf_multiplicative hm⟩
  by_cases hα : α = 1
  · subst α; exact source_prefix_last_one.1
  · have hpos : 1 < α := (lt_or_eq_of_le (Order.one_le_iff_pos.mpr hm.1)).resolve_right
      (fun h => hα h.symm)
    exact congrArg (fun xs => factorProduct (factorPrefix xs)) (canonicalMNF_multiplicative hm hpos)

end Alexander313.Wilken.MultiplicativeNormalForm
