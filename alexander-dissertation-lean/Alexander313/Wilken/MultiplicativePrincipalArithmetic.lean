import Alexander313.Wilken.AdditiveNormalForm

/-!
# Actual multiplication of an ANF by an infinite principal

The leading ANF summand bounds the real ordinal between two consecutive omega
powers. Finite right multiples stay below the upper additive-principal bound;
continuity at omega therefore gives the exact product by omega. Factoring any
positive exponent as 1 + (delta - 1) gives the general principal product law.

Wilken's multiplicative class is a subclass of the positive additive principals.
That condition matters: the bare mathlib multiplication-closure predicate also
holds at 2. The class below keeps both actual closure predicates, and its printed
description as 1 or a double omega power is proved from ordinal arithmetic.
All proof terms are uncompiled source candidates.
-/

namespace Alexander313.Wilken.MultiplicativePrincipalArithmetic

universe u

/-- A normalized nonempty ANF lies between its leading omega power and the
next omega power, with a strict upper bound even when the head repeats. -/
theorem principalSum_leading_bounds {a γ : Ordinal.{u}} {xs : List Ordinal.{u}}
    (hn : IsAdditiveNormalForm (a :: xs)) (ha : a = Ordinal.omega0 ^ γ) :
    Ordinal.omega0 ^ γ ≤ principalSum (a :: xs) ∧
      principalSum (a :: xs) < Ordinal.omega0 ^ (γ + 1) := by
  have hhead : a < Ordinal.omega0 ^ (γ + 1) := by
    rw [ha]
    exact (Ordinal.isNormal_opow Ordinal.one_lt_omega0).strictMono
      (lt_add_of_pos_right γ zero_lt_one)
  refine ⟨?_, ?_⟩
  · rw [← ha]
    exact principalSum_mem_le List.mem_cons_self
  · apply principalSum_lt (Ordinal.opow_pos _ Ordinal.omega0_pos)
      (Ordinal.isPrincipal_add_omega0_opow _) _
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hhead
    · exact (additiveNormalForm_head_ge hn hb).trans_lt hhead

/-- The actual head interval determines multiplication by omega. -/
theorem mul_omega_of_leading_bounds {α γ : Ordinal.{u}}
    (hl : Ordinal.omega0 ^ γ ≤ α) (hu : α < Ordinal.omega0 ^ (γ + 1)) :
    α * Ordinal.omega0 = Ordinal.omega0 ^ (γ + 1) := by
  apply le_antisymm
  · apply (Ordinal.mul_le_iff_of_isSuccLimit Ordinal.isSuccLimit_omega0).mpr
    intro b hb
    exact (Ordinal.mul_lt_omega0_opow
      (add_pos_of_right zero_lt_one γ) hu hb).le
  · rw [Ordinal.opow_add_one]
    exact mul_le_mul_left hl Ordinal.omega0

/-- Only genuine leading bounds are premises. The exponent subtraction is
ordinary left removal, justified by 1 <= delta; it is not right subtraction. -/
theorem mul_omegaPower_of_leading_bounds {α γ δ : Ordinal.{u}}
    (hl : Ordinal.omega0 ^ γ ≤ α) (hu : α < Ordinal.omega0 ^ (γ + 1))
    (hδ : 0 < δ) : α * Ordinal.omega0 ^ δ = Ordinal.omega0 ^ (γ + δ) := by
  have hsplit : 1 + (δ - 1) = δ :=
    Ordinal.add_sub_cancel_of_le (Order.one_le_iff_pos.mpr hδ)
  calc
    α * Ordinal.omega0 ^ δ =
        α * (Ordinal.omega0 * Ordinal.omega0 ^ (δ - 1)) := by
      rw [← Ordinal.opow_one_add, hsplit]
    _ = (α * Ordinal.omega0) * Ordinal.omega0 ^ (δ - 1) := by rw [mul_assoc]
    _ = Ordinal.omega0 ^ (γ + 1) * Ordinal.omega0 ^ (δ - 1) := by
      rw [mul_omega_of_leading_bounds hl hu]
    _ = Ordinal.omega0 ^ ((γ + 1) + (δ - 1)) :=
      (Ordinal.opow_add Ordinal.omega0 (γ + 1) (δ - 1)).symm
    _ = Ordinal.omega0 ^ (γ + δ) := by rw [add_assoc, hsplit]

theorem principalSum_mul_omegaPower {a γ δ : Ordinal.{u}} {xs : List Ordinal.{u}}
    (hn : IsAdditiveNormalForm (a :: xs)) (ha : a = Ordinal.omega0 ^ γ)
    (hδ : 0 < δ) :
    principalSum (a :: xs) * Ordinal.omega0 ^ δ = Ordinal.omega0 ^ (γ + δ) := by
  have hb := principalSum_leading_bounds hn ha
  exact mul_omegaPower_of_leading_bounds hb.1 hb.2 hδ

/-- Genuine ordinal multiplication distributes over the ordered right ANF. -/
theorem mul_principalSum (α : Ordinal.{u}) (xs : List Ordinal.{u}) :
    α * principalSum xs = principalSum (xs.map (fun β => α * β)) := by
  induction xs with
  | nil => simp [principalSum]
  | cons a xs ih => simp only [principalSum, List.map_cons, mul_add, ih]

theorem principalSum_mul_principal_coefficient {a γ δ : Ordinal.{u}}
    {xs : List Ordinal.{u}} (hn : IsAdditiveNormalForm (a :: xs))
    (ha : a = Ordinal.omega0 ^ γ) (hδ : 0 < δ) (n : Nat) :
    principalSum (a :: xs) * (Ordinal.omega0 ^ δ * (n : Ordinal)) =
      Ordinal.omega0 ^ (γ + δ) * (n : Ordinal) := by
  rw [← mul_assoc, principalSum_mul_omegaPower hn ha hδ]

/-- Positive left factors preserve and reflect strict order in the right
argument; this is the actual normality theorem for ordinal multiplication. -/
theorem positive_mul_strictMono {γ : Ordinal.{u}} (hγ : 0 < γ) :
    StrictMono (fun δ : Ordinal.{u} => γ * δ) :=
  (Ordinal.isNormal_mul_right hγ).strictMono

theorem positive_mul_injective {γ : Ordinal.{u}} (hγ : 0 < γ) :
    Function.Injective (fun δ : Ordinal.{u} => γ * δ) :=
  (positive_mul_strictMono hγ).injective

theorem quotient_le_product {γ : Ordinal.{u}} (hγ : 0 < γ) (δ : Ordinal.{u}) :
    δ ≤ γ * δ := Ordinal.le_mul_right δ hγ

/-- The source multiplicative class retains real additive and multiplicative
closure, and excludes zero. Bare multiplicative closure has a 2 exception. -/
def IsMultiplicativePrincipal (α : Ordinal.{u}) : Prop :=
  0 < α ∧ Ordinal.IsPrincipal (· + ·) α ∧ Ordinal.IsPrincipal (· * ·) α

theorem omegaPower_multiplicative_iff (δ : Ordinal.{u}) :
    Ordinal.IsPrincipal (· * ·) (Ordinal.omega0 ^ δ) ↔
      δ = 0 ∨ (0 < δ ∧ Ordinal.IsPrincipal (· + ·) δ) := by
  constructor
  · intro h
    by_cases hz : δ = 0
    · exact Or.inl hz
    · exact Or.inr ⟨pos_iff_ne_zero.mpr hz,
        Ordinal.isPrincipal_add_of_isPrincipal_mul_opow Ordinal.one_lt_omega0 h⟩
  · rintro (rfl | ⟨hp, ha⟩)
    · simpa only [Ordinal.opow_zero] using Ordinal.isPrincipal_mul_one
    · rcases Ordinal.isPrincipal_add_iff_zero_or_omega0_opow.mp ha with hz | ⟨ρ, hρ⟩
      · exact False.elim ((ne_of_gt hp) hz)
      · rw [← hρ]
        exact Ordinal.isPrincipal_mul_omega0_opow_opow ρ

theorem multiplicativePrincipal_iff (α : Ordinal.{u}) :
    IsMultiplicativePrincipal α ↔
      α = 1 ∨ ∃ ρ : Ordinal.{u}, α = Ordinal.omega0 ^ (Ordinal.omega0 ^ ρ) := by
  constructor
  · rintro ⟨hp, ha, hm⟩
    rcases Ordinal.isPrincipal_add_iff_zero_or_omega0_opow.mp ha with hz | ⟨δ, hδ⟩
    · exact False.elim ((ne_of_gt hp) hz)
    · rw [← hδ] at hm
      rcases (omegaPower_multiplicative_iff δ).mp hm with hz | ⟨hd, hdadd⟩
      · exact Or.inl (by rw [← hδ, hz]; exact Ordinal.opow_zero _)
      · rcases Ordinal.isPrincipal_add_iff_zero_or_omega0_opow.mp hdadd with hz | ⟨ρ, hρ⟩
        · exact False.elim ((ne_of_gt hd) hz)
        · exact Or.inr ⟨ρ, by rw [← hδ, ← hρ]⟩
  · rintro (rfl | ⟨ρ, rfl⟩)
    · exact ⟨zero_lt_one, Ordinal.isPrincipal_add_one, Ordinal.isPrincipal_mul_one⟩
    · exact ⟨Ordinal.opow_pos _ Ordinal.omega0_pos,
        Ordinal.isPrincipal_add_omega0_opow _, Ordinal.isPrincipal_mul_omega0_opow_opow _⟩

theorem bare_multiplicative_two : Ordinal.IsPrincipal (· * ·) (2 : Ordinal.{u}) :=
  Ordinal.isPrincipal_mul_two

theorem not_multiplicativePrincipal_zero : ¬ IsMultiplicativePrincipal (0 : Ordinal.{u}) := by
  rintro ⟨h, _⟩
  exact lt_irrefl _ h

theorem not_multiplicativePrincipal_two : ¬ IsMultiplicativePrincipal (2 : Ordinal.{u}) := by
  rintro ⟨_, ha, _⟩
  have h : (1 : Ordinal.{u}) + 1 < 2 := ha one_lt_two one_lt_two
  simpa only [one_add_one_eq_two, lt_self_iff_false] using h

end Alexander313.Wilken.MultiplicativePrincipalArithmetic
