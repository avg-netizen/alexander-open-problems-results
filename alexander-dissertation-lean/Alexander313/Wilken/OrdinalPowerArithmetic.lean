import Alexander313.Wilken.MultiplicativePrincipalArithmetic

/-!
# Real arbitrary-base ordinal powers at a limit and finite tail

For a nonzero limit lambda, multiplication by a positive finite left factor
fixes lambda. In particular (gamma + 1) * lambda = gamma * lambda whenever
gamma is positive. Monotonicity in the actual power base sandwiches the power
of any alpha in [omega^gamma, omega^(gamma+1)) between the same omega power.
For a finite base greater than one, the library's actual value at omega and
the true power-of-a-power law determine every exponent omega * delta.

Actual left division by omega splits every exponent into omega * delta + n,
with n a natural finite remainder and delta bounded by the exponent. The
limit/finite-tail formulas and genuine ANF leading bounds can therefore be
used by coded callers. No power graph, exponent decomposition, caller bound,
effectivity or termination oracle is assumed. Uncompiled source candidates.
-/

namespace Alexander313.Wilken.OrdinalPowerArithmetic

universe u

/-- A positive finite left factor is absorbed by every actual nonzero limit. -/
theorem nat_mul_limit {lam : Ordinal.{u}} (hlam : Order.IsSuccLimit lam)
    {n : Nat} (hn : 0 < n) : (n : Ordinal.{u}) * lam = lam := by
  apply Ordinal.mul_omega0_dvd (Nat.cast_pos'.mpr hn) (Ordinal.natCast_lt_omega0 n)
  exact Ordinal.isSuccPrelimit_iff_omega0_dvd.mp hlam.isSuccPrelimit

/-- The adjacent leading exponent has the same right limit product. This
uses positivity of gamma; the equation fails at gamma = 0. -/
theorem successor_mul_limit {γ lam : Ordinal.{u}} (hγ : 0 < γ)
    (hlam : Order.IsSuccLimit lam) : (γ + 1) * lam = γ * lam := by
  have htwo : (2 : Ordinal.{u}) * lam = lam := nat_mul_limit hlam (n := 2) (by decide)
  have hbound : γ + 1 ≤ γ * 2 := by
    rw [Ordinal.mul_two]
    exact add_le_add_right (Order.one_le_iff_pos.mpr hγ) γ
  apply le_antisymm
  · calc
      (γ + 1) * lam ≤ (γ * 2) * lam := mul_le_mul_left hbound lam
      _ = γ * lam := by rw [mul_assoc, htwo]
  · exact mul_le_mul_left le_self_add lam

/-- Genuine leading bounds suffice; no CNF or logarithm is supplied as an
interface. The strict upper bound is inherited from actual ANF. -/
theorem leading_bounds_opow_limit {α γ lam : Ordinal.{u}} (hγ : 0 < γ)
    (hl : Ordinal.omega0 ^ γ ≤ α) (hu : α < Ordinal.omega0 ^ (γ + 1))
    (hlam : Order.IsSuccLimit lam) : α ^ lam = Ordinal.omega0 ^ (γ * lam) := by
  apply le_antisymm
  · calc
      α ^ lam ≤ (Ordinal.omega0 ^ (γ + 1)) ^ lam := Ordinal.opow_le_opow_left lam hu.le
      _ = Ordinal.omega0 ^ ((γ + 1) * lam) := (Ordinal.opow_mul _ _ _).symm
      _ = Ordinal.omega0 ^ (γ * lam) := by rw [successor_mul_limit hγ hlam]
  · calc
      Ordinal.omega0 ^ (γ * lam) = (Ordinal.omega0 ^ γ) ^ lam := Ordinal.opow_mul _ _ _
      _ ≤ α ^ lam := Ordinal.opow_le_opow_left lam hl

theorem principalSum_opow_limit {a γ lam : Ordinal.{u}} {xs : List Ordinal.{u}}
    (hn : IsAdditiveNormalForm (a :: xs)) (ha : a = Ordinal.omega0 ^ γ)
    (hγ : 0 < γ) (hlam : Order.IsSuccLimit lam) :
    principalSum (a :: xs) ^ lam = Ordinal.omega0 ^ (γ * lam) := by
  have hb := MultiplicativePrincipalArithmetic.principalSum_leading_bounds hn ha
  exact leading_bounds_opow_limit hγ hb.1 hb.2 hlam

theorem leading_positive_of_infinite {α γ : Ordinal.{u}} (hinf : Ordinal.omega0 ≤ α)
    (hu : α < Ordinal.omega0 ^ (γ + 1)) : 0 < γ := by
  apply pos_iff_ne_zero.mpr
  intro hz
  rw [hz, zero_add, Ordinal.opow_one] at hu
  exact (not_lt_of_ge hinf) hu

theorem infinite_of_leading_positive {α γ : Ordinal.{u}} (hγ : 0 < γ)
    (hl : Ordinal.omega0 ^ γ ≤ α) : Ordinal.omega0 ≤ α := by
  have h := Ordinal.opow_le_opow_right Ordinal.omega0_pos (Order.one_le_iff_pos.mpr hγ)
  have hw : Ordinal.omega0 ≤ Ordinal.omega0 ^ γ := by simpa only [Ordinal.opow_one] using h
  exact hw.trans hl

/-- Every positive omega multiple is an actual nonzero limit, whether or not
delta itself is a limit. -/
theorem omega_mul_isSuccLimit {δ : Ordinal.{u}} (hδ : 0 < δ) :
    Order.IsSuccLimit (Ordinal.omega0 * δ) :=
  Ordinal.isSuccLimit_mul_left Ordinal.isSuccLimit_omega0 hδ

theorem leading_bounds_opow_omega_mul {α γ δ : Ordinal.{u}} (hγ : 0 < γ)
    (hl : Ordinal.omega0 ^ γ ≤ α) (hu : α < Ordinal.omega0 ^ (γ + 1))
    (hδ : 0 < δ) : α ^ (Ordinal.omega0 * δ) =
      Ordinal.omega0 ^ (γ * (Ordinal.omega0 * δ)) :=
  leading_bounds_opow_limit hγ hl hu (omega_mul_isSuccLimit hδ)

/-- This includes delta = 0; the base assumption is a literal natural > 1. -/
theorem finite_opow_omega_mul {m : Nat} (hm : 1 < m) (δ : Ordinal.{u}) :
    (m : Ordinal.{u}) ^ (Ordinal.omega0 * δ) = Ordinal.omega0 ^ δ := by
  rw [Ordinal.opow_mul, Ordinal.natCast_opow_omega0 hm]

theorem opow_add_nat (α lam : Ordinal.{u}) (n : Nat) :
    α ^ (lam + (n : Ordinal.{u})) = α ^ lam * α ^ (n : Ordinal.{u}) :=
  Ordinal.opow_add α lam n

theorem leading_bounds_opow_limit_add_nat {α γ lam : Ordinal.{u}} (hγ : 0 < γ)
    (hl : Ordinal.omega0 ^ γ ≤ α) (hu : α < Ordinal.omega0 ^ (γ + 1))
    (hlam : Order.IsSuccLimit lam) (n : Nat) :
    α ^ (lam + (n : Ordinal.{u})) = Ordinal.omega0 ^ (γ * lam) * α ^ (n : Ordinal.{u}) := by
  rw [opow_add_nat, leading_bounds_opow_limit hγ hl hu hlam]

theorem leading_bounds_opow_omega_mul_add_nat {α γ δ : Ordinal.{u}} (hγ : 0 < γ)
    (hl : Ordinal.omega0 ^ γ ≤ α) (hu : α < Ordinal.omega0 ^ (γ + 1))
    (hδ : 0 < δ) (n : Nat) :
    α ^ (Ordinal.omega0 * δ + (n : Ordinal.{u})) =
      Ordinal.omega0 ^ (γ * (Ordinal.omega0 * δ)) * α ^ (n : Ordinal.{u}) :=
  leading_bounds_opow_limit_add_nat hγ hl hu (omega_mul_isSuccLimit hδ) n

theorem finite_opow_omega_mul_add_nat {m : Nat} (hm : 1 < m)
    (δ : Ordinal.{u}) (n : Nat) :
    (m : Ordinal.{u}) ^ (Ordinal.omega0 * δ + (n : Ordinal.{u})) =
      Ordinal.omega0 ^ δ * (m : Ordinal.{u}) ^ (n : Ordinal.{u}) := by
  rw [opow_add_nat, finite_opow_omega_mul hm]

/-- Actual ordinal left division and remainder give the full exponent split.
The finite remainder is proved finite, not postulated by a coded caller. -/
theorem omega_finite_decomposition (β : Ordinal.{u}) :
    ∃ δ : Ordinal.{u}, ∃ n : Nat, β = Ordinal.omega0 * δ + (n : Ordinal.{u}) ∧ δ ≤ β := by
  obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp (Ordinal.mod_lt β Ordinal.omega0_ne_zero)
  refine ⟨β / Ordinal.omega0, n, ?_, ?_⟩
  · rw [← hn]
    exact (Ordinal.div_add_mod β Ordinal.omega0).symm
  · exact (MultiplicativePrincipalArithmetic.quotient_le_product Ordinal.omega0_pos _).trans
      (Ordinal.mul_div_le β Ordinal.omega0)

theorem omega_finite_prefix_le {β δ : Ordinal.{u}} {n : Nat}
    (h : β = Ordinal.omega0 * δ + (n : Ordinal.{u})) : Ordinal.omega0 * δ ≤ β := by
  rw [h]
  exact le_self_add

theorem omega_finite_prefix_zero_or_limit (δ : Ordinal.{u}) :
    Ordinal.omega0 * δ = 0 ∨ Order.IsSuccLimit (Ordinal.omega0 * δ) := by
  obtain rfl | hδ := eq_zero_or_pos δ
  · exact Or.inl (mul_zero _)
  · exact Or.inr (omega_mul_isSuccLimit hδ)

theorem omega_finite_quotient {β δ : Ordinal.{u}} {n : Nat}
    (h : β = Ordinal.omega0 * δ + (n : Ordinal.{u})) : β / Ordinal.omega0 = δ := by
  apply (Ordinal.div_eq_iff Ordinal.omega0_ne_zero).mpr
  constructor
  · exact omega_finite_prefix_le h
  · rw [h, mul_add_one]
    exact (add_lt_add_iff_left _).mpr (Ordinal.natCast_lt_omega0 n)

theorem omega_finite_decomposition_unique {β δ ε : Ordinal.{u}} {n m : Nat}
    (hδ : β = Ordinal.omega0 * δ + (n : Ordinal.{u}))
    (hε : β = Ordinal.omega0 * ε + (m : Ordinal.{u})) : δ = ε ∧ n = m := by
  have he : δ = ε := (omega_finite_quotient hδ).symm.trans (omega_finite_quotient hε)
  refine ⟨he, ?_⟩
  have hs := hδ.symm.trans hε
  rw [← he] at hs
  have hn : (n : Ordinal.{u}) = (m : Ordinal.{u}) := add_left_cancel hs
  exact Nat.cast_injective hn

theorem zero_base_positive_exponent {β : Ordinal.{u}} (hβ : 0 < β) :
    (0 : Ordinal.{u}) ^ β = 0 := Ordinal.zero_opow (ne_of_gt hβ)

theorem one_base (β : Ordinal.{u}) : (1 : Ordinal.{u}) ^ β = 1 := Ordinal.one_opow β

theorem zero_exponent (α : Ordinal.{u}) : α ^ (0 : Ordinal.{u}) = 1 := Ordinal.opow_zero α

theorem principal_base (γ β : Ordinal.{u}) :
    (Ordinal.omega0 ^ γ) ^ β = Ordinal.omega0 ^ (γ * β) := (Ordinal.opow_mul _ _ _).symm

end Alexander313.Wilken.OrdinalPowerArithmetic
