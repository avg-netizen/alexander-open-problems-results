import Alexander313.Wilken.OrdinalPowerArithmetic

/-!
# Uniqueness of the actual limit-plus-finite coefficient

Definition 3.6 uses a coefficient lambda+k with lambda zero or a successor
limit and k a natural number. Its finite tail is its actual remainder modulo
omega. Thus equality of the high parts fixes both coefficient components;
no syntactic equality or decomposition oracle is needed. Uncompiled.
-/

namespace Alexander313.Wilken.LimitFiniteDecomposition

universe u

theorem zero_or_limit_omega_dvd (lambda : Ordinal.{u})
    (h : lambda = 0 ∨ Order.IsSuccLimit lambda) : Ordinal.omega0 ∣ lambda := by
  rcases h with rfl | h
  · exact ⟨0, by simp⟩
  · exact Ordinal.isSuccPrelimit_iff_omega0_dvd.mp h.isSuccPrelimit

theorem finite_tail_mod (lambda : Ordinal.{u}) (k : Nat)
    (h : lambda = 0 ∨ Order.IsSuccLimit lambda) :
    (lambda + (k : Ordinal.{u})) % Ordinal.omega0 = (k : Ordinal.{u}) := by
  obtain ⟨delta, he⟩ := zero_or_limit_omega_dvd lambda h
  rw [he, Ordinal.mul_add_mod_self, Ordinal.natCast_mod_omega0]

theorem coefficient_unique (lambda other : Ordinal.{u}) (k n : Nat)
    (hl : lambda = 0 ∨ Order.IsSuccLimit lambda)
    (ho : other = 0 ∨ Order.IsSuccLimit other)
    (he : lambda + (k : Ordinal.{u}) = other + (n : Ordinal.{u})) :
    lambda = other ∧ k = n := by
  have ht : (k : Ordinal.{u}) = (n : Ordinal.{u}) := by
    calc
      (k : Ordinal.{u}) = (lambda + (k : Ordinal.{u})) % Ordinal.omega0 :=
        (finite_tail_mod lambda k hl).symm
      _ = (other + (n : Ordinal.{u})) % Ordinal.omega0 := congrArg (fun x : Ordinal.{u} => x % Ordinal.omega0) he
      _ = (n : Ordinal.{u}) := finite_tail_mod other n ho
  have hn : k = n := Nat.cast_injective ht
  subst n
  exact ⟨(Ordinal.add_right_cancel k).mp he, rfl⟩

theorem high_part_coefficient_unique (omega lambda other : Ordinal.{u}) (k n : Nat)
    (hw : 0 < omega)
    (hl : lambda = 0 ∨ Order.IsSuccLimit lambda)
    (ho : other = 0 ∨ Order.IsSuccLimit other)
    (he : omega * (lambda + (k : Ordinal.{u})) =
      omega * (other + (n : Ordinal.{u}))) : lambda = other ∧ k = n := by
  have hm : StrictMono (fun gamma : Ordinal.{u} => omega * gamma) :=
    fun _ _ h => mul_lt_mul_of_pos_left h hw
  exact coefficient_unique lambda other k n hl ho (hm.injective he)

end Alexander313.Wilken.LimitFiniteDecomposition
