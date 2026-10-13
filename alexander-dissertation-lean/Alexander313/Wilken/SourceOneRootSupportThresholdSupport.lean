import Alexander313.Wilken.SourceOneRootScalarSupport
import Alexander313.Wilken.SourceOneNativeIotaOrderSupport

/-!
# Genuine original source-one written support descent

Actual source-one theta comparison derives a written zero-index support
node carrying at least a requested divided head whenever its source
collapse lies below the original root. Strict original syntax descent
terminates. No positive-epsilon source parser or supplied cutoff. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.RootSupportThreshold

open ThetaCourse RootScalar

noncomputable def head (a : RelativeTerm Nat) : Ordinal.{0} :=
  SourceHighPartComparison.highPart (omegaSequence 1 1) (denote 0 a)

theorem argument_lt_of_head_lt (a u : RelativeTerm Nat) (hh : head a < head u) :
    denote 0 a < denote 0 u := by
  let Ω := omegaSequence 1 1
  have hΩ : 0 < Ω := (omegaSequence_isSuccLimit 1 0).bot_lt
  have hs := SourceFixedPointLimits.multiple_add_low_lt_of_lt Ω
    (SourceHighPartComparison.highPart Ω (denote 0 a))
    (SourceHighPartComparison.highPart Ω (denote 0 u))
    (SourceHighPartComparison.tailPart Ω (denote 0 a)) hΩ
    (SourceHighPartComparison.highPart_dvd Ω _) (SourceHighPartComparison.highPart_dvd Ω _)
    hh (SourceHighPartComparison.tailPart_lt Ω _ hΩ)
  rw [SourceHighPartComparison.highPart_add_tailPart] at hs
  exact hs.trans_le (SourceHighPartComparison.highPart_le Ω _)

private theorem support_carries_head_fuel (u : RelativeTerm Nat)
    (hu : check 0 (.theta 0 u) = true) (hnu : Theta.Normal 0 u) :
    ∀ fuel : Nat, ∀ a : RelativeTerm Nat, (.theta 0 a : RelativeTerm Nat).size ≤ fuel →
      check 0 (.theta 0 a) = true → Theta.Normal 0 a →
      denote 0 (.theta 0 u) ≤ denote 0 (.theta 0 a) →
      ∃ v : RelativeTerm Nat, .theta 0 v ∈ fullList (.theta 0 a) ∧
        denote 0 (.theta 0 u) ≤ denote 0 (.theta 0 v) ∧ head u ≤ head v := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro a hsize ha hna hvalue
    by_cases hh : head u ≤ head a
    · exact ⟨a, RelativeTerm.PrincipalSupport.principalList_root 0 a, hvalue, hh⟩
    · have harg := argument_lt_of_head_lt a u (lt_of_not_ge hh)
      obtain ⟨s, hs, hbound⟩ :=
        (above_argument_le_iff_support 0 a u ha hu hna hnu harg).mp hvalue
      have hc := OrderSupport.exposed_checked_normal 0 a s
        (SourceFixedPoint.checked_theta_argument 0 0 a ha) hna hs
      have hfull := RelativeTerm.PrincipalSupport.exposed_mem_principalList 0 a s hs
      have hsmall := RelativeTerm.PrincipalSupport.principalList_argument_size_lt 0 0 a s hfull
      obtain ⟨v, rfl⟩ := NativeContext.Iota.Enclosure.exposed_shape 0 a s hs
      obtain ⟨w, hw, hww, hhead⟩ := ih (.theta 0 v : RelativeTerm Nat).size
        (hsmall.trans_le hsize) v le_rfl hc.1 ((Theta.normal_theta 0 0 v).mp hc.2) hbound
      exact ⟨w, Localization.Refinements.principalList_trans 0 (.theta 0 a) (.theta 0 v)
        (.theta 0 w) (RelativeTerm.PrincipalSupport.principalList_nested 0 a _ hfull) hw,
        hww, hhead⟩

theorem support_carries_head (a u : RelativeTerm Nat)
    (ha : check 0 (.theta 0 a) = true) (hu : check 0 (.theta 0 u) = true)
    (hna : Theta.Normal 0 a) (hnu : Theta.Normal 0 u)
    (hv : denote 0 (.theta 0 u) ≤ denote 0 (.theta 0 a)) :
    ∃ v : RelativeTerm Nat, .theta 0 v ∈ fullList (.theta 0 a) ∧
      denote 0 (.theta 0 u) ≤ denote 0 (.theta 0 v) ∧ head u ≤ head v :=
  support_carries_head_fuel u hu hnu (.theta 0 a : RelativeTerm Nat).size a le_rfl ha hna hv

theorem highPart_successor (a : Ordinal.{0}) :
    SourceHighPartComparison.highPart (omegaSequence 1 1) (a + 1) =
      SourceHighPartComparison.highPart (omegaSequence 1 1) a := by
  let Ω := omegaSequence 1 1
  have hΩ := omegaSequence_isSuccLimit 1 0
  have htail : a % Ω + 1 < Ω := hΩ.add_one_lt (Ordinal.mod_lt a hΩ.bot_lt.ne')
  calc
    SourceHighPartComparison.highPart Ω (a + 1) =
        SourceHighPartComparison.highPart Ω
          (SourceHighPartComparison.highPart Ω a + (SourceHighPartComparison.tailPart Ω a + 1)) := by
      congr 1
      rw [← add_assoc, SourceHighPartComparison.highPart_add_tailPart]
    _ = SourceHighPartComparison.highPart Ω a := by
      change Ω * ((Ω * (a / Ω) + (a % Ω + 1)) / Ω) = Ω * (a / Ω)
      rw [Ordinal.mul_add_div _ hΩ.bot_lt.ne', Ordinal.div_eq_zero_of_lt htail, add_zero]

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.RootSupportThreshold
