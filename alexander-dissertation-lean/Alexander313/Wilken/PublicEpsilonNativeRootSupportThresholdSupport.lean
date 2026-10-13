import Alexander313.Wilken.HereditaryNativeRelativeLargerHeadSupport
import Alexander313.Wilken.PublicEpsilonNativeRootEndpointCollapse
import Alexander313.Wilken.PublicEpsilonNativeRootAboveHeadCollapse

/-!
# Genuine larger-head support descent

A checked Normal theta-zero value below an original root has a written
full-support node above it whose divided argument head is at least the
requested head. When the present node has smaller head, the actual exposed
comparison produces a strictly smaller original syntax subtree. Finite
syntax descent derives the witness, without a localization or cutoff oracle.
The finite maximal support threshold is constructed separately. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RootSupportThreshold

open ThetaCourse Iota.OrderInduction

noncomputable def head (q : Nat) (a : RelativeTerm Nat) : Ordinal.{0} :=
  SourceHighPartComparison.highPart (omegaSequence (base q) 1) (denote q a)

/-- Distinct actual divided heads separate the whole original arguments. -/
theorem argument_lt_of_head_lt (q : Nat) (a u : RelativeTerm Nat)
    (hh : head q a < head q u) : denote q a < denote q u := by
  let Ω := omegaSequence (base q) 1
  have hΩ : 0 < Ω := (omegaSequence_isSuccLimit (base q) 0).bot_lt
  have hs := SourceFixedPointLimits.multiple_add_low_lt_of_lt Ω
    (SourceHighPartComparison.highPart Ω (denote q a))
    (SourceHighPartComparison.highPart Ω (denote q u))
    (SourceHighPartComparison.tailPart Ω (denote q a)) hΩ
    (SourceHighPartComparison.highPart_dvd Ω _) (SourceHighPartComparison.highPart_dvd Ω _)
    hh (SourceHighPartComparison.tailPart_lt Ω _ hΩ)
  rw [SourceHighPartComparison.highPart_add_tailPart] at hs
  exact hs.trans_le (SourceHighPartComparison.highPart_le Ω _)

/-- Weak Normality holds at every actual full-depth theta-zero subtree. -/
theorem normal_full_node (q : Nat) (t s : RelativeTerm Nat)
    (ht : Comparison.Normal q t) (hs : s ∈ Iota.fullList t) : Comparison.Normal q s := by
  revert ht hs
  induction t with
  | parameter p =>
    intro ht hs
    simp only [Iota.fullList, RelativeTerm.PrincipalSupport.principalList, List.not_mem_nil] at hs
  | sum a b iha ihb =>
    intro ht hs
    rcases List.mem_append.mp hs with hs | hs
    · exact iha ht.1 hs
    · exact ihb ht.2.1 hs
  | theta k a ih =>
    intro ht hs
    cases k with
    | zero =>
      rw [Iota.fullList, RelativeTerm.PrincipalSupport.principalList_theta_same] at hs
      rcases List.mem_cons.mp hs with he | hs
      · subst s; exact ht
      · exact ih ht hs
    | succ k =>
      exact ih ht (by simpa only [Iota.fullList,
        RelativeTerm.PrincipalSupport.principalList_theta_higher 0 (k + 1) a (Nat.succ_pos k)] using hs)

private theorem support_carries_head_fuel (q : Nat) (u : RelativeTerm Nat)
    (hu : check q (.theta 0 u) = true) (hnu : Comparison.Normal q u) :
    ∀ fuel : Nat, ∀ a : RelativeTerm Nat, (.theta 0 a : RelativeTerm Nat).size ≤ fuel →
      check q (.theta 0 a) = true → Comparison.Normal q a →
      denote q (.theta 0 u) ≤ denote q (.theta 0 a) →
      ∃ v : RelativeTerm Nat, .theta 0 v ∈ Iota.fullList (.theta 0 a) ∧
        denote q (.theta 0 u) ≤ denote q (.theta 0 v) ∧ head q u ≤ head q v := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro a hsize ha hna hvalue
    by_cases hh : head q u ≤ head q a
    · exact ⟨a, RelativeTerm.PrincipalSupport.principalList_root 0 a, hvalue, hh⟩
    · have harg := argument_lt_of_head_lt q a u (lt_of_not_ge hh)
      obtain ⟨s, hs, hbound⟩ :=
        (RelativeLargerHeadSupport.above_argument_le_iff_support q 0 a u ha hu hna hnu harg).mp hvalue
      have hc := exposed_checked_normal q 0 a s
        (FixedPoint.checked_theta_argument q 0 a ha) hna hs
      have hfull := RelativeTerm.PrincipalSupport.exposed_mem_principalList 0 a s hs
      have hsmall := RelativeTerm.PrincipalSupport.principalList_argument_size_lt 0 0 a s hfull
      obtain ⟨v, rfl⟩ := Iota.Enclosure.exposed_shape 0 a s hs
      obtain ⟨w, hw, hww, hhead⟩ := ih (.theta 0 v : RelativeTerm Nat).size
        (hsmall.trans_le hsize) v le_rfl hc.1 hc.2 hbound
      exact ⟨w, _root_.Alexander313.Wilken.RelativeTerm.Hereditary.Localization.Refinements.principalList_trans 0 (.theta 0 a) (.theta 0 v)
        (.theta 0 w) (RelativeTerm.PrincipalSupport.principalList_nested 0 a _ hfull) hw,
        hww, hhead⟩

/-- The head-carrying witness is an actual original written subtree.
All exposed comparison callers and the finite descent are derived. -/
theorem support_carries_head (q : Nat) (a u : RelativeTerm Nat)
    (ha : check q (.theta 0 a) = true) (hu : check q (.theta 0 u) = true)
    (hna : Comparison.Normal q a) (hnu : Comparison.Normal q u)
    (hv : denote q (.theta 0 u) ≤ denote q (.theta 0 a)) :
    ∃ v : RelativeTerm Nat, .theta 0 v ∈ Iota.fullList (.theta 0 a) ∧
      denote q (.theta 0 u) ≤ denote q (.theta 0 v) ∧ head q u ≤ head q v :=
  support_carries_head_fuel q u hu hnu (.theta 0 a : RelativeTerm Nat).size a le_rfl ha hna hv

/-- Successor arguments retain their actual divided head at Omega-one. -/
theorem highPart_successor (q : Nat) (a : Ordinal.{0}) :
    SourceHighPartComparison.highPart (omegaSequence (base q) 1) (a + 1) =
      SourceHighPartComparison.highPart (omegaSequence (base q) 1) a := by
  let Ω := omegaSequence (base q) 1
  have hΩ := omegaSequence_isSuccLimit (base q) 0
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

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RootSupportThreshold
