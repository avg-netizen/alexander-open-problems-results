import Alexander313.Wilken.SourceOneRootSupportThreshold
import Alexander313.Wilken.DirectLimitComparison

/-!
# Genuine original source-one cutoff for arbitrary ordinal arguments

The global comparison law and the actual original source-one star/exposed-list
identity extend written support descent to arbitrary sorted source
notation arguments. No finite code for an arbitrary LOW ordinal tail is
assumed. The already constructed primitive-recursive maximal written
support node therefore bounds EVERY such collapse whose divided head
meets the requested head. This supplies a genuine all-tail cutoff for the
subsequent relative minimum induction. No scalar rewrite oracle. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.RelativeSupportCutoff

open ThetaCourse RootSupportThreshold RootScalar

/-- A real ordinal argument strictly above the original written argument
can lie below its collapse only through genuine original exposed support. -/
theorem above_ordinal_argument_support (a : RelativeTerm Nat)
    (ha : check 0 (.theta 0 a) = true) (hna : Theta.Normal 0 a)
    (u : GlobalNotationOrdinal 1 1) (hu : u.val < omegaSequence 1 2)
    (hau : denote 0 a < u.val)
    (hv : globalCollapse 1 0 u.val ≤ denote 0 (.theta 0 a)) :
    ∃ s ∈ exposedThetaList 0 a, globalCollapse 1 0 u.val ≤ denote 0 s := by
  classical
  have hτ : (0 : Ordinal.{0}) < 1 := zero_lt_one
  have haa := SourceFixedPoint.checked_theta_argument 0 0 a ha
  let ao := SourceFixedPoint.sourceOrdinal 0 0 a haa
  have has := SourceFixedPoint.checked_theta_sort 0 0 a ha
  have hstrict : globalCollapse 1 0 u.val < denote 0 (.theta 0 a) := by
    apply lt_of_le_of_ne hv
    intro he
    have harg := (globalCollapse_eq_iff 1 hτ 0 u ao hu has).mp he
    exact (ne_of_gt hau) harg
  have hsupport : globalCollapse 1 0 u.val ≤ globalStar 1 hτ 0 ao := by
    rcases (globalCollapse_lt_iff_globalStar 1 hτ 0 u ao hu has).mp hstrict with hfirst | hsupport
    · exact False.elim ((not_lt_of_gt hau) hfirst.1)
    · exact hsupport
  have hpos : 0 < globalCollapse 1 0 u.val :=
    globalCollapse_pos 1 hτ 0 u.val
      ((globalNotation_low_iff_lt_boundary 1 hτ 1 u.val).mp ⟨u.property, hu⟩)
  by_contra hn
  have hall : ∀ s ∈ exposedThetaList 0 a, denote 0 s < globalCollapse 1 0 u.val := by
    intro s hs
    exact lt_of_not_ge (fun hv => hn ⟨s, hs, hv⟩)
  have hsmall := (SourceFixedPoint.sourceStar_lt_iff_exposed 0 0 a haa hna _ hpos).mpr hall
  exact hsmall.not_ge hsupport

private theorem ordinal_support_carries_head_fuel (u : GlobalNotationOrdinal 1 1) (hu : u.val < omegaSequence 1 2) :
    ∀ fuel : Nat, ∀ a : RelativeTerm Nat, (.theta 0 a : RelativeTerm Nat).size ≤ fuel →
      check 0 (.theta 0 a) = true → Theta.Normal 0 a →
      globalCollapse 1 0 u.val ≤ denote 0 (.theta 0 a) →
      ∃ v : RelativeTerm Nat, .theta 0 v ∈ fullList (.theta 0 a) ∧
        globalCollapse 1 0 u.val ≤ denote 0 (.theta 0 v) ∧
        SourceHighPartComparison.highPart (omegaSequence 1 1) u.val ≤ head v := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro a hsize ha hna hv
    by_cases hh : SourceHighPartComparison.highPart (omegaSequence 1 1) u.val ≤ head a
    · exact ⟨a, RelativeTerm.PrincipalSupport.principalList_root 0 a, hv, hh⟩
    · let Ω := omegaSequence 1 1
      have hΩ : 0 < Ω := (omegaSequence_isSuccLimit 1 0).bot_lt
      have harg : denote 0 a < u.val := by
        have hsep := SourceFixedPointLimits.multiple_add_low_lt_of_lt Ω
          (SourceHighPartComparison.highPart Ω (denote 0 a))
          (SourceHighPartComparison.highPart Ω u.val)
          (SourceHighPartComparison.tailPart Ω (denote 0 a)) hΩ
          (SourceHighPartComparison.highPart_dvd Ω _) (SourceHighPartComparison.highPart_dvd Ω _)
          (lt_of_not_ge hh) (SourceHighPartComparison.tailPart_lt Ω _ hΩ)
        rw [SourceHighPartComparison.highPart_add_tailPart] at hsep
        exact hsep.trans_le (SourceHighPartComparison.highPart_le Ω _)
      obtain ⟨s, hs, hbound⟩ := above_ordinal_argument_support a ha hna u hu harg hv
      have hc := OrderSupport.exposed_checked_normal 0 a s (SourceFixedPoint.checked_theta_argument 0 0 a ha) hna hs
      have hfull := RelativeTerm.PrincipalSupport.exposed_mem_principalList 0 a s hs
      have hsmall := RelativeTerm.PrincipalSupport.principalList_argument_size_lt 0 0 a s hfull
      obtain ⟨v, rfl⟩ := NativeContext.Iota.Enclosure.exposed_shape 0 a s hs
      obtain ⟨w, hw, hvalue, hhead⟩ := ih (.theta 0 v : RelativeTerm Nat).size
        (hsmall.trans_le hsize) v le_rfl hc.1 ((Theta.normal_theta 0 0 v).mp hc.2) hbound
      exact ⟨w, _root_.Alexander313.Wilken.RelativeTerm.Hereditary.Localization.Refinements.principalList_trans
        0 (.theta 0 a) (.theta 0 v) (.theta 0 w)
        (RelativeTerm.PrincipalSupport.principalList_nested 0 a _ hfull) hw, hvalue, hhead⟩

/-- Original syntax descent carries the head of ANY actual sorted global
source argument, including arguments built with arbitrary LOW tails. -/
theorem ordinal_support_carries_head (a : RelativeTerm Nat)
    (ha : check 0 (.theta 0 a) = true) (hna : Theta.Normal 0 a)
    (u : GlobalNotationOrdinal 1 1) (hu : u.val < omegaSequence 1 2)
    (hv : globalCollapse 1 0 u.val ≤ denote 0 (.theta 0 a)) :
    ∃ v : RelativeTerm Nat, .theta 0 v ∈ fullList (.theta 0 a) ∧
      globalCollapse 1 0 u.val ≤ denote 0 (.theta 0 v) ∧
      SourceHighPartComparison.highPart (omegaSequence 1 1) u.val ≤ head v :=
  ordinal_support_carries_head_fuel u hu (.theta 0 a : RelativeTerm Nat).size a le_rfl ha hna hv

/-- The finite selected node is an exact VALUE cutoff for ALL genuine
sorted source arguments carrying at least the requested divided head. -/
theorem selected_value_cutoff (b c d : Nat)
    (hi : RootSupportThreshold.inputCheck b c = true)
    (hs : selected b c = some d)
    (u : GlobalNotationOrdinal 1 1) (hu : u.val < omegaSequence 1 2)
    (hh : SourceHighPartComparison.highPart (omegaSequence 1 1) (interpretation 0 c) ≤
      SourceHighPartComparison.highPart (omegaSequence 1 1) u.val) :
    globalCollapse 1 0 u.val ≤ interpretation 0 b ↔
      globalCollapse 1 0 u.val ≤ interpretation 0 d := by
  have hi' := (RootSupportThreshold.inputCheck_exact b c).mp hi
  have hd := selected_spec b c d hi hs
  have hinterval := selected_value_le_root b c d hi hs
  constructor
  · intro hbound
    obtain ⟨a, he, ha, hna, hhigh⟩ := (rootCheck_exact b).mp hi'.1
    obtain ⟨v, hv, hvalue, hhead⟩ := ordinal_support_carries_head a ha ((Theta.normal_theta 0 0 a).mp hna) u hu
      (by simpa only [he, interpretation_code] using hbound)
    have hfull : (.theta 0 v).code ∈ fullCodes b := (fullCodes_mem b _ hi'.1).mpr
      ⟨.theta 0 v, by simpa only [he, rawTree_code] using hv, rfl⟩
    have hel : eligible c (.theta 0 v).code = true :=
      (eligible_exact c _ ((sortedCheck_exact c).mp hi'.2.1).1
        (fullCodes_node b _ hi'.1 hfull)).mpr (by rw [nodeHead_theta]; exact hh.trans hhead)
    exact hvalue.trans (by simpa only [interpretation_code] using hd.2.2.2.2 (.theta 0 v).code hfull hel)
  · intro hbound
    exact hbound.trans hinterval

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.RelativeSupportCutoff
