import Alexander313.Wilken.PublicEpsilonNativeRootSupportThreshold

/-!
# Genuine support cutoff for arbitrary ordinal arguments

The global comparison law and the actual native source-star/exposed-list
identity extend written support descent to arbitrary sorted source
notation arguments. No finite code for an arbitrary LOW ordinal tail is
assumed. The already constructed primitive-recursive maximal written
support node therefore bounds EVERY such collapse whose divided head
meets the requested head. This supplies a genuine all-tail cutoff for the
subsequent relative minimum induction. No scalar rewrite oracle. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RelativeSupportCutoff

open ThetaCourse RootSupportThreshold Iota.OrderInduction

/-- A real ordinal argument strictly above the original written argument
can lie below its collapse only through genuine original exposed support. -/
theorem above_ordinal_argument_support (q : Nat) (a : RelativeTerm Nat)
    (ha : check q (.theta 0 a) = true) (hna : Comparison.Normal q a)
    (u : GlobalNotationOrdinal (base q) 1) (hu : u.val < omegaSequence (base q) 2)
    (hau : denote q a < u.val)
    (hv : globalCollapse (base q) 0 u.val ≤ denote q (.theta 0 a)) :
    ∃ s ∈ exposedThetaList 0 a, globalCollapse (base q) 0 u.val ≤ denote q s := by
  classical
  have hq := (Bool.and_eq_true.mp ha).1
  have hτ := base_pos q hq
  have haa := FixedPoint.checked_theta_argument q 0 a ha
  let ao := FixedPoint.sourceOrdinal q 0 a haa
  have has := FixedPoint.checked_theta_sort q 0 a ha
  have hstrict : globalCollapse (base q) 0 u.val < denote q (.theta 0 a) := by
    apply lt_of_le_of_ne hv
    intro he
    have harg := (globalCollapse_eq_iff (base q) hτ 0 u ao hu has).mp he
    exact (ne_of_gt hau) harg
  have hsupport : globalCollapse (base q) 0 u.val ≤ globalStar (base q) hτ 0 ao := by
    rcases (globalCollapse_lt_iff_globalStar (base q) hτ 0 u ao hu has).mp hstrict with hfirst | hsupport
    · exact False.elim ((not_lt_of_gt hau) hfirst.1)
    · exact hsupport
  have hpos : 0 < globalCollapse (base q) 0 u.val :=
    globalCollapse_pos (base q) hτ 0 u.val
      ((globalNotation_low_iff_lt_boundary (base q) hτ 1 u.val).mp ⟨u.property, hu⟩)
  by_contra hn
  have hall : ∀ s ∈ exposedThetaList 0 a, denote q s < globalCollapse (base q) 0 u.val := by
    intro s hs
    exact lt_of_not_ge (fun hv => hn ⟨s, hs, hv⟩)
  have hsmall := (FixedPoint.sourceStar_lt_iff_exposed q 0 a haa hna _ hpos).mpr hall
  exact hsmall.not_ge hsupport

private theorem ordinal_support_carries_head_fuel (q : Nat)
    (u : GlobalNotationOrdinal (base q) 1) (hu : u.val < omegaSequence (base q) 2) :
    ∀ fuel : Nat, ∀ a : RelativeTerm Nat, (.theta 0 a : RelativeTerm Nat).size ≤ fuel →
      check q (.theta 0 a) = true → Comparison.Normal q a →
      globalCollapse (base q) 0 u.val ≤ denote q (.theta 0 a) →
      ∃ v : RelativeTerm Nat, .theta 0 v ∈ Iota.fullList (.theta 0 a) ∧
        globalCollapse (base q) 0 u.val ≤ denote q (.theta 0 v) ∧
        SourceHighPartComparison.highPart (omegaSequence (base q) 1) u.val ≤ head q v := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro a hsize ha hna hv
    by_cases hh : SourceHighPartComparison.highPart (omegaSequence (base q) 1) u.val ≤ head q a
    · exact ⟨a, RelativeTerm.PrincipalSupport.principalList_root 0 a, hv, hh⟩
    · let Ω := omegaSequence (base q) 1
      have hΩ : 0 < Ω := (omegaSequence_isSuccLimit (base q) 0).bot_lt
      have harg : denote q a < u.val := by
        have hsep := SourceFixedPointLimits.multiple_add_low_lt_of_lt Ω
          (SourceHighPartComparison.highPart Ω (denote q a))
          (SourceHighPartComparison.highPart Ω u.val)
          (SourceHighPartComparison.tailPart Ω (denote q a)) hΩ
          (SourceHighPartComparison.highPart_dvd Ω _) (SourceHighPartComparison.highPart_dvd Ω _)
          (lt_of_not_ge hh) (SourceHighPartComparison.tailPart_lt Ω _ hΩ)
        rw [SourceHighPartComparison.highPart_add_tailPart] at hsep
        exact hsep.trans_le (SourceHighPartComparison.highPart_le Ω _)
      obtain ⟨s, hs, hbound⟩ := above_ordinal_argument_support q a ha hna u hu harg hv
      have hc := exposed_checked_normal q 0 a s (FixedPoint.checked_theta_argument q 0 a ha) hna hs
      have hfull := RelativeTerm.PrincipalSupport.exposed_mem_principalList 0 a s hs
      have hsmall := RelativeTerm.PrincipalSupport.principalList_argument_size_lt 0 0 a s hfull
      obtain ⟨v, rfl⟩ := Iota.Enclosure.exposed_shape 0 a s hs
      obtain ⟨w, hw, hvalue, hhead⟩ := ih (.theta 0 v : RelativeTerm Nat).size
        (hsmall.trans_le hsize) v le_rfl hc.1 hc.2 hbound
      exact ⟨w, _root_.Alexander313.Wilken.RelativeTerm.Hereditary.Localization.Refinements.principalList_trans
        0 (.theta 0 a) (.theta 0 v) (.theta 0 w)
        (RelativeTerm.PrincipalSupport.principalList_nested 0 a _ hfull) hw, hvalue, hhead⟩

/-- Original syntax descent carries the head of ANY actual sorted global
source argument, including arguments built with arbitrary LOW tails. -/
theorem ordinal_support_carries_head (q : Nat) (a : RelativeTerm Nat)
    (ha : check q (.theta 0 a) = true) (hna : Comparison.Normal q a)
    (u : GlobalNotationOrdinal (base q) 1) (hu : u.val < omegaSequence (base q) 2)
    (hv : globalCollapse (base q) 0 u.val ≤ denote q (.theta 0 a)) :
    ∃ v : RelativeTerm Nat, .theta 0 v ∈ Iota.fullList (.theta 0 a) ∧
      globalCollapse (base q) 0 u.val ≤ denote q (.theta 0 v) ∧
      SourceHighPartComparison.highPart (omegaSequence (base q) 1) u.val ≤ head q v :=
  ordinal_support_carries_head_fuel q u hu (.theta 0 a : RelativeTerm Nat).size a le_rfl ha hna hv

/-- The finite selected node is an exact VALUE cutoff for ALL genuine
sorted source arguments carrying at least the requested divided head. -/
theorem selected_value_cutoff (q b c d : Nat)
    (hi : RootSupportThreshold.inputCheck q b c = true)
    (hs : selected q b c = some d)
    (u : GlobalNotationOrdinal (base q) 1) (hu : u.val < omegaSequence (base q) 2)
    (hh : SourceHighPartComparison.highPart (omegaSequence (base q) 1) (interpretation q c) ≤
      SourceHighPartComparison.highPart (omegaSequence (base q) 1) u.val) :
    globalCollapse (base q) 0 u.val ≤ interpretation q b ↔
      globalCollapse (base q) 0 u.val ≤ interpretation q d := by
  have hi' := (RootSupportThreshold.inputCheck_exact q b c).mp hi
  have hd := selected_spec q b c d hi hs
  have hinterval := selected_interval q b c d hi hs
  constructor
  · intro hbound
    obtain ⟨a, he, ha, hna, hhigh⟩ := (RootLowCollapse.rootCheck_exact q b).mp hi'.1
    obtain ⟨v, hv, hvalue, hhead⟩ := ordinal_support_carries_head q a ha hna u hu
      (by simpa only [he, interpretation_code] using hbound)
    have hfull : (.theta 0 v).code ∈ fullCodes b := (fullCodes_mem q b _ hi'.1).mpr
      ⟨.theta 0 v, by simpa only [he, rawTree_code] using hv, rfl⟩
    have hel : eligible q c (.theta 0 v).code = true :=
      (eligible_exact q c _ ((RootAboveHeadCollapse.argumentCheck_exact q c).mp hi'.2.1).1
        (fullCodes_node q b _ hi'.1 hfull)).mpr (by rw [nodeHead_theta]; exact hh.trans hhead)
    exact hvalue.trans (by simpa only [interpretation_code] using hd.2.2.2.2 (.theta 0 v).code hfull hel)
  · intro hbound
    exact hbound.trans hinterval.2.2.2.2.2.1

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RelativeSupportCutoff
