import Alexander313.Wilken.PublicEpsilonNativeRootSupportThreshold
import Alexander313.Wilken.HereditaryNativeSourceChiInvariance
import Alexander313.Wilken.HereditaryNativeIotaInverseSupport

/-!
# Actual localization nodes at every original coded epsilon

These APIs use the literal original native-q checker and weak Normal
grammar. The written zero-level support, original argument comparator and
real exposed witness are derived at that SAME base. No public return,
relative predecessor or gap property is supplied. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceLocalization

open ThetaCourse

def Node (q c : Nat) : Prop := ∃ a : RelativeTerm Nat,
  c = (.theta 0 a).code ∧ check q (.theta 0 a) = true ∧ Comparison.Normal q a

abbrev argumentCode := Hereditary.Localization.argumentCode

theorem argumentCode_primrec : Primrec argumentCode := Hereditary.Localization.argumentCode_primrec

@[simp] theorem argumentCode_theta (a : RelativeTerm Nat) :
    argumentCode (.theta 0 a).code = a.code := Hereditary.Localization.argumentCode_theta a

noncomputable def value (q c : Nat) : Ordinal.{0} := interpretation q c

noncomputable def argumentValue (q c : Nat) : Ordinal.{0} := interpretation q (argumentCode c)

theorem node_baseCheck (q c : Nat) (hc : Node q c) : baseCheck q = true := by
  obtain ⟨a, rfl, ha, hn⟩ := hc
  exact (Bool.and_eq_true.mp ha).1

theorem node_accepted (q c : Nat) (hc : Node q c) : Comparison.acceptedCode q c = true := by
  obtain ⟨a, rfl, ha, hn⟩ := hc
  exact (Comparison.acceptedCode_exact q _).mpr
    ⟨by simpa only [checkCode_code] using ha,
      by simpa only [rawTree_code, Comparison.Normal] using hn⟩

theorem node_low (q c : Nat) (hc : Node q c) : lowCheckCode q c = true := by
  obtain ⟨a, rfl, ha, hn⟩ := hc
  simp only [lowCheckCode_code, lowCheck, ha, RelativeTerm.outerSort, Nat.zero_add,
    le_refl, decide_true, Bool.true_and]

theorem node_normal (q c : Nat) (hc : Node q c) : Comparison.Normal q (rawTree c) :=
  ((Comparison.acceptedCode_exact q c).mp (node_accepted q c hc)).2

theorem node_argument (q c : Nat) (hc : Node q c) :
    Comparison.acceptedCode q (argumentCode c) = true := by
  obtain ⟨a, rfl, ha, hn⟩ := hc
  rw [argumentCode_theta]
  exact (Comparison.acceptedCode_exact q _).mpr
    ⟨by simpa only [checkCode_code] using FixedPoint.checked_theta_argument q 0 a ha,
      by simpa only [rawTree_code] using hn⟩

theorem value_less_exact (q c d : Nat) (hc : Node q c) (hd : Node q d) :
    Normalization.lessRawCode q c d = true ↔ value q c < value q d := by
  have hcc := ((Comparison.acceptedCode_exact q c).mp (node_accepted q c hc)).1
  have hdc := ((Comparison.acceptedCode_exact q d).mp (node_accepted q d hd)).1
  simpa only [hcc, hdc, true_and, value] using Normalization.lessRawCode_exact q c d

theorem argument_less_exact (q c d : Nat) (hc : Node q c) (hd : Node q d) :
    Normalization.lessRawCode q (argumentCode c) (argumentCode d) = true ↔
      argumentValue q c < argumentValue q d := by
  have hcc := ((Comparison.acceptedCode_exact q _).mp (node_argument q c hc)).1
  have hdc := ((Comparison.acceptedCode_exact q _).mp (node_argument q d hd)).1
  simpa only [hcc, hdc, true_and, argumentValue] using
    Normalization.lessRawCode_exact q (argumentCode c) (argumentCode d)

theorem node_value_eq_iff_argument_eq (q c d : Nat) (hc : Node q c) (hd : Node q d) :
    value q c = value q d ↔ argumentValue q c = argumentValue q d := by
  obtain ⟨a, rfl, ha, hn⟩ := hc
  obtain ⟨b, rfl, hb, hnb⟩ := hd
  simp only [value, argumentValue, argumentCode_theta, interpretation_code]
  constructor
  · intro he
    exact (SourceChi.Invariance.theta_value_injective q 0 0 a b ha hb he).2
  · intro he
    change globalCollapse (base q) 0 (denote q a) = globalCollapse (base q) 0 (denote q b)
    exact congrArg (globalCollapse (base q) 0) he

def support (c : Nat) : List Nat := PrincipalSupport.listCode 0 c

theorem support_primrec : Primrec support :=
  PrincipalSupport.listCode_primrec.comp (Primrec.const 0) Primrec.id

theorem support_node (q c d : Nat) (hc : Node q c) (hd : d ∈ support c) : Node q d := by
  obtain ⟨a, rfl, ha, hn⟩ := hc
  rw [support, PrincipalSupport.listCode_code] at hd
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hd
  obtain ⟨b, rfl⟩ := RelativeTerm.PrincipalSupport.principalList_shape 0 (.theta 0 a) s hs
  exact ⟨b, rfl, Iota.checked_full_node q _ _ ha hs,
    RootSupportThreshold.normal_full_node q _ _ hn hs⟩

theorem support_root (q c : Nat) (hc : Node q c) : c ∈ support c := by
  obtain ⟨a, rfl, ha, hn⟩ := hc
  rw [support, PrincipalSupport.listCode_code]
  exact List.mem_map.mpr ⟨.theta 0 a, RelativeTerm.PrincipalSupport.principalList_root 0 a, rfl⟩

theorem support_bound (q c d : Nat) (hc : Node q c) (hd : d ∈ support c) :
    value q d ≤ value q c := by
  obtain ⟨a, rfl, ha, hn⟩ := hc
  rw [support, PrincipalSupport.listCode_code] at hd
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hd
  simpa only [value, interpretation_code] using
    Iota.Inverse.fullList_value_le_low q (.theta 0 a) s ha hn (by
      simp only [RelativeTerm.outerSort]; omega) hs

theorem support_trans (q c d e : Nat) (hc : Node q c)
    (hd : d ∈ support c) (he : e ∈ support d) : e ∈ support c := by
  obtain ⟨a, rfl, ha, hn⟩ := hc
  rw [support, PrincipalSupport.listCode_code] at hd
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hd
  rw [support, PrincipalSupport.listCode_code] at he ⊢
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp he
  exact List.mem_map.mpr ⟨t, Hereditary.Localization.Refinements.principalList_trans
    0 (.theta 0 a) s t hs ht, rfl⟩

theorem reversed_argument_witness (q c d : Nat) (hc : Node q c) (hd : Node q d)
    (hv : value q c < value q d) (ha : argumentValue q d ≤ argumentValue q c) :
    ∃ s : RelativeTerm Nat,
      s ∈ RelativeTerm.PrincipalSupport.principalList 0 (rawTree (argumentCode d)) ∧
      value q c ≤ denote q s := by
  obtain ⟨a, rfl, hca, hn⟩ := hc
  obtain ⟨b, rfl, hdb, hnb⟩ := hd
  have hcmp := (Iota.OrderInduction.checked_theta_lt_iff_exposed q 0 a b hca hdb hn hnb).mp
    (by simpa only [value, interpretation_code] using hv)
  have harg : denote q b ≤ denote q a := by
    simpa only [argumentValue, argumentCode_theta, interpretation_code] using ha
  rcases hcmp with hcmp | ⟨s, hs, hval⟩
  · exact False.elim (harg.not_gt hcmp.1)
  · exact ⟨s, by simpa only [argumentCode_theta, rawTree_code] using
      RelativeTerm.PrincipalSupport.exposed_mem_principalList 0 b s hs,
      by simpa only [value, interpretation_code] using hval⟩

theorem nested_support_size (q d : Nat) (hd : Node q d) (s : RelativeTerm Nat)
    (hs : s ∈ RelativeTerm.PrincipalSupport.principalList 0 (rawTree (argumentCode d))) :
    s.code ∈ support d ∧ (rawTree s.code).size < (rawTree d).size := by
  obtain ⟨b, rfl, hb, hn⟩ := hd
  have hsb : s ∈ RelativeTerm.PrincipalSupport.principalList 0 b := by
    simpa only [argumentCode_theta, rawTree_code] using hs
  constructor
  · rw [support, PrincipalSupport.listCode_code]
    exact List.mem_map.mpr ⟨s, RelativeTerm.PrincipalSupport.principalList_nested 0 b s hsb, rfl⟩
  · simpa only [rawTree_code] using
      RelativeTerm.PrincipalSupport.principalList_argument_size_lt 0 0 b s hsb

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceLocalization
