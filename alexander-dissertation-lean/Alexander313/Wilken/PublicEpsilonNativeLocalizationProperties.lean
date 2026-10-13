import Alexander313.Wilken.PublicEpsilonNativeLocalizationPropertiesSupport
import Alexander313.Wilken.SourceHighPartComparison
import Alexander313.Wilken.PublicEpsilonNativeUnboundedMu

/-!
# Actual divided-head descent and value-prefix locality, source 2.33(b/c)

Every pair of selected arguments is strictly reversed after the initial
base. The genuine global collapse comparison then forces strict descent
of their actual Omega-one division multiples. A proper intermediate node
therefore has a high argument and the actual original mu root caller;
the last path value is not asserted to be epsilon. Real source recurrence
and maximal-argument value uniqueness identify every prefix by ordinal
value with the localization at its endpoint. No literal spelling equality,
level, high-root or prefix-locality oracle is supplied. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceLocalization.Properties

open ThetaCourse

noncomputable def localizationLevel (q c : Nat) : Ordinal.{0} :=
  SourceHighPartComparison.highPart (omegaSequence (base q) 1) (argumentValue q c)

/-- The actual divided head is a genuine Omega-one multiple. -/
theorem localizationLevel_multiple (q c : Nat) :
    omegaSequence (base q) 1 ∣ localizationLevel q c :=
  SourceHighPartComparison.highPart_dvd _ _

/-- Actual increasing collapse values and reversed admitted arguments
force strict descent of their genuine divided heads. -/
theorem node_level_lt (q c d : Nat) (hc : Node q c) (hd : Node q d)
    (hv : value q c < value q d) (harg : argumentValue q d ≤ argumentValue q c) :
    localizationLevel q d < localizationLevel q c := by
  obtain ⟨a, rfl, ha, hn⟩ := hc
  obtain ⟨b, rfl, hb, hm⟩ := hd
  have hq := (Bool.and_eq_true.mp ha).1
  let an := FixedPoint.sourceOrdinal q 0 a (FixedPoint.checked_theta_argument q 0 a ha)
  let bn := FixedPoint.sourceOrdinal q 0 b (FixedPoint.checked_theta_argument q 0 b hb)
  have hvalues : globalCollapse (base q) 0 an.val < globalCollapse (base q) 0 bn.val := by
    change denote q (.theta 0 a) < denote q (.theta 0 b)
    simpa only [value, interpretation_code] using hv
  have harguments : bn.val ≤ an.val := by
    simpa only [argumentValue, argumentCode_theta, interpretation_code] using harg
  have hlevel := SourceHighPartComparison.global_highPart_lt_of_argument_le (base q)
    (base_pos q hq) 0 an bn (FixedPoint.checked_theta_sort q 0 a ha)
      (FixedPoint.checked_theta_sort q 0 b hb) hvalues harguments
  simpa only [localizationLevel, argumentValue, argumentCode_theta, interpretation_code] using hlevel

/-- Source 2.33(b): after the initial base, the actual divided heads
strictly decrease along the genuine original finite path. -/
theorem sourcePath_levels_descending {q : Nat} {source : List Nat} {c : Nat} {tail : List Nat}
    (hp : SourcePath q source (c :: tail)) :
    (tail.map (localizationLevel q)).Pairwise (fun a b => b < a) := by
  induction hp with
  | stop c hc hmax => simp only [List.map_nil, List.pairwise_nil]
  | next c d tail hc hcd hd harg hp ih =>
    apply List.pairwise_cons.mpr
    refine ⟨?_, ih⟩
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    have hde := sourcePath_head_lt_tail hp e he
    have hdn := hp.nodes d List.mem_cons_self
    have hen := hp.nodes e (List.mem_cons_of_mem _ he)
    have hle := harg e (sourcePath_tail_mem hp e he) (hcd.trans hde)
    exact node_level_lt q d e hdn hen hde hle

theorem nativePath_levels_descending (q root : Nat) (hi : inputCheck q root = true) :
    ((nativePath q root).tail.map (localizationLevel q)).Pairwise (fun a b => b < a) := by
  obtain ⟨tail, he⟩ := nativePath_head q root
  have hp := nativePath_source q root hi
  rw [he] at hp ⊢
  simpa only [List.tail_cons] using sourcePath_levels_descending hp

/-- Positive genuine divided head forces the original argument to be HIGH,
so the actual mu root caller follows from the existing source Node. -/
theorem node_high_of_level_pos (q c : Nat) (hc : Node q c)
    (hl : 0 < localizationLevel q c) : RootLowCollapse.rootCheck q c = true := by
  obtain ⟨a, rfl, ha, hn⟩ := hc
  have hca := FixedPoint.checked_theta_argument q 0 a ha
  have hhigh : 1 < a.outerSort := by
    apply lt_of_not_ge
    intro hlo
    have hsmall := (denote_lt_iff_outerSort_le q a hca 1 (by omega)).mpr hlo
    have hz : localizationLevel q (.theta 0 a : RelativeTerm Nat).code = 0 := by
      simp only [localizationLevel, argumentValue, argumentCode_theta, interpretation_code,
        SourceHighPartComparison.highPart, Ordinal.div_eq_zero_of_lt hsmall, mul_zero]
    rw [hz] at hl
    exact lt_irrefl _ hl
  exact (RootLowCollapse.rootCheck_exact q _).mpr ⟨a, rfl, ha, hn, hhigh⟩

/-- Every genuinely selected node with another selected node following it
is an actual HIGH epsilon root; the initial base is excluded explicitly. -/
theorem sourcePath_intermediate_high {q : Nat} {source : List Nat} {previous c d : Nat}
    {tail : List Nat} (hp : SourcePath q source (previous :: c :: d :: tail)) :
    RootLowCollapse.rootCheck q c = true := by
  have hs := sourcePath_levels_descending hp
  have hlt : localizationLevel q d < localizationLevel q c :=
    (List.pairwise_cons.mp hs).1 _ (List.mem_map.mpr ⟨d, List.mem_cons_self, rfl⟩)
  exact node_high_of_level_pos q c
    (hp.nodes c (List.mem_cons_of_mem _ List.mem_cons_self))
    ((show (0 : Ordinal.{0}) ≤ localizationLevel q d from bot_le).trans_lt hlt)

/-- Proper intermediate positions derive the full actual mu caller and its
strict source-base bound. No epsilon condition is imposed on the final value. -/
theorem nativePath_intermediate_high (q root : Nat) (hi : inputCheck q root = true)
    («prefix» : List Nat) (previous c d : Nat) (tail : List Nat)
    (he : nativePath q root = «prefix» ++ previous :: c :: d :: tail) :
    RootLowCollapse.rootCheck q c = true ∧ base q < value q c ∧
      Ordinal.omega0 ^ value q c = value q c := by
  have hp := sourcePath_suffix (nativePath_source q root hi) «prefix» previous (c :: d :: tail) he
  have hc := sourcePath_intermediate_high hp
  exact ⟨hc, PublicEpsilonUnboundedIota.root_base_lt q c hc,
    RootLowCollapse.root_epsilon q c hc⟩

/-- Every actual proper intermediate node is in the genuine normal mu
execution domain, with its caller derived from divided-head descent. -/
theorem nativePath_intermediate_mu_domain (q root : Nat) (hi : inputCheck q root = true)
    («prefix» : List Nat) (previous c d : Nat) (tail : List Nat)
    (he : nativePath q root = «prefix» ++ previous :: c :: d :: tail) :
    (PublicEpsilonUnboundedIota.Mu.execute q c).Dom :=
  (PublicEpsilonUnboundedIota.Mu.execute_domain q c).mpr
    (nativePath_intermediate_high q root hi «prefix» previous c d tail he).1

/-- Every selected tail node before its final entry has positive divided
head, hence the actual original HIGH root guard. -/
theorem sourcePath_proper_tail_high {q : Nat} {source : List Nat} {previous : Nat}
    {tail : List Nat} (hp : SourcePath q source (previous :: tail)) (c : Nat)
    (hc : c ∈ Hereditary.FinePredecessor.stripLast tail) :
    RootLowCollapse.rootCheck q c = true := by
  have hne : tail ≠ [] := by
    intro he
    subst tail
    exact List.not_mem_nil hc
  obtain ⟨d, he, _⟩ := Hereditary.FinePredecessor.stripLast_split tail hne
  have hs := sourcePath_levels_descending hp
  rw [he, List.map_append, List.map_cons, List.map_nil] at hs
  have hlt : localizationLevel q d < localizationLevel q c :=
    (List.pairwise_append.mp hs).2.2 _ (List.mem_map.mpr ⟨c, hc, rfl⟩) _ List.mem_cons_self
  exact node_high_of_level_pos q c
    (hp.nodes c (List.mem_cons_of_mem _ (Hereditary.FinePredecessor.stripLast_mem tail c hc)))
    ((show (0 : Ordinal.{0}) ≤ localizationLevel q d from bot_le).trans_lt hlt)

/-- All proper prefix entries after the initial base have the derived
actual mu domain and genuine epsilon/LOW source admission. -/
theorem nativePath_proper_prefix_spec (q root : Nat) (hi : inputCheck q root = true)
    (c : Nat) (hc : c ∈ Hereditary.FinePredecessor.stripLast (nativePath q root).tail) :
    RootLowCollapse.rootCheck q c = true ∧ lowCheckCode q c = true ∧
      base q < value q c ∧ Ordinal.omega0 ^ value q c = value q c ∧
        (PublicEpsilonUnboundedIota.Mu.execute q c).Dom := by
  obtain ⟨tail, he⟩ := nativePath_head q root
  have hp := nativePath_source q root hi
  rw [he] at hp
  rw [he, List.tail_cons] at hc
  have hroot := sourcePath_proper_tail_high hp c hc
  exact ⟨hroot, RootLowCollapse.root_low q c hroot,
    PublicEpsilonUnboundedIota.root_base_lt q c hroot,
    RootLowCollapse.root_epsilon q c hroot,
    (PublicEpsilonUnboundedIota.Mu.execute_domain q c).mpr hroot⟩

/-- Source 2.33(c): the actual value prefix is the complete value
localization at its endpoint, even if written support witnesses differ. -/
theorem nativePath_value_prefix (q root : Nat) (hroot : inputCheck q root = true)
    («prefix» : List Nat) (d : Nat) (suffix : List Nat)
    (he : nativePath q root = «prefix» ++ d :: suffix) :
    («prefix» ++ [d]).map (value q) = (nativePath q d).map (value q) := by
  have hrootNode := (inputCheck_exact q root).mp hroot
  have hp := nativePath_source q root hroot
  have hprefix := sourcePath_prefix_valuePath hrootNode hp «prefix» d suffix he
  have hdPath : d ∈ nativePath q root := by
    rw [he]
    exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  have hd := hp.nodes d hdPath
  have hdp := nativePath_source q d ((inputCheck_exact q d).mpr hd)
  obtain ⟨rootTail, hrootHead⟩ := nativePath_head q root
  have hprefixHead : ∃ tail : List Nat, «prefix» ++ [d] = baseRaw q :: tail := by
    cases «prefix» with
    | nil =>
      have hsame : baseRaw q :: rootTail = d :: suffix := by
        simpa only [List.nil_append] using hrootHead.symm.trans he
      rw [← (List.cons.inj hsame).1]
      exact ⟨[], rfl⟩
    | cons c «prefix» =>
      have hsame : baseRaw q :: rootTail = c :: («prefix» ++ d :: suffix) := by
        simpa only [List.cons_append] using hrootHead.symm.trans he
      rw [← (List.cons.inj hsame).1]
      exact ⟨«prefix» ++ [d], rfl⟩
  obtain ⟨prefixTail, hprefixHead⟩ := hprefixHead
  obtain ⟨dTail, hdHead⟩ := nativePath_head q d
  have hvalues : («prefix» ++ [d]).map (value q) = (nativePath q d).map (value q) := by
    rw [hprefixHead] at hprefix
    rw [hdHead] at hdp
    rw [hprefixHead, hdHead]
    exact hprefix.values_unique (fun e he => support_node q d e hd he) _ _
      (sourcePath_valuePath hdp) rfl
  exact hvalues

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceLocalization.Properties
