import Alexander313.Wilken.SourceOneNormalizationAtoms

/-!
# Actual terminating normalization of base-one source trees

Normalization recurses through every theta body. Written sums are replaced by
the reconstructed normalized list of their already normalized principal atoms.
All recursive operations are on literal finite trees/lists and use the actual
executing comparator. Source admission, finite denotation, NormalSums and
global denotation are proved together from the unchanged source constructions.

Accepted normal-code coverage follows for the actual global grammar and its
low boundary interval. No normalization or coverage oracle is an input. The
output is not claimed to be a unique canonical syntax, and uniform Primrec/
Program realization and hereditary-base normalization remain separate work.
-/

namespace Alexander313.Wilken.RelativeTerm.SourceOne.Normalization

def normalize : RelativeTerm Nat → RelativeTerm Nat
  | .parameter _ => .parameter 0
  | .theta k a => .theta k (normalize a)
  | .sum a b => buildAtoms (normalizeAtoms (thetaAtoms (normalize a) ++ thetaAtoms (normalize b)))

theorem normalize_spec (n : Nat) (t : RelativeTerm Nat) (ht : admissible n t) :
    admissible n (normalize t) ∧ Normal n (normalize t) ∧ denote n (normalize t) = denote n t := by
  induction ht with
  | @parameter p hp =>
    have hp0 := (parameter_lt_base_iff p).mp hp
    subst p
    exact ⟨.parameter ((parameter_lt_base_iff 0).mpr rfl), trivial, rfl⟩
  | @theta k a h0k hkn hsort ha ih =>
    have hnew : admissible n (.theta k (normalize a)) :=
      .theta h0k hkn (by
        change denote n (normalize a) < omegaSequence 1 (k + 2)
        rw [ih.2.2]
        exact hsort) ih.1
    refine ⟨hnew, ih.2.1, ?_⟩
    change sourceFiniteCollapse 1 n k (denote n (normalize a)) = sourceFiniteCollapse 1 n k (denote n a)
    rw [ih.2.2]
  | @sum a b ha hb iha ihb =>
    let atoms := thetaAtoms (normalize a) ++ thetaAtoms (normalize b)
    have hgood : GoodAtoms n atoms :=
      (GoodAtoms.thetaAtoms n (normalize a) iha.1 iha.2.1).append
        (GoodAtoms.thetaAtoms n (normalize b) ihb.1 ihb.2.1)
    have hnormal := normalizeAtoms_normal n atoms hgood
    have hretained := hgood.normalizeAtoms
    refine ⟨buildAtoms_admissible n (normalizeAtoms atoms) hretained,
      buildAtoms_normal n (normalizeAtoms atoms) hretained hnormal, ?_⟩
    calc
      denote n (normalize (.sum a b)) = principalSum ((normalizeAtoms atoms).map (denote n)) :=
        buildAtoms_denote n (normalizeAtoms atoms)
      _ = principalSum (atoms.map (denote n)) := normalizeAtoms_denote n atoms hgood
      _ = denote n (normalize a) + denote n (normalize b) := by
        rw [List.map_append, principalSum_append,
          thetaAtoms_denote_sum n (normalize a) iha.1 iha.2.1,
          thetaAtoms_denote_sum n (normalize b) ihb.1 ihb.2.1]
      _ = denote n (.sum a b) := by
        rw [iha.2.2, ihb.2.2]
        rfl

theorem normalize_admissible (n : Nat) (t : RelativeTerm Nat) (ht : admissible n t) :
    admissible n (normalize t) := (normalize_spec n t ht).1

theorem normalize_normal (n : Nat) (t : RelativeTerm Nat) (ht : admissible n t) :
    Normal n (normalize t) := (normalize_spec n t ht).2.1

theorem normalize_denote (n : Nat) (t : RelativeTerm Nat) (ht : admissible n t) :
    denote n (normalize t) = denote n t := (normalize_spec n t ht).2.2

theorem normalize_global_denote (n : Nat) (t : RelativeTerm Nat) (ht : admissible n t) :
    PublicCodes.denote (normalize t) = PublicCodes.denote t := by
  rw [PublicCodes.denote_eq_finite n (normalize t) (normalize_admissible n t ht),
    PublicCodes.denote_eq_finite n t ht]
  exact normalize_denote n t ht

theorem normalize_checked (n : Nat) (t : RelativeTerm Nat) (ht : admissible n t) :
    PublicCodes.check (normalize t) = true :=
  (PublicCodes.check_iff_finite_admissible (normalize t)).mpr ⟨n, normalize_admissible n t ht⟩

theorem normalize_accepted (n : Nat) (t : RelativeTerm Nat) (ht : admissible n t) :
    Comparison.acceptedCode (normalize t).code = true := by
  rw [Comparison.acceptedCode_code, Bool.and_eq_true]
  exact ⟨normalize_checked n t ht,
    (Comparison.normalCheck_correct n (normalize t) (normalize_admissible n t ht)).mpr
      (normalize_normal n t ht)⟩

def normalizeCode (c : Nat) : Nat :=
  ((RelativeTerm.decode c).map (fun t => (normalize t).code)).getD 0

@[simp] theorem normalizeCode_code (t : RelativeTerm Nat) :
    normalizeCode t.code = (normalize t).code := by
  simp only [normalizeCode, RelativeTerm.decode_code, Option.map_some, Option.getD_some]

/-- Actual syntax/admission excludes every auxiliary decoder default before
    assigning the normalized output its ordinal meaning. -/
theorem normalizeCode_checked (c : Nat) (hc : PublicCodes.checkCode c = true) :
    Comparison.acceptedCode (normalizeCode c) = true ∧
      PublicCodes.interpretation (normalizeCode c) = PublicCodes.interpretation c := by
  obtain ⟨t, rfl, ht⟩ := (PublicCodes.checkCode_iff c).mp hc
  have ha := (check_iff (PublicCodes.fragment t) t).mp ht
  rw [normalizeCode_code, PublicCodes.interpretation_code, PublicCodes.interpretation_code]
  exact ⟨normalize_accepted _ t ha, normalize_global_denote _ t ha⟩

theorem globalNotation_iff_normalCode (ξ : Ordinal.{0}) :
    GlobalNotation 1 0 ξ ↔
      ∃ c : Nat, Comparison.acceptedCode c = true ∧ PublicCodes.interpretation c = ξ := by
  constructor
  · intro hξ
    obtain ⟨c, hc, hvalue⟩ := (PublicCodes.globalNotation_iff_code ξ).mp hξ
    have hn := normalizeCode_checked c hc
    exact ⟨normalizeCode c, hn.1, hn.2.trans hvalue⟩
  · rintro ⟨c, hc, hvalue⟩
    exact (PublicCodes.globalNotation_iff_code ξ).mpr
      ⟨c, (Bool.and_eq_true_iff.mp hc).1, hvalue⟩

def acceptedLowCode (c : Nat) : Bool :=
  Comparison.acceptedCode c && decide (PublicCodes.outerSortCode c ≤ 1)

theorem acceptedLowCode_iff (c : Nat) : acceptedLowCode c = true ↔
    Comparison.acceptedCode c = true ∧ PublicCodes.interpretation c < globalBoundary 1 0 := by
  constructor
  · intro hc
    have hs : Comparison.acceptedCode c = true ∧ PublicCodes.outerSortCode c ≤ 1 := by
      simpa only [acceptedLowCode, Bool.and_eq_true, decide_eq_true_eq] using hc
    have hcheck : PublicCodes.lowCheckCode c = true := by
      have hsyntax := (Bool.and_eq_true_iff.mp hs.1).1
      simp only [PublicCodes.lowCheckCode, hsyntax, hs.2, decide_true, Bool.true_and]
    exact ⟨hs.1, (PublicCodes.lt_boundary_iff_code _).mpr ⟨c, hcheck, rfl⟩⟩
  · rintro ⟨hc, hξ⟩
    have hbase : (0 : Ordinal.{0}) < 1 := by simp
    have hlow := (globalNotation_low_iff_lt_boundary 1 hbase 0 _).mpr hξ
    obtain ⟨t, htc, ht, hnormal⟩ := (Comparison.acceptedCode_iff c).mp hc
    have hvaluet : PublicCodes.denote t = PublicCodes.interpretation c := by
      rw [← htc, PublicCodes.interpretation_code]
    have hsort : t.outerSort ≤ 1 :=
      (PublicCodes.denote_lt_iff_outerSort_le t ht 1 (by omega)).mp (by
        rw [hvaluet]
        exact hlow.2)
    have hsortCode : PublicCodes.outerSortCode c ≤ 1 := by
      simpa only [← htc, PublicCodes.outerSortCode_code] using hsort
    simp only [acceptedLowCode, hc, hsortCode, decide_true, Bool.true_and]

theorem lt_boundary_iff_normalCode (ξ : Ordinal.{0}) :
    ξ < globalBoundary 1 0 ↔
      ∃ c : Nat, acceptedLowCode c = true ∧ PublicCodes.interpretation c = ξ := by
  constructor
  · intro hξ
    have hbase : (0 : Ordinal.{0}) < 1 := by simp
    have hnotation := ((globalNotation_low_iff_lt_boundary 1 hbase 0 ξ).mpr hξ).1
    obtain ⟨c, hc, hvalue⟩ := (globalNotation_iff_normalCode ξ).mp hnotation
    exact ⟨c, (acceptedLowCode_iff c).mpr ⟨hc, by rw [hvalue]; exact hξ⟩, hvalue⟩
  · rintro ⟨c, hc, hvalue⟩
    simpa only [hvalue] using ((acceptedLowCode_iff c).mp hc).2

theorem normalizeCode_lowChecked (c : Nat) (hc : PublicCodes.lowCheckCode c = true) :
    acceptedLowCode (normalizeCode c) = true ∧
      PublicCodes.interpretation (normalizeCode c) = PublicCodes.interpretation c := by
  have hsyntax : PublicCodes.checkCode c = true := (Bool.and_eq_true_iff.mp hc).1
  have hn := normalizeCode_checked c hsyntax
  have hbound := (PublicCodes.lt_boundary_iff_code _).mpr ⟨c, hc, rfl⟩
  exact ⟨(acceptedLowCode_iff _).mpr ⟨hn.1, by rw [hn.2]; exact hbound⟩, hn.2⟩

def lessRawCode (c d : Nat) : Bool := Comparison.lessCode (normalizeCode c) (normalizeCode d)

def equalRawCode (c d : Nat) : Bool := Comparison.equalCode (normalizeCode c) (normalizeCode d)

theorem lessRawCode_correct (c d : Nat)
    (hc : PublicCodes.checkCode c = true) (hd : PublicCodes.checkCode d = true) :
    lessRawCode c d = true ↔ PublicCodes.interpretation c < PublicCodes.interpretation d := by
  have hcn := normalizeCode_checked c hc
  have hdn := normalizeCode_checked d hd
  simpa only [lessRawCode, hcn.2, hdn.2] using
    Comparison.lessCode_correct (normalizeCode c) (normalizeCode d) hcn.1 hdn.1

theorem equalRawCode_correct (c d : Nat)
    (hc : PublicCodes.checkCode c = true) (hd : PublicCodes.checkCode d = true) :
    equalRawCode c d = true ↔ PublicCodes.interpretation c = PublicCodes.interpretation d := by
  have hcn := normalizeCode_checked c hc
  have hdn := normalizeCode_checked d hd
  simpa only [equalRawCode, hcn.2, hdn.2] using
    Comparison.equalCode_correct (normalizeCode c) (normalizeCode d) hcn.1 hdn.1

end Alexander313.Wilken.RelativeTerm.SourceOne.Normalization
