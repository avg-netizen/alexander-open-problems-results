import Alexander313.Wilken.PublicEpsilonNativeFineLocalizationBaseChange

/-!
# Original raw fine-localization pi transport

The ORIGINAL raw theta-zero guard and chosen Par bound derive actual
target admission. Genuine normalization context agreement proves FULL
target payloads for the computed normalized root. The actual finite run
transport then supplies every path-node pi caller and the literal encoded
output equation. Raw value fidelity is not used as a provenance oracle.
All sources are uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceFineLocalization.Raw.BaseChange

open ThetaCourse

theorem target_input (q v c : Nat) (hc : Raw.inputCheck q c = true)
    (hv : baseCheck v = true) (hp : BaseTransformation.ParBounded q v (rawTree c)) :
    Raw.inputCheck v c = true := by
  obtain ⟨a, rfl, ha⟩ := (Raw.inputCheck_exact q c).mp hc
  have hpayload : Payloads v (.theta 0 a) :=
    (BaseTransformation.parBounded_iff_payloads q v _ ha hv).mp
      (by simpa only [rawTree_code] using hp)
  exact (Raw.inputCheck_exact v _).mpr
    ⟨a, rfl, BaseTransformation.check_change q v (.theta 0 a) ha hv hpayload⟩

theorem normalized_context (q v c : Nat) (hc : Raw.inputCheck q c = true)
    (hv : baseCheck v = true) (hp : BaseTransformation.ParBounded q v (rawTree c)) :
    Normalization.normalizeCode q c = Normalization.normalizeCode v c :=
  BaseTransformation.normalizeCode_context q v c (Bool.and_eq_true.mp hc).1
    (Bool.and_eq_true.mp (target_input q v c hc hv hp)).1

/-- The real target normalizer checker supplies FULL target payloads for
the actual original normalized root. No semantic cutoff is substituted. -/
theorem normalized_payloads (q v c : Nat) (hc : Raw.inputCheck q c = true)
    (hv : baseCheck v = true) (hp : BaseTransformation.ParBounded q v (rawTree c)) :
    Payloads v (rawTree (Normalization.normalizeCode q c)) := by
  have ht := target_input q v c hc hv hp
  have hs := (Normalization.normalizeCode_checked v c (Bool.and_eq_true.mp ht).1).1
  rw [← normalized_context q v c hc hv hp] at hs
  exact (checked_admissible v _ (Arithmetic.raw_checked v _ hs)).1

theorem normalized_Par (q v c : Nat) (hc : Raw.inputCheck q c = true)
    (hv : baseCheck v = true) (hp : BaseTransformation.ParBounded q v (rawTree c)) :
    BaseTransformation.ParBounded q v (rawTree (Normalization.normalizeCode q c)) :=
  (BaseTransformation.parBounded_iff_payloads q v _
    (Arithmetic.raw_checked q _
      (Normalization.normalizeCode_checked q c (Bool.and_eq_true.mp hc).1).1) hv).mpr
    (normalized_payloads q v c hc hv hp)

theorem execute_context (q v c : Nat) (hc : Raw.inputCheck q c = true)
    (hv : baseCheck v = true) (hp : BaseTransformation.ParBounded q v (rawTree c)) :
    Raw.execute q c = Raw.execute v c := by
  have ht := target_input q v c hc hv hp
  have hn := normalized_context q v c hc hv hp
  have hcq := Raw.normalized_node q c hc
  have hcv : SourceLocalization.Node v (Normalization.normalizeCode q c) := by
    rw [hn]; exact Raw.normalized_node v c ht
  have he := SourceFineLocalization.BaseChange.fineLocalization_context q v _ hcq hcv
  simp only [Raw.execute, hc, ht, Bool.cond_true]
  rw [he, hn]

/-- Complete actual raw output transport, with FULL chosen-source Par and
real pi admission for EVERY node of the genuinely computed finite path. -/
theorem execute_provenance (q v c output : Nat) (ho : output ∈ Raw.execute q c)
    (hv : baseCheck v = true) (hbase : base v < base q)
    (hp : BaseTransformation.ParBounded q v (rawTree c)) :
    output ∈ Raw.execute v c ∧ ∃ n,
      output = Encodable.encode (word q (Normalization.normalizeCode q c) n) ∧
      (∀ d ∈ word q (Normalization.normalizeCode q c) n, Payloads v (rawTree d)) ∧
      (∀ d ∈ word q (Normalization.normalizeCode q c) n,
        BaseTransformation.ParBounded q v (rawTree d)) ∧
      (∀ d ∈ word q (Normalization.normalizeCode q c) n,
        BaseTransformation.inputCheck q v d = true) ∧
      (word q (Normalization.normalizeCode q c) n).map (BaseTransformation.piCode q v) =
        word v (Normalization.normalizeCode v c) n := by
  obtain ⟨hc, hm⟩ := (Raw.execute_graph q c output).mp ho
  have hp' := normalized_Par q v c hc hv hp
  obtain ⟨_, n, he, hpay, hpar, hpi, hword⟩ :=
    SourceFineLocalization.BaseChange.execute_provenance q v _ output hm hv hbase hp'
  have hout : output ∈ Raw.execute v c := by rw [← execute_context q v c hc hv hp]; exact ho
  exact ⟨hout, n, he, hpay, hpar, hpi,
    by simpa only [normalized_context q v c hc hv hp] using hword⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceFineLocalization.Raw.BaseChange
