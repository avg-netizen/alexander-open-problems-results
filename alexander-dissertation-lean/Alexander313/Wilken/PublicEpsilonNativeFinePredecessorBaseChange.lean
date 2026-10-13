import Alexander313.Wilken.PublicEpsilonNativeLocalizationBaseChangeSupport
import Alexander313.Wilken.PublicEpsilonNativeFinePredecessor

/-!
# Actual fine-predecessor parameter provenance and literal pi transport

The original chosen parameter bound derives every second-source caller.
The genuine unit/STRICT prefix branch and actual ordinary-path fallback
agree literally on the SAME written original root. Target output admission
then proves the FULL payload and Par bound; no numerical value equality is
used as a substitute for parameter provenance. Source-only, uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceFinePredecessor.BaseChange

open ThetaCourse SourceLocalization

theorem equalRawCode_context (q v c d : Nat)
    (hcq : checkCode q c = true) (hdq : checkCode q d = true)
    (hcv : checkCode v c = true) (hdv : checkCode v d = true) :
    Normalization.equalRawCode q c d = Normalization.equalRawCode v c d := by
  have hnc := BaseTransformation.normalizeCode_context q v c hcq hcv
  have hnd := BaseTransformation.normalizeCode_context q v d hdq hdv
  have hccq := (Normalization.normalizeCode_checked q c hcq).1
  have hddq := (Normalization.normalizeCode_checked q d hdq).1
  have hccv : checkCode v (Normalization.normalizeCode q c) = true := by
    rw [hnc]; exact (Normalization.normalizeCode_checked v c hcv).1
  have hddv : checkCode v (Normalization.normalizeCode q d) = true := by
    rw [hnd]; exact (Normalization.normalizeCode_checked v d hdv).1
  have he := SourceChi.BaseChange.equalCode_context q v
    (Normalization.normalizeCode q c) (Normalization.normalizeCode q d) hccq hddq hccv hddv
  simp only [Normalization.equalRawCode, hcq, hdq, hcv, hdv, Bool.true_and]
  exact he.trans (congrArg₂ (Comparison.equalCode v) hnc hnd)

/-- The actual raw STRICT algorithm uses the SAME normalized written
argument at both admitted sources, including its genuine higher test. -/
theorem strictRawCode_context (q v m c : Nat)
    (hcq : checkCode q c = true) (hcv : checkCode v c = true) :
    FixedPoint.strictRawCode q m c = FixedPoint.strictRawCode v m c := by
  have hn := BaseTransformation.normalizeCode_context q v c hcq hcv
  have haq : Decomposition.inputCheck q (Normalization.normalizeCode q c) = true :=
    (Normalization.normalizeCode_accepted q c hcq).1
  have hav : Decomposition.inputCheck v (Normalization.normalizeCode q c) = true := by
    rw [hn]; exact (Normalization.normalizeCode_accepted v c hcv).1
  have he := SourceChi.BaseChange.strictCode_context q v m _ haq hav
  simp only [FixedPoint.strictRawCode, FixedPoint.rawInputCheck, hcq, hcv, Bool.true_and]
  rw [he, hn]

theorem firstBranch_context (q v c : Nat) (hcq : Node q c) (hcv : Node v c) :
    firstBranch q c = firstBranch v c := by
  by_cases he : lowWord q c = []
  · have hev : lowWord v c = [] := he
    simp only [firstBranch, he, hev, List.isEmpty_nil, Bool.not_true, Bool.false_and]
  · have hev : lowWord v c ≠ [] := he
    have hlq := low_split q c hcq he
    have hlv := low_split v c hcv hev
    have huq := unitCode_spec q (node_baseCheck q c hcq)
    have huv := unitCode_spec v (node_baseCheck v c hcv)
    have hu := equalRawCode_context q v (lastAtom q c).code (unitCode q)
      (by simpa only [checkCode_code] using hlq.2.1)
      ((Comparison.acceptedCode_exact q _).mp huq.1).1
      (by simpa only [checkCode_code] using hlv.2.1)
      ((Comparison.acceptedCode_exact v _).mp huv.1).1
    have hp := strictRawCode_context q v 0 (prefixCode q c)
      (prefix_checked q c hcq).1 (prefix_checked v c hcv).1
    change !(lowWord q c).isEmpty &&
        (Normalization.equalRawCode q (lastAtom q c).code (unitCode q) ||
          FixedPoint.strictRawCode q 0 (prefixCode q c)) =
      !(lowWord q c).isEmpty &&
        (Normalization.equalRawCode v (lastAtom q c).code (unitCode q) ||
          FixedPoint.strictRawCode v 0 (prefixCode q c))
    rw [hu, hp]

theorem inputCheck_context (q v c : Nat) (hcq : Node q c) (hcv : Node v c) :
    inputCheck q c = inputCheck v c := by
  have hbq := baseRaw_node q (node_baseCheck q c hcq)
  have hbv : Node v (baseRaw q) := by
    simpa only [baseRaw] using baseRaw_node v (node_baseCheck v c hcv)
  have he := OmegaPowers.BaseChange.lessRawCode_context q v (baseRaw q) c
    (SourceLocalization.BaseChange.node_checked q _ hbq)
    (SourceLocalization.BaseChange.node_checked q c hcq)
    (SourceLocalization.BaseChange.node_checked v _ hbv)
    (SourceLocalization.BaseChange.node_checked v c hcv)
  change SourceLocalization.inputCheck q c && Normalization.lessRawCode q (baseRaw q) c =
    SourceLocalization.inputCheck v c && Normalization.lessRawCode v (baseRaw q) c
  rw [SourceLocalization.BaseChange.inputCheck_context q v c hcq hcv, he]

theorem fallback_context (q v c : Nat) (hcq : Node q c) (hcv : Node v c) :
    fallback q c = fallback v c :=
  congrArg penultimate (SourceLocalization.BaseChange.nativePath_context q v c hcq hcv)

theorem nativeCode_context (q v c : Nat) (hcq : Node q c) (hcv : Node v c) :
    nativeCode q c = nativeCode v c := by
  change cond (firstBranch q c) (prefixNode q c) (fallback q c) =
    cond (firstBranch v c) (prefixNode q c) (fallback v c)
  rw [firstBranch_context q v c hcq hcv, fallback_context q v c hcq hcv]

theorem predecessorCode_context (q v c : Nat) (hcq : Node q c) (hcv : Node v c) :
    predecessorCode q c = predecessorCode v c := by
  simp only [predecessorCode, inputCheck_context q v c hcq hcv,
    nativeCode_context q v c hcq hcv]

/-- The original chosen Par bound derives the actual second-source Node
and proper caller; there is no target guard premise. -/
theorem target_input (q v c : Nat) (hc : inputCheck q c = true)
    (hv : baseCheck v = true) (hp : BaseTransformation.ParBounded q v (rawTree c)) :
    inputCheck v c = true := by
  have hn := ((inputCheck_exact q c).mp hc).1
  have ht := SourceLocalization.BaseChange.node_change q v c hn hv hp
  rw [← inputCheck_context q v c hn ht]
  exact hc

/-- FULL syntactic output payloads follow from the actual transported
predecessor checker, rather than from its ordinal value bound. -/
theorem predecessor_payloads (q v c : Nat) (hc : inputCheck q c = true)
    (hv : baseCheck v = true) (hp : BaseTransformation.ParBounded q v (rawTree c)) :
    Payloads v (rawTree (predecessorCode q c)) := by
  have hn := ((inputCheck_exact q c).mp hc).1
  have ht := SourceLocalization.BaseChange.node_change q v c hn hv hp
  have hi := target_input q v c hc hv hp
  have hout := SourceLocalization.BaseChange.node_checked v _ (predecessor_spec v c hi).1
  rw [← predecessorCode_context q v c hn ht] at hout
  exact (checked_admissible v _ (Arithmetic.raw_checked v _ hout)).1

theorem predecessor_Par (q v c : Nat) (hc : inputCheck q c = true)
    (hv : baseCheck v = true) (hp : BaseTransformation.ParBounded q v (rawTree c)) :
    BaseTransformation.ParBounded q v (rawTree (predecessorCode q c)) :=
  (BaseTransformation.parBounded_iff_payloads q v _
    (Arithmetic.raw_checked q _
      (SourceLocalization.BaseChange.node_checked q _ (predecessor_spec q c hc).1)) hv).mpr
    (predecessor_payloads q v c hc hv hp)

theorem predecessor_pi_input (q v c : Nat) (hc : inputCheck q c = true)
    (hv : baseCheck v = true) (hbase : base v < base q)
    (hp : BaseTransformation.ParBounded q v (rawTree c)) :
    BaseTransformation.inputCheck q v (predecessorCode q c) = true :=
  (BaseTransformation.inputCheck_exact q v _).mpr
    ⟨SourceLocalization.BaseChange.node_checked q _ (predecessor_spec q c hc).1,
      hv, hbase, predecessor_Par q v c hc hv hp⟩

theorem piCode_predecessorCode (q v c : Nat) (hc : inputCheck q c = true)
    (hv : baseCheck v = true) (hbase : base v < base q)
    (hp : BaseTransformation.ParBounded q v (rawTree c)) :
    BaseTransformation.piCode q v (predecessorCode q c) = predecessorCode v c := by
  rw [BaseTransformation.piCode_eq q v _ (predecessor_pi_input q v c hc hv hbase hp)]
  have hn := ((inputCheck_exact q c).mp hc).1
  exact predecessorCode_context q v c hn
    (SourceLocalization.BaseChange.node_change q v c hn hv hp)

/-- Literal partial execution agreement, with original target admission
and FULL output provenance derived from the original input bound. -/
theorem predecessor_execute_context (q v c : Nat) (hc : inputCheck q c = true)
    (hv : baseCheck v = true) (hp : BaseTransformation.ParBounded q v (rawTree c)) :
    predecessor q c = predecessor v c := by
  have hn := ((inputCheck_exact q c).mp hc).1
  have ht := SourceLocalization.BaseChange.node_change q v c hn hv hp
  simp only [predecessor, hc, target_input q v c hc hv hp, Bool.cond_true,
    predecessorCode_context q v c hn ht]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceFinePredecessor.BaseChange
