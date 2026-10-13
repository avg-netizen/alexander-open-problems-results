import Alexander313.Wilken.PublicEpsilonNativeUnboundedIotaFixedPointTransport

/-!
# Genuine endpoint-free zero-last-exponent and shifted high-choice transport

Actual source/target canonical ANF alignment identifies the target last
principal component as the mapped original end atom. The genuine original
unit and zero remain LOW and reflection supplies both tests. This proves
actual executing high-choice flags at shifted theta arguments, not equality
of indicators at different epsilon bases. Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.LogEndZeroTransport

open ThetaCourse FixedPointTransport

/-- The actual original end atom remains in the original Restricted domain,
including the genuine zero fallback of an empty principal word. -/
theorem endAtom_restricted (q b : Nat) (t : RelativeTerm Nat) (hr : Restricted q b t) :
    Restricted q b (LogEndZero.endAtom t.code) := by
  cases hw : (Decomposition.word t.code).reverse with
  | nil =>
    simpa only [LogEndZero.endAtom, hw, List.getElem?_nil, Option.getD_none] using
      zero_restricted q b
  | cons x xs =>
    have hx : x ∈ Comparison.atoms t := by
      have hm : x ∈ (Decomposition.word t.code).reverse := by
        rw [hw]
        exact List.mem_cons_self
      simpa only [List.mem_reverse, Decomposition.word, rawTree_code] using hm
    simpa only [LogEndZero.endAtom, hw, List.getElem?_cons_zero, Option.getD_some] using
      OrderSupport.restricted_atoms q b t x hr hx

/-- The WHOLE actual target last component is the value of the mapped
original end atom; genuine canonical word alignment covers all stops. -/
theorem endValue_transform (q b : Nat) (ha : rootCheck q b = true)
    (t : RelativeTerm Nat) (ht : check q t = true) (hn : Comparison.Normal q t)
    (hr : Restricted q b t) :
    Hereditary.LogEnd.endValue (denote (betaCode q b) (transform q b t)) =
      denote (betaCode q b) (transform q b (LogEndZero.endAtom t.code)) := by
  rw [Hereditary.LogEnd.endValue, Hereditary.LogEnd.componentValue, Bool.cond_true,
    ← transform_atoms_anf q b ha t ht hn hr, ← List.map_reverse]
  have hword : Decomposition.word t.code = Comparison.atoms t := by
    simp only [Decomposition.word, rawTree_code]
  cases hw : (Comparison.atoms t).reverse with
  | nil =>
    have hz := OrderSupport.transform_low_value q b ha Normalization.zeroTree
      (Normalization.zeroTree_checked q (source_checked q b ha))
      (zero_restricted q b) (Nat.zero_le 1)
    simpa only [LogEndZero.endAtom, hword, hw, List.map_nil,
      List.getElem?_nil, Option.getD_none, Normalization.zeroTree_denote] using hz.symm
  | cons x xs =>
    simp only [LogEndZero.endAtom, hword, hw, List.map_cons,
      List.getElem?_cons_zero, Option.getD_some]

theorem unit_restricted (q b : Nat) : Restricted q b (rawTree LogEndZero.unitCode) := by
  intro x hx
  simp only [LogEndZero.unitCode, rawTree_code, Restricted, Iota.fullList,
    RelativeTerm.PrincipalSupport.principalList, List.not_mem_nil] at hx

/-- Genuine equality reflection at the original LOW unit supplies the
exact mapped unit test, without an assumed indicator invariance. -/
theorem transform_unit_iff (q b : Nat) (ha : rootCheck q b = true)
    (t : RelativeTerm Nat) (ht : check q t = true) (hn : Comparison.Normal q t)
    (hr : Restricted q b t) :
    denote (betaCode q b) (transform q b t) = 1 ↔ denote q t = 1 := by
  have hu := Decomposition.input_tree q LogEndZero.unitCode
    (LogEndZero.unitCode_accepted q (source_checked q b ha))
  have huv : denote q (rawTree LogEndZero.unitCode) = 1 := by
    rw [← Decomposition.input_value q LogEndZero.unitCode
      (LogEndZero.unitCode_accepted q (source_checked q b ha))]
    exact LogEndZero.unitCode_value q
  have hφu : denote (betaCode q b) (transform q b (rawTree LogEndZero.unitCode)) = 1 :=
    (OrderSupport.transform_low_value q b ha _ hu.1 (unit_restricted q b) (by
      simp only [LogEndZero.unitCode, rawTree_code, outerSort]
      omega)).trans huv
  simpa only [hφu, huv] using transform_eq_iff q b ha t (rawTree LogEndZero.unitCode)
    ht hu.1 hn hu.2 hr (unit_restricted q b)

/-- The exact mathematical zero-last-exponent class is preserved by the
actual restricted iota, at every originally admitted Normal cardinal sort. -/
theorem sourceZero_transform (q b : Nat) (ha : rootCheck q b = true)
    (t : RelativeTerm Nat) (ht : check q t = true) (hn : Comparison.Normal q t)
    (hr : Restricted q b t) :
    Hereditary.LogEndZero.SourceZero (denote (betaCode q b) (transform q b t)) ↔
      Hereditary.LogEndZero.SourceZero (denote q t) := by
  have hi := ReturnedIota.original_accepted q t ht hn
  have he := LogEndZero.endAtom_checked q t.code hi
  rw [Hereditary.LogEndZero.SourceZero, Hereditary.LogEndZero.SourceZero,
    transform_zero_iff q b ha t ht hn hr, endValue_transform q b ha t ht hn hr,
    transform_unit_iff q b ha _ he.1 he.2 (endAtom_restricted q b t hr),
    LogEndZero.endAtom_value q t.code hi, interpretation_code]

/-- The actual executing zero-last-exponent flag, including every admitted
zero fallback and unit-last principal word, follows from original admission. -/
theorem logEndZero_transform (q b : Nat) (ha : rootCheck q b = true)
    (t : RelativeTerm Nat) (ht : check q t = true) (hn : Comparison.Normal q t)
    (hr : Restricted q b t) :
    LogEndZero.zeroCheck (betaCode q b) (transform q b t).code = LogEndZero.zeroCheck q t.code := by
  have hi := ReturnedIota.original_accepted q t ht hn
  have hφi := ReturnedIota.original_accepted (betaCode q b) (transform q b t)
    (transform_checked q b ha t ht hr) (transform_normal q b ha t ht hn hr)
  apply Bool.eq_iff_iff.mpr
  rw [LogEndZero.zeroCheck_correct (betaCode q b) (transform q b t).code hφi,
    LogEndZero.zeroCheck_correct q t.code hi]
  simpa only [interpretation_code] using sourceZero_transform q b ha t ht hn hr

/-- Actual low parts and their constructed mapped representatives supply
the executing shifted high-choice flag from only the original theta caller. -/
theorem chooseHigh_theta_argument_transform (q b m : Nat) (ha : rootCheck q b = true)
    (t : RelativeTerm Nat) (htheta : check q (.theta (m + 1) t) = true)
    (hn : Comparison.Normal q t) (hr : Restricted q b t) :
    SourceChi.chooseHigh (betaCode q b) m (transform q b t).code =
      SourceChi.chooseHigh q (m + 1) t.code := by
  have ht := FixedPoint.checked_theta_argument q (m + 1) t htheta
  have hi := ReturnedIota.original_accepted q t ht hn
  have hφi := ReturnedIota.original_accepted (betaCode q b) (transform q b t)
    (transform_checked q b ha t ht hr) (transform_normal q b ha t ht hn hr)
  have hp := Decomposition.parts_checked q (m + 1) t.code hi
  have hnp := Decomposition.parts_normal q (m + 1) t.code hi
  have hrp := parts_restricted q b (m + 1) t hr
  have hsLow := (Decomposition.parts_accepted q (m + 1) t.code hi).2
  have htLow := (Decomposition.parts_accepted (betaCode q b) m (transform q b t).code hφi).2
  have hz : LogEndZero.zeroCheck (betaCode q b) (Decomposition.lowCode m (transform q b t).code) =
      LogEndZero.zeroCheck q (Decomposition.lowCode (m + 1) t.code) := by
    apply Bool.eq_iff_iff.mpr
    rw [LogEndZero.zeroCheck_correct (betaCode q b) _ htLow,
      LogEndZero.zeroCheck_correct q _ hsLow]
    simpa only [Decomposition.lowCode, interpretation_code,
      lowPart_transform_value q b m ha t ht hn hr] using
      sourceZero_transform q b ha (Decomposition.lowPartTerm (m + 1) t.code) hp.2 hnp.2 hrp.2
  simp only [SourceChi.chooseHigh, fixedCode_theta_argument_transform q b m ha t htheta hn hr, hz]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.LogEndZeroTransport
