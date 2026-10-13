import Alexander313.Wilken.PublicEpsilonNativeContextTranslationSupport
import Alexander313.Wilken.PublicEpsilonNativeTrackingSequences

/-!
# Original raw principal callers for genuine localization

The actual SAME-q normalizer/final-atom producer constructs a genuine
admitted Normal theta-zero Node of the SAME value for EVERY original
RAW LOW additive principal at least as large as its admitted epsilon base.
The parameter branch is excluded by actual parameter admission, and LOW
admission excludes positive theta indices. No epsilon or HIGH premise is
needed for the full final-node domain. HIGH is derived separately on the
strict epsilon subcase. No root, representation, normalization or value
oracle is supplied. Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceLocalization.RootAdapter

open ThetaCourse

abbrev rootCode := ContextTranslation.Support.rootAtomCode

theorem rootCode_primrec : Primrec₂ rootCode :=
  ContextTranslation.Support.rootAtomCode_primrec

def inputCheck (q c : Nat) : Bool := SourceTrackingSequences.atLeastBaseCheck q c &&
  SourceTrackingSequences.Support.principalCheck q c

theorem inputCheck_primrec : Primrec₂ inputCheck :=
  (Primrec.and.comp SourceTrackingSequences.atLeastBaseCheck_primrec
    SourceTrackingSequences.Support.principalCheck_primrec).to₂

/-- Exact full original RAW LOW positive-principal domain for source3.19.
Positivity follows from the admitted epsilon base and is not a new guard. -/
theorem inputCheck_exact (q c : Nat) : inputCheck q c = true ↔
    lowCheckCode q c = true ∧ base q ≤ interpretation q c ∧
      Ordinal.IsPrincipal (· + ·) (interpretation q c) := by
  constructor
  · intro hi
    obtain ⟨hb, hp⟩ := Bool.and_eq_true.mp hi
    have hs := (SourceTrackingSequences.atLeastBaseCheck_exact q c).mp hb
    have ht := (SourceTrackingSequences.Support.principalCheck_exact q c).mp hp
    exact ⟨hs.1, hs.2, ht.2.2⟩
  · rintro ⟨hl, hb, hp⟩
    have hq := (HeightBoundary.input_spec q c hl).2.1
    exact Bool.and_eq_true.mpr
      ⟨(SourceTrackingSequences.atLeastBaseCheck_exact q c).mpr ⟨hl, hb⟩,
        (SourceTrackingSequences.Support.principalCheck_exact q c).mpr
          ⟨hl, (base_pos q hq).trans_le hb, hp⟩⟩

/-- The actual final-atom parser returns an ORIGINAL Normal theta-zero
Node of the SAME value on the entire raw principal domain, including
base values and non-epsilon final principals. -/
theorem rootCode_spec (q c : Nat) (hi : inputCheck q c = true) :
    Node q (rootCode q c) ∧ interpretation q (rootCode q c) = interpretation q c := by
  have hc := (inputCheck_exact q c).mp hi
  have hcheck := (Bool.and_eq_true.mp hc.1).1
  have hq := (HeightBoundary.input_spec q c hc.1).2.1
  have hpos : 0 < interpretation q c := (base_pos q hq).trans_le hc.2.1
  have hn := Normalization.normalizeCode_accepted q c hcheck
  have hnc := (Comparison.acceptedCode_exact q _).mp hn.1
  have hlow : lowCheckCode q (Normalization.normalizeCode q c) = true :=
    OmegaPowers.low_of_bound q _ hnc.1 (by
      rw [hn.2]
      exact (HeightBoundary.input_spec q c hc.1).2.2)
  have hpnc : 0 < interpretation q (Normalization.normalizeCode q c) := by
    rw [hn.2]
    exact hpos
  have hs := LogEnd.Support.endCode_spec q (Normalization.normalizeCode q c)
    hlow hn.1 (ne_of_gt hpnc)
  have hv : interpretation q (rootCode q c) = interpretation q c := by
    rw [rootCode, ContextTranslation.Support.rootAtomCode,
      LogEndZero.endCode_value q _ hn.1, hn.2,
      SourceChi.Powers.endValue_principal _ hpos hc.2.2]
  have ha := (Comparison.acceptedCode_exact q _).mp hs.2.1
  have hraw := Arithmetic.raw_checked q _ ha.1
  have hcode : (rawTree (rootCode q c)).code = rootCode q c := by
    obtain ⟨t, he, ht⟩ := (checkCode_exact q _).mp ha.1
    simpa only [← he, rawTree_code] using (rfl : t.code = t.code)
  rcases hs.2.2.2.2.2 with ⟨p, hshape⟩ | ⟨k, a, hshape⟩
  · have ht : check q (.parameter p) = true := by simpa only [hshape] using hraw
    have hb := (checked_parameters q (.parameter p) ht p
      (by simp only [RelativeTerm.parameters, List.mem_singleton])).2
    have heval : interpretation q (rootCode q c) = parameters p := by
      rw [← Arithmetic.raw_value q _ ha.1, hshape]
      rfl
    have hlt : interpretation q c < base q := by rw [← hv, heval]; exact hb
    exact False.elim (hc.2.1.not_gt hlt)
  · have hrootcode : rootCode q c = (.theta k a : RelativeTerm Nat).code :=
      hcode.symm.trans (congrArg RelativeTerm.code hshape)
    have hk : k = 0 := LogEnd.Support.theta_low_index q k a (by
      rw [← hrootcode]
      exact hs.1)
    subst k
    have ht : check q (.theta 0 a) = true := by simpa only [hshape] using hraw
    have hna : Comparison.Normal q a := by
      simpa only [hshape, Comparison.Normal] using ha.2
    exact ⟨⟨a, hrootcode, ht, hna⟩, hv⟩

/-- The actual ordinary-localization input guard is derived from the full
original raw principal caller, not supplied as a representation premise. -/
theorem rootInput (q c : Nat) (hi : inputCheck q c = true) :
    SourceLocalization.inputCheck q (rootCode q c) = true :=
  (SourceLocalization.inputCheck_exact q _).mpr (rootCode_spec q c hi).1

/-- The genuinely computed localization ends at the ORIGINAL raw value;
its selected Normal root spelling need not equal the original written code. -/
theorem localization_endpoint_value (q c : Nat) (hi : inputCheck q c = true) :
    value q (endpoint (nativePath q (rootCode q c))) = interpretation q c :=
  (nativePath_end q (rootCode q c) (rootInput q c hi)).trans (rootCode_spec q c hi).2

/-- The separate strict epsilon subcase derives the genuine HIGH mu caller
of the same actual parser; the full final-node domain needs no such premise. -/
theorem rootCode_high (q c : Nat) (hi : inputCheck q c = true)
    (hp : base q < interpretation q c)
    (he : Ordinal.omega0 ^ interpretation q c = interpretation q c) :
    RootLowCollapse.rootCheck q (rootCode q c) = true :=
  (ContextTranslation.Support.rootAtomCode_spec q c
    ((inputCheck_exact q c).mp hi).1 hp he).1

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceLocalization.RootAdapter
