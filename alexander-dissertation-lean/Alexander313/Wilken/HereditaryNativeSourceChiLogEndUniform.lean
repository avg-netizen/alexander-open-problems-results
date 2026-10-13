import Alexander313.Wilken.HereditaryNativeLogEnd

/-!
# Actual last-log indicator on every originally admitted LOW Normal code

The genuine final principal atom carries the original indicator. Its real
parameter or theta-zero shape supplies the log law, including the base
itself, whose indicator is true. No log/indicator oracle is supplied.
Source candidates only; not yet compiled or peer-reviewed.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceChi.LogEndUniform

open ThetaCourse

theorem rawTree_code_of_checked (q c : Nat) (hc : checkCode q c = true) :
    (rawTree c).code = c := by
  obtain ⟨t, he, ht⟩ := (checkCode_exact q c).mp hc
  simp only [← he, rawTree_code]

theorem chiCode_below (q c : Nat) (hc : Comparison.acceptedCode q c = true)
    (hl : interpretation q c < base q) : SourceChi.chiCode q c = false := by
  have hs := (Comparison.acceptedCode_exact q c).mp hc
  rw [← rawTree_code_of_checked q c hs.1,
    SourceChi.chiCode_correct q (rawTree c) (Arithmetic.raw_checked q c hs.1) hs.2]
  exact SourceChi.indicator_below_base q _ (Arithmetic.raw_checked q c hs.1) hs.2
    (by rw [Arithmetic.raw_value q c hs.1]; exact hl)

theorem chiCode_base (q c : Nat) (hc : Comparison.acceptedCode q c = true)
    (hl : interpretation q c = base q) : SourceChi.chiCode q c = true := by
  have hs := (Comparison.acceptedCode_exact q c).mp hc
  rw [← rawTree_code_of_checked q c hs.1,
    SourceChi.chiCode_correct q (rawTree c) (Arithmetic.raw_checked q c hs.1) hs.2]
  exact SourceChi.indicator_base q _ (Arithmetic.raw_checked q c hs.1) hs.2
    (by rw [Arithmetic.raw_value q c hs.1]; exact hl)

theorem chiCode_endCode (q c : Nat) (hc : Comparison.acceptedCode q c = true) :
    SourceChi.chiCode q (LogEndZero.endCode c) = SourceChi.chiCode q c := by
  have ht := Decomposition.input_tree q c hc
  have he := rawTree_code_of_checked q c ((Comparison.acceptedCode_exact q c).mp hc).1
  have hs := LogEndZero.endAtom_checked q c hc
  rw [LogEndZero.endCode, SourceChi.chiCode_correct q _ hs.1 hs.2]
  have hh := SourceChi.Powers.indicator_endAtom q (rawTree c) ht.1 ht.2
  rw [he] at hh
  rw [hh, ← SourceChi.chiCode_correct q _ ht.1 ht.2, he]

/-- The actual final logarithm preserves the actual source indicator on
EVERY originally admitted LOW Normal code, including zero and the base. -/
theorem chiCode_logend (q c ell : Nat) (hc : lowCheckCode q c = true)
    (hn : Comparison.acceptedCode q c = true) (hl : ell ∈ LogEnd.execute q c) :
    SourceChi.chiCode q ell = SourceChi.chiCode q c := by
  have hs := LogEnd.execute_spec q c ell hl
  have hq := (HeightBoundary.input_spec q c hc).2.1
  have hχell : SourceChi.inputCheck q ell = true :=
    (SourceChi.inputCheck_exact q ell).mpr ((Comparison.acceptedCode_exact q ell).mp hs.2.2.1)
  by_cases hz : interpretation q c = 0
  · have hel : interpretation q ell = 0 := by
      simpa only [Hereditary.LogEnd.SourceLogSpec, hz, if_pos rfl] using hs.2.2.2
    rw [chiCode_below q ell hs.2.2.1 (by rw [hel]; exact base_pos q hq),
      chiCode_below q c hn (by rw [hz]; exact base_pos q hq)]
  · have he := LogEnd.Support.endCode_spec q c hc hn hz
    have hpow : Ordinal.omega0 ^ interpretation q ell =
        interpretation q (LogEndZero.endCode c) := by
      rw [LogEndZero.endCode_value q c hn]
      simpa only [Hereditary.LogEnd.SourceLogSpec, if_neg hz,
        Hereditary.LogEnd.endValue] using hs.2.2.2
    have hecheck := ((Comparison.acceptedCode_exact q _).mp he.2.1).1
    have heraw := rawTree_code_of_checked q (LogEndZero.endCode c) hecheck
    have hat := Decomposition.input_tree q (LogEndZero.endCode c) he.2.1
    rcases he.2.2.2.2.2 with ⟨p, hp⟩ | ⟨k, a, ha⟩
    · have hv : interpretation q (LogEndZero.endCode c) < base q := by
        rw [← Arithmetic.raw_value q _ hecheck, hp]
        exact FixedPoint.checked_parameter_lt_base q p (by simpa only [hp] using hat.1)
      rw [chiCode_below q ell hs.2.2.1
          (((omegaPower_self_le _).trans_eq hpow).trans_lt hv),
        ← chiCode_endCode q c hn, chiCode_below q _ he.2.1 hv]
    · have hcode : LogEndZero.endCode c = (.theta k a : RelativeTerm Nat).code := by
        rw [← heraw, ha]
      have hk : k = 0 := LogEnd.Support.theta_low_index q k a
        (by simpa only [hcode] using he.1)
      subst k
      have hcheck : check q (.theta 0 a) = true := by simpa only [ha] using hat.1
      have hnormal : Comparison.Normal q (.theta 0 a) := by simpa only [ha] using hat.2
      have hv : interpretation q (LogEndZero.endCode c) = denote q (.theta 0 a) := by
        rw [hcode, interpretation_code]
      by_cases hproper : base q < denote q (.theta 0 a)
      · have hlogs : Hereditary.LogEnd.SourceLogSpec true
            (denote q (.theta 0 a)) (interpretation q ell) := by
          have hp := SourceChi.Powers.theta_principal q a hcheck
          simp only [Hereditary.LogEnd.SourceLogSpec, if_neg (ne_of_gt hp.1)]
          exact (hpow.trans hv).trans
            (SourceChi.Powers.endValue_principal _ hp.1 hp.2).symm
        exact (SourceChi.Powers.chi_logend q ell a hcheck hnormal hproper hχell hlogs).trans
          (by rw [← hcode]; exact chiCode_endCode q c hn)
      · have hbase : denote q (.theta 0 a) = base q := by
          apply le_antisymm (le_of_not_gt hproper)
          simpa only [omegaSequence_zero] using (FixedPoint.checked_theta_range q 0 a hcheck).1
        have hell : interpretation q ell = base q :=
          omegaPower_strictMono.injective
            ((hpow.trans (hv.trans hbase)).trans (SourceChi.epsilon_base q hq).symm)
        rw [chiCode_base q ell hs.2.2.1 hell, ← chiCode_endCode q c hn,
          chiCode_base q _ he.2.1 (hv.trans hbase)]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceChi.LogEndUniform
