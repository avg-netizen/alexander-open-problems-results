import Alexander313.Wilken.PublicEpsilonNativeUnboundedMu
import Alexander313.Wilken.PublicEpsilonNativeUnboundedReturnedIota
import Alexander313.Wilken.PublicEpsilonNativeUnboundedIotaShiftedIndicator

/-!
# Genuine original-source coefficient and mu exponent

The actual returned-source iota producer carries the original coefficient
provenance. Its genuine lowered sort supplies a LOW original-source code;
its value equals the actual mapped coefficient at the new beta base.
The shifted original finite indicator computes that actual NEW-base chi,
and original-source finite-tail addition executes the precise mu exponent.
Every admission, Normality, LOW and value caller is derived from the
original ANY-q high root, including the zero coefficient. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.MuSource

open ThetaCourse

abbrev inputCheck := PublicEpsilonUnboundedIota.rootCheck

theorem inputCheck_primrec : Primrec (fun p : Context => inputCheck p.1 p.2) :=
  PublicEpsilonUnboundedIota.rootCheck_primrec

def returnedCoefficient (q root : Nat) : Nat :=
  NativeContext.ReturnedIota.sourceTermCode q root (OmegaQuotient.coefficientCode q root)

theorem returnedCoefficient_primrec : Primrec (fun p : Context => returnedCoefficient p.1 p.2) :=
  NativeContext.ReturnedIota.sourceTermCode_primrec.comp Primrec.id
    OmegaQuotient.coefficientCode_primrec

theorem returnedCoefficient_spec (q root : Nat) (ha : inputCheck q root = true) :
    Comparison.acceptedCode q (returnedCoefficient q root) = true ∧
      interpretation q (returnedCoefficient q root) =
        interpretation (betaCode q root) (Mu.mappedCoefficient q root) := by
  simpa only [returnedCoefficient, Mu.mappedCoefficient] using
    ReturnedSource.sourceTermCode_spec q root _ (OmegaQuotient.coefficient_iota_input q root ha)

/-- The genuine source coefficient is below Omega-two, so the actual
returned producer's lowered sort derives LOW output, with no output guard. -/
theorem returnedCoefficient_low (q root : Nat) (ha : inputCheck q root = true) :
    lowCheckCode q (returnedCoefficient q root) = true := by
  have hc := OmegaQuotient.coefficientCode_accepted q root ha
  have hs := NativeContext.ReturnedIota.sourceTermCode_admitted q root _ ha hc
  have hi := ((Comparison.acceptedCode_exact q _).mp hc).1
  have ht := Arithmetic.raw_checked q _ hi
  have hsort : (rawTree (OmegaQuotient.coefficientCode q root)).outerSort ≤ 2 :=
    (denote_lt_iff_outerSort_le q _ ht 2 (by omega)).mp
      (by rw [Arithmetic.raw_value q _ hi]; exact OmegaQuotient.coefficient_below_second q root ha)
  have hout : (rawTree (returnedCoefficient q root)).outerSort ≤ 1 := by
    exact hs.2.trans (by omega)
  have ho := ((Comparison.acceptedCode_exact q _).mp (returnedCoefficient_spec q root ha).1).1
  obtain ⟨t, he, ht⟩ := (checkCode_exact q _).mp ho
  have hts : t.outerSort ≤ 1 := by simpa only [← he, rawTree_code] using hout
  have hl : lowCheck q t = true := by
    simp only [lowCheck, ht, hts, decide_true, Bool.true_and]
  simpa only [← he, lowCheckCode_code] using hl

def relativeChi (q root : Nat) : Bool :=
  ShiftedIndicator.chiCode q root (OmegaQuotient.coefficientCode q root)

theorem relativeChi_primrec : Primrec (fun p : Context => relativeChi p.1 p.2) :=
  ShiftedIndicator.chiCode_primrec.comp
    (Primrec.fst.pair (Primrec.snd.pair OmegaQuotient.coefficientCode_primrec))

/-- The original finite shifted fold computes the actual indicator at
beta; it is never identified with the original-q indicator. -/
theorem relativeChi_eq (q root : Nat) (ha : inputCheck q root = true) :
    relativeChi q root = Mu.chi q root := by
  obtain ⟨hr, t, he, ht, hn, hs⟩ :=
    (PublicEpsilonUnboundedIota.inputCheck_exact q root _).mp
      (OmegaQuotient.coefficient_iota_input q root ha)
  have hrest := (restricted_iff_sourceStar q root hr t ht hn).mpr hs
  rw [relativeChi, he, ShiftedIndicator.chiCode_correct q root hr t ht hn hrest]
  rw [Mu.chi, Mu.mappedCoefficient, he,
    PublicEpsilonUnboundedIota.literalCode_code q root hr t ht hn hrest]

def tail (q root : Nat) : Nat :=
  cond (relativeChi q root) 1 0 + OmegaQuotient.coefficientOffset q root

theorem tail_primrec : Primrec (fun p : Context => tail p.1 p.2) :=
  Primrec.nat_add.comp
    (relativeChi_primrec.cond (Primrec.const 1) (Primrec.const 0))
    OmegaQuotient.coefficientOffset_primrec

theorem tail_eq (q root : Nat) (ha : inputCheck q root = true) :
    tail q root = Mu.tail q root := by
  rw [tail, Mu.tail, relativeChi_eq q root ha]

def exponentCode (q root : Nat) : Nat :=
  OmegaPowerHeight.finiteTailCode q (returnedCoefficient q root) (tail q root)

theorem exponentCode_primrec : Primrec (fun p : Context => exponentCode p.1 p.2) :=
  OmegaPowerHeight.finiteTailCode_primrec.comp
    ((Primrec.fst.pair returnedCoefficient_primrec).pair tail_primrec)

theorem exponentCode_spec (q root : Nat) (ha : inputCheck q root = true) :
    lowCheckCode q (exponentCode q root) = true ∧
      Comparison.acceptedCode q (exponentCode q root) = true ∧
      interpretation q (exponentCode q root) =
        interpretation (betaCode q root) (Mu.exponentCode q root) := by
  have hq := OmegaPowerHeight.finiteTailCode_spec q (returnedCoefficient q root)
    (tail q root) (returnedCoefficient_low q root ha)
  have hβ := OmegaPowerHeight.finiteTailCode_spec (betaCode q root)
    (Mu.mappedCoefficient q root) (Mu.tail q root) (Mu.mappedCoefficient_spec q root ha).1
  refine ⟨hq.1, hq.2.1, ?_⟩
  rw [exponentCode, Mu.exponentCode, hq.2.2.1, hβ.2.2.1,
    (returnedCoefficient_spec q root ha).2, tail_eq q root ha]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.MuSource
