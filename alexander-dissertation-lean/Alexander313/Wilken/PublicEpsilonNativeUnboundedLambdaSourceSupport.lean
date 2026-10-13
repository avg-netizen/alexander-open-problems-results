import Alexander313.Wilken.PublicEpsilonNativeUnboundedMappedOmegaQuotient
import Alexander313.Wilken.PublicEpsilonNativeUnboundedReturnedIota
import Alexander313.Wilken.HereditaryNativeDirectZeta
import Alexander313.Wilken.HereditaryNativeOmegaPowerHeightSupport

/-!
# Genuine original-source divided-head and zeta callers for high lambda

The ORIGINAL ANY-coded-epsilon checked Normal high root supplies its
actual divided high part, full original restriction and real iota caller.
The actual returned-iota producer lowers this part to a LOW Normal
original-source code with the genuine mapped value. Direct zeta executes
at the same original source. No delta admission/restriction, LOW return,
target payload cutoff or selected endpoint is supplied. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.LambdaSource

open ThetaCourse

abbrev inputCheck := PublicEpsilonUnboundedIota.rootCheck

theorem inputCheck_primrec : Primrec (fun p : Context => inputCheck p.1 p.2) :=
  PublicEpsilonUnboundedIota.rootCheck_primrec

abbrev deltaCode := OmegaQuotient.deltaCode

theorem deltaCode_primrec : Primrec deltaCode := OmegaQuotient.deltaCode_primrec

theorem zeta_input (q root : Nat) (ha : inputCheck q root = true) :
    DirectZeta.inputCheck q root = true := by
  obtain ⟨t, he, ht, hn, hh⟩ := (rootCheck_exact q root).mp ha
  exact (DirectZeta.inputCheck_exact q root).mpr ⟨t, he, ht, hn⟩

theorem delta_accepted (q root : Nat) (ha : inputCheck q root = true) :
    Comparison.acceptedCode q (deltaCode root) = true :=
  (Decomposition.parts_accepted q 0 _ (OmegaQuotient.Support.argument_accepted q root ha)).1

theorem delta_below_second (q root : Nat) (ha : inputCheck q root = true) :
    interpretation q (deltaCode root) < omegaSequence (base q) 2 :=
  ((Decomposition.parts_le q 0 _ (OmegaQuotient.Support.argument_accepted q root ha)).1).trans_lt
    (DirectZeta.argument_sorted q root (zeta_input q root ha))

/-- The actual full restriction of the root argument and retained high
word derives the genuine iota caller, with no support premise. -/
theorem delta_iota_caller (q root : Nat) (ha : inputCheck q root = true) :
    PublicEpsilonUnboundedIota.inputCheck q root (deltaCode root) = true :=
  MappedOmegaQuotient.delta_iota_input q root ha

def returnedDelta (q root : Nat) : Nat :=
  NativeContext.ReturnedIota.sourceTermCode q root (deltaCode root)

theorem returnedDelta_primrec : Primrec (fun p : Context => returnedDelta p.1 p.2) :=
  NativeContext.ReturnedIota.sourceTermCode_primrec.comp Primrec.id
    (deltaCode_primrec.comp Primrec.snd)

theorem returnedDelta_spec (q root : Nat) (ha : inputCheck q root = true) :
    Comparison.acceptedCode q (returnedDelta q root) = true ∧
      interpretation q (returnedDelta q root) =
        interpretation (betaCode q root) (literalCode q root (deltaCode root)) :=
  ReturnedSource.sourceTermCode_spec q root _ (delta_iota_caller q root ha)

/-- The genuine divided high part is below Omega-two. The actual
returned producer's lowered sort therefore derives original-source LOW. -/
theorem returnedDelta_low (q root : Nat) (ha : inputCheck q root = true) :
    lowCheckCode q (returnedDelta q root) = true := by
  have hc := delta_accepted q root ha
  have hs := NativeContext.ReturnedIota.sourceTermCode_admitted q root _ ha hc
  have hi := ((Comparison.acceptedCode_exact q _).mp hc).1
  have ht := Arithmetic.raw_checked q _ hi
  have hsort : (rawTree (deltaCode root)).outerSort ≤ 2 :=
    (denote_lt_iff_outerSort_le q _ ht 2 (by omega)).mp
      (by rw [Arithmetic.raw_value q _ hi]; exact delta_below_second q root ha)
  have hout : (rawTree (returnedDelta q root)).outerSort ≤ 1 := by
    exact hs.2.trans (by omega)
  have ho := ((Comparison.acceptedCode_exact q _).mp (returnedDelta_spec q root ha).1).1
  obtain ⟨t, he, ht⟩ := (checkCode_exact q _).mp ho
  have hts : t.outerSort ≤ 1 := by simpa only [← he, rawTree_code] using hout
  have hl : lowCheck q t = true := by
    simp only [lowCheck, ht, hts, decide_true, Bool.true_and]
  simpa only [← he, lowCheckCode_code] using hl

/-- The genuine target iota output is LOW Normal as well. Both its
admission and lowered sort follow from the original divided-head caller. -/
theorem mappedDelta_spec (q root : Nat) (ha : inputCheck q root = true) :
    lowCheckCode (betaCode q root) (literalCode q root (deltaCode root)) = true ∧
      Comparison.acceptedCode (betaCode q root) (literalCode q root (deltaCode root)) = true := by
  have hi := delta_iota_caller q root ha
  obtain ⟨hr, t, he, ht, hn, hs⟩ := (PublicEpsilonUnboundedIota.inputCheck_exact q root _).mp hi
  have hrest := (restricted_iff_sourceStar q root hr t ht hn).mpr hs
  have hsort : t.outerSort ≤ 2 :=
    (denote_lt_iff_outerSort_le q t ht 2 (by omega)).mp
      (by simpa only [he, interpretation_code] using delta_below_second q root ha)
  have hc := transform_checked q root ha t ht hrest
  have hout : (transform q root t).outerSort ≤ 1 := by
    have h := transform_outerSort q root ha t ht hrest
    omega
  refine ⟨?_, literalCode_accepted q root _ hi⟩
  rw [he, literalCode_code q root ha t ht hn hrest, lowCheckCode_code]
  simp only [lowCheck, hc, hout, decide_true, Bool.true_and]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.LambdaSource
