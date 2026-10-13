import Alexander313.Wilken.HereditaryNativeSourceRhoHeightSupport

/-!
# Actual all-index endpoint closure and native finite tails

The height-zero endpoint is the actual coded epsilon base, so omega powers
and addition stay below every height endpoint, including zero. The genuine
native addition producer is normal; semantic endpoint closure proves its
canonical height bound on original low inputs. Every finite numeral is an
original admitted parameter of height zero at ANY coded epsilon base. Its
addition to the original input therefore preserves canonical value height.
No endpoint, admission, height or finite-tail representation oracle is used.
Uncompiled source candidates outside the current checkpoint.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.OmegaPowerHeight

theorem endpoint_epsilon_all (q n : Nat) (hq : baseCheck q = true) :
    Ordinal.omega0 ^ HeightBoundary.endpoint q n = HeightBoundary.endpoint q n := by
  by_cases hn : n = 0
  · subst n
    rw [HeightBoundary.endpoint_zero q hq]
    exact SourceChi.epsilon_base q hq
  · exact HeightBoundary.endpoint_epsilon q n hq (Nat.pos_of_ne_zero hn)

theorem endpoint_add_closed_all (q n : Nat) (hq : baseCheck q = true) :
    Ordinal.IsPrincipal (· + ·) (HeightBoundary.endpoint q n) := by
  rw [← endpoint_epsilon_all q n hq]
  exact Ordinal.isPrincipal_add_omega0_opow _

private theorem low_of_endpoint_bound (q n c : Nat) (hq : baseCheck q = true)
    (hc : checkCode q c = true) (hb : interpretation q c < HeightBoundary.endpoint q n) :
    lowCheckCode q c = true := by
  obtain ⟨t, he, ht⟩ := (checkCode_exact q c).mp hc
  have hv : denote q t < omegaSequence (base q) 1 := by
    simpa only [← he, interpretation_code] using
      hb.trans (HeightBoundary.endpoint_lt_cardinal q n hq)
  have hs : t.outerSort ≤ 1 := (denote_lt_iff_outerSort_le q t ht 1 (by omega)).mp hv
  rw [← he, lowCheckCode_code]
  exact Bool.and_eq_true.mpr ⟨ht, by simpa only [decide_eq_true_eq] using hs⟩

/-- Actual addition on both original LOW inputs preserves the maximum
canonical input height, even for raw spellings and height zero. -/
theorem addCode_low_height (q c d : Nat) (hc : lowCheckCode q c = true)
    (hd : lowCheckCode q d = true) :
    lowCheckCode q (Arithmetic.addCode q c d) = true ∧
      heightCode (Arithmetic.addCode q c d) ≤
        max (CanonicalHeight.canonicalHeightCode q c) (CanonicalHeight.canonicalHeightCode q d) := by
  have hcs := HeightBoundary.input_spec q c hc
  have hds := HeightBoundary.input_spec q d hd
  have hs := Arithmetic.addCode_spec q c d hcs.1 hds.1
  let n := max (CanonicalHeight.canonicalHeightCode q c) (CanonicalHeight.canonicalHeightCode q d)
  have hcb := (HeightBoundary.canonicalHeightCode_le_iff_endpoint q n c hc).mp (le_max_left _ _)
  have hdb := (HeightBoundary.canonicalHeightCode_le_iff_endpoint q n d hd).mp (le_max_right _ _)
  have hb : interpretation q (Arithmetic.addCode q c d) < HeightBoundary.endpoint q n := by
    rw [hs.2.1]
    exact endpoint_add_closed_all q n hcs.2.1 hcb hdb
  have hlo := low_of_endpoint_bound q n _ hcs.2.1
    ((Comparison.acceptedCode_exact q _).mp hs.1).1 hb
  have hh := (HeightBoundary.canonicalHeightCode_le_iff_endpoint q n _ hlo).mpr hb
  rw [CanonicalHeight.canonicalHeightCode_normal q _ hs.1] at hh
  exact ⟨hlo, hh⟩

def numeralCode (n : Nat) : Nat :=
  (.parameter (CanonicalArithmetic.numeralCode n) : RelativeTerm Nat).code

theorem numeralCode_primrec : Primrec numeralCode :=
  code_primrec.comp (parameter_primrec.comp CanonicalArithmetic.numeralCode_primrec)

/-- A finite ordinal is genuinely an atomic height-zero parameter at
EVERY original coded epsilon, with its original public numeral payload. -/
theorem numeralCode_spec (q n : Nat) (hq : baseCheck q = true) :
    lowCheckCode q (numeralCode n) = true ∧ Comparison.acceptedCode q (numeralCode n) = true ∧
      interpretation q (numeralCode n) = (n : Ordinal.{0}) ∧
        CanonicalHeight.canonicalHeightCode q (numeralCode n) = 0 := by
  have hp : parameterCheck q (CanonicalArithmetic.numeralCode n) = true :=
    (parameterCheck_exact q _).mpr ⟨Canonical.check_original (CanonicalArithmetic.numeralCode_checked n),
      ((baseCheck_exact q).mp hq).1, by
        rw [parameters, CanonicalArithmetic.numeralCode_value]
        exact (Ordinal.natCast_lt_omega0 n).trans (epsilon_omega_lt (SourceChi.epsilon_base q hq))⟩
  have ha : admissible q 0 (.parameter (CanonicalArithmetic.numeralCode n)) :=
    ⟨hp, .parameter (by simpa only [omegaSequence_zero] using parameter_sound q _ hp)⟩
  have ht := Comparison.admitted_checked q 0 hq _ ha
  have hc : checkCode q (numeralCode n) = true := by
    simpa only [numeralCode, checkCode_code] using ht
  have hn : Comparison.Normal q (ThetaCourse.rawTree (numeralCode n)) := by
    simp only [numeralCode, ThetaCourse.rawTree_code, Comparison.Normal]
  have haccepted := (Comparison.acceptedCode_exact q _).mpr ⟨hc, hn⟩
  refine ⟨?_, haccepted, ?_, ?_⟩
  · simp only [numeralCode, lowCheckCode_code, lowCheck, ht, RelativeTerm.outerSort,
      Nat.zero_le, decide_true, Bool.true_and]
  · simp only [numeralCode, interpretation_code, denote, parameters,
      CanonicalArithmetic.numeralCode_value]
  · rw [CanonicalHeight.canonicalHeightCode_normal q _ haccepted]
    simp only [numeralCode, heightCode_code, RelativeTerm.height]

def finiteTailCode (q c n : Nat) : Nat := Arithmetic.addCode q c (numeralCode n)

theorem finiteTailCode_primrec : Primrec
    (fun p : (Nat × Nat) × Nat => finiteTailCode p.1.1 p.1.2 p.2) :=
  Arithmetic.addCode_primrec.comp ((Primrec.fst.comp Primrec.fst).pair
    ((Primrec.snd.comp Primrec.fst).pair (numeralCode_primrec.comp Primrec.snd)))

/-- The actual finite-tail addition has exactly its original value and
never increases canonical input height at ANY original coded epsilon. -/
theorem finiteTailCode_spec (q c n : Nat) (hc : lowCheckCode q c = true) :
    lowCheckCode q (finiteTailCode q c n) = true ∧
      Comparison.acceptedCode q (finiteTailCode q c n) = true ∧
      interpretation q (finiteTailCode q c n) = interpretation q c + (n : Ordinal.{0}) ∧
      heightCode (finiteTailCode q c n) ≤ CanonicalHeight.canonicalHeightCode q c := by
  have hi := HeightBoundary.input_spec q c hc
  have hn := numeralCode_spec q n hi.2.1
  have hs := Arithmetic.addCode_spec q c _ hi.1 ((Comparison.acceptedCode_exact q _).mp hn.2.1).1
  have hh := addCode_low_height q c _ hc hn.1
  refine ⟨hh.1, hs.1, ?_, ?_⟩
  · simpa only [finiteTailCode, hn.2.2.1] using hs.2.1
  · simpa only [finiteTailCode, hn.2.2.2, max_zero] using hh.2

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.OmegaPowerHeight
