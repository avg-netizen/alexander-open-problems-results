import Alexander313.Wilken.SourceOneOmegaQuotient
import Alexander313.Wilken.HereditaryNativeOmegaPowers

/-!
# Actual Definition 3.6 execution at the original source base one

The original base-one high root derives the complete actual Omega-one
quotient, genuine iota coefficient, source chi, finite-tail and arbitrary
coded-alpha power callers. The resulting numerical operation is primitive
recursive and its partial execution has exactly the original source guard.
The raw wrapper computes the original normalizer and accepts precisely
original admitted epsilon theta-zero roots. No positive-source dictionary,
quotient/admission/indicator/arithmetic oracle or recoding premise. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.Mu

abbrev inputCheck := SourceOneIota.rootCheck

theorem inputCheck_primrec : Primrec inputCheck := rootCheck_primrec

theorem inputCheck_exact (a : Nat) : inputCheck a = true ↔
    ∃ t : RelativeTerm Nat, a = (.theta 0 t).code ∧ check 0 (.theta 0 t) = true ∧
      Theta.Normal 0 (.theta 0 t) ∧ 1 < t.outerSort := rootCheck_exact a

def mappedCoefficient (a : Nat) : Nat := literalCode a (OmegaQuotient.coefficientCode a)

theorem mappedCoefficient_primrec : Primrec mappedCoefficient :=
  literalCode_primrec.comp Primrec.id OmegaQuotient.coefficientCode_primrec

theorem mappedCoefficient_spec (a : Nat) (ha : inputCheck a = true) :
    NativeContext.lowCheckCode (alphaCode a) (mappedCoefficient a) = true ∧
      NativeContext.Comparison.acceptedCode (alphaCode a) (mappedCoefficient a) = true :=
  OmegaQuotient.coefficient_iota_low a ha

def chi (a : Nat) : Bool := NativeContext.SourceChi.chiCode (alphaCode a) (mappedCoefficient a)

theorem chi_primrec : Primrec chi := NativeContext.SourceChi.chiCode_primrec.comp alphaCode_primrec mappedCoefficient_primrec

theorem chi_correct (a : Nat) (ha : inputCheck a = true) :
    chi a = NativeContext.SourceChi.indicator (alphaCode a) (ThetaCourse.rawTree (mappedCoefficient a)) := by
  have hs := (NativeContext.Comparison.acceptedCode_exact _ _).mp (mappedCoefficient_spec a ha).2
  have hc : (ThetaCourse.rawTree (mappedCoefficient a)).code = mappedCoefficient a := by
    obtain ⟨t, he, ht⟩ := (NativeContext.checkCode_exact _ _).mp hs.1
    simp only [← he, ThetaCourse.rawTree_code]
  simpa only [chi, hc] using NativeContext.SourceChi.chiCode_correct (alphaCode a)
    (ThetaCourse.rawTree (mappedCoefficient a)) (NativeContext.Arithmetic.raw_checked _ _ hs.1) hs.2

def tail (a : Nat) : Nat := cond (chi a) 1 0 + OmegaQuotient.coefficientOffset a

theorem tail_primrec : Primrec tail :=
  Primrec.nat_add.comp (chi_primrec.cond (Primrec.const 1) (Primrec.const 0)) OmegaQuotient.coefficientOffset_primrec

def exponentCode (a : Nat) : Nat :=
  NativeContext.OmegaPowerHeight.finiteTailCode (alphaCode a) (mappedCoefficient a) (tail a)

theorem exponentCode_primrec : Primrec exponentCode :=
  NativeContext.OmegaPowerHeight.finiteTailCode_primrec.comp ((alphaCode_primrec.pair mappedCoefficient_primrec).pair tail_primrec)

theorem exponentCode_spec (a : Nat) (ha : inputCheck a = true) :
    NativeContext.lowCheckCode (alphaCode a) (exponentCode a) = true ∧
      NativeContext.Comparison.acceptedCode (alphaCode a) (exponentCode a) = true ∧
      NativeContext.interpretation (alphaCode a) (exponentCode a) =
        NativeContext.interpretation (alphaCode a) (mappedCoefficient a) +
          cond (chi a) (1 : Ordinal.{0}) 0 + (OmegaQuotient.coefficientOffset a : Ordinal.{0}) := by
  have hs := NativeContext.OmegaPowerHeight.finiteTailCode_spec (alphaCode a) (mappedCoefficient a) (tail a)
    (mappedCoefficient_spec a ha).1
  refine ⟨hs.1, hs.2.1, ?_⟩
  rw [hs.2.2.1, tail, Nat.cast_add, add_assoc]
  cases h : chi a <;> simp only [h, Bool.cond_true, Bool.cond_false, Nat.cast_zero, Nat.cast_one]

noncomputable def sourceValue (a : Nat) : Ordinal.{0} := Ordinal.omega0 ^
  (NativeContext.interpretation (alphaCode a) (mappedCoefficient a) +
    cond (NativeContext.SourceChi.indicator (alphaCode a) (ThetaCourse.rawTree (mappedCoefficient a))) 1 0 +
      (OmegaQuotient.coefficientOffset a : Ordinal.{0}))

def muCode (a : Nat) : Nat := cond (inputCheck a)
  (NativeContext.OmegaPowers.powerCode (alphaCode a) (exponentCode a)) 0

theorem muCode_primrec : Primrec muCode := inputCheck_primrec.cond
  (NativeContext.OmegaPowers.powerCode_primrec.comp alphaCode_primrec exponentCode_primrec) (Primrec.const 0)

theorem muCode_literal (a : Nat) (ha : inputCheck a = true) :
    muCode a = NativeContext.OmegaPowers.powerCode (alphaCode a) (exponentCode a) := by
  simp only [muCode, ha, Bool.cond_true]

theorem muCode_rejected (a : Nat) (ha : inputCheck a = false) : muCode a = 0 := by
  simp only [muCode, ha, Bool.cond_false]

theorem muCode_spec (a : Nat) (ha : inputCheck a = true) :
    NativeContext.lowCheckCode (alphaCode a) (muCode a) = true ∧
      NativeContext.Comparison.acceptedCode (alphaCode a) (muCode a) = true ∧
      NativeContext.interpretation (alphaCode a) (muCode a) = sourceValue a := by
  have hs := NativeContext.OmegaPowers.powerCode_spec (alphaCode a) (exponentCode a) (exponentCode_spec a ha).1
  rw [muCode_literal a ha]
  refine ⟨hs.1, hs.2.1, ?_⟩
  rw [hs.2.2, (exponentCode_spec a ha).2.2, sourceValue, chi_correct a ha]

theorem definition_3_6_spec (a : Nat) (ha : inputCheck a = true) :
    (interpretation 0 (OmegaQuotient.coefficientCode a) = 0 ∨
      IsSuccLimit (interpretation 0 (OmegaQuotient.coefficientCode a))) ∧
      omegaSequence (finiteBase 0) 1 *
        (interpretation 0 (OmegaQuotient.coefficientCode a) + (OmegaQuotient.coefficientOffset a : Ordinal.{0})) =
        interpretation 0 (OmegaQuotient.deltaCode a) ∧
      SourceOneIota.inputCheck a (OmegaQuotient.coefficientCode a) = true ∧
      NativeContext.lowCheckCode (alphaCode a) (muCode a) = true ∧
      NativeContext.Comparison.acceptedCode (alphaCode a) (muCode a) = true ∧
      NativeContext.interpretation (alphaCode a) (muCode a) = sourceValue a := by
  have hc := OmegaQuotient.coefficientCode_spec a ha
  exact ⟨hc.2.2.1, hc.2.2.2, hc.2.1, muCode_spec a ha⟩

theorem muCode_height_mappedCoefficient (a : Nat) (ha : inputCheck a = true) :
    heightCode (muCode a) ≤ NativeContext.CanonicalHeight.canonicalHeightCode (alphaCode a) (mappedCoefficient a) := by
  have he := NativeContext.OmegaPowerHeight.finiteTailCode_spec (alphaCode a) (mappedCoefficient a) (tail a)
    (mappedCoefficient_spec a ha).1
  have hp := NativeContext.OmegaPowers.powerCode_height (alphaCode a) (exponentCode a) he.1
  rw [NativeContext.CanonicalHeight.canonicalHeightCode_normal _ _ he.2.1] at hp
  rw [muCode_literal a ha]
  exact hp.trans he.2.2.2

def execute (a : Nat) : Part Nat := cond (inputCheck a) (Part.some (muCode a)) Part.none

theorem execute_partrec : Partrec execute :=
  Partrec.cond inputCheck_primrec.to_comp muCode_primrec.to_comp.partrec Partrec.none

theorem execute_domain (a : Nat) : (execute a).Dom ↔ inputCheck a = true := by
  cases h : inputCheck a <;> simp [execute, h]

theorem execute_graph (a out : Nat) : out ∈ execute a ↔ inputCheck a = true ∧ out = muCode a := by
  cases h : inputCheck a <;> simp [execute, h]

theorem execute_spec (a out : Nat) (ho : out ∈ execute a) :
    inputCheck a = true ∧ NativeContext.lowCheckCode (alphaCode a) out = true ∧
      NativeContext.Comparison.acceptedCode (alphaCode a) out = true ∧
      NativeContext.interpretation (alphaCode a) out = sourceValue a := by
  obtain ⟨ha, rfl⟩ := (execute_graph a out).mp ho
  exact ⟨ha, muCode_spec a ha⟩

namespace Raw

def normalizedRoot (a : Nat) : Nat := Theta.Normalization.normalizeCode 0 a

theorem normalizedRoot_primrec : Primrec normalizedRoot :=
  Theta.Normalization.Effective.normalizeCode_primrec.comp (Primrec.const 0) Primrec.id

def inputCheck (a : Nat) : Bool := SourceZeta.rawInputCheck 0 a && Mu.inputCheck (normalizedRoot a)

theorem inputCheck_primrec : Primrec inputCheck :=
  Primrec.and.comp (SourceZeta.rawInputCheck_primrec.comp (Primrec.const 0) Primrec.id)
    (Mu.inputCheck_primrec.comp normalizedRoot_primrec)

/-- The actual normalizer supplies the original normal root. Its source-one
high branch is exactly epsilon, because the zero-argument epsilon exception
requires a strictly positive source level or theta index. -/
theorem inputCheck_exact (a : Nat) : inputCheck a = true ↔
    (∃ t : RelativeTerm Nat, a = (.theta 0 t).code ∧ check 0 (.theta 0 t) = true) ∧
      Ordinal.omega0 ^ interpretation 0 a = interpretation 0 a := by
  rw [inputCheck, Bool.and_eq_true]
  constructor
  · rintro ⟨ha, hn⟩
    have hc := (Bool.and_eq_true.mp ha).1
    have hv := (Theta.Normalization.normalizeCode_checked 0 a hc).2.2
    exact ⟨(SourceZeta.rawInputCheck_exact 0 a).mp ha,
      by simpa only [normalizedRoot, hv] using root_epsilon _ hn⟩
  · rintro ⟨ha, he⟩
    have hr := (SourceZeta.rawInputCheck_exact 0 a).mpr ha
    have hi := SourceZeta.raw_normalized_input 0 a hr
    obtain ⟨t, ht, hc, hn⟩ := (SourceZeta.inputCheck_exact 0 (normalizedRoot a)).mp hi
    have hv := (Theta.Normalization.normalizeCode_checked 0 a (Bool.and_eq_true.mp hr).1).2.2
    have he' : Ordinal.omega0 ^ denote 0 (.theta 0 t) = denote 0 (.theta 0 t) := by
      simpa only [← ht, ← interpretation_code, normalizedRoot, hv] using he
    have hh : 1 < t.outerSort := by
      simpa only [Nat.zero_add, lt_self_iff_false, or_self, and_false, or_false] using
        (Epsilon.theta_epsilon_iff 0 0 t hc).mp he'
    exact ⟨hr, (rootCheck_exact _).mpr ⟨t, ht, hc, hn, hh⟩⟩

theorem inputCheck_proper (a : Nat) (ha : inputCheck a = true) : 1 < interpretation 0 a :=
  EpsilonOffsets.epsilon_one_lt ((inputCheck_exact a).mp ha).2

def outputContext (a : Nat) : Nat := alphaCode (normalizedRoot a)

theorem outputContext_primrec : Primrec outputContext := alphaCode_primrec.comp normalizedRoot_primrec

theorem outputContext_value (a : Nat) (ha : inputCheck a = true) :
    NativeContext.base (outputContext a) = interpretation 0 a := by
  have hs := Bool.and_eq_true.mp ha
  have hc := (Bool.and_eq_true.mp hs.1).1
  rw [outputContext, OrderSupport.alpha_base _ hs.2]
  exact (Theta.Normalization.normalizeCode_checked 0 a hc).2.2

def muCode (a : Nat) : Nat := cond (inputCheck a) (Mu.muCode (normalizedRoot a)) 0

theorem muCode_primrec : Primrec muCode :=
  inputCheck_primrec.cond (Mu.muCode_primrec.comp normalizedRoot_primrec) (Primrec.const 0)

def execute (a : Nat) : Part Nat := cond (inputCheck a) (Part.some (muCode a)) Part.none

theorem execute_partrec : Partrec execute :=
  Partrec.cond inputCheck_primrec.to_comp muCode_primrec.to_comp.partrec Partrec.none

theorem execute_domain (a : Nat) : (execute a).Dom ↔ inputCheck a = true := by
  cases h : inputCheck a <;> simp [execute, h]

theorem execute_graph (a out : Nat) : out ∈ execute a ↔ inputCheck a = true ∧ out = muCode a := by
  cases h : inputCheck a <;> simp [execute, h]

theorem execute_spec (a out : Nat) (ho : out ∈ execute a) :
    inputCheck a = true ∧ NativeContext.lowCheckCode (outputContext a) out = true ∧
      NativeContext.Comparison.acceptedCode (outputContext a) out = true ∧
      NativeContext.interpretation (outputContext a) out = Mu.sourceValue (normalizedRoot a) := by
  obtain ⟨ha, rfl⟩ := (execute_graph a out).mp ho
  have hs := Mu.muCode_spec _ (Bool.and_eq_true.mp ha).2
  exact ⟨ha, by simpa only [muCode, ha, Bool.cond_true, outputContext] using hs⟩

end Raw
end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.Mu
