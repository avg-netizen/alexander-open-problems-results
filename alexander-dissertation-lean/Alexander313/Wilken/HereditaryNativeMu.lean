import Alexander313.Wilken.HereditaryNativeOmegaQuotient
import Alexander313.Wilken.HereditaryNativeOmegaPowers
import Alexander313.Wilken.HereditaryNativeLambdaRawBranches

/-!
# Actual finite execution of source Definition 3.6 mu

The original admitted normal high theta-zero root supplies its actual
Omega-one coefficient lambda and finite k. Its genuine iota image is LOW
and normal at the actual coded alpha. The original source indicator, native
finite-tail addition and native omega power execute the printed expression
in that same context. Every caller is derived from the original root guard.
The raw wrapper recognizes original proper epsilon theta-zero inputs and
constructs their actual normal root. No quotient, admission, translation,
indicator, arithmetic or execution oracle is a premise. Uncompiled drafts.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Mu

open NativePublicBridge (contextCode)

abbrev inputCheck := Iota.rootCheck

theorem inputCheck_primrec : Primrec₂ inputCheck := Iota.rootCheck_primrec

theorem inputCheck_exact (s a : Nat) : inputCheck s a = true ↔
    ∃ t : RelativeTerm Nat, a = (.theta 0 t).code ∧
      check (contextCode s) (.theta 0 t) = true ∧
        Comparison.Normal (contextCode s) t ∧ 1 < t.outerSort :=
  Iota.rootCheck_exact s a

def mappedCoefficient (s a : Nat) : Nat :=
  Iota.literalCode s a (OmegaQuotient.coefficientCode s a)

theorem mappedCoefficient_primrec : Primrec₂ mappedCoefficient :=
  (Iota.literalCode_primrec.comp (Primrec.id.pair OmegaQuotient.coefficientCode_primrec)).to₂

theorem mappedCoefficient_spec (s a : Nat) (ha : inputCheck s a = true) :
    lowCheckCode (Iota.alphaCode s a) (mappedCoefficient s a) = true ∧
      Comparison.acceptedCode (Iota.alphaCode s a) (mappedCoefficient s a) = true :=
  OmegaQuotient.coefficient_iota_low s a ha

def chi (s a : Nat) : Bool :=
  SourceChi.chiCode (Iota.alphaCode s a) (mappedCoefficient s a)

theorem chi_primrec : Primrec₂ chi :=
  (SourceChi.chiCode_primrec.comp Iota.alphaCode_primrec mappedCoefficient_primrec).to₂

theorem chi_correct (s a : Nat) (ha : inputCheck s a = true) :
    chi s a = SourceChi.indicator (Iota.alphaCode s a)
      (ThetaCourse.rawTree (mappedCoefficient s a)) := by
  have hs := (Comparison.acceptedCode_exact _ _).mp (mappedCoefficient_spec s a ha).2
  have hc : (ThetaCourse.rawTree (mappedCoefficient s a)).code = mappedCoefficient s a := by
    obtain ⟨t, he, ht⟩ := (checkCode_exact _ _).mp hs.1
    simp only [← he, ThetaCourse.rawTree_code]
  simpa only [chi, hc] using SourceChi.chiCode_correct (Iota.alphaCode s a)
    (ThetaCourse.rawTree (mappedCoefficient s a))
    (Arithmetic.raw_checked _ _ hs.1) hs.2

def tail (s a : Nat) : Nat := cond (chi s a) 1 0 + OmegaQuotient.coefficientOffset s a

theorem tail_primrec : Primrec₂ tail :=
  (Primrec.nat_add.comp (chi_primrec.cond (Primrec.const 1) (Primrec.const 0))
    OmegaQuotient.coefficientOffset_primrec).to₂

def exponentCode (s a : Nat) : Nat :=
  OmegaPowerHeight.finiteTailCode (Iota.alphaCode s a) (mappedCoefficient s a) (tail s a)

theorem exponentCode_primrec : Primrec₂ exponentCode :=
  (OmegaPowerHeight.finiteTailCode_primrec.comp
    ((Iota.alphaCode_primrec.pair mappedCoefficient_primrec).pair tail_primrec)).to₂

theorem exponentCode_spec (s a : Nat) (ha : inputCheck s a = true) :
    lowCheckCode (Iota.alphaCode s a) (exponentCode s a) = true ∧
      Comparison.acceptedCode (Iota.alphaCode s a) (exponentCode s a) = true ∧
      interpretation (Iota.alphaCode s a) (exponentCode s a) =
        interpretation (Iota.alphaCode s a) (mappedCoefficient s a) +
          (cond (chi s a) (1 : Ordinal.{0}) 0) +
            (OmegaQuotient.coefficientOffset s a : Ordinal.{0}) := by
  have hs := OmegaPowerHeight.finiteTailCode_spec (Iota.alphaCode s a)
    (mappedCoefficient s a) (tail s a) (mappedCoefficient_spec s a ha).1
  refine ⟨hs.1, hs.2.1, ?_⟩
  rw [hs.2.2.1, tail, Nat.cast_add, add_assoc]
  cases h : chi s a <;> simp only [h, Bool.cond_true, Bool.cond_false, Nat.cast_zero, Nat.cast_one]

/-- The mathematical value uses the genuine computed source chi on the
constructed iota coefficient, exactly as in Definition 3.6. -/
noncomputable def sourceValue (s a : Nat) : Ordinal.{0} := Ordinal.omega0 ^
  (interpretation (Iota.alphaCode s a) (mappedCoefficient s a) +
    cond (SourceChi.indicator (Iota.alphaCode s a)
      (ThetaCourse.rawTree (mappedCoefficient s a))) 1 0 +
        (OmegaQuotient.coefficientOffset s a : Ordinal.{0}))

def muCode (s a : Nat) : Nat := cond (inputCheck s a)
  (OmegaPowers.powerCode (Iota.alphaCode s a) (exponentCode s a)) 0

theorem muCode_primrec : Primrec₂ muCode :=
  (inputCheck_primrec.cond
    (OmegaPowers.powerCode_primrec.comp Iota.alphaCode_primrec exponentCode_primrec)
    (Primrec.const 0)).to₂

theorem muCode_literal (s a : Nat) (ha : inputCheck s a = true) :
    muCode s a = OmegaPowers.powerCode (Iota.alphaCode s a) (exponentCode s a) := by
  simp only [muCode, ha, Bool.cond_true]

theorem muCode_rejected (s a : Nat) (ha : inputCheck s a = false) : muCode s a = 0 := by
  simp only [muCode, ha, Bool.cond_false]

/-- The full original high-root guard alone constructs the literal mu
output, with actual LOW admission, Normality, and printed source value. -/
theorem muCode_spec (s a : Nat) (ha : inputCheck s a = true) :
    lowCheckCode (Iota.alphaCode s a) (muCode s a) = true ∧
      Comparison.acceptedCode (Iota.alphaCode s a) (muCode s a) = true ∧
        interpretation (Iota.alphaCode s a) (muCode s a) = sourceValue s a := by
  have hs := OmegaPowers.powerCode_spec (Iota.alphaCode s a) (exponentCode s a)
    (exponentCode_spec s a ha).1
  rw [muCode_literal s a ha]
  refine ⟨hs.1, hs.2.1, ?_⟩
  rw [hs.2.2, (exponentCode_spec s a ha).2.2, sourceValue, chi_correct s a ha]

/-- Every printed coefficient condition and actual mu output follows from
the ORIGINAL native normal high-root guard, including lambda equal to zero.
This is the positive finite-epsilon source context, not the source base one. -/
theorem definition_3_6_spec (s a : Nat) (ha : inputCheck s a = true) :
    (interpretation (contextCode s) (OmegaQuotient.coefficientCode s a) = 0 ∨
      IsSuccLimit (interpretation (contextCode s) (OmegaQuotient.coefficientCode s a))) ∧
      omegaSequence (base (contextCode s)) 1 *
        (interpretation (contextCode s) (OmegaQuotient.coefficientCode s a) +
          (OmegaQuotient.coefficientOffset s a : Ordinal.{0})) =
        interpretation (contextCode s) (Lambda.deltaCode a) ∧
      Iota.inputCheck s a (OmegaQuotient.coefficientCode s a) = true ∧
      lowCheckCode (Iota.alphaCode s a) (muCode s a) = true ∧
      Comparison.acceptedCode (Iota.alphaCode s a) (muCode s a) = true ∧
        interpretation (Iota.alphaCode s a) (muCode s a) = sourceValue s a := by
  have hc := OmegaQuotient.coefficientCode_spec s a ha
  exact ⟨hc.2.2.1, hc.2.2.2, hc.2.1, muCode_spec s a ha⟩

theorem muCode_height_mappedCoefficient (s a : Nat) (ha : inputCheck s a = true) :
    heightCode (muCode s a) ≤
      CanonicalHeight.canonicalHeightCode (Iota.alphaCode s a) (mappedCoefficient s a) := by
  have he := OmegaPowerHeight.finiteTailCode_spec (Iota.alphaCode s a)
    (mappedCoefficient s a) (tail s a) (mappedCoefficient_spec s a ha).1
  have hp := OmegaPowers.powerCode_height (Iota.alphaCode s a) (exponentCode s a) he.1
  rw [CanonicalHeight.canonicalHeightCode_normal _ _ he.2.1] at hp
  rw [muCode_literal s a ha]
  exact hp.trans he.2.2.2

def execute (s a : Nat) : Part Nat := cond (inputCheck s a) (Part.some (muCode s a)) Part.none

theorem execute_partrec : Partrec₂ execute :=
  (Partrec.cond inputCheck_primrec.to_comp muCode_primrec.to_comp.partrec Partrec.none).to₂

theorem execute_domain (s a : Nat) : (execute s a).Dom ↔ inputCheck s a = true := by
  cases h : inputCheck s a <;> simp [execute, h]

theorem execute_graph (s a out : Nat) : out ∈ execute s a ↔
    inputCheck s a = true ∧ out = muCode s a := by
  cases h : inputCheck s a <;> simp [execute, h]

theorem execute_spec (s a out : Nat) (ho : out ∈ execute s a) :
    inputCheck s a = true ∧ lowCheckCode (Iota.alphaCode s a) out = true ∧
      Comparison.acceptedCode (Iota.alphaCode s a) out = true ∧
        interpretation (Iota.alphaCode s a) out = sourceValue s a := by
  obtain ⟨ha, rfl⟩ := (execute_graph s a out).mp ho
  exact ⟨ha, muCode_spec s a ha⟩

namespace Raw

abbrev normalizedRoot := Lambda.Branches.Raw.normalizedRoot

/-- The normal root is actually computed. The exact domain below is stated
on the original raw proper epsilon root, without a normalization premise. -/
def inputCheck (s a : Nat) : Bool := Lambda.Branches.Raw.inputCheck s a &&
  Mu.inputCheck s (normalizedRoot s a)

theorem inputCheck_primrec : Primrec₂ inputCheck :=
  (Primrec.and.comp Lambda.Branches.Raw.inputCheck_primrec
    (Mu.inputCheck_primrec.comp Primrec.fst Lambda.Branches.Raw.normalizedRoot_primrec)).to₂

theorem inputCheck_exact (s a : Nat) : inputCheck s a = true ↔
    (∃ t : RelativeTerm Nat, a = (.theta 0 t).code ∧
      check (contextCode s) (.theta 0 t) = true ∧
        base (contextCode s) < denote (contextCode s) (.theta 0 t)) ∧
      Ordinal.omega0 ^ interpretation (contextCode s) a = interpretation (contextCode s) a := by
  rw [inputCheck, Bool.and_eq_true]
  constructor
  · rintro ⟨ha, hn⟩
    exact ⟨(Lambda.Branches.Raw.inputCheck_exact s a).mp ha,
      (Lambda.Branches.Raw.branch_epsilon_iff_original s a ha).mp hn⟩
  · rintro ⟨ha, he⟩
    have hr := (Lambda.Branches.Raw.inputCheck_exact s a).mpr ha
    exact ⟨hr, (Lambda.Branches.Raw.branch_epsilon_iff_original s a hr).mpr he⟩

def outputContext (s a : Nat) : Nat := Iota.alphaCode s (normalizedRoot s a)

theorem outputContext_value (s a : Nat) (ha : inputCheck s a = true) :
    base (outputContext s a) = interpretation (contextCode s) a := by
  have hs := Bool.and_eq_true.mp ha
  have hc := (Bool.and_eq_true.mp (Bool.and_eq_true.mp hs.1).1).1
  change unionInterpretation (Iota.alphaCode s (normalizedRoot s a)) = _
  rw [(Iota.alphaCode_spec s _ hs.2).2]
  exact (Normalization.normalizeCode_accepted (contextCode s) a hc).2

def muCode (s a : Nat) : Nat := cond (inputCheck s a) (Mu.muCode s (normalizedRoot s a)) 0

theorem muCode_primrec : Primrec₂ muCode :=
  (inputCheck_primrec.cond (Mu.muCode_primrec.comp Primrec.fst
    Lambda.Branches.Raw.normalizedRoot_primrec) (Primrec.const 0)).to₂

def execute (s a : Nat) : Part Nat := cond (inputCheck s a) (Part.some (muCode s a)) Part.none

theorem execute_partrec : Partrec₂ execute :=
  (Partrec.cond inputCheck_primrec.to_comp muCode_primrec.to_comp.partrec Partrec.none).to₂

theorem execute_domain (s a : Nat) : (execute s a).Dom ↔ inputCheck s a = true := by
  cases h : inputCheck s a <;> simp [execute, h]

theorem execute_graph (s a out : Nat) : out ∈ execute s a ↔
    inputCheck s a = true ∧ out = muCode s a := by
  cases h : inputCheck s a <;> simp [execute, h]

theorem execute_spec (s a out : Nat) (ho : out ∈ execute s a) :
    inputCheck s a = true ∧ lowCheckCode (outputContext s a) out = true ∧
      Comparison.acceptedCode (outputContext s a) out = true ∧
        interpretation (outputContext s a) out = Mu.sourceValue s (normalizedRoot s a) := by
  obtain ⟨ha, rfl⟩ := (execute_graph s a out).mp ho
  have hs := Mu.muCode_spec s _ (Bool.and_eq_true.mp ha).2
  exact ⟨ha, by simpa only [muCode, ha, Bool.cond_true, outputContext] using hs⟩

end Raw
end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Mu
