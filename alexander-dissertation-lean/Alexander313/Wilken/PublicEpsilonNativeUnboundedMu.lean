import Alexander313.Wilken.PublicEpsilonNativeUnboundedOmegaQuotient

/-!
# Genuine finite mu on the full original coded-epsilon high-root domain

The original ANY-q admitted Normal high root supplies the complete
Omega-one coefficient, with no dictionary or selected endpoint.
Actual iota, source chi, finite-tail addition and ANY-q omega power execute
Definition 3.6, including lambda zero. Every local caller is derived.
This constructs the producer; syntactic Par preservation and printed 3.9
base-change commutation remain separate mathematical work. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.Mu

abbrev inputCheck := PublicEpsilonUnboundedIota.rootCheck

theorem inputCheck_primrec : Primrec (fun p : Context => inputCheck p.1 p.2) :=
  PublicEpsilonUnboundedIota.rootCheck_primrec

/-- EXACT original admitted Normal high theta-zero root, at ANY original
admitted coded epsilon. No selected endpoint or canonical spelling guard. -/
theorem inputCheck_exact (q root : Nat) : inputCheck q root = true ↔
    ∃ t : RelativeTerm Nat, root = (.theta 0 t).code ∧
      check q (.theta 0 t) = true ∧ Comparison.Normal q t ∧
        1 < t.outerSort :=
  PublicEpsilonUnboundedIota.rootCheck_exact q root

theorem root_base_lt (q root : Nat) (ha : inputCheck q root = true) :
    base q < interpretation q root := PublicEpsilonUnboundedIota.root_base_lt q root ha

/-- The genuine first-cardinal interval follows from the original root
checker, rather than from any selected public return endpoint. -/
theorem root_interval (q root : Nat) (ha : inputCheck q root = true) :
    base q < interpretation q root ∧
      interpretation q root < omegaSequence (base q) 1 :=
  ⟨root_base_lt q root ha, RootLowCollapse.root_lt_first q root ha⟩

def mappedCoefficient (q root : Nat) : Nat :=
  literalCode q root (OmegaQuotient.coefficientCode q root)

theorem mappedCoefficient_primrec : Primrec
    (fun p : Context => mappedCoefficient p.1 p.2) :=
  literalCode_primrec.comp Primrec.id OmegaQuotient.coefficientCode_primrec

theorem mappedCoefficient_spec (q root : Nat) (ha : inputCheck q root = true) :
    lowCheckCode (betaCode q root) (mappedCoefficient q root) = true ∧
      Comparison.acceptedCode (betaCode q root) (mappedCoefficient q root) = true :=
  OmegaQuotient.coefficient_iota_low q root ha

def chi (q root : Nat) : Bool :=
  SourceChi.chiCode (betaCode q root) (mappedCoefficient q root)

theorem chi_primrec : Primrec (fun p : Context => chi p.1 p.2) :=
  SourceChi.chiCode_primrec.comp betaCode_primrec mappedCoefficient_primrec

theorem chi_correct (q root : Nat) (ha : inputCheck q root = true) :
    chi q root = SourceChi.indicator (betaCode q root)
      (ThetaCourse.rawTree (mappedCoefficient q root)) := by
  have hs := (Comparison.acceptedCode_exact _ _).mp (mappedCoefficient_spec q root ha).2
  have hc : (ThetaCourse.rawTree (mappedCoefficient q root)).code = mappedCoefficient q root := by
    obtain ⟨t, he, ht⟩ := (checkCode_exact _ _).mp hs.1
    simp only [← he, ThetaCourse.rawTree_code]
  simpa only [chi, hc] using SourceChi.chiCode_correct (betaCode q root)
    (ThetaCourse.rawTree (mappedCoefficient q root))
    (Arithmetic.raw_checked _ _ hs.1) hs.2

def tail (q root : Nat) : Nat := cond (chi q root) 1 0 +
  OmegaQuotient.coefficientOffset q root

theorem tail_primrec : Primrec (fun p : Context => tail p.1 p.2) :=
  Primrec.nat_add.comp (chi_primrec.cond (Primrec.const 1) (Primrec.const 0))
    OmegaQuotient.coefficientOffset_primrec

def exponentCode (q root : Nat) : Nat :=
  OmegaPowerHeight.finiteTailCode (betaCode q root) (mappedCoefficient q root) (tail q root)

theorem exponentCode_primrec : Primrec (fun p : Context => exponentCode p.1 p.2) :=
  OmegaPowerHeight.finiteTailCode_primrec.comp
    ((betaCode_primrec.pair mappedCoefficient_primrec).pair tail_primrec)

theorem exponentCode_spec (q root : Nat) (ha : inputCheck q root = true) :
    lowCheckCode (betaCode q root) (exponentCode q root) = true ∧
      Comparison.acceptedCode (betaCode q root) (exponentCode q root) = true ∧
      interpretation (betaCode q root) (exponentCode q root) =
        interpretation (betaCode q root) (mappedCoefficient q root) +
          cond (chi q root) (1 : Ordinal.{0}) 0 +
            (OmegaQuotient.coefficientOffset q root : Ordinal.{0}) := by
  have hs := OmegaPowerHeight.finiteTailCode_spec (betaCode q root)
    (mappedCoefficient q root) (tail q root) (mappedCoefficient_spec q root ha).1
  refine ⟨hs.1, hs.2.1, ?_⟩
  rw [hs.2.2.1, tail, Nat.cast_add, add_assoc]
  cases h : chi q root <;>
    simp only [h, Bool.cond_true, Bool.cond_false, Nat.cast_zero, Nat.cast_one]

noncomputable def sourceValue (q root : Nat) : Ordinal.{0} := Ordinal.omega0 ^
  (interpretation (betaCode q root) (mappedCoefficient q root) +
    cond (SourceChi.indicator (betaCode q root)
      (ThetaCourse.rawTree (mappedCoefficient q root))) 1 0 +
        (OmegaQuotient.coefficientOffset q root : Ordinal.{0}))

def muCode (q root : Nat) : Nat := cond (inputCheck q root)
  (OmegaPowers.powerCode (betaCode q root) (exponentCode q root)) 0

theorem muCode_primrec : Primrec (fun p : Context => muCode p.1 p.2) :=
  inputCheck_primrec.cond
    (OmegaPowers.powerCode_primrec.comp betaCode_primrec exponentCode_primrec) (Primrec.const 0)

theorem muCode_literal (q root : Nat) (ha : inputCheck q root = true) :
    muCode q root = OmegaPowers.powerCode (betaCode q root) (exponentCode q root) := by
  simp only [muCode, ha, Bool.cond_true]

theorem muCode_rejected (q root : Nat) (ha : inputCheck q root = false) : muCode q root = 0 := by
  simp only [muCode, ha, Bool.cond_false]

theorem muCode_spec (q root : Nat) (ha : inputCheck q root = true) :
    lowCheckCode (betaCode q root) (muCode q root) = true ∧
      Comparison.acceptedCode (betaCode q root) (muCode q root) = true ∧
        interpretation (betaCode q root) (muCode q root) = sourceValue q root := by
  have hs := OmegaPowers.powerCode_spec (betaCode q root) (exponentCode q root)
    (exponentCode_spec q root ha).1
  rw [muCode_literal q root ha]
  refine ⟨hs.1, hs.2.1, ?_⟩
  rw [hs.2.2, (exponentCode_spec q root ha).2.2, sourceValue, chi_correct q root ha]

theorem definition_3_6_spec (q root : Nat) (ha : inputCheck q root = true) :
    (interpretation q (OmegaQuotient.coefficientCode q root) = 0 ∨
      IsSuccLimit (interpretation q (OmegaQuotient.coefficientCode q root))) ∧
      omegaSequence (base q) 1 *
        (interpretation q (OmegaQuotient.coefficientCode q root) +
          (OmegaQuotient.coefficientOffset q root : Ordinal.{0})) =
        interpretation q (OmegaQuotient.deltaCode root) ∧
      PublicEpsilonUnboundedIota.inputCheck q root (OmegaQuotient.coefficientCode q root) = true ∧
      lowCheckCode (betaCode q root) (muCode q root) = true ∧
      Comparison.acceptedCode (betaCode q root) (muCode q root) = true ∧
        interpretation (betaCode q root) (muCode q root) = sourceValue q root := by
  have hc := OmegaQuotient.coefficientCode_spec q root ha
  exact ⟨hc.2.2.1, hc.2.2.2, hc.2.1, muCode_spec q root ha⟩

theorem muCode_height_mappedCoefficient (q root : Nat) (ha : inputCheck q root = true) :
    heightCode (muCode q root) ≤
      CanonicalHeight.canonicalHeightCode (betaCode q root) (mappedCoefficient q root) := by
  have he := OmegaPowerHeight.finiteTailCode_spec (betaCode q root)
    (mappedCoefficient q root) (tail q root) (mappedCoefficient_spec q root ha).1
  have hp := OmegaPowers.powerCode_height (betaCode q root) (exponentCode q root) he.1
  rw [CanonicalHeight.canonicalHeightCode_normal _ _ he.2.1] at hp
  rw [muCode_literal q root ha]
  exact hp.trans he.2.2.2

def execute (q root : Nat) : Part Nat :=
  cond (inputCheck q root) (Part.some (muCode q root)) Part.none

theorem execute_partrec : Partrec (fun p : Context => execute p.1 p.2) :=
  Partrec.cond inputCheck_primrec.to_comp muCode_primrec.to_comp.partrec Partrec.none

theorem execute_domain (q root : Nat) : (execute q root).Dom ↔ inputCheck q root = true := by
  cases h : inputCheck q root <;> simp [execute, h]

theorem execute_graph (q root out : Nat) : out ∈ execute q root ↔
    inputCheck q root = true ∧ out = muCode q root := by
  cases h : inputCheck q root <;> simp [execute, h]

theorem execute_spec (q root out : Nat) (ho : out ∈ execute q root) :
    inputCheck q root = true ∧ lowCheckCode (betaCode q root) out = true ∧
      Comparison.acceptedCode (betaCode q root) out = true ∧
        interpretation (betaCode q root) out = sourceValue q root := by
  obtain ⟨ha, rfl⟩ := (execute_graph q root out).mp ho
  exact ⟨ha, muCode_spec q root ha⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.Mu
