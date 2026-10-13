import Alexander313.Wilken.HereditaryNativeBoundedContextOmegaQuotient

/-!
# Actual mu in the bounded intermediate coded-alpha source

The genuine original intermediate root supplies its complete Omega-one
coefficient and finite tail. Its actual iota image at the computed beta
is admitted LOW and Normal. The real beta-context source indicator,
finite-tail addition and ANY-coded-epsilon omega producer execute the
written Definition 3.6 formula. Every local caller follows from the
original executing bounded intermediate root guard, including lambda zero.
This constructs the intermediate producer; Lemma 3.8 translation invariance
is a separate ensuing theorem. Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.BoundedContextIota.Mu

abbrev inputCheck := BoundedContextIota.rootCheck

theorem inputCheck_primrec : Primrec (fun p : Context => inputCheck p.1.1 p.1.2 p.2) :=
  BoundedContextIota.rootCheck_primrec

theorem inputCheck_exact (s a root : Nat) : inputCheck s a root = true ↔
    Iota.rootCheck s a = true ∧
      (∃ t : RelativeTerm Nat, root = (.theta 0 t).code ∧
        check (sourceCode s a) (.theta 0 t) = true ∧ Comparison.Normal (sourceCode s a) t ∧
          1 < t.outerSort) ∧
      interpretation (sourceCode s a) root < Iota.AlphaPlus.sourceValue s a :=
  BoundedContextIota.rootCheck_exact s a root

theorem root_base_lt (s a root : Nat) (ha : inputCheck s a root = true) :
    base (sourceCode s a) < interpretation (sourceCode s a) root := by
  obtain ⟨_, ⟨t, he, ht, hn, hh⟩, _⟩ := (inputCheck_exact s a root).mp ha
  let q := sourceCode s a
  have hq := sourceCode_checked s a root ha
  have hac := FixedPoint.checked_theta_argument q 0 t ht
  have hhigh : omegaSequence (base q) 1 ≤ denote q t := by
    apply le_of_not_gt
    intro h
    exact (not_le_of_gt hh) ((denote_lt_iff_outerSort_le q t hac 1 (by omega)).mp h)
  rw [he, interpretation_code]
  exact SourceChi.Powers.global_high_base_lt (base q) (base_pos q hq)
    (FixedPoint.sourceOrdinal q 0 t hac) (FixedPoint.checked_theta_sort q 0 t ht) hhigh

theorem root_interval (s a root : Nat) (ha : inputCheck s a root = true) :
    base (sourceCode s a) < interpretation (sourceCode s a) root ∧
      interpretation (sourceCode s a) root < Iota.AlphaPlus.sourceValue s a :=
  ⟨root_base_lt s a root ha, ((inputCheck_exact s a root).mp ha).2.2⟩

def mappedCoefficient (s a root : Nat) : Nat :=
  literalCode s a root (OmegaQuotient.coefficientCode s a root)

theorem mappedCoefficient_primrec : Primrec
    (fun p : Context => mappedCoefficient p.1.1 p.1.2 p.2) :=
  literalCode_primrec.comp (Primrec.id.pair OmegaQuotient.coefficientCode_primrec)

theorem mappedCoefficient_spec (s a root : Nat) (ha : inputCheck s a root = true) :
    lowCheckCode (betaCode s a root) (mappedCoefficient s a root) = true ∧
      Comparison.acceptedCode (betaCode s a root) (mappedCoefficient s a root) = true :=
  OmegaQuotient.coefficient_iota_low s a root ha

def chi (s a root : Nat) : Bool :=
  SourceChi.chiCode (betaCode s a root) (mappedCoefficient s a root)

theorem chi_primrec : Primrec (fun p : Context => chi p.1.1 p.1.2 p.2) :=
  SourceChi.chiCode_primrec.comp betaCode_primrec mappedCoefficient_primrec

theorem chi_correct (s a root : Nat) (ha : inputCheck s a root = true) :
    chi s a root = SourceChi.indicator (betaCode s a root)
      (ThetaCourse.rawTree (mappedCoefficient s a root)) := by
  have hs := (Comparison.acceptedCode_exact _ _).mp (mappedCoefficient_spec s a root ha).2
  have hc : (ThetaCourse.rawTree (mappedCoefficient s a root)).code = mappedCoefficient s a root := by
    obtain ⟨t, he, ht⟩ := (checkCode_exact _ _).mp hs.1
    simp only [← he, ThetaCourse.rawTree_code]
  simpa only [chi, hc] using SourceChi.chiCode_correct (betaCode s a root)
    (ThetaCourse.rawTree (mappedCoefficient s a root))
    (Arithmetic.raw_checked _ _ hs.1) hs.2

def tail (s a root : Nat) : Nat := cond (chi s a root) 1 0 +
  OmegaQuotient.coefficientOffset s a root

theorem tail_primrec : Primrec (fun p : Context => tail p.1.1 p.1.2 p.2) :=
  Primrec.nat_add.comp (chi_primrec.cond (Primrec.const 1) (Primrec.const 0))
    OmegaQuotient.coefficientOffset_primrec

def exponentCode (s a root : Nat) : Nat :=
  OmegaPowerHeight.finiteTailCode (betaCode s a root) (mappedCoefficient s a root) (tail s a root)

theorem exponentCode_primrec : Primrec (fun p : Context => exponentCode p.1.1 p.1.2 p.2) :=
  OmegaPowerHeight.finiteTailCode_primrec.comp
    ((betaCode_primrec.pair mappedCoefficient_primrec).pair tail_primrec)

theorem exponentCode_spec (s a root : Nat) (ha : inputCheck s a root = true) :
    lowCheckCode (betaCode s a root) (exponentCode s a root) = true ∧
      Comparison.acceptedCode (betaCode s a root) (exponentCode s a root) = true ∧
      interpretation (betaCode s a root) (exponentCode s a root) =
        interpretation (betaCode s a root) (mappedCoefficient s a root) +
          cond (chi s a root) (1 : Ordinal.{0}) 0 +
            (OmegaQuotient.coefficientOffset s a root : Ordinal.{0}) := by
  have hs := OmegaPowerHeight.finiteTailCode_spec (betaCode s a root)
    (mappedCoefficient s a root) (tail s a root) (mappedCoefficient_spec s a root ha).1
  refine ⟨hs.1, hs.2.1, ?_⟩
  rw [hs.2.2.1, tail, Nat.cast_add, add_assoc]
  cases h : chi s a root <;>
    simp only [h, Bool.cond_true, Bool.cond_false, Nat.cast_zero, Nat.cast_one]

noncomputable def sourceValue (s a root : Nat) : Ordinal.{0} := Ordinal.omega0 ^
  (interpretation (betaCode s a root) (mappedCoefficient s a root) +
    cond (SourceChi.indicator (betaCode s a root)
      (ThetaCourse.rawTree (mappedCoefficient s a root))) 1 0 +
        (OmegaQuotient.coefficientOffset s a root : Ordinal.{0}))

def muCode (s a root : Nat) : Nat := cond (inputCheck s a root)
  (OmegaPowers.powerCode (betaCode s a root) (exponentCode s a root)) 0

theorem muCode_primrec : Primrec (fun p : Context => muCode p.1.1 p.1.2 p.2) :=
  inputCheck_primrec.cond
    (OmegaPowers.powerCode_primrec.comp betaCode_primrec exponentCode_primrec) (Primrec.const 0)

theorem muCode_literal (s a root : Nat) (ha : inputCheck s a root = true) :
    muCode s a root = OmegaPowers.powerCode (betaCode s a root) (exponentCode s a root) := by
  simp only [muCode, ha, Bool.cond_true]

theorem muCode_rejected (s a root : Nat) (ha : inputCheck s a root = false) : muCode s a root = 0 := by
  simp only [muCode, ha, Bool.cond_false]

theorem muCode_spec (s a root : Nat) (ha : inputCheck s a root = true) :
    lowCheckCode (betaCode s a root) (muCode s a root) = true ∧
      Comparison.acceptedCode (betaCode s a root) (muCode s a root) = true ∧
        interpretation (betaCode s a root) (muCode s a root) = sourceValue s a root := by
  have hs := OmegaPowers.powerCode_spec (betaCode s a root) (exponentCode s a root)
    (exponentCode_spec s a root ha).1
  rw [muCode_literal s a root ha]
  refine ⟨hs.1, hs.2.1, ?_⟩
  rw [hs.2.2, (exponentCode_spec s a root ha).2.2, sourceValue, chi_correct s a root ha]

theorem definition_3_6_spec (s a root : Nat) (ha : inputCheck s a root = true) :
    (interpretation (sourceCode s a) (OmegaQuotient.coefficientCode s a root) = 0 ∨
      IsSuccLimit (interpretation (sourceCode s a) (OmegaQuotient.coefficientCode s a root))) ∧
      omegaSequence (base (sourceCode s a)) 1 *
        (interpretation (sourceCode s a) (OmegaQuotient.coefficientCode s a root) +
          (OmegaQuotient.coefficientOffset s a root : Ordinal.{0})) =
        interpretation (sourceCode s a) (OmegaQuotient.deltaCode root) ∧
      BoundedContextIota.inputCheck s a root (OmegaQuotient.coefficientCode s a root) = true ∧
      lowCheckCode (betaCode s a root) (muCode s a root) = true ∧
      Comparison.acceptedCode (betaCode s a root) (muCode s a root) = true ∧
        interpretation (betaCode s a root) (muCode s a root) = sourceValue s a root := by
  have hc := OmegaQuotient.coefficientCode_spec s a root ha
  exact ⟨hc.2.2.1, hc.2.2.2, hc.2.1, muCode_spec s a root ha⟩

theorem muCode_height_mappedCoefficient (s a root : Nat) (ha : inputCheck s a root = true) :
    heightCode (muCode s a root) ≤
      CanonicalHeight.canonicalHeightCode (betaCode s a root) (mappedCoefficient s a root) := by
  have he := OmegaPowerHeight.finiteTailCode_spec (betaCode s a root)
    (mappedCoefficient s a root) (tail s a root) (mappedCoefficient_spec s a root ha).1
  have hp := OmegaPowers.powerCode_height (betaCode s a root) (exponentCode s a root) he.1
  rw [CanonicalHeight.canonicalHeightCode_normal _ _ he.2.1] at hp
  rw [muCode_literal s a root ha]
  exact hp.trans he.2.2.2

def execute (s a root : Nat) : Part Nat :=
  cond (inputCheck s a root) (Part.some (muCode s a root)) Part.none

theorem execute_partrec : Partrec (fun p : Context => execute p.1.1 p.1.2 p.2) :=
  Partrec.cond inputCheck_primrec.to_comp muCode_primrec.to_comp.partrec Partrec.none

theorem execute_domain (s a root : Nat) : (execute s a root).Dom ↔ inputCheck s a root = true := by
  cases h : inputCheck s a root <;> simp [execute, h]

theorem execute_graph (s a root out : Nat) : out ∈ execute s a root ↔
    inputCheck s a root = true ∧ out = muCode s a root := by
  cases h : inputCheck s a root <;> simp [execute, h]

theorem execute_spec (s a root out : Nat) (ho : out ∈ execute s a root) :
    inputCheck s a root = true ∧ lowCheckCode (betaCode s a root) out = true ∧
      Comparison.acceptedCode (betaCode s a root) out = true ∧
        interpretation (betaCode s a root) out = sourceValue s a root := by
  obtain ⟨ha, rfl⟩ := (execute_graph s a root out).mp ho
  exact ⟨ha, muCode_spec s a root ha⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.BoundedContextIota.Mu
