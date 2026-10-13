import Alexander313.Carlson.PrimitiveRationalExactness
import Alexander313.Carlson.RationalCertificateExamples
import Alexander313.Carlson.FiniteCertificateExamples

/-!
# Controls for executable rational exactness

The positive proper extension uses an actual accepted downward-reflection
certificate; its initial span contains a genuinely new point. The negative
control keeps both patternhood and generation true, and fails only because
an old point has a first-relation edge outside the initial span. Empty
sources and malformed original certificates are checked separately.
Numeric witness encodings are used only through encode/decode theorems.
-/

namespace Alexander313.Carlson.Finite.RationalExactnessExamples

open RationalPresentation

set_option maxRecDepth 8192

private theorem accepts_encoded_generation {n : ℕ} (labels : Fin n → ℚ)
    (d : GenerationCertificate n) (P Q : RationalPresentation)
    (hn : 0 < n) (hm : StrictMono labels)
    (eP : Str.IsIso d.source.toStr P.toStr labels)
    (eQ : Str.IsIso d.target.toStr Q.toStr labels) (hd : d.check = true) :
    RationalPresentation.checkGeneration P Q
      (Encodable.encode
        (⟨n, ⟨labels, d.source, d.target, Encodable.encode d⟩⟩ : RationalCertificate)) =
      true := by
  apply (RationalPresentation.checkCertificate_eq_true
    (fun n => @Finite.checkGeneration n) P Q _).mpr
  refine ⟨_, Encodable.encodek _, ?_⟩
  apply (RationalWitness.check_eq_true _ _ P Q).mpr
  refine ⟨hn, hm, eP, eQ, ?_⟩
  exact (Finite.checkGeneration_eq_true d.source d.target (Encodable.encode d)).mpr
    ⟨d, Encodable.encodek d, hd, rfl, rfl⟩

/-- Keep only the finite carrier entries of a finite-grid pattern. -/
def onGrid {n : ℕ} (C : PatternCode n) (labels : Fin n → ℚ) :
    RationalPresentation where
  U := C.U.image labels
  r₁ := ((C.U ×ˢ C.U).filter (fun ij => C.r₁ ij.1 ij.2 = true)).image
    (fun ij => (labels ij.1, labels ij.2))
  r₂ := ((C.U ×ˢ C.U).filter (fun ij => C.r₂ ij.1 ij.2 = true)).image
    (fun ij => (labels ij.1, labels ij.2))

def labels (i : Fin 4) : ℚ := i.val

def source := onGrid CertificateExamples.base labels

def target := onGrid CertificateExamples.downwardRule.target labels

def downwardGeneration : GenerationCertificate 4 :=
  ⟨.tail (.refl CertificateExamples.base) CertificateExamples.downwardRule,
    CertificateExamples.downwardRule.target⟩

def downwardCode : ℕ := Encodable.encode
  (⟨4, ⟨labels, downwardGeneration.source, downwardGeneration.target,
    Encodable.encode downwardGeneration⟩⟩ : RationalCertificate)

/-- This accepted generation actually introduces a new carrier point. -/
theorem downward_generation_is_proper : source.U ≠ target.U ∧
    0 ∈ target.U ∧ 0 ∉ source.U := by decide

theorem downward_generation_accepts :
    RationalPresentation.checkGeneration source (target.initialSpan source.U)
      downwardCode = true := by
  exact accepts_encoded_generation labels downwardGeneration source
    (target.initialSpan source.U) (by decide)
    (by unfold StrictMono; decide) (by decide) (by decide) (by decide)

/-- The original certificate certifies exactness of a proper generated extension. -/
theorem proper_exactness_accepts : checkExact source target downwardCode = true := by
  apply (checkExact_eq_true source target downwardCode).mpr
  exact ⟨(checkPattern_eq_true target).mp (by decide), downward_generation_accepts,
    (checkInitialSpanCorrect_eq_true target source.U).mp (by decide)⟩

theorem proper_exactness_semantics : Str.Exact source.toStr target.toStr :=
  checkExact_sound proper_exactness_accepts

/-- A first-relation edge from `0` to `1` crosses the old singleton's span. -/
def crossing : RationalPresentation where
  U := {0, 1}
  r₁ := {(0, 0), (0, 1), (1, 1)}
  r₂ := {(0, 0), (1, 1)}

abbrev singleton := RationalCertificateExamples.singleton

/-- Generation and patternhood both pass in the negative control. -/
theorem crossing_generation_accepts : crossing.checkPattern = true ∧
    RationalPresentation.checkGeneration singleton (crossing.initialSpan singleton.U)
      RationalCertificateExamples.generationCode = true := by
  refine ⟨by decide, ?_⟩
  exact accepts_encoded_generation RationalCertificateExamples.labels
    RationalCertificateExamples.generation singleton (crossing.initialSpan singleton.U)
    (by decide) (by unfold StrictMono; decide) (by decide) (by decide) (by decide)

theorem crossing_correctness_rejects :
    crossing.checkInitialSpanCorrect singleton.U = false := by decide

/-- Every certificate is rejected solely because correctness fails. -/
theorem crossing_exactness_rejects (code : ℕ) :
    checkExact singleton crossing code = false := by
  simp only [checkExact, crossing_correctness_rejects, Bool.and_false]

theorem crossing_is_not_exact : ¬ Str.Exact singleton.toStr crossing.toStr := by
  intro h
  obtain ⟨code, hc⟩ := checkExact_complete h
  rw [crossing_exactness_rejects] at hc
  cases hc

def emptyPattern : PatternCode 1 where
  U := ∅
  r₁ _ _ := false
  r₂ _ _ := false

def empty : RationalPresentation := ⟨∅, ∅, ∅⟩

def emptyLabels (i : Fin 1) : ℚ := i.val

def emptyGeneration : GenerationCertificate 1 := ⟨.refl emptyPattern, emptyPattern⟩

def emptyCode : ℕ := Encodable.encode
  (⟨1, ⟨emptyLabels, emptyPattern, emptyPattern,
    Encodable.encode emptyGeneration⟩⟩ : RationalCertificate)

/-- The target can be nonempty while the source and its initial span are empty. -/
theorem empty_source_accepts_nonempty_target : checkExact empty crossing emptyCode = true := by
  apply (checkExact_eq_true empty crossing emptyCode).mpr
  refine ⟨(checkPattern_eq_true crossing).mp (by decide), ?_,
    (checkInitialSpanCorrect_eq_true crossing empty.U).mp (by decide)⟩
  exact accepts_encoded_generation emptyLabels emptyGeneration empty
    (crossing.initialSpan empty.U) (by decide)
    (by unfold StrictMono; decide) (by decide) (by decide) (by decide)

theorem empty_source_is_exact : Str.Exact empty.toStr crossing.toStr :=
  checkExact_sound empty_source_accepts_nonempty_target

/-- Off-carrier edge tables are retained even when the initial span is empty. -/
theorem empty_span_retains_tables :
    (crossing.initialSpan empty.U).r₁ = crossing.r₁ ∧
      (crossing.initialSpan empty.U).r₂ = crossing.r₂ := ⟨rfl, rfl⟩

def nonPattern : RationalPresentation where
  U := {0}
  r₁ := ∅
  r₂ := ∅

theorem nonpattern_target_rejects (code : ℕ) :
    checkExact empty nonPattern code = false := by
  have h : nonPattern.checkPattern = false := by decide
  simp only [checkExact, h, Bool.false_and]

theorem malformed_original_certificate_rejects (P Q : RationalPresentation) :
    checkExact P Q 0 = false :=
  checkExact_decode_none P Q 0 (by decide +kernel)

/-- One actual machine accepts the proper and empty examples, and rejects
every crossing witness and the malformed original code on arbitrary endpoints. -/
theorem exactness_machine_controls : ∃ machine : Nat.Partrec.Code,
    machine.eval (Encodable.encode ((source, target), downwardCode)) =
      Part.some (Encodable.encode true) ∧
    machine.eval (Encodable.encode ((empty, crossing), emptyCode)) =
      Part.some (Encodable.encode true) ∧
    (∀ code : ℕ, machine.eval (Encodable.encode ((singleton, crossing), code)) =
      Part.some (Encodable.encode false)) ∧
    (∀ P Q : RationalPresentation, machine.eval (Encodable.encode ((P, Q), (0 : ℕ))) =
      Part.some (Encodable.encode false)) := by
  obtain ⟨machine, hm⟩ := PrimitiveRationalExactness.checkExact_program
  refine ⟨machine, ?_, ?_, ?_, ?_⟩
  · simpa only [proper_exactness_accepts] using hm source target downwardCode
  · simpa only [empty_source_accepts_nonempty_target] using hm empty crossing emptyCode
  · intro code
    simpa only [crossing_exactness_rejects] using hm singleton crossing code
  · intro P Q
    simpa only [malformed_original_certificate_rejects] using hm P Q 0

end Alexander313.Carlson.Finite.RationalExactnessExamples
