import Alexander313.Carlson.RationalExactnessExamples

open Alexander313.Carlson
open Finite

-- The checker recognizes the existing semantic exactness predicate on
-- the actual stored rational endpoint structures.
example (P Q : RationalPresentation) :
    Str.Exact P.toStr Q.toStr ↔ ∃ code, RationalPresentation.checkExact P Q code = true :=
  RationalPresentation.exact_iff_exists_code P Q

-- A single real machine handles all raw certificates, and its accepting
-- witnesses are equivalent to original semantic exactness.
example : ∃ machine : Nat.Partrec.Code, ∀ P Q : RationalPresentation,
    (∀ code : ℕ, machine.eval (Encodable.encode ((P, Q), code)) =
      Part.some (Encodable.encode (RationalPresentation.checkExact P Q code))) ∧
    (Str.Exact P.toStr Q.toStr ↔ ∃ code : ℕ,
      machine.eval (Encodable.encode ((P, Q), code)) = Part.some (Encodable.encode true)) :=
  PrimitiveRationalExactness.exactness_machine

-- Inspect the original dependent decoder and common-grid derivation,
-- so replacing it with a new tagged encoding cannot satisfy this gate.
example (P Q : RationalPresentation) (code : ℕ) :
    RationalPresentation.checkExact P Q code = true ↔ ∃ c : RationalCertificate,
      Encodable.decode code = some c ∧ Q.toStr.IsPattern ∧
      0 < c.1 ∧ StrictMono c.2.labels ∧
      Str.IsIso c.2.source.toStr P.toStr c.2.labels ∧
      Str.IsIso c.2.target.toStr (Q.toStr.initialSpan P.U) c.2.labels ∧
      Finite.checkGeneration c.2.source c.2.target c.2.derivation = true ∧
      (Q.toStr.initialSpan P.U).KCorrect Q.toStr Lvl.one := by
  rw [RationalPresentation.checkExact_decoded_iff]
  simp only [RationalWitness.check_eq_true, RationalPresentation.toStr_initialSpan,
    and_assoc]

#print axioms Alexander313.Carlson.Finite.RationalPresentation.restrict_U
#print axioms Alexander313.Carlson.Finite.RationalPresentation.toStr_restrict
#print axioms Alexander313.Carlson.Finite.RationalPresentation.toStr_initialSpan
#print axioms Alexander313.Carlson.Finite.RationalPresentation.mem_initialSpan
#print axioms Alexander313.Carlson.Finite.RationalPresentation.initialSpan_empty
#print axioms Alexander313.Carlson.Finite.RationalPresentation.instDecidableToStrIsPattern
#print axioms Alexander313.Carlson.Finite.RationalPresentation.checkPattern_eq_true
#print axioms Alexander313.Carlson.Finite.RationalPresentation.checkInitialSpanCorrect_eq_true
#print axioms Alexander313.Carlson.Finite.RationalPresentation.checkExact_eq_true
#print axioms Alexander313.Carlson.Finite.RationalPresentation.checkExact_sound
#print axioms Alexander313.Carlson.Finite.RationalPresentation.checkExact_complete
#print axioms Alexander313.Carlson.Finite.RationalPresentation.exact_iff_exists_code
#print axioms Alexander313.Carlson.Finite.RationalPresentation.checkExact_decoded_iff
#print axioms Alexander313.Carlson.Finite.RationalPresentation.checkExact_encode
#print axioms Alexander313.Carlson.Finite.RationalPresentation.checkExact_decode_none
#print axioms Alexander313.Carlson.Finite.RationalPresentation.exact_iff_encoded_code
#print axioms Alexander313.Carlson.PrimitiveRationalExactness.checkPattern_primrec
#print axioms Alexander313.Carlson.PrimitiveRationalExactness.restrict_primrec
#print axioms Alexander313.Carlson.PrimitiveRationalExactness.initialSpan_primrec
#print axioms Alexander313.Carlson.PrimitiveRationalExactness.checkInitialSpanCorrect_primrec
#print axioms Alexander313.Carlson.PrimitiveRationalExactness.checkExact_primrec
#print axioms Alexander313.Carlson.PrimitiveRationalExactness.checkExact_program
#print axioms Alexander313.Carlson.PrimitiveRationalExactness.exactness_machine
#print axioms Alexander313.Carlson.Finite.RationalExactnessExamples.downward_generation_is_proper
#print axioms Alexander313.Carlson.Finite.RationalExactnessExamples.downward_generation_accepts
#print axioms Alexander313.Carlson.Finite.RationalExactnessExamples.proper_exactness_accepts
#print axioms Alexander313.Carlson.Finite.RationalExactnessExamples.proper_exactness_semantics
#print axioms Alexander313.Carlson.Finite.RationalExactnessExamples.crossing_generation_accepts
#print axioms Alexander313.Carlson.Finite.RationalExactnessExamples.crossing_correctness_rejects
#print axioms Alexander313.Carlson.Finite.RationalExactnessExamples.crossing_exactness_rejects
#print axioms Alexander313.Carlson.Finite.RationalExactnessExamples.crossing_is_not_exact
#print axioms Alexander313.Carlson.Finite.RationalExactnessExamples.empty_source_accepts_nonempty_target
#print axioms Alexander313.Carlson.Finite.RationalExactnessExamples.empty_source_is_exact
#print axioms Alexander313.Carlson.Finite.RationalExactnessExamples.empty_span_retains_tables
#print axioms Alexander313.Carlson.Finite.RationalExactnessExamples.nonpattern_target_rejects
#print axioms Alexander313.Carlson.Finite.RationalExactnessExamples.malformed_original_certificate_rejects
#print axioms Alexander313.Carlson.Finite.RationalExactnessExamples.exactness_machine_controls
