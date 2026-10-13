import Alexander313.Carlson.PartialPointedComparison
import Alexander313.Carlson.AmalgamationCertificateExamples

open Alexander313.Carlson
open Finite

-- Expand the original Definition 15.8 obligations for the computed target.
example {n : ℕ} (P : Fin n → RationalPresentation) (hP : ∀ i, (P i).toStr.IsPattern) :
    let c := ComputableAmalgamation.compute P hP
    c.1.toStr.IsPattern ∧
      (∀ i, Str.IsIso (P i).toStr (c.1.toStr.restrict ((P i).U.image (c.maps i))) (c.maps i)) ∧
      c.1.U = Finset.univ.biUnion (fun i => (P i).U.image (c.maps i)) ∧
      (∀ i, Str.Exact (c.1.toStr.restrict ((P i).U.image (c.maps i))) c.1.toStr) := by
  let d := ComputableAmalgamation.compute_amalgamation P hP
  exact ⟨d.pattern, d.embeddings, d.union, d.exact⟩

-- Terminating minimization is implemented by a real machine using the
-- ordinary list encoding of all fixed-size input presentations.
example (n : ℕ) : ∃ machine : Nat.Partrec.Code,
    ∀ (P : Fin n → RationalPresentation) (hP : ∀ i, (P i).toStr.IsPattern),
      machine.eval (Encodable.encode (List.ofFn P)) =
        Part.some (ComputableAmalgamation.leastCode P hP) := by
  simpa only [PrimitiveAmalgamationCertificates.familyCode_eq] using
    PartialAmalgamationSearch.terminating_search_program n

-- The five outputs compare the actual existing least ordinal labels.
example (p q : PointedPattern) :
    ((PointedPattern.compare p q).eq = true ↔
      (coreRealization p.seed).label p.point = (coreRealization q.seed).label q.point) ∧
    ((PointedPattern.compare p q).le = true ↔
      (coreRealization p.seed).label p.point ≤ (coreRealization q.seed).label q.point) ∧
    ((PointedPattern.compare p q).lt = true ↔
      (coreRealization p.seed).label p.point < (coreRealization q.seed).label q.point) ∧
    ((PointedPattern.compare p q).one = true ↔
      R1 ((coreRealization p.seed).label p.point) ((coreRealization q.seed).label q.point)) ∧
    ((PointedPattern.compare p q).two = true ↔
      R2 ((coreRealization p.seed).label p.point) ((coreRealization q.seed).label q.point)) :=
  PointedPattern.compare_correct p q

-- One actual machine outputs all five Boolean answers from finite input data.
-- Neither ordinal labels nor a comparison function is supplied as an input.
example : ∃ machine : Nat.Partrec.Code, ∀ p q : PointedPattern,
    ∃ e l t a b : Bool,
      machine.eval (Encodable.encode ((p.seed.val, p.point), (q.seed.val, q.point))) =
        Part.some (Encodable.encode (e, l, t, a, b)) ∧
      (e = true ↔ (coreRealization p.seed).label p.point = (coreRealization q.seed).label q.point) ∧
      (l = true ↔ (coreRealization p.seed).label p.point ≤ (coreRealization q.seed).label q.point) ∧
      (t = true ↔ (coreRealization p.seed).label p.point < (coreRealization q.seed).label q.point) ∧
      (a = true ↔ R1 ((coreRealization p.seed).label p.point) ((coreRealization q.seed).label q.point)) ∧
      (b = true ↔ R2 ((coreRealization p.seed).label p.point) ((coreRealization q.seed).label q.point)) := by
  obtain ⟨machine, hm⟩ := PartialPointedComparison.comparison_program
  refine ⟨machine, fun p q => ?_⟩
  exact ⟨_, _, _, _, _, hm p q, PointedPattern.compare_correct p q⟩

#print axioms Alexander313.Carlson.Finite.RationalMap.Table
#print axioms Alexander313.Carlson.Finite.RationalMap.eval
#print axioms Alexander313.Carlson.Finite.RationalMap.graph
#print axioms Alexander313.Carlson.Finite.RationalMap.eval_graph
#print axioms Alexander313.Carlson.Finite.RationalMap.eval_nil
#print axioms Alexander313.Carlson.Finite.RationalMap.eval_cons
#print axioms Alexander313.Carlson.Str.IsIso
#print axioms Alexander313.Carlson.Str.Amalgamation
#print axioms Alexander313.Carlson.PrimitiveRationalMaps.eval_eq_foldr
#print axioms Alexander313.Carlson.PrimitiveRationalMaps.eval_primrec
#print axioms Alexander313.Carlson.PrimitiveRationalMaps.eval_program
#print axioms Alexander313.Carlson.PrimitiveRationalIso.PairCondition
#print axioms Alexander313.Carlson.PrimitiveRationalIso.IsoData
#print axioms Alexander313.Carlson.PrimitiveRationalIso.pairCondition_primrec
#print axioms Alexander313.Carlson.PrimitiveRationalIso.isoData_primrec
#print axioms Alexander313.Carlson.PrimitiveRationalIso.isoData_iff
#print axioms Alexander313.Carlson.PrimitiveRationalIso.check
#print axioms Alexander313.Carlson.PrimitiveRationalIso.check_eq_true
#print axioms Alexander313.Carlson.PrimitiveRationalIso.check_primrec
#print axioms Alexander313.Carlson.PrimitiveRationalIso.check_program
#print axioms Alexander313.Carlson.Finite.AmalgamationCertificate
#print axioms Alexander313.Carlson.Finite.instEncodableAmalgamationCertificate
#print axioms Alexander313.Carlson.Finite.AmalgamationCertificate.maps
#print axioms Alexander313.Carlson.Finite.AmalgamationCertificate.image
#print axioms Alexander313.Carlson.Finite.AmalgamationCertificate.checkEmbeddings
#print axioms Alexander313.Carlson.Finite.AmalgamationCertificate.checkEmbeddings_eq_true
#print axioms Alexander313.Carlson.Finite.AmalgamationCertificate.check
#print axioms Alexander313.Carlson.Finite.AmalgamationCertificate.check_eq_true
#print axioms Alexander313.Carlson.Finite.AmalgamationCertificate.check_sound
#print axioms Alexander313.Carlson.Finite.AmalgamationCertificate.check_complete
#print axioms Alexander313.Carlson.Finite.AmalgamationCertificate.checkCode
#print axioms Alexander313.Carlson.Finite.AmalgamationCertificate.checkCode_encode
#print axioms Alexander313.Carlson.Finite.AmalgamationCertificate.checkCode_eq_true
#print axioms Alexander313.Carlson.Finite.AmalgamationCertificate.exists_amalgamation_iff_code
#print axioms Alexander313.Carlson.Finite.AmalgamationCertificate.exists_code
#print axioms Alexander313.Carlson.Finite.ComputableAmalgamation.leastCode
#print axioms Alexander313.Carlson.Finite.ComputableAmalgamation.leastCode_check
#print axioms Alexander313.Carlson.Finite.ComputableAmalgamation.leastCode_le
#print axioms Alexander313.Carlson.Finite.ComputableAmalgamation.emptyCertificate
#print axioms Alexander313.Carlson.Finite.ComputableAmalgamation.compute
#print axioms Alexander313.Carlson.Finite.ComputableAmalgamation.compute_check
#print axioms Alexander313.Carlson.Finite.ComputableAmalgamation.compute_amalgamation
#print axioms Alexander313.Carlson.PointedPattern.pairFamily
#print axioms Alexander313.Carlson.PointedPattern.pairFamily_pattern
#print axioms Alexander313.Carlson.PointedPattern.Comparison
#print axioms Alexander313.Carlson.PointedPattern.compare
#print axioms Alexander313.Carlson.PointedPattern.compare_correct
#print axioms Alexander313.Carlson.PrimitiveAmalgamationCertificates.Input
#print axioms Alexander313.Carlson.PrimitiveAmalgamationCertificates.source_primrec
#print axioms Alexander313.Carlson.PrimitiveAmalgamationCertificates.target_primrec
#print axioms Alexander313.Carlson.PrimitiveAmalgamationCertificates.table_primrec
#print axioms Alexander313.Carlson.PrimitiveAmalgamationCertificates.exactCode_primrec
#print axioms Alexander313.Carlson.PrimitiveAmalgamationCertificates.imageCarrier_primrec
#print axioms Alexander313.Carlson.PrimitiveAmalgamationCertificates.image_primrec
#print axioms Alexander313.Carlson.PrimitiveAmalgamationCertificates.checkEmbeddings_primrec
#print axioms Alexander313.Carlson.PrimitiveAmalgamationCertificates.union_primrec
#print axioms Alexander313.Carlson.PrimitiveAmalgamationCertificates.check_primrec
#print axioms Alexander313.Carlson.PrimitiveAmalgamationCertificates.checkCode_primrec
#print axioms Alexander313.Carlson.PrimitiveAmalgamationCertificates.familyCode
#print axioms Alexander313.Carlson.PrimitiveAmalgamationCertificates.familyCode_eq
#print axioms Alexander313.Carlson.PrimitiveAmalgamationCertificates.checkCode_program
#print axioms Alexander313.Carlson.Finite.PartialAmalgamationSearch.search
#print axioms Alexander313.Carlson.Finite.PartialAmalgamationSearch.search_partrec
#print axioms Alexander313.Carlson.Finite.PartialAmalgamationSearch.search_eq_leastCode
#print axioms Alexander313.Carlson.Finite.PartialAmalgamationSearch.search_program
#print axioms Alexander313.Carlson.Finite.PartialAmalgamationSearch.terminating_search_program
#print axioms Alexander313.Carlson.PartialPointedComparison.Input
#print axioms Alexander313.Carlson.PartialPointedComparison.Answers
#print axioms Alexander313.Carlson.PartialPointedComparison.input
#print axioms Alexander313.Carlson.PartialPointedComparison.family
#print axioms Alexander313.Carlson.PartialPointedComparison.family_primrec
#print axioms Alexander313.Carlson.PartialPointedComparison.answers
#print axioms Alexander313.Carlson.PartialPointedComparison.read
#print axioms Alexander313.Carlson.PartialPointedComparison.read_primrec
#print axioms Alexander313.Carlson.PartialPointedComparison.compare
#print axioms Alexander313.Carlson.PartialPointedComparison.compare_partrec
#print axioms Alexander313.Carlson.PartialPointedComparison.compare_eq
#print axioms Alexander313.Carlson.PartialPointedComparison.comparison_program
#print axioms Alexander313.Carlson.Finite.AmalgamationCertificateExamples.first_duplicate_key_wins
#print axioms Alexander313.Carlson.Finite.AmalgamationCertificateExamples.missing_key_defaults_to_zero
#print axioms Alexander313.Carlson.Finite.AmalgamationCertificateExamples.noInputs
#print axioms Alexander313.Carlson.Finite.AmalgamationCertificateExamples.empty_family_certificate_accepts
#print axioms Alexander313.Carlson.Finite.AmalgamationCertificateExamples.empty_family_nonempty_target_rejects
#print axioms Alexander313.Carlson.Finite.AmalgamationCertificateExamples.singletonAt
#print axioms Alexander313.Carlson.Finite.AmalgamationCertificateExamples.singletonInputs
#print axioms Alexander313.Carlson.Finite.AmalgamationCertificateExamples.coalesced
#print axioms Alexander313.Carlson.Finite.AmalgamationCertificateExamples.coalesced_certificate_accepts
#print axioms Alexander313.Carlson.Finite.AmalgamationCertificateExamples.coalesced_encoded_certificate_accepts
#print axioms Alexander313.Carlson.Finite.AmalgamationCertificateExamples.coalesced_search_has_witness_bound
#print axioms Alexander313.Carlson.Finite.AmalgamationCertificateExamples.crossingInputs
#print axioms Alexander313.Carlson.Finite.AmalgamationCertificateExamples.crossingUnion
#print axioms Alexander313.Carlson.Finite.AmalgamationCertificateExamples.covered_union_frame_passes
#print axioms Alexander313.Carlson.Finite.AmalgamationCertificateExamples.covered_union_exactness_rejects
#print axioms Alexander313.Carlson.Finite.AmalgamationCertificateExamples.malformed_candidate_code_rejects
#print axioms Alexander313.Carlson.PointedPattern.compare_self
#print axioms Alexander313.Carlson.PointedPattern.compare_reverse_of_lt

#print axioms Alexander313.Carlson.Finite.AmalgamationCertificateExamples.malformed_two_input_zero_rejects
#print axioms Alexander313.Carlson.Finite.AmalgamationCertificateExamples.coalesced_five_answers
#print axioms Alexander313.Carlson.PointedPattern.self_comparison_machine
