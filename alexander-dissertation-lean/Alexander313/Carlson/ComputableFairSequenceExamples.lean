import Alexander313.Carlson.ComputableFairLimit
import Alexander313.Carlson.FiniteCertificateExamples
import Alexander313.Carlson.RationalCertificateExamples

/-!
# Checked requests and computed fair-sequence transitions

These examples pass a genuine downward-reflection certificate through the
request scheduler and compute two successive lifts of that request. The
second lift must use the new predecessor created by the first. Rejected
requests retain the supplied presentation literally, including off-carrier
edges, and malformed early schedule entries preserve the initial stage.

Certificate encodings and schedule indices remain symbolic. Their proved
encode/decode equations expose the small finite checks before computation;
no enormous encoded natural number is reduced by the kernel. The separate
finite checks, lifting outputs, early stages, and bounded union queries are
computed by `decide +kernel`.
-/

namespace Alexander313.Carlson.Finite.ComputableFairSequenceExamples

open ComputableRequests ComputableFairSequence

set_option maxRecDepth 8192

/-- Certify a rational rule from its finite data while retaining both
numeric encodings symbolically. -/
private theorem accepts_encoded_rule {n : ℕ} (labels : Fin n → ℚ)
    (d : RuleCertificate n) (P Q : RationalPresentation)
    (hn : 0 < n) (hm : StrictMono labels)
    (eP : Str.IsIso d.source.toStr P.toStr labels)
    (eQ : Str.IsIso d.target.toStr Q.toStr labels) (hd : d.check = true) :
    RationalPresentation.checkRule P Q
      (Encodable.encode
        (⟨n, ⟨labels, d.source, d.target, Encodable.encode d⟩⟩ : RationalCertificate)) =
      true := by
  apply (RationalPresentation.checkCertificate_eq_true
    (fun n => @Alexander313.Carlson.Finite.checkRule n) P Q _).mpr
  refine ⟨⟨n, ⟨labels, d.source, d.target, Encodable.encode d⟩⟩,
    Encodable.encodek _, ?_⟩
  apply (RationalWitness.check_eq_true _ _ P Q).mpr
  refine ⟨hn, hm, eP, eQ, ?_⟩
  exact (checkRule_eq_true d.source d.target (Encodable.encode d)).mpr
    ⟨d, Encodable.encodek d, hd, rfl, rfl⟩

def labels (i : Fin 4) : ℚ := i.val

/-- The two old points are related at both levels. -/
def base : RationalPresentation :=
  ⟨{1, 3}, {(1, 1), (1, 3), (3, 3)}, {(1, 1), (1, 3), (3, 3)}⟩

/-- Downward second-level reflection adds `0`; its outgoing first-level
edges reach the old points, while its only second-level edge is reflexive. -/
def lower : RationalPresentation :=
  ⟨{0, 1, 3}, {(0, 0), (0, 1), (0, 3), (1, 1), (1, 3), (3, 3)},
    {(0, 0), (1, 1), (1, 3), (3, 3)}⟩

def downwardCode : ℕ :=
  Encodable.encode (⟨4, ⟨labels, CertificateExamples.downwardRule.source,
    CertificateExamples.downwardRule.target,
    Encodable.encode CertificateExamples.downwardRule⟩⟩ : RationalCertificate)

def downwardRequest : Request := ⟨lower, downwardCode⟩

def downwardIndex : ℕ := index 0 downwardRequest

theorem downward_code_accepts : base.checkRule lower downwardCode = true := by
  exact accepts_encoded_rule labels CertificateExamples.downwardRule base lower
    (by decide +kernel) (by unfold StrictMono; decide +kernel)
    (by decide +kernel) (by decide +kernel) CertificateExamples.downward_accepts

/-- Pairing recovers every part of a request and makes its source stage
available, without expanding the encoded certificate. -/
theorem scheduled_request_roundtrip (n : ℕ) :
    sourceIndex (index n downwardRequest) = n ∧
    n ≤ index n downwardRequest ∧
    decode (index n downwardRequest) = some downwardRequest ∧
    target (index n downwardRequest) = lower ∧
    ComputableRequests.check base (index n downwardRequest) = true := by
  refine ⟨sourceIndex_index n downwardRequest,
    Nat.left_le_pair n (Encodable.encode downwardRequest),
    decode_index n downwardRequest, target_index n downwardRequest, ?_⟩
  simpa only [check_index, downwardRequest] using downward_code_accepts

theorem scheduled_downward_accepts :
    ComputableRequests.check base downwardIndex = true :=
  (scheduled_request_roundtrip 0).2.2.2.2

/-- The first schedule entry is a genuinely failed request decode. -/
theorem malformed_schedule_zero : decode 0 = none := by
  decide +kernel

theorem malformed_request_preserves (P Q : RationalPresentation) : next P Q 0 = Q :=
  next_of_reject P Q 0 (check_of_decode_none P malformed_schedule_zero)

/-- This witness certifies a singleton at `0`, not the claimed target at `1`. -/
def wrongEndpointRequest : Request :=
  ⟨RationalCertificateExamples.wrongCarrier, RationalCertificateExamples.ruleCode⟩

theorem wrong_endpoint_rejected (n : ℕ) :
    ComputableRequests.check RationalCertificateExamples.singleton
      (index n wrongEndpointRequest) = false := by
  simpa only [check_index, wrongEndpointRequest] using
    RationalCertificateExamples.rule_rejects_wrong_carrier

/-- A nonempty-grid requirement is checked even for empty endpoints. -/
def zeroGridRequest : Request :=
  ⟨RationalCertificateExamples.emptyPresentation, RationalCertificateExamples.zeroCode⟩

theorem zero_grid_rejected (n : ℕ) :
    ComputableRequests.check RationalCertificateExamples.emptyPresentation
      (index n zeroGridRequest) = false := by
  simpa only [check_index, zeroGridRequest] using
    RationalCertificateExamples.rule_rejects_zero_grid

/-- Both extra edges are outside the carrier; rejection must preserve the
literal stored tables, not merely their induced finite structure. -/
def rawBase : RationalPresentation :=
  ⟨base.U, {(1, 1), (1, 3), (3, 3), (99, 98)},
    {(1, 1), (1, 3), (3, 3), (98, 99)}⟩

theorem rejected_request_preserves :
    next RationalCertificateExamples.singleton rawBase
      (index 4 wrongEndpointRequest) = rawBase :=
  next_of_reject _ _ _ (wrong_endpoint_rejected 4)

def first : RationalPresentation := (RationalPresentation.lift base lower base id).1

def second : RationalPresentation := (RationalPresentation.lift base lower first id).1

def expectedFirst : RationalPresentation :=
  ⟨{1 / 5, 1, 3},
    {(1 / 5, 1 / 5), (1 / 5, 1), (1 / 5, 3), (1, 1), (1, 3), (3, 3)},
    {(1 / 5, 1 / 5), (1, 1), (1, 3), (3, 3)}⟩

def expectedSecond : RationalPresentation :=
  ⟨{1 / 5, 9 / 25, 1, 3},
    {(1 / 5, 1 / 5), (1 / 5, 9 / 25), (1 / 5, 1), (1 / 5, 3),
      (9 / 25, 9 / 25), (9 / 25, 1), (9 / 25, 3), (1, 1), (1, 3), (3, 3)},
    {(1 / 5, 1 / 5), (9 / 25, 9 / 25), (1, 1), (1, 3), (3, 3)}⟩

/-- The second transition places its new point above the first transition's
new predecessor, and both complete relation tables are computed. -/
theorem two_lifts_compute : first = expectedFirst ∧ second = expectedSecond := by
  decide +kernel

theorem next_first : next base base downwardIndex = first := by
  rw [next_of_check base base downwardIndex scheduled_downward_accepts]
  simp only [downwardIndex, target_index, downwardRequest, first]

theorem next_second : next base first downwardIndex = second := by
  rw [next_of_check base first downwardIndex scheduled_downward_accepts]
  simp only [downwardIndex, target_index, downwardRequest, second]

/-- Dispatching the checked request twice gives two actual successive
transitions. Numeric encodings are eliminated by their proved equations. -/
theorem two_transition_regression :
    next base base downwardIndex = expectedFirst ∧
    next base (next base base downwardIndex) downwardIndex = expectedSecond := by
  rw [next_first, next_second]
  exact two_lifts_compute

/-- The checked and computed transitions form genuine generating steps,
so the finite computation is linked to the semantic generating calculus. -/
theorem two_transition_rules :
    Str.GeneratingRule base.toStr first.toStr ∧
    Str.GeneratingRule first.toStr second.toStr := by
  have hbase := (RationalPresentation.checkRule_sound downward_code_accepts).source_pattern
  have hE := (Str.GeneratingRule.refl hbase).continuous.inclusionEmbedding
  have hfirst := next_rule (k := downwardIndex) hbase hE
  rw [next_first] at hfirst
  have hsecond := next_rule (k := downwardIndex) hfirst.target_pattern
    hfirst.continuous.inclusionEmbedding
  rw [next_second] at hsecond
  exact ⟨hfirst, hsecond⟩

/-- Several malformed early schedule entries are evaluated through the
actual stage recursion, preserving even the initial off-carrier entries. -/
theorem early_stage_regression :
    stage rawBase 0 = rawBase ∧ stage rawBase 1 = rawBase ∧
    stage rawBase 4 = rawBase ∧ stage rawBase 8 = rawBase := by
  decide +kernel

/-- Bounded queries distinguish the two relation levels and exclude raw
off-carrier edges. A zero bound checks no stages. -/
theorem bounded_query_regression :
    containsBelow first (1 / 5) 0 = false ∧
    containsBelow first (1 / 5) 1 = true ∧
    containsBelow first 0 1 = false ∧
    relatesBelow first .one (1 / 5) 1 1 = true ∧
    relatesBelow first .two (1 / 5) 1 1 = false ∧
    relatesBelow first .two 1 3 1 = true ∧
    relatesBelow rawBase .one 99 98 1 = false ∧
    relatesBelow rawBase .two 98 99 1 = false := by
  decide +kernel

def empty : RationalPresentation := ⟨∅, ∅, ∅⟩

theorem empty_pattern : empty.toStr.IsPattern := by
  apply (Str.isPattern_iff_conditions empty.toStr).mpr
  simp [empty, RationalPresentation.toStr]

/-- An empty seed stays empty at every stage, as required by the bounded
generating calculus. This does not assume a finite cutoff for the schedule. -/
theorem empty_stage_carrier (n : ℕ) : (stage empty n).U = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  let S := toGeneratingSequence empty empty_pattern
  obtain ⟨a, ha, _⟩ := S.bounded 0 (S.mem_carrier n hx)
  exact Finset.notMem_empty a ha

/-- One audit entry point covers dispatch, rejection, two nontrivial
transitions, recursive stages, bounded limit queries, and the empty seed. -/
theorem regression_suite :
    decode 0 = none ∧
    ComputableRequests.check base downwardIndex = true ∧
    ComputableRequests.check RationalCertificateExamples.singleton
      (index 4 wrongEndpointRequest) = false ∧
    ComputableRequests.check RationalCertificateExamples.emptyPresentation
      (index 0 zeroGridRequest) = false ∧
    next RationalCertificateExamples.singleton rawBase
      (index 4 wrongEndpointRequest) = rawBase ∧
    next base base downwardIndex = expectedFirst ∧
    next base (next base base downwardIndex) downwardIndex = expectedSecond ∧
    stage rawBase 8 = rawBase ∧
    relatesBelow first .one (1 / 5) 1 1 = true ∧
    relatesBelow first .two (1 / 5) 1 1 = false ∧
    relatesBelow rawBase .one 99 98 1 = false ∧
    (∀ n, (stage empty n).U = ∅) :=
  ⟨malformed_schedule_zero, scheduled_downward_accepts,
    wrong_endpoint_rejected 4, zero_grid_rejected 0, rejected_request_preserves,
    two_transition_regression.1, two_transition_regression.2,
    early_stage_regression.2.2.2,
    bounded_query_regression.2.2.2.1, bounded_query_regression.2.2.2.2.1,
    bounded_query_regression.2.2.2.2.2.2.1, empty_stage_carrier⟩

end Alexander313.Carlson.Finite.ComputableFairSequenceExamples
