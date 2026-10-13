import Alexander313.Carlson.PrimitiveDerivationRecognition
import Alexander313.Carlson.PrimitiveRecursiveCertificatesExamples
import Alexander313.Carlson.RationalCertificateExamples

/-! Kernel controls for recursive semantic verification and the total machines. -/

namespace Alexander313.Carlson.PrimitiveRecursiveChecksExamples

open Encodable Finite PrimitiveCertificateAlgebra PrimitiveRecursiveChecks

set_option maxRecDepth 8192

private def empty (n : ℕ) : PatternCode n := ⟨∅, fun _ _ => false, fun _ _ => false⟩
private def offCarrier : PatternCode 1 := ⟨∅, fun _ _ => true, fun _ _ => false⟩
private def point : PatternCode 1 := ⟨{0}, fun _ _ => true, fun _ _ => true⟩

theorem malformed_rule_child_rejected (n d a b s f : ℕ) :
    summarizeRule n (PrimitiveRecursiveCertificates.nodeCode 2
      [PrimitiveRecursiveCertificates.atomCode d, PrimitiveRecursiveCertificates.atomCode a,
       PrimitiveRecursiveCertificates.atomCode b, PrimitiveRecursiveCertificates.atomCode s,
       PrimitiveRecursiveCertificates.atomCode f]) = none := by
  simp only [summarizeRule,
    PrimitiveRecursiveCertificatesExamples.rejects_atom_rule_child, Option.map_none]

-- Prove the bridge with an arbitrary certificate, so regressions never reduce
-- the very large numeral denoted by a nested derived encoding.
private theorem rule_self_check {n : ℕ} (d : RuleCertificate n) :
    checkRule n (encode d.source) (encode d.target) (encode d) = d.check := by
  rw [checkRule_encode_endpoints]
  simp only [Finite.checkRule, Encodable.encodek, and_self, decide_true, Bool.and_true]

private theorem chain_self_check {n : ℕ} (c : ChainCertificate n) :
    checkChain n (encode c.source) (encode c.target) (encode c) = c.check := by
  rw [checkChain_encode_endpoints]
  simp only [Finite.checkChain, Encodable.encodek, and_self, decide_true, Bool.and_true]

private theorem generation_self_check {n : ℕ} (c : GenerationCertificate n) :
    PrimitiveGenerationChecks.checkGeneration n (encode c.source) (encode c.target)
      (encode c) = c.check := by
  rw [PrimitiveGenerationChecks.checkGeneration_encode_endpoints]
  simp only [Finite.checkGeneration, Encodable.encodek, and_self, decide_true, Bool.and_true]

theorem empty_bound_accepts_all_three :
    checkRule 0 (encode (empty 0)) (encode (empty 0))
      (encode (RuleCertificate.arithmetic (empty 0) (empty 0))) = true ∧
    checkChain 0 (encode (empty 0)) (encode (empty 0))
      (encode (ChainCertificate.refl (empty 0))) = true ∧
    PrimitiveGenerationChecks.checkGeneration 0 (encode (empty 0)) (encode (empty 0))
      (encode (⟨.refl (empty 0), empty 0⟩ : GenerationCertificate 0)) = true := by
  refine ⟨(rule_self_check (.arithmetic (empty 0) (empty 0))).trans ?_,
    (chain_self_check (.refl (empty 0))).trans ?_,
    (generation_self_check (⟨.refl (empty 0), empty 0⟩ : GenerationCertificate 0)).trans ?_⟩ <;> decide +kernel

theorem false_downward_has_exact_endpoints :
    let d : RuleCertificate 1 := .downward (empty 1) .one 0 0 ∅ ∅ id
    summarizeRule 1 (encode d) =
      some (encode (empty 1), encode ((empty 1).downward .one 0 0 ∅ id), false) := by
  change summarizeRule 1 (encode (RuleCertificate.downward (empty 1) .one 0 0 ∅ ∅ id)) = _
  have hc : (RuleCertificate.downward (empty 1) .one 0 0 ∅ ∅ id).check = false := by
    decide +kernel
  exact (summarizeRule_encode _).trans (by
    simp only [ruleSummary, RuleCertificate.source, RuleCertificate.target, hc])

theorem false_upward_child_conditions_rejected :
    let d : RuleCertificate 1 := .upward (.arithmetic (empty 1) (empty 1)) 0 0 ∅ id
    checkRule 1 (encode d.source) (encode d.target) (encode d) = false := by
  exact (rule_self_check (.upward (.arithmetic (empty 1) (empty 1)) 0 0 ∅ id)).trans (by decide +kernel)

theorem restriction_requires_new_point :
    let d : RuleCertificate 1 := .finiteRestriction (.refl point) point 0
    checkRule 1 (encode d.source) (encode d.target) (encode d) = false := by
  exact (rule_self_check (.finiteRestriction (.refl point) point 0)).trans (by decide +kernel)

theorem identity_lifting_accepted :
    let d : RuleCertificate 1 := .lifting (.arithmetic point point) point point id id
    checkRule 1 (encode point) (encode point) (encode d) = true := by
  exact (rule_self_check (.lifting (.arithmetic point point) point point id id)).trans (by decide +kernel)

theorem lifting_checks_recursive_child :
    let d : RuleCertificate 1 := .lifting
      (.downward (empty 1) .one 0 0 ∅ ∅ id) (empty 1) (empty 1) id id
    checkRule 1 (encode (empty 1)) (encode (empty 1)) (encode d) = false := by
  exact (rule_self_check (.lifting (.downward (empty 1) .one 0 0 ∅ ∅ id) (empty 1) (empty 1) id id)).trans (by decide +kernel)

theorem off_carrier_join_rejected :
    let c : ChainCertificate 1 := .tail (.refl (empty 1)) (.arithmetic offCarrier offCarrier)
    checkChain 1 (encode (empty 1)) (encode offCarrier) (encode c) = false := by
  exact (chain_self_check (.tail (.refl (empty 1)) (.arithmetic offCarrier offCarrier))).trans (by decide +kernel)

theorem nested_chain_and_generation_accepted :
    let d : RuleCertificate 1 := .lifting (.arithmetic point point) point point id id
    let c : ChainCertificate 1 := .tail (.tail (.refl point) d) (.arithmetic point point)
    checkChain 1 (encode point) (encode point) (encode c) = true ∧
    PrimitiveGenerationChecks.checkGeneration 1 (encode point) (encode point)
      (encode (⟨c, point⟩ : GenerationCertificate 1)) = true := by
  exact ⟨(chain_self_check (.tail (.tail (.refl point) (.lifting (.arithmetic point point) point point id id)) (.arithmetic point point))).trans (by decide +kernel),
    (generation_self_check (⟨(.tail (.tail (.refl point) (.lifting (.arithmetic point point) point point id id)) (.arithmetic point point)), point⟩ : GenerationCertificate 1)).trans (by decide +kernel)⟩

theorem generation_requires_source_carrier :
    PrimitiveGenerationChecks.checkGeneration 1 (encode point) (encode (empty 1))
      (encode (⟨.refl point, empty 1⟩ : GenerationCertificate 1)) = false := by
  exact (generation_self_check (⟨.refl point, empty 1⟩ : GenerationCertificate 1)).trans (by decide +kernel)

theorem rational_rule_machine_controls : ∃ machine : Nat.Partrec.Code,
    machine.eval (encode ((RationalCertificateExamples.singleton,
      RationalCertificateExamples.singleton), RationalCertificateExamples.ruleCode)) =
      Part.some (encode true) ∧
    machine.eval (encode ((RationalCertificateExamples.offCarrierEdges,
      RationalCertificateExamples.offCarrierEdges), RationalCertificateExamples.ruleCode)) =
      Part.some (encode true) ∧
    machine.eval (encode ((RationalCertificateExamples.singleton,
      RationalCertificateExamples.singleton), RationalCertificateExamples.duplicateCode)) =
      Part.some (encode false) ∧
    machine.eval (encode ((RationalCertificateExamples.singleton,
      RationalCertificateExamples.wrongCarrier), RationalCertificateExamples.ruleCode)) =
      Part.some (encode false) ∧
    machine.eval (encode ((RationalCertificateExamples.emptyPresentation,
      RationalCertificateExamples.emptyPresentation), RationalCertificateExamples.zeroCode)) =
      Part.some (encode false) ∧
    machine.eval (encode ((RationalCertificateExamples.emptyWithEdges,
      RationalCertificateExamples.emptyWithEdges), RationalCertificateExamples.positiveEmptyCode)) =
      Part.some (encode true) := by
  obtain ⟨machine, hm⟩ := PrimitiveDerivationRecognition.rational_rule_check_program
  refine ⟨machine, ?_⟩
  simp only [hm, RationalCertificateExamples.rule_accepts,
    RationalCertificateExamples.rule_accepts_off_carrier_edges,
    RationalCertificateExamples.rule_rejects_duplicate_unused_label,
    RationalCertificateExamples.rule_rejects_wrong_carrier,
    RationalCertificateExamples.rule_rejects_zero_grid,
    RationalCertificateExamples.rule_accepts_empty_carriers, and_self]

theorem rational_chain_generation_machine_controls :
    ∃ chainMachine generationMachine : Nat.Partrec.Code,
      chainMachine.eval (encode ((RationalCertificateExamples.singleton,
        RationalCertificateExamples.singleton), RationalCertificateExamples.chainCode)) =
        Part.some (encode true) ∧
      generationMachine.eval (encode ((RationalCertificateExamples.singleton,
        RationalCertificateExamples.singleton), RationalCertificateExamples.generationCode)) =
        Part.some (encode true) := by
  obtain ⟨chainMachine, hc⟩ := PrimitiveDerivationRecognition.rational_chain_check_program
  obtain ⟨generationMachine, hg⟩ := PrimitiveDerivationRecognition.rational_generation_check_program
  refine ⟨chainMachine, generationMachine, ?_, ?_⟩
  · rw [hc, RationalCertificateExamples.chain_accepts]
  · rw [hg, RationalCertificateExamples.generation_accepts]

end Alexander313.Carlson.PrimitiveRecursiveChecksExamples
