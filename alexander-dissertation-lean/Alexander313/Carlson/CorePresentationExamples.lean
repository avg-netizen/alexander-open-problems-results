import Alexander313.Carlson.EffectiveCorePackage

/-!
# Kernel controls for the effective common-core presentation

Small finite checks are evaluated by the kernel. Search-machine properties
are checked symbolically through their correctness proofs; enormous nested
amalgamation-certificate codes are never evaluated by `native_decide`.
-/

namespace Alexander313.Carlson.CorePresentationExamples

open Finite ComputablePointedPresentation CanonicalPointedCodes

/-- A distinguished point on a nonreflexive carrier is invalid. -/
def nonpattern : Data := (⟨{0}, ∅, ∅⟩, 0)

theorem nonpattern_rejected : ¬ ComputablePointedPresentation.Valid nonpattern := by decide

theorem nonpattern_replaced : data (Encodable.encode nonpattern) = fallback :=
  data_of_invalid nonpattern nonpattern_rejected

/-- The seed is a pattern, but its distinguished point is outside the carrier. -/
def offCarrierPoint : Data := (fallback.1, 1)

theorem offCarrierPoint_seed_valid : offCarrierPoint.1.checkPattern = true := by decide

theorem offCarrierPoint_rejected : ¬ ComputablePointedPresentation.Valid offCarrierPoint := by decide

theorem offCarrierPoint_replaced : data (Encodable.encode offCarrierPoint) = fallback :=
  data_of_invalid offCarrierPoint offCarrierPoint_rejected

/-- Patternhood alone is not enough for an empty pointed carrier either. -/
def emptyCarrier : Data := (⟨∅, ∅, ∅⟩, 0)

theorem emptyCarrier_seed_valid : emptyCarrier.1.checkPattern = true := by decide

theorem emptyCarrier_rejected : ¬ ComputablePointedPresentation.Valid emptyCarrier := by decide

theorem emptyCarrier_replaced : data (Encodable.encode emptyCarrier) = fallback :=
  data_of_invalid emptyCarrier emptyCarrier_rejected

/-- The original codec permits off-carrier edges. The new presentation must
preserve these stored tables instead of silently normalizing the codec. -/
def offCarrierEdges : Data := (⟨{0}, {(0, 0), (1, 0)}, {(0, 0), (2, 1)}⟩, 0)

theorem offCarrierEdges_valid : ComputablePointedPresentation.Valid offCarrierEdges := by decide

theorem offCarrierEdges_preserved : data (Encodable.encode offCarrierEdges) = offCarrierEdges := by
  simp only [data, rawData, Encodable.encodek, Option.getD_some, if_pos offCarrierEdges_valid]

theorem normalization_idempotent (n : ℕ) :
    representative (representative n) = representative n := representative_canonical n

theorem duplicate_normalization (m n : ℕ) (h : same m n = true) :
    representative m = representative n := (representative_eq_iff m n).mpr ((same_eq_true m n).mp h)

theorem zero_is_first : ComputableCoreEnumeration.enumerate 0 = 0 := rfl

theorem no_enumeration_duplicates (m n : ℕ) :
    (ComputableCoreEnumeration.compare m n).1 = true ↔ m = n :=
  ComputableCoreEnumeration.compare_eq_iff m n

theorem strict_self_rejects (n : ℕ) : EffectiveCorePackage.less n n = false := by
  cases h : EffectiveCorePackage.less n n with
  | false => rfl
  | true => exact (lt_irrefl _ ((EffectiveCorePackage.less_correct n n).mp h)).elim

theorem first_self_accepts (n : ℕ) : EffectiveCorePackage.first n n = true :=
  (EffectiveCorePackage.first_correct n n).mpr (R1_refl _)

theorem second_self_accepts (n : ℕ) : EffectiveCorePackage.second n n = true :=
  (EffectiveCorePackage.second_correct n n).mpr (R2_refl _)

/-- Positive recognition does not mistake a halting rejection for acceptance. -/
theorem false_program_has_empty_domain : ∃ machine : Program, ∀ n, ¬ machine.domain n := by
  obtain ⟨machine, hm⟩ := EffectiveCorePackage.recognizing_program (fun _ => false) (Computable.const false)
  exact ⟨machine, fun n h => Bool.noConfusion ((hm n).mp h)⟩

theorem true_program_has_full_domain : ∃ machine : Program, ∀ n, machine.domain n := by
  obtain ⟨machine, hm⟩ := EffectiveCorePackage.recognizing_program (fun _ => true) (Computable.const true)
  exact ⟨machine, fun n => (hm n).mpr rfl⟩

end Alexander313.Carlson.CorePresentationExamples
