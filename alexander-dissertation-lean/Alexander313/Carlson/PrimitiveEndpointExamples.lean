import Alexander313.Carlson.PrimitiveEndpointIso
import Alexander313.Carlson.RationalCertificateExamples

/-!
# Regression checks for primitive-recursive endpoint checks

The frame checks reuse the two-point grid of `RationalCertificateExamples`,
whose second grid point is unused by both endpoint carriers. They exercise
acceptance, stored off-carrier rational edges, a wrong target carrier, a
missing on-carrier source edge, and the global grid conditions. The
data-level checks show that a missing table entry reads as `false` and
that the data view agrees with the original isomorphism check.

The finite checks use ordinary kernel reduction. The machine regressions
instantiate the proved uniform specification without evaluating any
machine code.
-/

namespace Alexander313.Carlson.PrimitiveEndpointExamples

open Encodable Finite PrimitivePatternCode PrimitiveEndpointIso

set_option maxRecDepth 8192

/-- The accepted two-point rule witness, as a dependent certificate. -/
def ruleCertificate : RationalCertificate := ⟨2, RationalCertificateExamples.ruleWitness⟩

/-- The same witness with equal labels at both grid points. -/
def duplicateCertificate : RationalCertificate :=
  ⟨2, RationalCertificateExamples.duplicateWitness⟩

/-- The same witness with the unused grid point placed first. -/
def reversedCertificate : RationalCertificate :=
  ⟨2, RationalCertificateExamples.reversedUnusedWitness⟩

theorem frame_accepts :
    checkFrame ruleCertificate RationalCertificateExamples.singleton
      RationalCertificateExamples.singleton = true := by
  decide +kernel

/-- Stored off-carrier rational edges do not affect either endpoint check. -/
theorem frame_accepts_off_carrier_edges :
    checkFrame ruleCertificate RationalCertificateExamples.offCarrierEdges
      RationalCertificateExamples.offCarrierEdges = true := by
  decide +kernel

theorem frame_rejects_wrong_carrier :
    checkFrame ruleCertificate RationalCertificateExamples.singleton
      RationalCertificateExamples.wrongCarrier = false := by
  decide +kernel

theorem frame_rejects_missing_source_edge :
    checkFrame ruleCertificate RationalCertificateExamples.missingEdge
      RationalCertificateExamples.singleton = false := by
  decide +kernel

/-- Both endpoint isomorphisms hold here; only the whole-grid check fails. -/
theorem frame_rejects_grid :
    checkSource duplicateCertificate RationalCertificateExamples.singleton = true ∧
    checkTarget duplicateCertificate RationalCertificateExamples.singleton = true ∧
    checkFrame duplicateCertificate RationalCertificateExamples.singleton
      RationalCertificateExamples.singleton = false ∧
    checkSource reversedCertificate RationalCertificateExamples.singleton = true ∧
    checkFrame reversedCertificate RationalCertificateExamples.singleton
      RationalCertificateExamples.singleton = false := by
  decide +kernel

/-- A raw data view without tables reads every entry as `false`, so it cannot
match a presentation with an on-carrier edge; explicit `true` entries can. -/
theorem missing_table_regression :
    ¬ IsoData (({0}, [], []) : Data) [0] RationalCertificateExamples.singleton ∧
      IsoData (({0}, [[true]], [[true]]) : Data) [0]
        RationalCertificateExamples.singleton := by
  decide +kernel

/-- The data view of the two-point source agrees with the original check. -/
theorem dataView_regression :
    IsoData (dataView RationalCertificateExamples.point)
      (List.ofFn RationalCertificateExamples.labels) RationalCertificateExamples.singleton :=
  (isoData_dataView_iff _ _ _).mpr (by decide +kernel)

/-- One certified machine returns both answers of the frame check. -/
theorem frame_machine_regression : ∃ p : Nat.Partrec.Code,
    p.eval (encode (ruleCertificate, RationalCertificateExamples.singleton,
      RationalCertificateExamples.singleton)) = Part.some (encode true) ∧
    p.eval (encode (ruleCertificate, RationalCertificateExamples.singleton,
      RationalCertificateExamples.wrongCarrier)) = Part.some (encode false) := by
  obtain ⟨p, hp⟩ := frame_check_program
  refine ⟨p, ?_, ?_⟩
  · rw [hp, frame_accepts]
  · rw [hp, frame_rejects_wrong_carrier]

end Alexander313.Carlson.PrimitiveEndpointExamples
