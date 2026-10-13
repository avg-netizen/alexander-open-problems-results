import Alexander313.Wilken.HereditaryPublicTrackingSequences

/-!
# Actual canonical public erasure and constructed omega extensions

The independent selected original-source mu is at least omega by its real
high-root caller. A genuine canonical omega code therefore extends every
relative public reference to a tracking sequence. Both directions of the
printed erasure characterization are derived, including the empty prefix.
No final code, mu bound or supplied tracker is an admission premise.
Global finite-upsilon prefixes and evaluation remain separate. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.PublicTrackingSequences

open SkPublicRecurrence (muValue mu_input_canonical)
open Hereditary.FinePredecessor (stripLast)
open NativeContext.SourceTrackingSequences (lastCode lastCode_mem lastCode_append_singleton
  stripLast_append_singleton)

/-- Every proper public predecessor has its true original high-root mu
caller, so its concrete public mu is at least omega. -/
theorem omega_le_muValue (a : Nat) (ha : MuPublicDictionary.Support.inputCheck a = true) :
    Ordinal.omega0 ≤ muValue a := by
  rw [muValue, (MuPublicDictionary.publicCode_spec a ha).2, MuPublicDictionary.Support.sourceValue]
  cases hb : PublicEpsilonSourceDictionary.level a == 0 with
  | true =>
    have hs := MuPublicDictionary.Support.source_one_root a ha (beq_iff_eq.mp hb)
    simpa only [hb, Bool.cond_true] using
      SourceOneIota.SourceTrackingSupport.omega_le_mu _ hs.1
  | false =>
    have hl : PublicEpsilonSourceDictionary.level a ≠ 0 := by
      intro he
      have ht : (PublicEpsilonSourceDictionary.level a == 0) = true := beq_iff_eq.mpr he
      rw [hb] at ht
      cases ht
    have hs := MuPublicDictionary.Support.native_root a ha hl
    simpa only [hb, Bool.cond_false] using
      NativeContext.SourceTrackingSequences.Support.omega_le_mu _ _ hs.1

def omegaCode : Nat := OmegaPowers.powerCode FinitePowers.oneCode

theorem omegaCode_spec : Canonical.check omegaCode = true ∧
    unionInterpretation omegaCode = Ordinal.omega0 := by
  have hc := Canonical.check_original FinitePowers.oneCode_checked
  refine ⟨OmegaPowers.powerCode_checked _ hc, ?_⟩
  rw [omegaCode, OmegaPowers.powerCode_value _ hc, FinitePowers.oneCode_value, Ordinal.opow_one]

/-- The final omega extension is a real computed canonical code; its mu
cover follows from the genuine selected-source root rather than a witness. -/
theorem Reference.omega_extension {xs : List Nat} (hr : Reference xs) :
    Tracking (xs ++ [omegaCode]) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.append_eq_nil_iff, List.cons_ne_nil, and_false, not_false_eq_true]
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact mu_input_canonical c (hr.nodes c hc)
    · simpa only [List.mem_singleton.mp hc] using omegaCode_spec.1
  · simpa only [stripLast_append_singleton] using hr
  · simpa only [lastCode_append_singleton, omegaCode_spec.2] using Ordinal.omega0_pos
  · simpa only [lastCode_append_singleton, omegaCode_spec.2] using Ordinal.isPrincipal_add_omega0
  · rw [stripLast_append_singleton, lastCode_append_singleton, omegaCode_spec.2]
    by_cases he : xs = []
    · rw [if_pos he]
      exact Ordinal.one_lt_omega0.le
    · rw [if_neg he]
      exact ⟨Ordinal.one_lt_omega0, omega_le_muValue _ (hr.nodes _ (lastCode_mem xs he))⟩

theorem tracking_erasure (codes : List Nat) (ht : trackingCheck codes = true) :
    referenceCheck (stripLast codes) = true :=
  (referenceCheck_exact _).mpr ((trackingCheck_exact _).mp ht).2.2.1

/-- Exact relative public source3.17 erasure, with a constructed omega
extension in the forward direction, including the empty reference. -/
theorem reference_erasure_iff (xs : List Nat) : referenceCheck xs = true ↔
    ∃ codes, trackingCheck codes = true ∧ stripLast codes = xs := by
  constructor
  · intro hr
    exact ⟨xs ++ [omegaCode],
      (trackingCheck_exact _).mpr ((referenceCheck_exact _).mp hr).omega_extension,
      stripLast_append_singleton _ _⟩
  · rintro ⟨codes, ht, he⟩
    simpa only [he] using tracking_erasure codes ht

end Alexander313.Wilken.RelativeTerm.Hereditary.PublicTrackingSequences
