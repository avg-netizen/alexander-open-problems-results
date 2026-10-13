import Alexander313.Wilken.HereditaryGlobalTrackingAssignmentBounds
import Alexander313.Wilken.HereditaryGlobalTrackingSequences

/-!
# The complete genuine global assignment returns independent trackers

Every actual finite-stage Definition3.24 branch satisfies the independently
defined Definition3.18 predicate. Source-zero relative outputs have their
actual first endpoint bound. Native relative outputs derive their genuine
source gap and every final cover. Endpoint and cancellation branches use
the real finite chain and independently executing extended mu. The exact
primitive-recursive recognizer accepts every output as a consequence.
Evaluation, inverses and order are separate. Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.GlobalTrackingSequences.Assignment

open GlobalAdditiveTracking
open GlobalAdditiveTracking.Source (baseWord level)
open AssignmentSupport AssignmentBounds
open NativeContext.SourceTrackingSequences (lastCode lastCode_mem lastCode_singleton
  stripLast_singleton)
open Hereditary.FinePredecessor (stripLast)

theorem sourceOneExecute_tracking (alpha : Nat) (codes : List Nat)
    (ho : codes ∈ Return.sourceOneExecute alpha) : Tracking codes := by
  have ht := RelativeCertificate.sourceOneExecute_tracking alpha codes ho
  have hb := (sourceOneExecute_bound alpha codes ho _ (lastCode_mem codes ht.1)).le
  have h := tracking_with_baseWord 0 codes ht (sourceOneExecute_gap alpha codes ho) hb
    (fun hn => False.elim (hn rfl))
  have hz : baseWord 0 = [] := rfl
  simpa only [hz, List.nil_append] using h

theorem nativeExecute_tracking (alpha : Nat) (codes : List Nat)
    (hn : level alpha ≠ 0) (ho : codes ∈ Return.nativeExecute alpha) :
    Tracking (baseWord (level alpha) ++ codes) := by
  have ht := RelativeCertificate.nativeExecute_tracking alpha codes ho
  exact tracking_with_baseWord _ codes ht (nativeExecute_gap alpha codes hn ho)
    (nativeExecute_bound alpha codes hn ho _ (lastCode_mem codes ht.1)).le
    (fun _ => nativeExecute_final_one_lt alpha codes ho)

theorem cancellationExecute_tracking (alpha quotient : Nat)
    (hi : Source.inputCheck alpha = true) (hn : level alpha ≠ 0)
    (ho : quotient ∈ Cancellation.execute (Source.endpointCode (level alpha)) alpha) :
    Tracking (baseWord (level alpha) ++ [quotient]) := by
  have hs := Cancellation.execute_spec _ _ quotient ho
  have ht := PublicTrackingSequences.singleton_tracking quotient hs.2.1
    (zero_lt_one.trans hs.2.2.1) hs.2.2.2.1 hs.2.2.1.le
  have hu := (PublicEpsilonSourceDictionary.level_bound alpha ((Source.inputCheck_exact alpha).mp hi).1).2.1
  have hb : unionInterpretation quotient ≤ sourceUpsilon ((level alpha + 1 : Nat) : Ordinal.{0}) :=
    (hs.2.2.2.2.2.trans_lt hu).le.trans_eq (PublicUpsilonSegment.successor_value _).symm
  apply tracking_with_baseWord _ [quotient] ht
  · rw [stripLast_singleton]; trivial
  · simpa only [lastCode_singleton] using hb
  · intro h
    simpa only [lastCode_singleton] using hs.2.2.1

/-- All source branch conditions, relative trackers, LOW bounds and
extended-mu callers are derived from the actual global execution. -/
theorem execute_tracking (alpha : Nat) (codes : List Nat)
    (ho : codes ∈ GlobalAdditiveTracking.execute alpha) : Tracking codes := by
  obtain ⟨hi, hclauses⟩ := GlobalAdditiveTracking.execute_clauses alpha codes ho
  rcases hclauses with ⟨hl, hc⟩ | ⟨hl, he, rfl⟩ |
    ⟨hl, hlt, hb, quotient, hq, rfl⟩ | ⟨hl, hb, tail, ht, rfl⟩
  · exact sourceOneExecute_tracking alpha codes hc
  · exact tracking_baseWord _ hl
  · exact cancellationExecute_tracking alpha quotient hi hl hq
  · exact nativeExecute_tracking alpha tail hl ht

theorem execute_trackingCheck (alpha : Nat) (codes : List Nat)
    (ho : codes ∈ GlobalAdditiveTracking.execute alpha) : trackingCheck codes = true :=
  (trackingCheck_exact codes).mpr (execute_tracking alpha codes ho)

theorem sourceClauses_tracking (alpha : Nat) (codes : List Nat)
    (hi : Source.inputCheck alpha = true) (hc : GlobalAdditiveTracking.SourceClauses alpha codes) :
    Tracking codes := execute_tracking alpha codes
      ((GlobalAdditiveTracking.execute_iff_clauses alpha codes).mpr ⟨hi, hc⟩)

theorem execute_returns_tracking (alpha : Nat) (hi : Source.inputCheck alpha = true) :
    ∃ codes, codes ∈ GlobalAdditiveTracking.execute alpha ∧ Tracking codes ∧ trackingCheck codes = true := by
  obtain ⟨codes, hc⟩ := GlobalAdditiveTracking.execute_returns alpha hi
  exact ⟨codes, hc, execute_tracking alpha codes hc, execute_trackingCheck alpha codes hc⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.GlobalTrackingSequences.Assignment
