import Alexander313.Wilken.HereditaryPublicTrackingSequencesSupport

/-!
# Actual public sk output has its genuine canonical tracking certificate

The complete public recurrence derives all independent mu callers. Actual
MNF truncation retains the genuine multiplicative cutoff greater than one,
giving its final positive principal and real cover. Every strict epsilon
continuation prepends a genuine reference entry. No tracker, assigned
sequence or evaluation is supplied. Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SkPublicRecurrence

open PublicTrackingSequences

/-- The maximal public recurrence itself derives the reference prefix and
all actual final-entry conditions at the genuine source3.33 cutoff. -/
theorem Path.tracking {cutoff : Nat} {codes : List Nat} (hp : Path cutoff codes)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation cutoff))
    (hone : 1 < unionInterpretation cutoff) : PublicTrackingSequences.Tracking codes := by
  induction hp with
  | stop a ha hs =>
    have he := mu_input_epsilon a ha
    have hb := EpsilonOffsets.epsilon_one_lt he
    have hprincipal : Ordinal.IsPrincipal (· + ·) (unionInterpretation a) := by
      rw [← he]
      exact Ordinal.isPrincipal_add_omega0_opow _
    exact singleton_tracking a (mu_input_canonical a ha)
      (zero_lt_one.trans hb) hprincipal hb.le
  | nextStop a d ha hd he hv hs =>
    have hmu := muValue_positive_principal a ha
    have ht := MultiplicativeFactorTruncation.truncate_pos_principal (muValue a) (unionInterpretation cutoff)
    have hb := MultiplicativeFactorTruncation.truncate_ge_source hmu.1 hmu.2 hm hone he
    have hc := MultiplicativeFactorTruncation.truncate_le hmu.1 hmu.2 (unionInterpretation cutoff)
    exact pair_tracking a d ha hd
      (by rw [hv]; exact ht.1) (by rw [hv]; exact ht.2)
      (hone.trans_le (by rw [hv]; exact hb)) (by rw [hv]; exact hc)
  | nextContinue a b xs ha hb he hv hab ht ih =>
    have hmu := muValue_positive_principal a ha
    have hcover : unionInterpretation b ≤ muValue a := by
      rw [hv]
      exact MultiplicativeFactorTruncation.truncate_le hmu.1 hmu.2 (unionInterpretation cutoff)
    exact tracking_prepend a b xs ha hab hcover
      (EpsilonOffsets.epsilon_one_lt (mu_input_epsilon b hb)) ih

/-- The independently terminating canonical public producer realizes a
genuine relative TS certificate on precisely the printed multiplicative
cutoff domain, without an output tracking premise. -/
theorem execute_tracking (gamma cutoff : Nat) (codes : List Nat)
    (ho : codes ∈ SkPublicDictionary.execute (gamma, cutoff))
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation cutoff))
    (hone : 1 < unionInterpretation cutoff) : PublicTrackingSequences.Tracking codes :=
  (execute_path gamma cutoff codes ho).tracking hm hone

theorem execute_reference (gamma cutoff : Nat) (codes : List Nat)
    (ho : codes ∈ SkPublicDictionary.execute (gamma, cutoff))
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation cutoff))
    (hone : 1 < unionInterpretation cutoff) :
    PublicTrackingSequences.Reference (Hereditary.FinePredecessor.stripLast codes) :=
  (execute_tracking gamma cutoff codes ho hm hone).2.2.1

theorem execute_reference_strict (gamma cutoff : Nat) (codes : List Nat)
    (ho : codes ∈ SkPublicDictionary.execute (gamma, cutoff))
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation cutoff))
    (hone : 1 < unionInterpretation cutoff) :
    ((Hereditary.FinePredecessor.stripLast codes).map unionInterpretation).Pairwise (· < ·) :=
  (execute_reference gamma cutoff codes ho hm hone).strict

end Alexander313.Wilken.RelativeTerm.Hereditary.SkPublicRecurrence
