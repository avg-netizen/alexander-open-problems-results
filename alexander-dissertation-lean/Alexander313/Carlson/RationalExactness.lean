import Alexander313.Carlson.RationalRecognition
import Alexander313.Carlson.Exactness
import Alexander313.Carlson.DenseGenerationTransport

/-!
# Executable recognition of exact rational subpatterns

Definition 15.5 uses generation of the initial span and its 1-correctness
in the target. The span is computed by filtering a finite rational carrier.
For that initial subcarrier, correctness is exactly the absence of first
relation edges crossing its boundary. The generation check uses the
original natural-number rational certificate and its original decoder.

Every check is total. Existential acceptance is equivalent to actual
exactness; an unsuccessful unbounded search is not claimed to terminate.
Stored relation entries outside a restricted carrier are retained and
remain irrelevant to all carrier-sensitive semantic checks.
-/

namespace Alexander313.Carlson.Finite.RationalPresentation

/-- Restrict the finite carrier while preserving the original edge tables. -/
def restrict (Q : RationalPresentation) (U : Finset ℚ) : RationalPresentation :=
  ⟨U, Q.r₁, Q.r₂⟩

@[simp] theorem restrict_U (Q : RationalPresentation) (U : Finset ℚ) :
    (Q.restrict U).U = U := rfl

@[simp] theorem toStr_restrict (Q : RationalPresentation) (U : Finset ℚ) :
    (Q.restrict U).toStr = Q.toStr.restrict U := rfl

/-- Compute the initial span, including the empty source carrier. -/
def initialSpan (Q : RationalPresentation) (U : Finset ℚ) : RationalPresentation :=
  Q.restrict (Q.U.filter (fun x => ∃ p ∈ U, x ≤ p))

@[simp] theorem toStr_initialSpan (Q : RationalPresentation) (U : Finset ℚ) :
    (Q.initialSpan U).toStr = Q.toStr.initialSpan U := rfl

@[simp] theorem mem_initialSpan {Q : RationalPresentation} {U : Finset ℚ} {x : ℚ} :
    x ∈ (Q.initialSpan U).U ↔ x ∈ Q.U ∧ ∃ p ∈ U, x ≤ p := by
  simp [initialSpan]

@[simp] theorem initialSpan_empty (Q : RationalPresentation) :
    Q.initialSpan ∅ = Q.restrict ∅ := by
  simp [initialSpan]

set_option synthInstance.maxSize 1024 in
/-- Decide the eight original finite pattern axioms on a rational carrier. -/
instance instDecidableToStrIsPattern (Q : RationalPresentation) : Decidable Q.toStr.IsPattern :=
  decidable_of_iff _ (Str.isPattern_iff_conditions Q.toStr).symm

def checkPattern (Q : RationalPresentation) : Bool := decide Q.toStr.IsPattern

@[simp] theorem checkPattern_eq_true (Q : RationalPresentation) :
    Q.checkPattern = true ↔ Q.toStr.IsPattern := by
  simp only [checkPattern, decide_eq_true_eq]

/-- A finite check of the original initial-span 1-correctness obligation. -/
def checkInitialSpanCorrect (Q : RationalPresentation) (U : Finset ℚ) : Bool :=
  decide (∀ x ∈ (Q.initialSpan U).U, ∀ y ∈ Q.U,
    Q.toStr.r₁ x y → y ∈ (Q.initialSpan U).U)

@[simp] theorem checkInitialSpanCorrect_eq_true (Q : RationalPresentation) (U : Finset ℚ) :
    Q.checkInitialSpanCorrect U = true ↔
      Str.KCorrect (Q.toStr.initialSpan U) Q.toStr .one := by
  rw [Str.initialSpan_correct_iff]
  simp only [checkInitialSpanCorrect, decide_eq_true_eq, ← toStr_initialSpan, toStr_U]

/-- Recognize exactness with the original generation certificate code. -/
def checkExact (P Q : RationalPresentation) (code : ℕ) : Bool :=
  Q.checkPattern && checkGeneration P (Q.initialSpan P.U) code &&
    Q.checkInitialSpanCorrect P.U

@[simp] theorem checkExact_eq_true (P Q : RationalPresentation) (code : ℕ) :
    checkExact P Q code = true ↔ Q.toStr.IsPattern ∧
      checkGeneration P (Q.initialSpan P.U) code = true ∧
      Str.KCorrect (Q.toStr.initialSpan P.U) Q.toStr .one := by
  simp only [checkExact, Bool.and_eq_true, checkPattern_eq_true,
    checkInitialSpanCorrect_eq_true, and_assoc]

/-- Soundness for the original `Str.Exact`, not a substitute predicate. -/
theorem checkExact_sound {P Q : RationalPresentation} {code : ℕ}
    (h : checkExact P Q code = true) : Str.Exact P.toStr Q.toStr := by
  obtain ⟨hQ, hd, hc⟩ := (checkExact_eq_true P Q code).mp h
  exact ⟨hQ, by simpa only [toStr_initialSpan, toStr_U] using checkGeneration_sound hd, hc⟩

/-- Every exact rational subpattern has an accepted original generation code. -/
theorem checkExact_complete {P Q : RationalPresentation} (d : Str.Exact P.toStr Q.toStr) :
    ∃ code, checkExact P Q code = true := by
  obtain ⟨code, hc⟩ := checkGeneration_complete
    (show Str.Generates P.toStr (Q.initialSpan P.U).toStr from d.generates)
  exact ⟨code, (checkExact_eq_true P Q code).mpr ⟨d.pattern, hc, d.correct⟩⟩

/-- Exact certificate recognition, with no coveredness assumption. -/
theorem exact_iff_exists_code (P Q : RationalPresentation) :
    Str.Exact P.toStr Q.toStr ↔ ∃ code, checkExact P Q code = true :=
  ⟨checkExact_complete, fun ⟨_, h⟩ => checkExact_sound h⟩

/-- Every raw input retains the original dependent rational decoder. -/
theorem checkExact_decoded_iff (P Q : RationalPresentation) (code : ℕ) :
    checkExact P Q code = true ↔ ∃ c : RationalCertificate,
      Encodable.decode code = some c ∧ Q.toStr.IsPattern ∧
      c.2.check (fun C D k => @Finite.checkGeneration c.1 C D k)
        P (Q.initialSpan P.U) = true ∧
      Str.KCorrect (Q.toStr.initialSpan P.U) Q.toStr .one := by
  rw [checkExact_eq_true, checkGeneration, checkCertificate_eq_true]
  constructor
  · rintro ⟨hQ, ⟨c, hd, hc⟩, hcorrect⟩
    exact ⟨c, hd, hQ, hc, hcorrect⟩
  · rintro ⟨c, hd, hQ, hc, hcorrect⟩
    exact ⟨hQ, ⟨c, hd, hc⟩, hcorrect⟩

/-- Checking an encoded witness avoids reducing its potentially large
numeric code and preserves the original common-grid check exactly. -/
@[simp] theorem checkExact_encode (P Q : RationalPresentation) (c : RationalCertificate) :
    checkExact P Q (Encodable.encode c) =
      (Q.checkPattern &&
        c.2.check (fun C D k => @Finite.checkGeneration c.1 C D k)
          P (Q.initialSpan P.U) && Q.checkInitialSpanCorrect P.U) := by
  unfold checkExact checkGeneration
  rw [checkCertificate_encode]

/-- Malformed outer certificates are rejected regardless of the endpoint data. -/
theorem checkExact_decode_none (P Q : RationalPresentation) (code : ℕ)
    (hd : Encodable.decode (α := RationalCertificate) code = none) :
    checkExact P Q code = false := by
  simp only [checkExact, checkGeneration, checkCertificate, hd, Bool.and_false,
    Bool.false_and]

/-- Finite presentations preserve exactness even when the original
structures have arbitrary propositional values away from their carriers. -/
theorem exact_iff_encoded_code (P Q : Str ℚ) :
    Str.Exact P Q ↔ ∃ code, checkExact (encode P) (encode Q) code = true := by
  classical
  constructor
  · intro d
    exact checkExact_complete
      (d.of_rational_isos (presentation_iso P) (presentation_iso Q) (fun _ _ => rfl))
  · intro h
    have d := (exact_iff_exists_code (encode P) (encode Q)).mpr h
    exact d.of_rational_isos (presentation_iso P).symm_id
      (presentation_iso Q).symm_id (fun _ _ => rfl)

end Alexander313.Carlson.Finite.RationalPresentation
