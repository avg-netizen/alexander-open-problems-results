import Alexander313.Carlson.RationalRecognition

/-!
# Computable scheduling of certified rational generating requests

A request supplies a finite rational target presentation and a natural-number
certificate for a generating rule. At time `k`, `Nat.unpair k` gives the
requested source-stage index and the encoded request. The first component
is at most `k`, so the requested source stage is already available. A failed
decode is rejected; a decoded request is accepted only by the existing total
rational generating-rule checker.

Pairing the source index with the encoding of a request schedules that exact
request at a definite time. Certificate completeness ensures that every rational
generating rule is eventually accepted at its source index. Arbitrary
off-carrier relations are covered through a finite presentation and an
identity isomorphism. Choosing that presentation occurs only in the
completeness proof; the scheduler's data operations use finite supplied data.
-/

namespace Alexander313.Carlson.Finite.ComputableRequests

/-- Finite untrusted data for a request from a specified earlier stage. -/
structure Request where
  target : RationalPresentation
  certificate : ℕ
  deriving DecidableEq, Encodable

/-- The source stage requested at time `k`. -/
def sourceIndex (k : ℕ) : ℕ := (Nat.unpair k).1

/-- Decode the request scheduled at time `k`. Failed encodings stay absent. -/
def decode (k : ℕ) : Option Request :=
  Encodable.decode (α := Request) (Nat.unpair k).2

/-- The requested finite target. A failed decode has an empty fallback;
`check` still rejects it, independently of the source presentation. -/
def target (k : ℕ) : RationalPresentation :=
  match decode k with
  | none => ⟨∅, ∅, ∅⟩
  | some r => r.target

/-- Check the scheduled request against the supplied source presentation.
This executes one total finite-certificate check, never an unbounded search. -/
def check (P : RationalPresentation) (k : ℕ) : Bool :=
  match decode k with
  | none => false
  | some r => P.checkRule r.target r.certificate

/-- The time at which the indicated source and finite request are scheduled. -/
def index (n : ℕ) (r : Request) : ℕ :=
  Nat.pair n (Encodable.encode r)

/-- Every scheduled source stage is available by the time of its request. -/
theorem sourceIndex_le (k : ℕ) : sourceIndex k ≤ k :=
  Nat.unpair_left_le k

@[simp] theorem sourceIndex_index (n : ℕ) (r : Request) :
    sourceIndex (index n r) = n := by
  simp only [sourceIndex, index, Nat.unpair_pair]

@[simp] theorem decode_index (n : ℕ) (r : Request) :
    decode (index n r) = some r := by
  simp only [decode, index, Nat.unpair_pair, Encodable.encodek]

@[simp] theorem target_index (n : ℕ) (r : Request) :
    target (index n r) = r.target := by
  simp only [target, decode_index]

/-- Encoded requests can be reasoned about symbolically, without reducing
their potentially large natural-number encodings. -/
@[simp] theorem check_index (P : RationalPresentation) (n : ℕ) (r : Request) :
    check P (index n r) = P.checkRule r.target r.certificate := by
  simp only [check, decode_index]

/-- Rejection of a malformed encoding does not depend on the source. -/
theorem check_of_decode_none (P : RationalPresentation) {k : ℕ}
    (h : decode k = none) : check P k = false := by
  simp only [check, h]

/-- A decoded request uses exactly its stored target and certificate. -/
theorem check_of_decode_some (P : RationalPresentation) {k : ℕ} {r : Request}
    (h : decode k = some r) : check P k = P.checkRule r.target r.certificate := by
  simp only [check, h]

/-- Acceptance includes both a successful decode and a valid certificate
for the supplied source and the decoded finite target. -/
theorem check_eq_true (P : RationalPresentation) (k : ℕ) :
    check P k = true ↔
      ∃ r : Request, decode k = some r ∧ P.checkRule r.target r.certificate = true := by
  cases h : decode k <;> simp [check, h]

/-- Every accepted request is a generating rule for the actual decoded
target presentation. -/
theorem check_sound {P : RationalPresentation} {k : ℕ} (h : check P k = true) :
    Str.GeneratingRule P.toStr (target k).toStr := by
  obtain ⟨r, hr, hc⟩ := (check_eq_true P k).mp h
  simpa only [target, hr] using RationalPresentation.checkRule_sound hc

/-- Every rule between supplied finite presentations has a scheduled
accepted certificate with exactly the requested target presentation. -/
theorem complete_presentation (P : RationalPresentation) (n : ℕ)
    (Q : RationalPresentation) (d : Str.GeneratingRule P.toStr Q.toStr) :
    ∃ k, sourceIndex k = n ∧ n ≤ k ∧ check P k = true ∧ target k = Q := by
  obtain ⟨certificate, hc⟩ := RationalPresentation.checkRule_complete d
  let r : Request := ⟨Q, certificate⟩
  refine ⟨index n r, sourceIndex_index n r,
    Nat.left_le_pair n (Encodable.encode r), ?_, target_index n r⟩
  simpa only [check_index] using hc

/-- Completeness includes every rational target structure, even with
arbitrary off-carrier relation values. Its scheduled finite presentation
is isomorphic by the identity and has exactly the same carrier. -/
theorem complete (P : RationalPresentation) (n : ℕ) (Q : Str ℚ)
    (d : Str.GeneratingRule P.toStr Q) :
    ∃ k, sourceIndex k = n ∧ n ≤ k ∧ check P k = true ∧
      Str.IsIso Q (target k).toStr id := by
  let Q' := RationalPresentation.encode Q
  have e : Str.IsIso Q Q'.toStr id := RationalPresentation.presentation_iso Q
  have d' : Str.GeneratingRule P.toStr Q'.toStr :=
    d.of_isIso (Str.IsIso.refl _) e (fun _ _ => rfl)
  obtain ⟨k, hn, hnk, hc, hQ⟩ := complete_presentation P n Q' d'
  refine ⟨k, hn, hnk, hc, ?_⟩
  rw [hQ]
  exact e

end Alexander313.Carlson.Finite.ComputableRequests
