import Alexander313.Carlson.AmalgamationCertificates
import Mathlib.Data.Nat.Find

/-!
# Terminating search for actual finite amalgamations

The search tests natural codes in increasing order with the executable
certificate verifier. The proved existence of an accepted code supplies
termination for every finite family of pure patterns. Existence proofs are
erased from the executable computation; they do not select its output.
-/

namespace Alexander313.Carlson.Finite.ComputableAmalgamation

open AmalgamationCertificate

variable {n : ℕ}

/-- The first code accepted by the original finite amalgamation verifier. -/
def leastCode (P : Fin n → RationalPresentation) (hP : ∀ i, (P i).toStr.IsPattern) : ℕ :=
  Nat.find (AmalgamationCertificate.exists_code P hP)

theorem leastCode_check (P : Fin n → RationalPresentation)
    (hP : ∀ i, (P i).toStr.IsPattern) :
    checkCode P (leastCode P hP) = true :=
  Nat.find_spec (AmalgamationCertificate.exists_code P hP)

/-- The search never passes a supplied accepted witness. This bounds the
number of candidate tests, without assuming a uniform witness bound. -/
theorem leastCode_le {P : Fin n → RationalPresentation}
    (hP : ∀ i, (P i).toStr.IsPattern) {code : ℕ} (hc : checkCode P code = true) :
    leastCode P hP ≤ code :=
  Nat.find_min' (AmalgamationCertificate.exists_code P hP) hc

/-- A total fallback for decoded data. It is never selected by a valid
pattern-family search, since malformed codes are rejected by the checker. -/
def emptyCertificate (n : ℕ) : AmalgamationCertificate n :=
  (⟨∅, ∅, ∅⟩, fun _ => [], fun _ => 0)

/-- Decode the first accepted certificate. Every computation used here
is an executable operation on finite data and natural numbers. -/
def compute (P : Fin n → RationalPresentation) (hP : ∀ i, (P i).toStr.IsPattern) :
    AmalgamationCertificate n :=
  (Encodable.decode (leastCode P hP)).getD (emptyCertificate n)

theorem compute_check (P : Fin n → RationalPresentation)
    (hP : ∀ i, (P i).toStr.IsPattern) : (compute P hP).check P = true := by
  obtain ⟨c, hd, hc⟩ := (checkCode_eq_true P (leastCode P hP)).mp (leastCode_check P hP)
  simpa only [compute, hd, Option.getD_some] using hc

/-- The computed finite target and stored maps satisfy the original
embedding, union and exactness conditions of Definition 15.8. -/
theorem compute_amalgamation (P : Fin n → RationalPresentation)
    (hP : ∀ i, (P i).toStr.IsPattern) :
    Str.Amalgamation (fun i => (P i).toStr) (compute P hP).1.toStr
      (compute P hP).maps :=
  check_sound (compute_check P hP)

end Alexander313.Carlson.Finite.ComputableAmalgamation
