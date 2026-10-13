import Alexander313.Carlson.PrimitiveCertificateAlgebra

/-! Exact original endpoint/check equations for every certificate constructor. -/

namespace Alexander313.Carlson.PrimitiveCertificateAlgebra

open Encodable Finite
open PrimitiveContinuityChecks (level)

def ruleSummary {n : ℕ} (d : RuleCertificate n) : Summary :=
  (encode d.source, encode d.target, d.check)

def chainSummary {n : ℕ} (c : ChainCertificate n) : Summary :=
  (encode c.source, encode c.target, c.check)

theorem arithmetic_encode {n : ℕ} (P Q : PatternCode n) :
    arithmetic n (encode P) (encode Q) = ruleSummary (.arithmetic P Q) := by
  simp [arithmetic, ruleSummary, RuleCertificate.source, RuleCertificate.target,
    RuleCertificate.check, PatternCode.checkPattern, PatternCode.checkSub,
    carrier_eq_iff, Bool.and_assoc]

theorem downward_encode {n : ℕ} (P : PatternCode n) (k : Lvl) (a b : Fin n)
    (X N : Finset (Fin n)) (g : Fin n → Fin n) :
    downward n (encode P) (encode k) (encode a) (encode b) (encode X) (encode N) (encode g) =
      ruleSummary (.downward P k a b X N g) := by
  cases k <;>
    simp [downward, ruleSummary, RuleCertificate.source, RuleCertificate.target,
      RuleCertificate.check, PatternCode.checkDownward, level,
      show encode Lvl.one = 2 from rfl, show encode Lvl.two = 6 from rfl]

theorem upward_encode {n : ℕ} (d : RuleCertificate n) (a b : Fin n)
    (N : Finset (Fin n)) (g : Fin n → Fin n) :
    upward n (ruleSummary d) (encode a) (encode b) (encode N) (encode g) =
      ruleSummary (.upward d a b N g) := by
  simp [upward, ruleSummary, RuleCertificate.source, RuleCertificate.target,
    RuleCertificate.check, PatternCode.checkUpward]

theorem restriction_encode {n : ℕ} (c : ChainCertificate n) (Q : PatternCode n) (a : Fin n) :
    restriction n (chainSummary c) (encode Q) (encode a) =
      ruleSummary (.finiteRestriction c Q a) := by
  simp [restriction, ruleSummary, chainSummary, RuleCertificate.source, RuleCertificate.target,
    RuleCertificate.check, PatternCode.checkSub, PatternCode.checkExtensionAt]

theorem lifting_encode {n : ℕ} (d : RuleCertificate n) (Q Qplus : PatternCode n)
    (h f : Fin n → Fin n) :
    lifting n (ruleSummary d) (encode Q) (encode Qplus) (encode h) (encode f) =
      ruleSummary (.lifting d Q Qplus h f) := by
  simp [lifting, ruleSummary, RuleCertificate.source, RuleCertificate.target,
    RuleCertificate.check, PatternCode.checkEmbedding, PatternCode.checkLifting,
    PatternCode.checkMinimal, Bool.and_assoc]

theorem refl_encode {n : ℕ} (P : PatternCode n) :
    refl n (encode P) = chainSummary (.refl P) := by
  simp [refl, chainSummary, ChainCertificate.source, ChainCertificate.target,
    ChainCertificate.check, PatternCode.checkPattern]

theorem tail_encode {n : ℕ} (c : ChainCertificate n) (d : RuleCertificate n) :
    tail (chainSummary c) (ruleSummary d) = chainSummary (.tail c d) := by
  simp [tail, chainSummary, ruleSummary, ChainCertificate.source,
    ChainCertificate.target, ChainCertificate.check, encode_inj]
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]

end Alexander313.Carlson.PrimitiveCertificateAlgebra
