import Alexander313.Wilken.HereditaryFactorTruncation
import Alexander313.Wilken.HereditarySourceZetaTransport
import Alexander313.Wilken.SourceOneNativeMultiplicativePrincipal
import Alexander313.Wilken.MultiplicativeFactorRemoval

/-!
# Actual public MNF prefix producer for original source-one return

The actual canonical principal logarithm and coefficient word supply the
retained exponent prefix. Genuine canonical addition and omega power form
its ordered product. The last factor is the actual finite MNF producer.
Return to original check0 requires a bound derived by the consumer; no
Native base-one grammar or assigned factorization is used. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.FactorSupport

open Hereditary.FinePredecessor (stripLast stripLast_primrec stripLast_mem)
open Alexander313.Wilken.MultiplicativeNormalForm

/-- Retain precisely the original canonical logarithm's proper ANF prefix. -/
def prefixPublicCode (d : Nat) : Nat := OmegaPowers.powerCode
  (FactorTruncation.sumCodes (stripLast (CanonicalCoefficients.word d)))

theorem prefixPublicCode_primrec : Primrec prefixPublicCode :=
  OmegaPowers.powerCode_primrec.comp
    (FactorTruncation.sumCodes_primrec.comp (stripLast_primrec.comp CanonicalCoefficients.word_primrec))

theorem prefixPublicCode_spec (d : Nat) (hd : unionCheck d = true) :
    Canonical.check (prefixPublicCode d) = true ∧
      unionInterpretation (prefixPublicCode d) =
        factorProduct (factorPrefix (omegaFactors (unionInterpretation d))) := by
  have hs := FactorTruncation.sumCodes_spec (stripLast (CanonicalCoefficients.word d))
    (fun a ha => Canonical.check_original
      (CanonicalCoefficients.word_head_spec d hd a (stripLast_mem _ _ ha)).1)
  refine ⟨OmegaPowers.powerCode_checked _ (Canonical.check_original hs.1), ?_⟩
  rw [prefixPublicCode, OmegaPowers.powerCode_value _ (Canonical.check_original hs.1), hs.2,
    omegaFactors, ← CanonicalCoefficients.word_anf d hd]
  simp only [factorPrefix, stripLast, List.map_reverse, List.map_tail]
  exact (factorProduct_omega_map _).symm

abbrev lastPublicCode := MultiplicativeNormalForm.lastFactorCode

theorem lastPublicCode_primrec : Primrec lastPublicCode :=
  MultiplicativeNormalForm.lastFactorCode_primrec

theorem lastPublicCode_spec (d : Nat) (hd : unionCheck d = true) :
    Canonical.check (lastPublicCode d) = true ∧
      unionInterpretation (lastPublicCode d) = lastFactor (omegaFactors (unionInterpretation d)) := by
  refine ⟨MultiplicativeNormalForm.lastFactorCode_checked d hd, ?_⟩
  rw [lastPublicCode, MultiplicativeNormalForm.lastFactorCode_value,
    MultiplicativeNormalForm.factorWord_values d hd]

def prefixCode (d : Nat) : Nat := SourceZeta.Transport.returnCode 0 (prefixPublicCode d)

def lastCode (d : Nat) : Nat := SourceZeta.Transport.returnCode 0 (lastPublicCode d)

theorem prefixCode_primrec : Primrec prefixCode :=
  SourceZeta.Transport.returnCode_primrec.comp (Primrec.const 0) prefixPublicCode_primrec

theorem lastCode_primrec : Primrec lastCode :=
  SourceZeta.Transport.returnCode_primrec.comp (Primrec.const 0) lastPublicCode_primrec

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.FactorSupport
