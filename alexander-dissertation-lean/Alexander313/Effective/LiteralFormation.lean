import Alexander313.Effective.CanonicalFormation
import Alexander313.Effective.FormulaSubstitution
import Alexander313.Alexander.LiteralCoding

/-!
# Primitive-recursive operations on the actual typed source syntax

The literal `Primcodable` instances use the previously proved exact code
images. The numerical algorithms therefore certify the typed operations,
with the same codes used by the comparator and joint machine programs.
-/

namespace Alexander313

namespace Term

theorem variableBound_primrec : Primrec variableBound := by
  simpa only [variableBoundCode_code] using variableBoundCode_primrec.comp code_primrec

theorem numeral_primrec : Primrec numeral := by
  apply Primrec.encode_iff.1
  simpa only [encode_eq_code, numeralCode_eq] using
    (show Primrec (fun n => numeralCode n) from numeralCode_primrec)

theorem renameShift_primrec : Primrec (fun p : Nat × Term =>
    p.2.renameVariables (fun v => p.1 + v)) := by
  apply Primrec.encode_iff.1
  simpa only [encode_eq_code, shiftCode_code] using
    shiftCode_primrec.comp Primrec.fst (code_primrec.comp Primrec.snd)

theorem singleNumeralSubst_primrec : Primrec (fun p : (Nat × Nat) × Term =>
    p.2.subst (singleNumeralSubstitution p.1.1 p.1.2)) := by
  apply Primrec.encode_iff.1
  simpa only [encode_eq_code, substCode_code] using
    substCode_primrec.comp (Primrec.fst.pair (code_primrec.comp Primrec.snd))

end Term

namespace Formula

theorem renameShift_primrec : Primrec (fun p : Nat × Formula Nat =>
    p.2.renameVariables (fun v => p.1 + v)) := by
  apply Primrec.encode_iff.1
  simpa only [encode_eq_code, shiftCode_code] using
    shiftCode_primrec.comp Primrec.fst (code_primrec.comp Primrec.snd)

theorem singleNumeralSubst_primrec : Primrec (fun p : (Nat × Nat) × Formula Nat =>
    p.2.subst (singleNumeralSubstitution p.1.1 p.1.2)) := by
  apply Primrec.encode_iff.1
  simpa only [encode_eq_code, substCode_code] using
    substCode_primrec.comp (Primrec.fst.pair (code_primrec.comp Primrec.snd))

theorem prefix_primrec : Primrec (fun p : (Nat × Formula Nat) × Nat =>
    «prefix» p.1.1 p.2 p.1.2) := by
  apply Primrec.encode_iff.1
  have hp := prefixCode_primrec.comp
    (((Primrec.fst.comp Primrec.fst).pair
      (code_primrec.comp (Primrec.snd.comp Primrec.fst))).pair Primrec.snd)
  simpa only [encode_eq_code, prefixCode_eq] using hp

end Formula

theorem ArithmeticTemplate.member_primrec (T : ArithmeticTemplate Nat) :
    Primrec₂ T.member := by
  apply Primrec.encode_iff.1
  have hp := ArithmeticTemplate.memberCode_primrec.comp
    (((Primrec.const (T.body.code id)).pair (Term.code_primrec.comp Primrec.fst)).pair
      (Term.code_primrec.comp Primrec.snd))
  simpa only [Formula.encode_eq_code, ArithmeticTemplate.memberCode_eq] using hp

theorem canonicalArithmeticCoding_member_primrec :
    Primrec₂ (canonicalArithmeticCoding Nat).member :=
  (universalExecutionTemplate Nat).member_primrec

end Alexander313
