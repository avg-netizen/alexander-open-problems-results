import Alexander313.Effective.FormulaOperations
import Alexander313.Arithmetic.UniversalExecution

/-!
# Actual primitive-recursive formation of canonical arithmetic queries

The fresh-variable bound and literal shift are computed from the actual
argument syntax. The resulting code is exactly the hygienic template
member formula, for arbitrary arithmetic argument terms. Particular-code,
mechanicalness and knowledge-prefix formulas then have literal numerical
constructors. No arithmetic-correctness or syntax-effectivity contract is
introduced here.
-/

namespace Alexander313

namespace ArithmeticTemplate

def memberCode (body e x : Nat) : Nat :=
  let k := max (Term.variableBoundCode e) (Term.variableBoundCode x)
  EncodedSyntax.binary 7 k
    (EncodedSyntax.binary 3 (EncodedSyntax.binary 1 (EncodedSyntax.«variable» k) e)
      (EncodedSyntax.binary 7 (k + 1)
        (EncodedSyntax.binary 3 (EncodedSyntax.binary 1 (EncodedSyntax.«variable» (k + 1)) x)
          (Formula.shiftCode k body))))

theorem memberCode_primrec : Primrec (fun p : (Nat × Nat) × Nat =>
    memberCode p.1.1 p.1.2 p.2) := by
  have he : Primrec (fun p : (Nat × Nat) × Nat => p.1.2) := Primrec.snd.comp Primrec.fst
  have hx : Primrec (fun p : (Nat × Nat) × Nat => p.2) := Primrec.snd
  have hbody : Primrec (fun p : (Nat × Nat) × Nat => p.1.1) := Primrec.fst.comp Primrec.fst
  have hk := Primrec.nat_max.comp (Term.variableBoundCode_primrec.comp he)
    (Term.variableBoundCode_primrec.comp hx)
  have hnext := Primrec.succ.comp hk
  have hvar := EncodedSyntax.variable_primrec.comp hk
  have hvarnext := EncodedSyntax.variable_primrec.comp hnext
  have hshift := Formula.shiftCode_primrec.comp hk hbody
  have heq := (EncodedSyntax.binary_primrec 1).comp hvar he
  have heqnext := (EncodedSyntax.binary_primrec 1).comp hvarnext hx
  exact (EncodedSyntax.binary_primrec 7).comp hk
    ((EncodedSyntax.binary_primrec 3).comp heq
      ((EncodedSyntax.binary_primrec 7).comp hnext
        ((EncodedSyntax.binary_primrec 3).comp heqnext hshift)))

@[simp] theorem memberCode_eq (T : ArithmeticTemplate Nat) (e x : Term) :
    memberCode (T.body.code id) e.code x.code = (T.member e x).code id := by
  simp only [memberCode, member, base, Formula.code, Term.code,
    Term.variableBoundCode_code, Formula.shiftCode_code,
    EncodedSyntax.binary, EncodedSyntax.«variable», EncodedSyntax.node]

end ArithmeticTemplate

def canonicalTemplateCode : Nat := (universalExecutionTemplate Nat).body.code id

def canonicalMemberCode (e x : Nat) : Nat :=
  ArithmeticTemplate.memberCode canonicalTemplateCode e x

private theorem memberCode_fixed_body_primrec (body : Nat) :
    Primrec₂ (ArithmeticTemplate.memberCode body) :=
  (ArithmeticTemplate.memberCode_primrec.comp
    (((Primrec.const body).pair Primrec.fst).pair Primrec.snd)).to₂

theorem canonicalMemberCode_primrec : Primrec₂ canonicalMemberCode :=
  memberCode_fixed_body_primrec canonicalTemplateCode

@[simp] theorem canonicalMemberCode_eq (e x : Term) :
    canonicalMemberCode e.code x.code = ((canonicalArithmeticCoding Nat).member e x).code id :=
  (universalExecutionTemplate Nat).memberCode_eq e x

def canonicalNumeralQueryCode (e n : Nat) : Nat :=
  canonicalMemberCode (Term.numeralCode e) (Term.numeralCode n)

theorem canonicalNumeralQueryCode_primrec : Primrec₂ canonicalNumeralQueryCode :=
  canonicalMemberCode_primrec.comp (Term.numeralCode_primrec.comp Primrec.fst)
    (Term.numeralCode_primrec.comp Primrec.snd)

@[simp] theorem canonicalNumeralQueryCode_eq (e n : Nat) :
    canonicalNumeralQueryCode e n =
      ((canonicalArithmeticCoding Nat).member (Term.numeral e) (Term.numeral n)).code id := by
  simp only [canonicalNumeralQueryCode, Term.numeralCode_eq, canonicalMemberCode_eq]

def canonicalInputQueryCode (e x : Nat) : Nat :=
  canonicalMemberCode (Term.numeralCode e) (EncodedSyntax.«variable» x)

theorem canonicalInputQueryCode_primrec : Primrec₂ canonicalInputQueryCode :=
  canonicalMemberCode_primrec.comp (Term.numeralCode_primrec.comp Primrec.fst)
    (EncodedSyntax.variable_primrec.comp Primrec.snd)

@[simp] theorem canonicalInputQueryCode_eq (e x : Nat) :
    canonicalInputQueryCode e x =
      ((canonicalArithmeticCoding Nat).member (Term.numeral e) (.var x)).code id := by
  simp only [canonicalInputQueryCode, Term.numeralCode_eq,
    EncodedSyntax.variable_code, canonicalMemberCode_eq]

namespace EncodedSyntax

def equivalence (left right : Nat) : Nat :=
  binary 3 (binary 2 left right) (binary 2 right left)

theorem equivalence_primrec : Primrec₂ equivalence :=
  (binary_primrec 3).comp ((binary_primrec 2).comp Primrec.fst Primrec.snd)
    ((binary_primrec 2).comp Primrec.snd Primrec.fst)

@[simp] theorem equivalence_code (φ ψ : Formula Nat) :
    equivalence (φ.code id) (ψ.code id) = (Formula.iff φ ψ).code id := rfl

end EncodedSyntax

def particularCodeSentenceCode (j body input e : Nat) : Nat :=
  EncodedSyntax.binary 6 input (EncodedSyntax.equivalence
    (EncodedSyntax.binary 8 j body) (canonicalInputQueryCode e input))

theorem particularCodeSentenceCode_primrec : Primrec (fun p : ((Nat × Nat) × Nat) × Nat =>
    particularCodeSentenceCode p.1.1.1 p.1.1.2 p.1.2 p.2) := by
  have hj : Primrec (fun p : ((Nat × Nat) × Nat) × Nat => p.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hbody : Primrec (fun p : ((Nat × Nat) × Nat) × Nat => p.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hx : Primrec (fun p : ((Nat × Nat) × Nat) × Nat => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  exact (EncodedSyntax.binary_primrec 6).comp hx
    (EncodedSyntax.equivalence_primrec.comp ((EncodedSyntax.binary_primrec 8).comp hj hbody)
      (canonicalInputQueryCode_primrec.comp Primrec.snd hx))

@[simp] theorem particularCodeSentenceCode_eq (j : Nat) (φ : UnaryFormula Nat) (e : Nat) :
    particularCodeSentenceCode j (φ.body.code id) φ.input e =
      (codeSentence (canonicalArithmeticCoding Nat) j φ e).code id := by
  simp only [particularCodeSentenceCode, codeSentence, canonicalInputQueryCode_eq,
    Formula.iff, Formula.code, EncodedSyntax.equivalence, EncodedSyntax.binary,
    EncodedSyntax.node, id_eq]

def mechanicalSentenceCode (j body input : Nat) : Nat :=
  EncodedSyntax.binary 7 (input + 1) (EncodedSyntax.binary 6 input
    (EncodedSyntax.equivalence (EncodedSyntax.binary 8 j body)
      (canonicalMemberCode (EncodedSyntax.«variable» (input + 1)) (EncodedSyntax.«variable» input))))

theorem mechanicalSentenceCode_primrec : Primrec (fun p : (Nat × Nat) × Nat =>
    mechanicalSentenceCode p.1.1 p.1.2 p.2) := by
  have hj : Primrec (fun p : (Nat × Nat) × Nat => p.1.1) := Primrec.fst.comp Primrec.fst
  have hbody : Primrec (fun p : (Nat × Nat) × Nat => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hx : Primrec (fun p : (Nat × Nat) × Nat => p.2) := Primrec.snd
  have hnext := Primrec.succ.comp hx
  have hmember := canonicalMemberCode_primrec.comp
    (EncodedSyntax.variable_primrec.comp hnext) (EncodedSyntax.variable_primrec.comp hx)
  exact (EncodedSyntax.binary_primrec 7).comp hnext
    ((EncodedSyntax.binary_primrec 6).comp hx
      (EncodedSyntax.equivalence_primrec.comp ((EncodedSyntax.binary_primrec 8).comp hj hbody) hmember))

@[simp] theorem mechanicalSentenceCode_eq (j : Nat) (φ : UnaryFormula Nat) :
    mechanicalSentenceCode j (φ.body.code id) φ.input =
      (mechanicalSentence (canonicalArithmeticCoding Nat) j φ).code id := by
  simp only [mechanicalSentenceCode, mechanicalSentence, EncodedSyntax.variable_code,
    canonicalMemberCode_eq, Formula.iff, EncodedSyntax.equivalence,
    Formula.code, EncodedSyntax.binary, EncodedSyntax.node, id_eq]

def prefixCode (i n body : Nat) : Nat :=
  Nat.rec body (fun _ previous => EncodedSyntax.binary 8 i previous) n

theorem prefixCode_primrec : Primrec (fun p : (Nat × Nat) × Nat =>
    prefixCode p.1.1 p.2 p.1.2) :=
  Primrec.nat_rec Primrec.snd
    (((EncodedSyntax.binary_primrec 8).comp (Primrec.fst.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd)).to₂)

@[simp] theorem prefixCode_eq (i n : Nat) (φ : Formula Nat) :
    prefixCode i n (φ.code id) = (Formula.«prefix» i n φ).code id := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (EncodedSyntax.binary 8 i) ih

end Alexander313
