import Alexander313.Wilken.SourceOneNativeIotaInverse
import Alexander313.Effective.SourceOneIotaPrograms
import Alexander313.Computability

/-!
# Executing the genuine original source-one inverse

Every admitted alpha target code and the actual original high root supplies
an ORIGINAL admitted Normal restricted inverse. The true finite atom return,
raised theta construction and actual target normalizer are already proved.
A genuine Program now executes that primitive recursive producer. Complete
numerical graphs and primitive recursive fixed-root/output columns include
output zero. The actual forward Program accepts the returned inverse, and
its output has the ORIGINAL target value. This is the inverse of iota as an
order isomorphism, not arbitrary same-value base recoding. Uncompiled.
-/

namespace Alexander313.SourceOneIotaInverseProgram

open Wilken.RelativeTerm.Hereditary

/-- The exact original guard is evaluated before the literal finite fold. -/
def evaluation (query : Nat) : Part Nat :=
  cond (SourceOneIota.Inverse.inverseInput query.unpair.1 query.unpair.2)
    (Part.some (SourceOneIota.Inverse.inverseCode query.unpair.1 query.unpair.2)) Part.none

theorem evaluation_partrec : Partrec evaluation :=
  Partrec.cond (SourceOneIota.Inverse.inverseInput_primrec.comp Primrec.unpair).to_comp
    (SourceOneIota.Inverse.inverseCode_primrec.comp Primrec.unpair).to_comp.partrec Partrec.none

theorem program_exists : ∃ p : Program, ∀ query, p.eval query = evaluation query := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp evaluation_partrec)
  exact ⟨p, fun query => congrFun hp query⟩

noncomputable def program : Program := Classical.choose program_exists

theorem program_eval (a c : Nat) : program.eval (Nat.pair a c) =
    cond (SourceOneIota.Inverse.inverseInput a c) (Part.some (SourceOneIota.Inverse.inverseCode a c)) Part.none := by
  simpa only [evaluation, Nat.unpair_pair] using
    Classical.choose_spec program_exists (Nat.pair a c)

theorem program_domain (a c : Nat) : program.domain (Nat.pair a c) ↔
    SourceOneIota.Inverse.inverseInput a c = true := by
  rw [Program.domain, program_eval]
  cases h : SourceOneIota.Inverse.inverseInput a c <;> simp [h]

/-- Every admitted target code enters; target weak Normality is constructed
by the actual normalizer and is not a domain premise. -/
theorem program_domain_original (a c : Nat) : program.domain (Nat.pair a c) ↔
    SourceOneIota.rootCheck a = true ∧ NativeContext.checkCode (SourceOneIota.alphaCode a) c = true := by
  rw [program_domain]
  simp only [SourceOneIota.Inverse.inverseInput, Bool.and_eq_true]

theorem program_graph (a c out : Nat) : out ∈ program.eval (Nat.pair a c) ↔
    SourceOneIota.Inverse.inverseInput a c = true ∧ out = SourceOneIota.Inverse.inverseCode a c := by
  rw [program_eval]
  cases h : SourceOneIota.Inverse.inverseInput a c <;> simp [h]

/-- Every actual returned code is originally admitted, Normal and inside
the complete printed iota source-star domain. Forward evaluation has the
input target value; no original-source SAME-value assertion is made. -/
theorem program_iota_spec (a c out : Nat) (ho : out ∈ program.eval (Nat.pair a c)) :
    Theta.acceptedCode 0 out = true ∧ SourceOneIota.inputCheck a out = true ∧
      NativeContext.interpretation (SourceOneIota.alphaCode a) (SourceOneIota.literalCode a out) =
        NativeContext.interpretation (SourceOneIota.alphaCode a) c := by
  obtain ⟨hc, rfl⟩ := (program_graph a c out).mp ho
  exact SourceOneIota.Inverse.inverseCode_spec a c hc

/-- Two actual inverse outputs reflect the genuine target order. -/
theorem program_order (a c d out out' : Nat)
    (ho : out ∈ program.eval (Nat.pair a c))
    (ho' : out' ∈ program.eval (Nat.pair a d)) :
    interpretation 0 out < interpretation 0 out' ↔
      NativeContext.interpretation (SourceOneIota.alphaCode a) c <
        NativeContext.interpretation (SourceOneIota.alphaCode a) d := by
  have hc := program_iota_spec a c out ho
  have hd := program_iota_spec a d out' ho'
  have hi := SourceOneIota.literalCode_lt_iff a out out' hc.2.1 hd.2.1
  rw [hc.2.2, hd.2.2] at hi
  exact hi.symm

/-- The two ACTUAL Program executions compose. The forward numerical
result need not be the input spelling, but its target ordinal is identical. -/
theorem program_roundtrip (a c out : Nat) (ho : out ∈ program.eval (Nat.pair a c)) :
    SourceOneIota.literalCode a out ∈ (SourceOneIotaProgram.sourceColumn a).eval out ∧
      NativeContext.interpretation (SourceOneIota.alphaCode a) (SourceOneIota.literalCode a out) =
        NativeContext.interpretation (SourceOneIota.alphaCode a) c := by
  have hs := program_iota_spec a c out ho
  exact ⟨(SourceOneIotaProgram.sourceColumn_graph a out _).mpr ⟨hs.2.1, rfl⟩, hs.2.2⟩

noncomputable def sourceColumn (a : Nat) : Program := program.column a

theorem sourceColumn_primrec : Primrec sourceColumn :=
  Program.column_primrec.comp (Primrec.const program) Primrec.id

theorem sourceColumn_domain (a c : Nat) : (sourceColumn a).domain c ↔
    SourceOneIota.Inverse.inverseInput a c = true := by
  rw [sourceColumn, Program.column_domain]
  exact program_domain a c

theorem sourceColumn_graph (a c out : Nat) : out ∈ (sourceColumn a).eval c ↔
    SourceOneIota.Inverse.inverseInput a c = true ∧ out = SourceOneIota.Inverse.inverseCode a c := by
  rw [sourceColumn, Nat.Partrec.Code.eval_curry]
  exact program_graph a c out

theorem sourceColumn_iota_spec (a c out : Nat) (ho : out ∈ (sourceColumn a).eval c) :
    Theta.acceptedCode 0 out = true ∧ SourceOneIota.inputCheck a out = true ∧
      NativeContext.interpretation (SourceOneIota.alphaCode a) (SourceOneIota.literalCode a out) =
        NativeContext.interpretation (SourceOneIota.alphaCode a) c := by
  obtain ⟨hc, rfl⟩ := (sourceColumn_graph a c out).mp ho
  exact SourceOneIota.Inverse.inverseCode_spec a c hc

/-- The graph recognizer compares the output numeral even when it is zero. -/
def graphBool (query : Nat) : Bool :=
  SourceOneIota.Inverse.inverseInput query.unpair.1.unpair.1 query.unpair.1.unpair.2 &&
    (query.unpair.2 == SourceOneIota.Inverse.inverseCode query.unpair.1.unpair.1 query.unpair.1.unpair.2)

theorem graphBool_primrec : Primrec graphBool := by
  have hd : Primrec (fun query : Nat => query.unpair.1.unpair) :=
    Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)
  exact Primrec.and.comp (SourceOneIota.Inverse.inverseInput_primrec.comp hd)
    (Primrec.beq.comp (Primrec.snd.comp Primrec.unpair) (SourceOneIota.Inverse.inverseCode_primrec.comp hd))

def graphEvaluation (query : Nat) : Part Nat := cond (graphBool query) (Part.some 0) Part.none

theorem graphEvaluation_partrec : Partrec graphEvaluation :=
  Partrec.cond graphBool_primrec.to_comp (Computable.const 0).partrec Partrec.none

theorem graphProgram_exists : ∃ p : Program, ∀ query, p.eval query = graphEvaluation query := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp graphEvaluation_partrec)
  exact ⟨p, fun query => congrFun hp query⟩

noncomputable def graphProgram : Program := Classical.choose graphProgram_exists

theorem graphProgram_domain (a c out : Nat) :
    graphProgram.domain (Nat.pair (Nat.pair a c) out) ↔
      SourceOneIota.Inverse.inverseInput a c = true ∧ out = SourceOneIota.Inverse.inverseCode a c := by
  rw [Program.domain, Classical.choose_spec graphProgram_exists]
  simp only [graphEvaluation, graphBool, Nat.unpair_pair]
  cases h : SourceOneIota.Inverse.inverseInput a c <;> cases he : out == SourceOneIota.Inverse.inverseCode a c <;>
    simp [h, he, Bool.eq_iff_iff, beq_iff_eq] at *

noncomputable def graphColumn (a c : Nat) : Program := graphProgram.column (Nat.pair a c)

theorem graphColumn_primrec : Primrec₂ graphColumn :=
  Program.column_primrec.comp (Primrec.const graphProgram)
    (Primrec₂.natPair.comp Primrec.fst Primrec.snd)

theorem graphColumn_domain (a c out : Nat) : (graphColumn a c).domain out ↔
    out ∈ (sourceColumn a).eval c := by
  rw [graphColumn, Program.column_domain, graphProgram_domain, sourceColumn_graph]

end Alexander313.SourceOneIotaInverseProgram
