import Alexander313.Wilken.SourceOneNativeIotaOrder
import Alexander313.Computability

/-!
# Programs on the genuine original source-one iota domain

The partial numerical function tests the actual original source-one root,
source admission, weak Normality and complete principal restriction. It
executes the actual finite syntax transform. Its output is admitted and
Normal in the actual alpha context; its order and written-height claims
are inherited from the derived semantic construction. Rejected inputs
are outside the Program domain, and output zero is included in its complete
graph. Every fixed-root column and numerical output-graph column has a
primitive recursive compiler. No source-base-one epsilon parser or supplied
Program/caller/semantic correctness interface occurs. Uncompiled.
-/

namespace Alexander313.SourceOneIotaProgram

open Wilken.RelativeTerm.Hereditary

/-- The exact original guard is evaluated before the literal finite fold. -/
def evaluation (query : Nat) : Part Nat :=
  cond (SourceOneIota.inputCheck query.unpair.1 query.unpair.2)
    (Part.some (SourceOneIota.literalCode query.unpair.1 query.unpair.2)) Part.none

theorem evaluation_partrec : Partrec evaluation :=
  Partrec.cond (SourceOneIota.inputCheck_primrec.comp Primrec.unpair).to_comp
    (SourceOneIota.literalCode_primrec.comp Primrec.unpair).to_comp.partrec Partrec.none

theorem program_exists : ∃ p : Program, ∀ query, p.eval query = evaluation query := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp evaluation_partrec)
  exact ⟨p, fun query => congrFun hp query⟩

noncomputable def program : Program := Classical.choose program_exists

theorem program_eval (a c : Nat) : program.eval (Nat.pair a c) =
    cond (SourceOneIota.inputCheck a c) (Part.some (SourceOneIota.literalCode a c)) Part.none := by
  simpa only [evaluation, Nat.unpair_pair] using
    Classical.choose_spec program_exists (Nat.pair a c)

theorem program_domain (a c : Nat) : program.domain (Nat.pair a c) ↔
    SourceOneIota.inputCheck a c = true := by
  rw [Program.domain, program_eval]
  cases h : SourceOneIota.inputCheck a c <;> simp [h]

/-- No malformed or unrestricted original source code enters this domain.
Every accepted ORIGINAL guard enters, independently of its output numeral. -/
theorem program_domain_original (a c : Nat) : program.domain (Nat.pair a c) ↔
    ∃ t : Wilken.RelativeTerm Nat, SourceOneIota.rootCheck a = true ∧ c = t.code ∧
      check 0 t = true ∧ Theta.Normal 0 t ∧
        SourceOneIota.sourceStar t < interpretation 0 a := by
  rw [program_domain, SourceOneIota.inputCheck_exact]
  constructor
  · rintro ⟨ha, t, hc, ht, hn, hs⟩
    exact ⟨t, ha, hc, ht, hn, hs⟩
  · rintro ⟨t, ha, hc, ht, hn, hs⟩
    exact ⟨ha, t, hc, ht, hn, hs⟩

theorem program_graph (a c out : Nat) : out ∈ program.eval (Nat.pair a c) ↔
    SourceOneIota.inputCheck a c = true ∧ out = SourceOneIota.literalCode a c := by
  rw [program_eval]
  cases h : SourceOneIota.inputCheck a c <;> simp [h]

theorem program_accepted (a c out : Nat) (ho : out ∈ program.eval (Nat.pair a c)) :
    NativeContext.Comparison.acceptedCode (SourceOneIota.alphaCode a) out = true := by
  obtain ⟨hc, rfl⟩ := (program_graph a c out).mp ho
  exact SourceOneIota.literalCode_accepted a c hc

theorem program_height (a c out : Nat) (ho : out ∈ program.eval (Nat.pair a c)) :
    heightCode out ≤ heightCode c - 1 := by
  obtain ⟨hc, rfl⟩ := (program_graph a c out).mp ho
  exact SourceOneIota.literalCode_height a c hc

/-- Order preservation and reflection apply to the actually returned codes,
including hidden high arguments on the full original guarded domain. -/
theorem program_order (a c d out out' : Nat)
    (ho : out ∈ program.eval (Nat.pair a c))
    (ho' : out' ∈ program.eval (Nat.pair a d)) :
    NativeContext.interpretation (SourceOneIota.alphaCode a) out <
        NativeContext.interpretation (SourceOneIota.alphaCode a) out' ↔
      interpretation 0 c < interpretation 0 d := by
  obtain ⟨hc, rfl⟩ := (program_graph a c out).mp ho
  obtain ⟨hd, rfl⟩ := (program_graph a d out').mp ho'
  exact SourceOneIota.literalCode_lt_iff a c d hc hd

noncomputable def sourceColumn (a : Nat) : Program := program.column a

theorem sourceColumn_primrec : Primrec sourceColumn :=
  Program.column_primrec.comp (Primrec.const program) Primrec.id

theorem sourceColumn_domain (a c : Nat) : (sourceColumn a).domain c ↔
    SourceOneIota.inputCheck a c = true := by
  rw [sourceColumn, Program.column_domain]
  exact program_domain a c

theorem sourceColumn_graph (a c out : Nat) : out ∈ (sourceColumn a).eval c ↔
    SourceOneIota.inputCheck a c = true ∧ out = SourceOneIota.literalCode a c := by
  rw [sourceColumn, Nat.Partrec.Code.eval_curry]
  exact program_graph a c out

theorem sourceColumn_accepted (a c out : Nat) (ho : out ∈ (sourceColumn a).eval c) :
    NativeContext.Comparison.acceptedCode (SourceOneIota.alphaCode a) out = true := by
  obtain ⟨hc, rfl⟩ := (sourceColumn_graph a c out).mp ho
  exact SourceOneIota.literalCode_accepted a c hc

theorem sourceColumn_height (a c out : Nat) (ho : out ∈ (sourceColumn a).eval c) :
    heightCode out ≤ heightCode c - 1 := by
  obtain ⟨hc, rfl⟩ := (sourceColumn_graph a c out).mp ho
  exact SourceOneIota.literalCode_height a c hc

/-- The graph recognizer compares the output numeral even when it is zero. -/
def graphBool (query : Nat) : Bool :=
  SourceOneIota.inputCheck query.unpair.1.unpair.1 query.unpair.1.unpair.2 &&
    (query.unpair.2 == SourceOneIota.literalCode query.unpair.1.unpair.1 query.unpair.1.unpair.2)

theorem graphBool_primrec : Primrec graphBool := by
  have hd : Primrec (fun query : Nat => query.unpair.1.unpair) :=
    Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)
  exact Primrec.and.comp (SourceOneIota.inputCheck_primrec.comp hd)
    (Primrec.beq.comp (Primrec.snd.comp Primrec.unpair) (SourceOneIota.literalCode_primrec.comp hd))

def graphEvaluation (query : Nat) : Part Nat := cond (graphBool query) (Part.some 0) Part.none

theorem graphEvaluation_partrec : Partrec graphEvaluation :=
  Partrec.cond graphBool_primrec.to_comp (Computable.const 0).partrec Partrec.none

theorem graphProgram_exists : ∃ p : Program, ∀ query, p.eval query = graphEvaluation query := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp graphEvaluation_partrec)
  exact ⟨p, fun query => congrFun hp query⟩

noncomputable def graphProgram : Program := Classical.choose graphProgram_exists

theorem graphProgram_domain (a c out : Nat) :
    graphProgram.domain (Nat.pair (Nat.pair a c) out) ↔
      SourceOneIota.inputCheck a c = true ∧ out = SourceOneIota.literalCode a c := by
  rw [Program.domain, Classical.choose_spec graphProgram_exists]
  simp only [graphEvaluation, graphBool, Nat.unpair_pair]
  cases h : SourceOneIota.inputCheck a c <;> cases he : out == SourceOneIota.literalCode a c <;>
    simp [h, he, Bool.eq_iff_iff, beq_iff_eq] at *

noncomputable def graphColumn (a c : Nat) : Program := graphProgram.column (Nat.pair a c)

theorem graphColumn_primrec : Primrec₂ graphColumn :=
  Program.column_primrec.comp (Primrec.const graphProgram)
    (Primrec₂.natPair.comp Primrec.fst Primrec.snd)

theorem graphColumn_domain (a c out : Nat) : (graphColumn a c).domain out ↔
    out ∈ (sourceColumn a).eval c := by
  rw [graphColumn, Program.column_domain, graphProgram_domain, sourceColumn_graph]

end Alexander313.SourceOneIotaProgram
