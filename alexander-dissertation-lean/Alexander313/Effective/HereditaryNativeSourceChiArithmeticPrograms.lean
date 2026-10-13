import Alexander313.Wilken.HereditaryNativeSourceChiArithmetic

/-!
# Actual native addition-indicator Programs

The input is (q,(beta,argument)); the literal right term is theta-zero of
the ORIGINAL argument. The source guard checks an original low beta, an
original admitted weak-normal argument, the genuine theta call, and its
nonzero proviso. Actual native addition and chi compute the output numeral.
The derived addition theorem identifies it with the original right chi.

The source Program has exactly that original domain. The numerical graph
recognizer includes both outputs zero and one, and the total decision also
returns zero on rejected inputs. Uniform columns use the actual Program
compiler. No value-invariance, recoding, arithmetic-chi or graph oracle is
supplied. Other clauses of Lemma 3.5 remain outside this module.
All proof candidates are uncompiled.
-/

namespace Alexander313.HereditaryNativeSourceChiArithmeticProgram

open Wilken.RelativeTerm.Hereditary
open Wilken.RelativeTerm.Hereditary.NativeContext
open Wilken.RelativeTerm.Hereditary.NativeContext.SourceChi.Arithmetic

abbrev Data := Nat × (Nat × Nat)

def answer (q c a : Nat) : Nat := cond (additionChi q c a) 1 0

theorem answer_primrec : Primrec (fun p : Data => answer p.1 p.2.1 p.2.2) :=
  additionChi_primrec.cond (Primrec.const 1) (Primrec.const 0)

def rawInput (query : Nat) : Bool :=
  sourceInput query.unpair.1 query.unpair.2.unpair.1 query.unpair.2.unpair.2

def rawAnswer (query : Nat) : Nat :=
  answer query.unpair.1 query.unpair.2.unpair.1 query.unpair.2.unpair.2

theorem rawInput_primrec : Primrec rawInput := sourceInput_primrec.comp
  ((Primrec.fst.comp Primrec.unpair).pair (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))

theorem rawAnswer_primrec : Primrec rawAnswer := answer_primrec.comp
  ((Primrec.fst.comp Primrec.unpair).pair (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))

def valueEvaluation (query : Nat) : Part Nat :=
  cond (rawInput query) (Part.some (rawAnswer query)) Part.none

theorem valueEvaluation_partrec : Partrec valueEvaluation :=
  Partrec.cond rawInput_primrec.to_comp rawAnswer_primrec.to_comp.partrec Partrec.none

theorem valueProgram_exists : ∃ p : Program, ∀ query, p.eval query = valueEvaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp valueEvaluation_partrec)

noncomputable def valueProgram : Program := Classical.choose valueProgram_exists

theorem valueProgram_eval (q c a : Nat) :
    valueProgram.eval (Nat.pair q (Nat.pair c a)) =
      cond (sourceInput q c a) (Part.some (answer q c a)) Part.none := by
  simpa only [valueEvaluation, rawInput, rawAnswer, Nat.unpair_pair] using
    Classical.choose_spec valueProgram_exists (Nat.pair q (Nat.pair c a))

theorem valueProgram_domain (q c a : Nat) :
    valueProgram.domain (Nat.pair q (Nat.pair c a)) ↔ sourceInput q c a = true := by
  rw [Program.domain, valueProgram_eval]
  cases h : sourceInput q c a <;> simp [h]

theorem valueProgram_graph (q c a output : Nat) :
    output ∈ valueProgram.eval (Nat.pair q (Nat.pair c a)) ↔
      sourceInput q c a = true ∧ output = answer q c a := by
  rw [valueProgram_eval]
  cases h : sourceInput q c a <;> simp [h]

noncomputable def valueColumn (q c : Nat) : Program := (valueProgram.column q).column c

theorem valueColumn_primrec : Primrec₂ valueColumn := by
  have hq := Program.column_primrec.comp (Primrec.const valueProgram) Primrec.fst
  exact (Program.column_primrec.comp hq Primrec.snd).to₂

theorem valueColumn_eval (q c a : Nat) :
    (valueColumn q c).eval a =
      cond (sourceInput q c a) (Part.some (answer q c a)) Part.none := by
  simp only [valueColumn, Nat.Partrec.Code.eval_curry, valueProgram_eval]

theorem valueColumn_domain (q c a : Nat) :
    (valueColumn q c).domain a ↔ sourceInput q c a = true := by
  rw [valueColumn, Program.column_domain, Program.column_domain]
  exact valueProgram_domain q c a

theorem valueColumn_original_domain (q c a : Nat) : (valueColumn q c).domain a ↔
    lowCheckCode q c = true ∧ checkCode q a = true ∧
      Comparison.Normal q (Wilken.RelativeTerm.Hereditary.ThetaCourse.rawTree a) ∧
      check q (.theta 0 (Wilken.RelativeTerm.Hereditary.ThetaCourse.rawTree a)) = true ∧
      base q < denote q (.theta 0 (Wilken.RelativeTerm.Hereditary.ThetaCourse.rawTree a)) := by
  rw [valueColumn_domain]
  exact sourceInput_literal q c a

/-- The value Program really returns chi(beta+alpha), and the constructed
source law identifies this numeral with chi of the original proper alpha. -/
theorem valueColumn_source (q c a : Nat) (h : sourceInput q c a = true) :
    (valueColumn q c).eval a = Part.some
      (cond (SourceChi.chiCode q (rightCode a)) 1 0) := by
  rw [valueColumn_eval, h]
  simp only [Bool.cond_true, answer, additionChi_correct q c a h]

theorem valueColumn_literal (q c a output : Nat) :
    output ∈ (valueColumn q c).eval a ↔ sourceInput q c a = true ∧
      output = cond (SourceChi.chiCode q (NativeContext.Arithmetic.addCode q c (rightCode a))) 1 0 := by
  rw [valueColumn_eval]
  cases h : sourceInput q c a <;> simp [h, answer, additionChi]

def decisionEvaluation (query : Nat) : Part Nat := Part.some (rawAnswer query)

theorem decisionEvaluation_partrec : Partrec decisionEvaluation := rawAnswer_primrec.to_comp.partrec

theorem decisionProgram_exists : ∃ p : Program, ∀ query, p.eval query = decisionEvaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp decisionEvaluation_partrec)

noncomputable def decisionProgram : Program := Classical.choose decisionProgram_exists

theorem decisionProgram_eval (q c a : Nat) :
    decisionProgram.eval (Nat.pair q (Nat.pair c a)) = Part.some (answer q c a) := by
  simpa only [decisionEvaluation, rawAnswer, Nat.unpair_pair] using
    Classical.choose_spec decisionProgram_exists (Nat.pair q (Nat.pair c a))

theorem decisionProgram_total (query : Nat) : decisionProgram.domain query := by
  rw [Program.domain, Classical.choose_spec decisionProgram_exists]
  exact Part.some_dom _

theorem decisionProgram_positive (q c a : Nat) :
    1 ∈ decisionProgram.eval (Nat.pair q (Nat.pair c a)) ↔ additionChi q c a = true := by
  rw [decisionProgram_eval]
  cases h : additionChi q c a <;> simp [answer, h]

noncomputable def decisionColumn (q c : Nat) : Program := (decisionProgram.column q).column c

theorem decisionColumn_primrec : Primrec₂ decisionColumn := by
  have hq := Program.column_primrec.comp (Primrec.const decisionProgram) Primrec.fst
  exact (Program.column_primrec.comp hq Primrec.snd).to₂

theorem decisionColumn_eval (q c a : Nat) : (decisionColumn q c).eval a = Part.some (answer q c a) := by
  simp only [decisionColumn, Nat.Partrec.Code.eval_curry, decisionProgram_eval]

def graph (q c a output : Nat) : Bool := sourceInput q c a && (output == answer q c a)

theorem graph_primrec : Primrec
    (fun p : Data × Nat => graph p.1.1 p.1.2.1 p.1.2.2 p.2) :=
  Primrec.and.comp (sourceInput_primrec.comp Primrec.fst)
    (Primrec.beq.comp Primrec.snd (answer_primrec.comp Primrec.fst))

theorem graph_exact (q c a output : Nat) : graph q c a output = true ↔
    sourceInput q c a = true ∧ output = answer q c a := by
  simp only [graph, Bool.and_eq_true, beq_iff_eq]

theorem graph_unique (q c a : Nat) (h : sourceInput q c a = true) :
    ∃! output, graph q c a output = true := by
  refine ⟨answer q c a, (graph_exact q c a _).mpr ⟨h, rfl⟩, ?_⟩
  intro output ho
  exact ((graph_exact q c a output).mp ho).2

def graphRaw (query : Nat) : Bool :=
  graph query.unpair.1.unpair.1 query.unpair.1.unpair.2.unpair.1
    query.unpair.1.unpair.2.unpair.2 query.unpair.2

theorem graphRaw_primrec : Primrec graphRaw := graph_primrec.comp
  ((((Primrec.fst.comp Primrec.unpair).pair
      (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))).comp
        (Primrec.fst.comp Primrec.unpair)).pair (Primrec.snd.comp Primrec.unpair))

def graphEvaluation (query : Nat) : Part Nat := cond (graphRaw query) (Part.some 1) Part.none

theorem graphEvaluation_partrec : Partrec graphEvaluation :=
  Partrec.cond graphRaw_primrec.to_comp (Computable.const 1).partrec Partrec.none

theorem graphProgram_exists : ∃ p : Program, ∀ query, p.eval query = graphEvaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp graphEvaluation_partrec)

noncomputable def graphProgram : Program := Classical.choose graphProgram_exists

theorem graphProgram_domain (q c a output : Nat) :
    graphProgram.domain (Nat.pair (Nat.pair q (Nat.pair c a)) output) ↔
      sourceInput q c a = true ∧ output = answer q c a := by
  rw [Program.domain, Classical.choose_spec graphProgram_exists]
  change (cond (graph q c a output) (Part.some 1) Part.none).Dom ↔ _
  have he : (cond (graph q c a output) (Part.some 1) Part.none).Dom ↔
      graph q c a output = true := by
    cases h : graph q c a output <;> simp [h, Part.some, Part.none]
  exact he.trans (graph_exact q c a output)

noncomputable def graphColumn (q c a : Nat) : Program :=
  graphProgram.column (Nat.pair q (Nat.pair c a))

theorem graphColumn_primrec : Primrec
    (fun p : Data => graphColumn p.1 p.2.1 p.2.2) :=
  Program.column_primrec.comp (Primrec.const graphProgram)
    (Primrec₂.natPair.comp Primrec.fst
      (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)))

theorem graphColumn_domain (q c a output : Nat) : (graphColumn q c a).domain output ↔
    sourceInput q c a = true ∧ output = answer q c a := by
  rw [graphColumn, Program.column_domain]
  exact graphProgram_domain q c a output

theorem graphColumn_matches_value (q c a output : Nat) :
    (graphColumn q c a).domain output ↔ output ∈ (valueColumn q c).eval a := by
  rw [graphColumn_domain, valueColumn_eval]
  cases h : sourceInput q c a <;> simp [h]

end Alexander313.HereditaryNativeSourceChiArithmeticProgram
