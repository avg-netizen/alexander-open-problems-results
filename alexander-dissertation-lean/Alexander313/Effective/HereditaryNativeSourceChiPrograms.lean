import Alexander313.Wilken.HereditaryNativeSourceChi

/-!
# Actual source-chi Programs in original native epsilon contexts

The value Program has tag 0 for original weak-normal input and tag 1 for
original raw input followed by the genuine native normalizer. Its domain
retains the original coded epsilon base and every actual native payload,
source constructor and sort check. It returns the actual indicator numeral.
Six decision tags expose raw domain/chi/dual and normal domain/chi/dual.
The complete positive numerical graph includes both 0 and 1; every column
uses the genuine primitive-recursive Program compiler.

Source semantics are the derived literal Definition 3.3 syntax clauses;
raw execution refers to the genuinely constructed normalized spelling.
No chi spelling invariance, arbitrary translation or source oracle is added.
All proof candidates remain uncompiled.
-/

namespace Alexander313.HereditaryNativeSourceChiProgram

open Wilken.RelativeTerm.Hereditary.NativeContext
open Wilken.RelativeTerm.Hereditary.NativeContext.SourceChi

def kernel (tag q c : Nat) : Bool :=
  cond (tag == 0) (rawInputCheck q c)
    (cond (tag == 1) (rawChiCode q c)
      (cond (tag == 2) (rawDualCode q c)
        (cond (tag == 3) (inputCheck q c)
          (cond (tag == 4) (chiCode q c)
            (cond (tag == 5) (dualCode q c) false)))))

theorem kernel_primrec : Primrec (fun p : Nat × (Nat × Nat) => kernel p.1 p.2.1 p.2.2) := by
  have ht (k : Nat) := Primrec.beq.comp Primrec.fst (Primrec.const k)
  have hq := Primrec.fst.comp Primrec.snd
  have hc := Primrec.snd.comp Primrec.snd
  exact (ht 0).cond (rawInputCheck_primrec.comp hq hc)
    ((ht 1).cond (rawChiCode_primrec.comp hq hc)
      ((ht 2).cond (rawDualCode_primrec.comp hq hc)
        ((ht 3).cond (inputCheck_primrec.comp hq hc)
          ((ht 4).cond (chiCode_primrec.comp hq hc)
            ((ht 5).cond (dualCode_primrec.comp hq hc) (Primrec.const false))))))

def raw (query : Nat) : Bool := kernel query.unpair.1 query.unpair.2.unpair.1 query.unpair.2.unpair.2

theorem raw_primrec : Primrec raw := kernel_primrec.comp
  ((Primrec.fst.comp Primrec.unpair).pair (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))

def answer (tag q c : Nat) : Nat := cond (kernel tag q c) 1 0

def decisionEvaluation (query : Nat) : Part Nat := Part.some (cond (raw query) 1 0)

theorem decisionEvaluation_partrec : Partrec decisionEvaluation :=
  (raw_primrec.cond (Primrec.const 1) (Primrec.const 0)).to_comp.partrec

theorem decisionProgram_exists : ∃ p : Program, ∀ query, p.eval query = decisionEvaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp decisionEvaluation_partrec)

noncomputable def decisionProgram : Program := Classical.choose decisionProgram_exists

theorem decisionProgram_eval (tag q c : Nat) :
    decisionProgram.eval (Nat.pair tag (Nat.pair q c)) = Part.some (answer tag q c) := by
  simpa only [decisionEvaluation, raw, answer, Nat.unpair_pair] using
    Classical.choose_spec decisionProgram_exists (Nat.pair tag (Nat.pair q c))

theorem decisionProgram_total (query : Nat) : decisionProgram.domain query := by
  rw [Program.domain, Classical.choose_spec decisionProgram_exists]
  exact Part.some_dom _

theorem decisionProgram_graph (tag q c output : Nat) :
    output ∈ decisionProgram.eval (Nat.pair tag (Nat.pair q c)) ↔ output = answer tag q c := by
  simp only [decisionProgram_eval, Part.mem_some_iff]

theorem decisionProgram_positive (tag q c : Nat) :
    1 ∈ decisionProgram.eval (Nat.pair tag (Nat.pair q c)) ↔ kernel tag q c = true := by
  rw [decisionProgram_graph]
  cases h : kernel tag q c <;> simp [answer, h]

noncomputable def decisionColumn (tag q : Nat) : Program := (decisionProgram.column tag).column q

theorem decisionColumn_primrec : Primrec₂ decisionColumn := by
  have ht := Program.column_primrec.comp (Primrec.const decisionProgram) Primrec.fst
  exact (Program.column_primrec.comp ht Primrec.snd).to₂

theorem decisionColumn_eval (tag q c : Nat) :
    (decisionColumn tag q).eval c = Part.some (answer tag q c) := by
  simp only [decisionColumn, Nat.Partrec.Code.eval_curry, decisionProgram_eval]

def inputEvaluation (query : Nat) : Part Nat := cond (raw query) (Part.some 0) Part.none

theorem inputEvaluation_partrec : Partrec inputEvaluation :=
  Partrec.cond raw_primrec.to_comp (Computable.const 0).partrec Partrec.none

theorem inputProgram_exists : ∃ p : Program, ∀ query, p.eval query = inputEvaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp inputEvaluation_partrec)

noncomputable def inputProgram : Program := Classical.choose inputProgram_exists

theorem inputProgram_domain (tag q c : Nat) :
    inputProgram.domain (Nat.pair tag (Nat.pair q c)) ↔ kernel tag q c = true := by
  rw [Program.domain, Classical.choose_spec inputProgram_exists]
  cases h : kernel tag q c <;> simp [inputEvaluation, raw, Nat.unpair_pair, h]

noncomputable def inputColumn (tag q : Nat) : Program := (inputProgram.column tag).column q

theorem inputColumn_primrec : Primrec₂ inputColumn := by
  have ht := Program.column_primrec.comp (Primrec.const inputProgram) Primrec.fst
  exact (Program.column_primrec.comp ht Primrec.snd).to₂

theorem inputColumn_domain (tag q c : Nat) : (inputColumn tag q).domain c ↔ kernel tag q c = true := by
  rw [inputColumn, Program.column_domain, Program.column_domain]
  exact inputProgram_domain tag q c

theorem rawDomainColumn_exact (q c : Nat) :
    (inputColumn 0 q).domain c ↔ checkCode q c = true := by
  rw [inputColumn_domain]
  change rawInputCheck q c = true ↔ _
  exact rawInputCheck_exact q c

theorem normalDomainColumn_exact (q c : Nat) : (inputColumn 3 q).domain c ↔
    checkCode q c = true ∧ Comparison.Normal q (Wilken.RelativeTerm.Hereditary.ThetaCourse.rawTree c) := by
  rw [inputColumn_domain]
  change inputCheck q c = true ↔ _
  exact inputCheck_exact q c

theorem normalChiColumn_exact (q : Nat) (t : Wilken.RelativeTerm Nat)
    (ht : check q t = true) (hn : Comparison.Normal q t) :
    (inputColumn 4 q).domain t.code ↔ indicator q t = true := by
  rw [inputColumn_domain]
  change chiCode q t.code = true ↔ _
  rw [chiCode_correct q t ht hn]

theorem normalDualColumn_exact (q : Nat) (t : Wilken.RelativeTerm Nat)
    (ht : check q t = true) (hn : Comparison.Normal q t) :
    (inputColumn 5 q).domain t.code ↔ indicator q t = false := by
  rw [inputColumn_domain]
  change dualCode q t.code = true ↔ _
  rw [dualCode_correct q t ht hn, Bool.not_eq_true]

theorem rawChiColumn_exact (q c : Nat) (hc : rawInputCheck q c = true) :
    (inputColumn 1 q).domain c ↔
      indicator q (Normalization.normalize q (Wilken.RelativeTerm.Hereditary.ThetaCourse.rawTree c)) = true := by
  rw [inputColumn_domain]
  change rawChiCode q c = true ↔ _
  rw [rawChiCode_correct q c hc]

theorem rawDualColumn_exact (q c : Nat) (hc : rawInputCheck q c = true) :
    (inputColumn 2 q).domain c ↔
      indicator q (Normalization.normalize q (Wilken.RelativeTerm.Hereditary.ThetaCourse.rawTree c)) = false := by
  rw [inputColumn_domain]
  change rawDualCode q c = true ↔ _
  rw [rawDualCode_correct q c hc, Bool.not_eq_true]

theorem inputColumn_unknown (tag q c : Nat) (h0 : tag ≠ 0) (h1 : tag ≠ 1) (h2 : tag ≠ 2)
    (h3 : tag ≠ 3) (h4 : tag ≠ 4) (h5 : tag ≠ 5) : ¬ (inputColumn tag q).domain c := by
  rw [inputColumn_domain]
  simp [kernel, h0, h1, h2, h3, h4, h5]

/-- The actual value operation, with raw and weak-normal guards retained. -/
def valueInput (tag q c : Nat) : Bool :=
  cond (tag == 0) (inputCheck q c) (cond (tag == 1) (rawInputCheck q c) false)

def valueBool (tag q c : Nat) : Bool := cond (tag == 0) (chiCode q c) (rawChiCode q c)

def valueAnswer (tag q c : Nat) : Nat := cond (valueBool tag q c) 1 0

theorem valueInput_primrec : Primrec (fun p : Nat × (Nat × Nat) => valueInput p.1 p.2.1 p.2.2) :=
  (Primrec.beq.comp Primrec.fst (Primrec.const 0)).cond
    (inputCheck_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
    ((Primrec.beq.comp Primrec.fst (Primrec.const 1)).cond
      (rawInputCheck_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
      (Primrec.const false))

theorem valueBool_primrec : Primrec (fun p : Nat × (Nat × Nat) => valueBool p.1 p.2.1 p.2.2) :=
  (Primrec.beq.comp Primrec.fst (Primrec.const 0)).cond
    (chiCode_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
    (rawChiCode_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))

theorem valueAnswer_primrec : Primrec (fun p : Nat × (Nat × Nat) => valueAnswer p.1 p.2.1 p.2.2) :=
  valueBool_primrec.cond (Primrec.const 1) (Primrec.const 0)

def valueInputRaw (query : Nat) : Bool :=
  valueInput query.unpair.1 query.unpair.2.unpair.1 query.unpair.2.unpair.2

def valueAnswerRaw (query : Nat) : Nat :=
  valueAnswer query.unpair.1 query.unpair.2.unpair.1 query.unpair.2.unpair.2

theorem valueInputRaw_primrec : Primrec valueInputRaw := valueInput_primrec.comp
  ((Primrec.fst.comp Primrec.unpair).pair (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))

theorem valueAnswerRaw_primrec : Primrec valueAnswerRaw := valueAnswer_primrec.comp
  ((Primrec.fst.comp Primrec.unpair).pair (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))

def valueEvaluation (query : Nat) : Part Nat :=
  cond (valueInputRaw query) (Part.some (valueAnswerRaw query)) Part.none

theorem valueEvaluation_partrec : Partrec valueEvaluation :=
  Partrec.cond valueInputRaw_primrec.to_comp valueAnswerRaw_primrec.to_comp.partrec Partrec.none

theorem valueProgram_exists : ∃ p : Program, ∀ query, p.eval query = valueEvaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp valueEvaluation_partrec)

noncomputable def valueProgram : Program := Classical.choose valueProgram_exists

theorem valueProgram_eval (tag q c : Nat) :
    valueProgram.eval (Nat.pair tag (Nat.pair q c)) =
      cond (valueInput tag q c) (Part.some (valueAnswer tag q c)) Part.none := by
  simpa only [valueEvaluation, valueInputRaw, valueAnswerRaw, Nat.unpair_pair] using
    Classical.choose_spec valueProgram_exists (Nat.pair tag (Nat.pair q c))

theorem valueProgram_domain (tag q c : Nat) :
    valueProgram.domain (Nat.pair tag (Nat.pair q c)) ↔ valueInput tag q c = true := by
  rw [Program.domain, valueProgram_eval]
  cases h : valueInput tag q c <;> simp [h]

theorem valueProgram_graph (tag q c output : Nat) :
    output ∈ valueProgram.eval (Nat.pair tag (Nat.pair q c)) ↔
      valueInput tag q c = true ∧ output = valueAnswer tag q c := by
  rw [valueProgram_eval]
  cases h : valueInput tag q c <;> simp [h]

noncomputable def valueColumn (tag q : Nat) : Program := (valueProgram.column tag).column q

theorem valueColumn_primrec : Primrec₂ valueColumn := by
  have ht := Program.column_primrec.comp (Primrec.const valueProgram) Primrec.fst
  exact (Program.column_primrec.comp ht Primrec.snd).to₂

theorem valueColumn_eval (tag q c : Nat) :
    (valueColumn tag q).eval c = cond (valueInput tag q c) (Part.some (valueAnswer tag q c)) Part.none := by
  simp only [valueColumn, Nat.Partrec.Code.eval_curry, valueProgram_eval]

theorem normalValueColumn_domain (q c : Nat) : (valueColumn 0 q).domain c ↔
    checkCode q c = true ∧ Comparison.Normal q (Wilken.RelativeTerm.Hereditary.ThetaCourse.rawTree c) := by
  rw [valueColumn, Program.column_domain, Program.column_domain, valueProgram_domain]
  change inputCheck q c = true ↔ _
  exact inputCheck_exact q c

theorem rawValueColumn_domain (q c : Nat) :
    (valueColumn 1 q).domain c ↔ checkCode q c = true := by
  rw [valueColumn, Program.column_domain, Program.column_domain, valueProgram_domain]
  change rawInputCheck q c = true ↔ _
  exact rawInputCheck_exact q c

theorem normalValueColumn_source (q : Nat) (t : Wilken.RelativeTerm Nat)
    (ht : check q t = true) (hn : Comparison.Normal q t) :
    (valueColumn 0 q).eval t.code = Part.some (cond (indicator q t) 1 0) := by
  have hi := (inputCheck_exact q t.code).mpr ⟨by simpa only [checkCode_code] using ht,
    by simpa only [Wilken.RelativeTerm.Hereditary.ThetaCourse.rawTree_code] using hn⟩
  simp only [valueColumn_eval, valueInput, valueAnswer, valueBool, beq_self_eq_true,
    Bool.cond_true, hi, chiCode_correct q t ht hn]

theorem rawValueColumn_source (q c : Nat) (hc : rawInputCheck q c = true) :
    (valueColumn 1 q).eval c =
      Part.some (cond (indicator q (Normalization.normalize q (Wilken.RelativeTerm.Hereditary.ThetaCourse.rawTree c))) 1 0) := by
  simp only [valueColumn_eval, valueInput, valueAnswer, valueBool, show (1 == 0) = false from rfl,
    beq_self_eq_true, Bool.cond_false, Bool.cond_true, hc, rawChiCode_correct q c hc]

theorem valueColumn_unknown (tag q c : Nat) (h0 : tag ≠ 0) (h1 : tag ≠ 1) :
    ¬ (valueColumn tag q).domain c := by
  rw [valueColumn, Program.column_domain, Program.column_domain, valueProgram_domain]
  simp [valueInput, h0, h1]

/-- A genuine PR certificate for the complete 0/1 output of the actual
partial value operation, including both accepted outcomes. -/
def valueGraphRaw (query : Nat) : Bool := valueInputRaw query.unpair.1 &&
  (query.unpair.2 == valueAnswerRaw query.unpair.1)

theorem valueGraphRaw_primrec : Primrec valueGraphRaw := Primrec.and.comp
  (valueInputRaw_primrec.comp (Primrec.fst.comp Primrec.unpair))
  (Primrec.beq.comp (Primrec.snd.comp Primrec.unpair)
    (valueAnswerRaw_primrec.comp (Primrec.fst.comp Primrec.unpair)))

def graphEvaluation (query : Nat) : Part Nat := cond (valueGraphRaw query) (Part.some 0) Part.none

theorem graphEvaluation_partrec : Partrec graphEvaluation :=
  Partrec.cond valueGraphRaw_primrec.to_comp (Computable.const 0).partrec Partrec.none

theorem graphProgram_exists : ∃ p : Program, ∀ query, p.eval query = graphEvaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp graphEvaluation_partrec)

noncomputable def graphProgram : Program := Classical.choose graphProgram_exists

theorem graphProgram_domain (tag q c output : Nat) :
    graphProgram.domain (Nat.pair (Nat.pair tag (Nat.pair q c)) output) ↔
      valueInput tag q c = true ∧ output = valueAnswer tag q c := by
  rw [Program.domain, Classical.choose_spec graphProgram_exists]
  simp only [graphEvaluation, valueGraphRaw, valueInputRaw, valueAnswerRaw, Nat.unpair_pair]
  cases hi : valueInput tag q c <;> cases ho : output == valueAnswer tag q c <;>
    simp [hi, ho, ← beq_iff_eq]

noncomputable def graphColumn (tag q c : Nat) : Program := graphProgram.column (Nat.pair tag (Nat.pair q c))

theorem graphColumn_primrec : Primrec (fun p : Nat × (Nat × Nat) => graphColumn p.1 p.2.1 p.2.2) :=
  Program.column_primrec.comp (Primrec.const graphProgram) (Primrec₂.natPair.comp Primrec.fst
    (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)))

theorem graphColumn_domain (tag q c output : Nat) : (graphColumn tag q c).domain output ↔
    valueInput tag q c = true ∧ output = valueAnswer tag q c := by
  rw [graphColumn, Program.column_domain]
  exact graphProgram_domain tag q c output

theorem graphColumn_execution (tag q c output : Nat) : (graphColumn tag q c).domain output ↔
    output ∈ (valueColumn tag q).eval c := by
  rw [graphColumn_domain, valueColumn, Nat.Partrec.Code.eval_curry, Nat.Partrec.Code.eval_curry]
  exact (valueProgram_graph tag q c output).symm

theorem graphColumn_unique (tag q c : Nat) (hc : valueInput tag q c = true) :
    ∃! output, (graphColumn tag q c).domain output := by
  refine ⟨valueAnswer tag q c, (graphColumn_domain tag q c _).mpr ⟨hc, rfl⟩, ?_⟩
  intro output ho
  exact ((graphColumn_domain tag q c output).mp ho).2

end Alexander313.HereditaryNativeSourceChiProgram
