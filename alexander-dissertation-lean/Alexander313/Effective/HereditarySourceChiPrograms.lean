import Alexander313.Wilken.HereditarySourceChi

/-!
# Actual Programs for the public epsilon-base source indicator

The value Program has tag 0 for original weak-normal input and tag 1 for
original raw input followed by the actual normalizer. It returns the literal
indicator numeral on exactly the corresponding positive-level admission
domain. The six decision tags expose raw domain/chi/dual and normal
domain/chi/dual. Complete numerical output graphs include both 0 and 1,
and every column is compiled by the genuine PR Program compiler.

The source clauses are those proved for the real syntax indicator; no
alternate-spelling or temporary-context translation claim is added.
All candidates are uncompiled.
-/

namespace Alexander313.HereditarySourceChiProgram

open Wilken.RelativeTerm.Hereditary
open SourceChi

def kernel (tag r c : Nat) : Bool :=
  cond (tag == 0) (rawInputCheck r c)
    (cond (tag == 1) (rawChiCode r c)
      (cond (tag == 2) (rawDualCode r c)
        (cond (tag == 3) (inputCheck r c)
          (cond (tag == 4) (chiCode r c)
            (cond (tag == 5) (dualCode r c) false)))))

theorem kernel_primrec : Primrec (fun p : Nat × (Nat × Nat) => kernel p.1 p.2.1 p.2.2) := by
  have ht (k : Nat) := Primrec.beq.comp Primrec.fst (Primrec.const k)
  have hr := Primrec.fst.comp Primrec.snd
  have hc := Primrec.snd.comp Primrec.snd
  exact (ht 0).cond (rawInputCheck_primrec.comp hr hc)
    ((ht 1).cond (rawChiCode_primrec.comp hr hc)
      ((ht 2).cond (rawDualCode_primrec.comp hr hc)
        ((ht 3).cond (inputCheck_primrec.comp hr hc)
          ((ht 4).cond (chiCode_primrec.comp hr hc)
            ((ht 5).cond (dualCode_primrec.comp hr hc) (Primrec.const false))))))

def raw (query : Nat) : Bool := kernel query.unpair.1 query.unpair.2.unpair.1 query.unpair.2.unpair.2

theorem raw_primrec : Primrec raw := kernel_primrec.comp
  ((Primrec.fst.comp Primrec.unpair).pair (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))

def answer (tag r c : Nat) : Nat := cond (kernel tag r c) 1 0

def decisionEvaluation (query : Nat) : Part Nat := Part.some (cond (raw query) 1 0)

theorem decisionEvaluation_partrec : Partrec decisionEvaluation :=
  (raw_primrec.cond (Primrec.const 1) (Primrec.const 0)).to_comp.partrec

theorem decisionProgram_exists : ∃ p : Program, ∀ query, p.eval query = decisionEvaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp decisionEvaluation_partrec)

noncomputable def decisionProgram : Program := Classical.choose decisionProgram_exists

theorem decisionProgram_eval (tag r c : Nat) :
    decisionProgram.eval (Nat.pair tag (Nat.pair r c)) = Part.some (answer tag r c) := by
  simpa only [decisionEvaluation, raw, answer, Nat.unpair_pair] using
    Classical.choose_spec decisionProgram_exists (Nat.pair tag (Nat.pair r c))

theorem decisionProgram_total (query : Nat) : decisionProgram.domain query := by
  rw [Program.domain, Classical.choose_spec decisionProgram_exists]
  exact Part.some_dom _

theorem decisionProgram_graph (tag r c output : Nat) :
    output ∈ decisionProgram.eval (Nat.pair tag (Nat.pair r c)) ↔ output = answer tag r c := by
  simp only [decisionProgram_eval, Part.mem_some_iff]

theorem decisionProgram_positive (tag r c : Nat) :
    1 ∈ decisionProgram.eval (Nat.pair tag (Nat.pair r c)) ↔ kernel tag r c = true := by
  rw [decisionProgram_graph]
  cases h : kernel tag r c <;> simp [answer, h]

noncomputable def decisionColumn (tag r : Nat) : Program := (decisionProgram.column tag).column r

theorem decisionColumn_primrec : Primrec₂ decisionColumn := by
  have ht := Program.column_primrec.comp (Primrec.const decisionProgram) Primrec.fst
  exact (Program.column_primrec.comp ht Primrec.snd).to₂

theorem decisionColumn_eval (tag r c : Nat) :
    (decisionColumn tag r).eval c = Part.some (answer tag r c) := by
  simp only [decisionColumn, Nat.Partrec.Code.eval_curry, decisionProgram_eval]

def inputEvaluation (query : Nat) : Part Nat := cond (raw query) (Part.some 0) Part.none

theorem inputEvaluation_partrec : Partrec inputEvaluation :=
  Partrec.cond raw_primrec.to_comp (Computable.const 0).partrec Partrec.none

theorem inputProgram_exists : ∃ p : Program, ∀ query, p.eval query = inputEvaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp inputEvaluation_partrec)

noncomputable def inputProgram : Program := Classical.choose inputProgram_exists

theorem inputProgram_domain (tag r c : Nat) :
    inputProgram.domain (Nat.pair tag (Nat.pair r c)) ↔ kernel tag r c = true := by
  rw [Program.domain, Classical.choose_spec inputProgram_exists]
  cases h : kernel tag r c <;> simp [inputEvaluation, raw, Nat.unpair_pair, h]

noncomputable def inputColumn (tag r : Nat) : Program := (inputProgram.column tag).column r

theorem inputColumn_primrec : Primrec₂ inputColumn := by
  have ht := Program.column_primrec.comp (Primrec.const inputProgram) Primrec.fst
  exact (Program.column_primrec.comp ht Primrec.snd).to₂

theorem inputColumn_domain (tag r c : Nat) : (inputColumn tag r).domain c ↔ kernel tag r c = true := by
  rw [inputColumn, Program.column_domain, Program.column_domain]
  exact inputProgram_domain tag r c

theorem rawDomainColumn_exact (r c : Nat) :
    (inputColumn 0 r).domain c ↔ 0 < r ∧ checkCode r c = true := by
  rw [inputColumn_domain]
  change rawInputCheck r c = true ↔ _
  exact rawInputCheck_exact r c

theorem normalDomainColumn_exact (r c : Nat) : (inputColumn 3 r).domain c ↔
    0 < r ∧ checkCode r c = true ∧ Theta.Normal r (ThetaCourse.rawTree c) := by
  rw [inputColumn_domain]
  change inputCheck r c = true ↔ _
  exact inputCheck_exact r c

theorem normalChiColumn_exact (r : Nat) (t : Wilken.RelativeTerm Nat) (hr : 0 < r)
    (ht : check r t = true) (hn : Theta.Normal r t) :
    (inputColumn 4 r).domain t.code ↔ indicator r t = true := by
  rw [inputColumn_domain]
  change chiCode r t.code = true ↔ _
  rw [chiCode_correct r t hr ht hn]

theorem normalDualColumn_exact (r : Nat) (t : Wilken.RelativeTerm Nat) (hr : 0 < r)
    (ht : check r t = true) (hn : Theta.Normal r t) :
    (inputColumn 5 r).domain t.code ↔ indicator r t = false := by
  rw [inputColumn_domain]
  change dualCode r t.code = true ↔ _
  rw [dualCode_correct r t hr ht hn, Bool.not_eq_true]

theorem rawChiColumn_exact (r c : Nat) (hc : rawInputCheck r c = true) :
    (inputColumn 1 r).domain c ↔
      indicator r (Theta.Normalization.normalize r (ThetaCourse.rawTree c)) = true := by
  rw [inputColumn_domain]
  change rawChiCode r c = true ↔ _
  rw [rawChiCode_correct r c hc]

theorem rawDualColumn_exact (r c : Nat) (hc : rawInputCheck r c = true) :
    (inputColumn 2 r).domain c ↔
      indicator r (Theta.Normalization.normalize r (ThetaCourse.rawTree c)) = false := by
  rw [inputColumn_domain]
  change rawDualCode r c = true ↔ _
  rw [rawDualCode_correct r c hc, Bool.not_eq_true]

theorem inputColumn_unknown (tag r c : Nat) (h0 : tag ≠ 0) (h1 : tag ≠ 1) (h2 : tag ≠ 2)
    (h3 : tag ≠ 3) (h4 : tag ≠ 4) (h5 : tag ≠ 5) : ¬ (inputColumn tag r).domain c := by
  rw [inputColumn_domain]
  simp [kernel, h0, h1, h2, h3, h4, h5]

/-- The actual value operation, with raw and weak-normal guards retained. -/
def valueInput (tag r c : Nat) : Bool :=
  cond (tag == 0) (inputCheck r c) (cond (tag == 1) (rawInputCheck r c) false)

def valueBool (tag r c : Nat) : Bool := cond (tag == 0) (chiCode r c) (rawChiCode r c)

def valueAnswer (tag r c : Nat) : Nat := cond (valueBool tag r c) 1 0

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

theorem valueProgram_eval (tag r c : Nat) :
    valueProgram.eval (Nat.pair tag (Nat.pair r c)) =
      cond (valueInput tag r c) (Part.some (valueAnswer tag r c)) Part.none := by
  simpa only [valueEvaluation, valueInputRaw, valueAnswerRaw, Nat.unpair_pair] using
    Classical.choose_spec valueProgram_exists (Nat.pair tag (Nat.pair r c))

theorem valueProgram_domain (tag r c : Nat) :
    valueProgram.domain (Nat.pair tag (Nat.pair r c)) ↔ valueInput tag r c = true := by
  rw [Program.domain, valueProgram_eval]
  cases h : valueInput tag r c <;> simp [h]

theorem valueProgram_graph (tag r c output : Nat) :
    output ∈ valueProgram.eval (Nat.pair tag (Nat.pair r c)) ↔
      valueInput tag r c = true ∧ output = valueAnswer tag r c := by
  rw [valueProgram_eval]
  cases h : valueInput tag r c <;> simp [h]

noncomputable def valueColumn (tag r : Nat) : Program := (valueProgram.column tag).column r

theorem valueColumn_primrec : Primrec₂ valueColumn := by
  have ht := Program.column_primrec.comp (Primrec.const valueProgram) Primrec.fst
  exact (Program.column_primrec.comp ht Primrec.snd).to₂

theorem valueColumn_eval (tag r c : Nat) :
    (valueColumn tag r).eval c = cond (valueInput tag r c) (Part.some (valueAnswer tag r c)) Part.none := by
  simp only [valueColumn, Nat.Partrec.Code.eval_curry, valueProgram_eval]

theorem normalValueColumn_domain (r c : Nat) : (valueColumn 0 r).domain c ↔
    0 < r ∧ checkCode r c = true ∧ Theta.Normal r (ThetaCourse.rawTree c) := by
  rw [valueColumn, Program.column_domain, Program.column_domain, valueProgram_domain]
  change inputCheck r c = true ↔ _
  exact inputCheck_exact r c

theorem rawValueColumn_domain (r c : Nat) :
    (valueColumn 1 r).domain c ↔ 0 < r ∧ checkCode r c = true := by
  rw [valueColumn, Program.column_domain, Program.column_domain, valueProgram_domain]
  change rawInputCheck r c = true ↔ _
  exact rawInputCheck_exact r c

theorem normalValueColumn_source (r : Nat) (t : Wilken.RelativeTerm Nat) (hr : 0 < r)
    (ht : check r t = true) (hn : Theta.Normal r t) :
    (valueColumn 0 r).eval t.code = Part.some (cond (indicator r t) 1 0) := by
  have hi := (inputCheck_exact r t.code).mpr ⟨hr, by simpa only [checkCode_code] using ht,
    by simpa only [ThetaCourse.rawTree_code] using hn⟩
  simp only [valueColumn_eval, valueInput, valueAnswer, valueBool, beq_self_eq_true,
    Bool.cond_true, hi, chiCode_correct r t hr ht hn]

theorem rawValueColumn_source (r c : Nat) (hc : rawInputCheck r c = true) :
    (valueColumn 1 r).eval c =
      Part.some (cond (indicator r (Theta.Normalization.normalize r (ThetaCourse.rawTree c))) 1 0) := by
  simp only [valueColumn_eval, valueInput, valueAnswer, valueBool, show (1 == 0) = false from rfl,
    beq_self_eq_true, Bool.cond_false, Bool.cond_true, hc, rawChiCode_correct r c hc]

theorem valueColumn_unknown (tag r c : Nat) (h0 : tag ≠ 0) (h1 : tag ≠ 1) :
    ¬ (valueColumn tag r).domain c := by
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

theorem graphProgram_domain (tag r c output : Nat) :
    graphProgram.domain (Nat.pair (Nat.pair tag (Nat.pair r c)) output) ↔
      valueInput tag r c = true ∧ output = valueAnswer tag r c := by
  rw [Program.domain, Classical.choose_spec graphProgram_exists]
  simp only [graphEvaluation, valueGraphRaw, valueInputRaw, valueAnswerRaw, Nat.unpair_pair]
  cases hi : valueInput tag r c <;> cases ho : output == valueAnswer tag r c <;>
    simp [hi, ho, ← beq_iff_eq]

noncomputable def graphColumn (tag r c : Nat) : Program := graphProgram.column (Nat.pair tag (Nat.pair r c))

theorem graphColumn_primrec : Primrec (fun p : Nat × (Nat × Nat) => graphColumn p.1 p.2.1 p.2.2) :=
  Program.column_primrec.comp (Primrec.const graphProgram) (Primrec₂.natPair.comp Primrec.fst
    (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)))

theorem graphColumn_domain (tag r c output : Nat) : (graphColumn tag r c).domain output ↔
    valueInput tag r c = true ∧ output = valueAnswer tag r c := by
  rw [graphColumn, Program.column_domain]
  exact graphProgram_domain tag r c output

theorem graphColumn_execution (tag r c output : Nat) : (graphColumn tag r c).domain output ↔
    output ∈ (valueColumn tag r).eval c := by
  rw [graphColumn_domain, valueColumn, Nat.Partrec.Code.eval_curry, Nat.Partrec.Code.eval_curry]
  exact (valueProgram_graph tag r c output).symm

theorem graphColumn_unique (tag r c : Nat) (hc : valueInput tag r c = true) :
    ∃! output, (graphColumn tag r c).domain output := by
  refine ⟨valueAnswer tag r c, (graphColumn_domain tag r c _).mpr ⟨hc, rfl⟩, ?_⟩
  intro output ho
  exact ((graphColumn_domain tag r c output).mp ho).2

end Alexander313.HereditarySourceChiProgram
