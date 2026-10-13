import Alexander313.Wilken.HereditaryNativeSourceChiBaseChange

/-!
# Executing indicator triangles at genuine smaller epsilon bases

Tags 0/1 execute chi/dual after the original weak-normal pi operation;
tags 2/3 execute chi/dual after the original normalize-first raw pi operation.
Each domain is exactly the existing original base-change guard. The actual
answer agrees with the source indicator by the newly proved triangles.
Unknown tags reject. The complete numerical graphs include answer zero.

All finite kernels and compiler columns are genuinely primitive recursive.
Programs execute those kernels; no operation, graph or effectivity interface
is supplied. The chosen-presentation Par guard is not identified with unique
printed Par across arbitrary spellings. All candidates are uncompiled.
-/

namespace Alexander313.HereditaryNativeSourceChiBaseChangeProgram

open Wilken.RelativeTerm.Hereditary
open NativeContext

abbrev Data := (Nat × Nat) × (Nat × Nat)

def input (tag q v c : Nat) : Bool :=
  cond (tag == 0) (BaseTransformation.normalInputCheck q v c)
    (cond (tag == 1) (BaseTransformation.normalInputCheck q v c)
      (cond (tag == 2) (BaseTransformation.rawInputCheck q v c)
        (cond (tag == 3) (BaseTransformation.rawInputCheck q v c) false)))

theorem input_primrec : Primrec (fun p : Data => input p.1.1 p.1.2 p.2.1 p.2.2) := by
  have ht := Primrec.fst.comp Primrec.fst
  have hp := (Primrec.snd.comp Primrec.fst).pair Primrec.snd
  have hn := BaseTransformation.normalInputCheck_primrec.comp hp
  have hr := BaseTransformation.rawInputCheck_primrec.comp hp
  exact (Primrec.beq.comp ht (Primrec.const 0)).cond hn
    ((Primrec.beq.comp ht (Primrec.const 1)).cond hn
      ((Primrec.beq.comp ht (Primrec.const 2)).cond hr
        ((Primrec.beq.comp ht (Primrec.const 3)).cond hr (Primrec.const false))))

theorem input_exact (tag q v c : Nat) : input tag q v c = true ↔
    (tag = 0 ∧ BaseTransformation.normalInputCheck q v c = true) ∨
      (tag = 1 ∧ BaseTransformation.normalInputCheck q v c = true) ∨
      (tag = 2 ∧ BaseTransformation.rawInputCheck q v c = true) ∨
      (tag = 3 ∧ BaseTransformation.rawInputCheck q v c = true) := by
  by_cases h0 : tag = 0
  · subst tag; simp [input]
  · by_cases h1 : tag = 1
    · subst tag; simp [input]
    · by_cases h2 : tag = 2
      · subst tag; simp [input]
      · by_cases h3 : tag = 3 <;> simp [input, h0, h1, h2, h3]

theorem input_unknown (tag q v c : Nat) (h : 4 ≤ tag) : input tag q v c = false := by
  have h0 : tag ≠ 0 := by omega
  have h1 : tag ≠ 1 := by omega
  have h2 : tag ≠ 2 := by omega
  have h3 : tag ≠ 3 := by omega
  simp [input, h0, h1, h2, h3]

def transformedCode (tag q v c : Nat) : Nat :=
  cond ((tag == 2) || (tag == 3)) (BaseTransformation.rawPiCode q v c)
    (BaseTransformation.piCode q v c)

theorem transformedCode_primrec : Primrec
    (fun p : Data => transformedCode p.1.1 p.1.2 p.2.1 p.2.2) := by
  have ht := Primrec.fst.comp Primrec.fst
  have hp := (Primrec.snd.comp Primrec.fst).pair Primrec.snd
  exact (Primrec.or.comp (Primrec.beq.comp ht (Primrec.const 2))
    (Primrec.beq.comp ht (Primrec.const 3))).cond
      (BaseTransformation.rawPiCode_primrec.comp hp) (BaseTransformation.piCode_primrec.comp hp)

def answer (tag q v c : Nat) : Bool :=
  cond ((tag == 1) || (tag == 3)) (SourceChi.dualCode v (transformedCode tag q v c))
    (SourceChi.chiCode v (transformedCode tag q v c))

theorem answer_primrec : Primrec (fun p : Data => answer p.1.1 p.1.2 p.2.1 p.2.2) := by
  have ht := Primrec.fst.comp Primrec.fst
  have hv := Primrec.fst.comp Primrec.snd
  exact (Primrec.or.comp (Primrec.beq.comp ht (Primrec.const 1))
    (Primrec.beq.comp ht (Primrec.const 3))).cond
      (SourceChi.dualCode_primrec.comp hv transformedCode_primrec)
      (SourceChi.chiCode_primrec.comp hv transformedCode_primrec)

def sourceAnswer (tag q c : Nat) : Bool :=
  cond ((tag == 2) || (tag == 3))
    (cond (tag == 3) (SourceChi.rawDualCode q c) (SourceChi.rawChiCode q c))
    (cond (tag == 1) (SourceChi.dualCode q c) (SourceChi.chiCode q c))

theorem answer_commute (tag q v c : Nat) (hi : input tag q v c = true) :
    answer tag q v c = sourceAnswer tag q c := by
  rcases (input_exact tag q v c).mp hi with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
  · simpa [answer, transformedCode, sourceAnswer] using SourceChi.BaseChange.source_lemma_3_4 q v c h
  · simpa [answer, transformedCode, sourceAnswer] using SourceChi.BaseChange.source_lemma_3_4_dual q v c h
  · simpa [answer, transformedCode, sourceAnswer] using SourceChi.BaseChange.raw_chi_commute q v c h
  · simpa [answer, transformedCode, sourceAnswer] using SourceChi.BaseChange.raw_dual_commute q v c h

theorem transformedCode_accepted (tag q v c : Nat) (hi : input tag q v c = true) :
    SourceChi.inputCheck v (transformedCode tag q v c) = true := by
  rcases (input_exact tag q v c).mp hi with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
  · simpa [transformedCode] using (SourceChi.BaseChange.normal_inputs q v c h).2
  · simpa [transformedCode] using (SourceChi.BaseChange.normal_inputs q v c h).2
  · simpa [transformedCode] using (SourceChi.BaseChange.raw_inputs q v c h).2.2
  · simpa [transformedCode] using (SourceChi.BaseChange.raw_inputs q v c h).2.2

def output (tag q v c : Nat) : Nat := cond (answer tag q v c) 1 0

theorem output_primrec : Primrec (fun p : Data => output p.1.1 p.1.2 p.2.1 p.2.2) :=
  answer_primrec.cond (Primrec.const 1) (Primrec.const 0)

theorem output_commute (tag q v c : Nat) (hi : input tag q v c = true) :
    output tag q v c = cond (sourceAnswer tag q c) 1 0 := by
  rw [output, answer_commute tag q v c hi]

theorem output_zero_or_one (tag q v c : Nat) : output tag q v c = 0 ∨ output tag q v c = 1 := by
  cases h : answer tag q v c <;> simp only [output, h, Bool.cond_false, Bool.cond_true] <;> simp

def data (query : Nat) : Data :=
  ((query.unpair.1, query.unpair.2.unpair.1), query.unpair.2.unpair.2.unpair)

theorem data_primrec : Primrec data := by
  have h := Primrec.unpair
  have hp := Primrec.unpair.comp (Primrec.snd.comp h)
  exact ((Primrec.fst.comp h).pair (Primrec.fst.comp hp)).pair
    (Primrec.unpair.comp (Primrec.snd.comp hp))

def evaluation (query : Nat) : Part Nat :=
  let p := data query
  cond (input p.1.1 p.1.2 p.2.1 p.2.2) (Part.some (output p.1.1 p.1.2 p.2.1 p.2.2)) Part.none

theorem evaluation_partrec : Partrec evaluation :=
  Partrec.cond (input_primrec.comp data_primrec).to_comp
    (output_primrec.comp data_primrec).to_comp.partrec Partrec.none

theorem program_exists : ∃ p : Program, ∀ query, p.eval query = evaluation query := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp evaluation_partrec)
  exact ⟨p, fun query => congrFun hp query⟩

noncomputable def program : Program := Classical.choose program_exists

theorem program_eval (tag q v c : Nat) : program.eval (Nat.pair tag (Nat.pair q (Nat.pair v c))) =
    cond (input tag q v c) (Part.some (output tag q v c)) Part.none := by
  simpa only [evaluation, data, Nat.unpair_pair] using
    Classical.choose_spec program_exists (Nat.pair tag (Nat.pair q (Nat.pair v c)))

theorem program_domain (tag q v c : Nat) : program.domain (Nat.pair tag (Nat.pair q (Nat.pair v c))) ↔
    input tag q v c = true := by
  rw [Program.domain, program_eval]
  cases h : input tag q v c <;> simp [h]

theorem program_graph (tag q v c out : Nat) : out ∈ program.eval (Nat.pair tag (Nat.pair q (Nat.pair v c))) ↔
    input tag q v c = true ∧ out = output tag q v c := by
  rw [program_eval]
  cases h : input tag q v c <;> simp [h]

noncomputable def sourceColumn (tag q v : Nat) : Program := ((program.column tag).column q).column v

theorem sourceColumn_primrec : Primrec (fun p : Nat × (Nat × Nat) => sourceColumn p.1 p.2.1 p.2.2) :=
  Program.column_primrec.comp (Program.column_primrec.comp
    (Program.column_primrec.comp (Primrec.const program) Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)

theorem sourceColumn_eval (tag q v c : Nat) : (sourceColumn tag q v).eval c =
    cond (input tag q v c) (Part.some (output tag q v c)) Part.none := by
  simp only [sourceColumn, Nat.Partrec.Code.eval_curry]
  exact program_eval tag q v c

theorem sourceColumn_domain (tag q v c : Nat) : (sourceColumn tag q v).domain c ↔ input tag q v c = true := by
  simp only [sourceColumn, Program.column_domain]
  exact program_domain tag q v c

theorem sourceColumn_graph (tag q v c out : Nat) : out ∈ (sourceColumn tag q v).eval c ↔
    input tag q v c = true ∧ out = output tag q v c := by
  simp only [sourceColumn, Nat.Partrec.Code.eval_curry]
  exact program_graph tag q v c out

theorem sourceColumn_commute (tag q v c out : Nat) (ho : out ∈ (sourceColumn tag q v).eval c) :
    out = cond (sourceAnswer tag q c) 1 0 := by
  obtain ⟨hi, rfl⟩ := (sourceColumn_graph tag q v c out).mp ho
  exact output_commute tag q v c hi

theorem normalColumn_domain (tag q v c : Nat) (ht : tag = 0 ∨ tag = 1) :
    (sourceColumn tag q v).domain c ↔
      checkCode q c = true ∧ baseCheck v = true ∧ base v < base q ∧
        BaseTransformation.ParBounded q v (ThetaCourse.rawTree c) ∧
          Comparison.Normal q (ThetaCourse.rawTree c) := by
  rw [sourceColumn_domain]
  have he : input tag q v c = BaseTransformation.normalInputCheck q v c := by
    rcases ht with rfl | rfl <;> simp [input]
  rw [he, BaseTransformation.normalInputCheck_exact, BaseTransformation.inputCheck_exact]
  simp only [and_assoc]

theorem rawColumn_domain (tag q v c : Nat) (ht : tag = 2 ∨ tag = 3) :
    (sourceColumn tag q v).domain c ↔
      checkCode q c = true ∧ baseCheck v = true ∧ base v < base q ∧
        BaseTransformation.ParBounded q v (ThetaCourse.rawTree (Normalization.normalizeCode q c)) := by
  rw [sourceColumn_domain]
  have he : input tag q v c = BaseTransformation.rawInputCheck q v c := by
    rcases ht with rfl | rfl <;> simp [input]
  rw [he, BaseTransformation.rawInputCheck_exact]

def inputEvaluation (query : Nat) : Part Nat :=
  let p := data query
  cond (input p.1.1 p.1.2 p.2.1 p.2.2) (Part.some 1) Part.none

theorem inputEvaluation_partrec : Partrec inputEvaluation :=
  Partrec.cond (input_primrec.comp data_primrec).to_comp (Computable.const 1).partrec Partrec.none

theorem inputProgram_exists : ∃ p : Program, ∀ query, p.eval query = inputEvaluation query := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp inputEvaluation_partrec)
  exact ⟨p, fun query => congrFun hp query⟩

noncomputable def inputProgram : Program := Classical.choose inputProgram_exists

theorem inputProgram_domain (tag q v c : Nat) :
    inputProgram.domain (Nat.pair tag (Nat.pair q (Nat.pair v c))) ↔ input tag q v c = true := by
  rw [Program.domain, Classical.choose_spec inputProgram_exists]
  simp only [inputEvaluation, data, Nat.unpair_pair]
  cases h : input tag q v c <;> simp [h]

noncomputable def inputColumn (tag q v : Nat) : Program := ((inputProgram.column tag).column q).column v

theorem inputColumn_primrec : Primrec (fun p : Nat × (Nat × Nat) => inputColumn p.1 p.2.1 p.2.2) :=
  Program.column_primrec.comp (Program.column_primrec.comp
    (Program.column_primrec.comp (Primrec.const inputProgram) Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)

theorem inputColumn_domain (tag q v c : Nat) : (inputColumn tag q v).domain c ↔ input tag q v c = true := by
  simp only [inputColumn, Program.column_domain]
  exact inputProgram_domain tag q v c

def graph (tag q v c out : Nat) : Bool := input tag q v c && (out == output tag q v c)

theorem graph_primrec : Primrec (fun p : Data × Nat => graph p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2 p.2) :=
  Primrec.and.comp (input_primrec.comp Primrec.fst)
    (Primrec.beq.comp Primrec.snd (output_primrec.comp Primrec.fst))

theorem graph_exact (tag q v c out : Nat) : graph tag q v c out = true ↔
    input tag q v c = true ∧ out = output tag q v c := by
  simp only [graph, Bool.and_eq_true, beq_iff_eq]

def graphEvaluation (query : Nat) : Part Nat :=
  let p := data query.unpair.1
  cond (graph p.1.1 p.1.2 p.2.1 p.2.2 query.unpair.2) (Part.some 1) Part.none

theorem graphEvaluation_partrec : Partrec graphEvaluation :=
  Partrec.cond (graph_primrec.comp ((data_primrec.comp (Primrec.fst.comp Primrec.unpair)).pair
    (Primrec.snd.comp Primrec.unpair))).to_comp (Computable.const 1).partrec Partrec.none

theorem graphProgram_exists : ∃ p : Program, ∀ query, p.eval query = graphEvaluation query := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp graphEvaluation_partrec)
  exact ⟨p, fun query => congrFun hp query⟩

noncomputable def graphProgram : Program := Classical.choose graphProgram_exists

theorem graphProgram_domain (tag q v c out : Nat) :
    graphProgram.domain (Nat.pair (Nat.pair tag (Nat.pair q (Nat.pair v c))) out) ↔
      input tag q v c = true ∧ out = output tag q v c := by
  rw [Program.domain, Classical.choose_spec graphProgram_exists]
  simp only [graphEvaluation, data, Nat.unpair_pair]
  cases h : graph tag q v c out with
  | true => simp [h, (graph_exact tag q v c out).mp h]
  | false =>
    have hn : ¬(input tag q v c = true ∧ out = output tag q v c) := by
      intro he
      have ht := (graph_exact tag q v c out).mpr he
      simp only [h, Bool.false_eq_true] at ht
    simp [h, hn]

noncomputable def graphColumn (tag q v c : Nat) : Program :=
  graphProgram.column (Nat.pair tag (Nat.pair q (Nat.pair v c)))

theorem graphColumn_primrec : Primrec (fun p : Data => graphColumn p.1.1 p.1.2 p.2.1 p.2.2) :=
  Program.column_primrec.comp (Primrec.const graphProgram)
    (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.fst)
      (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst)
        (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))))

theorem graphColumn_domain (tag q v c out : Nat) : (graphColumn tag q v c).domain out ↔
    input tag q v c = true ∧ out = output tag q v c := by
  rw [graphColumn, Program.column_domain]
  exact graphProgram_domain tag q v c out

theorem graphColumn_execution (tag q v c out : Nat) : (graphColumn tag q v c).domain out ↔
    out ∈ (sourceColumn tag q v).eval c := by rw [graphColumn_domain, sourceColumn_graph]

theorem graphColumn_unique (tag q v c : Nat) (hi : input tag q v c = true) :
    ∃! out, (graphColumn tag q v c).domain out := by
  refine ⟨output tag q v c, (graphColumn_domain tag q v c _).mpr ⟨hi, rfl⟩, ?_⟩
  intro out ho
  exact ((graphColumn_domain tag q v c out).mp ho).2

end Alexander313.HereditaryNativeSourceChiBaseChangeProgram
