import Alexander313.Wilken.HereditaryNativeBaseTransformation

/-!
# Actual Programs for changing a native coded epsilon base

Tag 0 retains an originally admitted Par-bounded word; tag 1 additionally
requires original weak normality; tag 2 normalizes an original raw input
before testing the actual smaller-base bound. Unknown tags reject. The
finite syntax operation changes its real interpretation context, preserves
order and equality, and commutes with actual normalized addition.

The guards, outputs and complete literal output graphs, including zero, are
PR. Source Programs and positive input/graph Programs execute these kernels;
all fixed-context compiler columns are genuinely PR. The domain uses the
chosen presentation's atomic-stop bound. No unique printed Par set, target
one, arbitrary iota/mu, native spelling uniqueness or chi law is asserted.
All proof candidates remain uncompiled.
-/

namespace Alexander313.HereditaryNativeBaseTransformationProgram

open Wilken.RelativeTerm.Hereditary
open NativeContext

abbrev Data := (Nat × Nat) × (Nat × Nat)

def input (tag q v c : Nat) : Bool := cond (tag == 0) (BaseTransformation.inputCheck q v c)
  (cond (tag == 1) (BaseTransformation.normalInputCheck q v c)
    (cond (tag == 2) (BaseTransformation.rawInputCheck q v c) false))

theorem input_primrec : Primrec (fun p : Data => input p.1.1 p.1.2 p.2.1 p.2.2) := by
  have ht := Primrec.fst.comp Primrec.fst
  have hp := (Primrec.snd.comp Primrec.fst).pair Primrec.snd
  exact (Primrec.beq.comp ht (Primrec.const 0)).cond
    (BaseTransformation.inputCheck_primrec.comp hp)
    ((Primrec.beq.comp ht (Primrec.const 1)).cond
      (BaseTransformation.normalInputCheck_primrec.comp hp)
      ((Primrec.beq.comp ht (Primrec.const 2)).cond
        (BaseTransformation.rawInputCheck_primrec.comp hp) (Primrec.const false)))

theorem input_exact (tag q v c : Nat) : input tag q v c = true ↔
    (tag = 0 ∧ BaseTransformation.inputCheck q v c = true) ∨
      (tag = 1 ∧ BaseTransformation.normalInputCheck q v c = true) ∨
      (tag = 2 ∧ BaseTransformation.rawInputCheck q v c = true) := by
  by_cases h0 : tag = 0
  · subst tag; simp [input]
  · by_cases h1 : tag = 1
    · subst tag; simp [input]
    · by_cases h2 : tag = 2 <;> simp [input, h0, h1, h2]

theorem input_unknown (tag q v c : Nat) (h : 3 ≤ tag) : input tag q v c = false := by
  have h0 : tag ≠ 0 := by omega
  have h1 : tag ≠ 1 := by omega
  have h2 : tag ≠ 2 := by omega
  simp [input, h0, h1, h2]

def output (tag q v c : Nat) : Nat := cond (tag == 2) (BaseTransformation.rawPiCode q v c)
  (BaseTransformation.piCode q v c)

theorem output_primrec : Primrec (fun p : Data => output p.1.1 p.1.2 p.2.1 p.2.2) := by
  have ht := Primrec.fst.comp Primrec.fst
  have hp := (Primrec.snd.comp Primrec.fst).pair Primrec.snd
  exact (Primrec.beq.comp ht (Primrec.const 2)).cond
    (BaseTransformation.rawPiCode_primrec.comp hp) (BaseTransformation.piCode_primrec.comp hp)

theorem output_spec (tag q v c : Nat) (hi : input tag q v c = true) :
    checkCode q c = true ∧ checkCode q (output tag q v c) = true ∧
      checkCode v (output tag q v c) = true ∧
      interpretation q (output tag q v c) = interpretation q c := by
  rcases (input_exact tag q v c).mp hi with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
  · have hs := BaseTransformation.inputCheck_checks q v c h
    have he : checkCode q c = true ∧ checkCode q c = true ∧ checkCode v c = true ∧
        interpretation q c = interpretation q c := ⟨hs.1, hs.1, hs.2.1, rfl⟩
    simpa only [output, show (0 == 2) = false from rfl, Bool.cond_false,
      BaseTransformation.piCode_eq q v c h] using he
  · have hh := ((BaseTransformation.normalInputCheck_exact q v c).mp h).1
    have hs := BaseTransformation.inputCheck_checks q v c hh
    have he : checkCode q c = true ∧ checkCode q c = true ∧ checkCode v c = true ∧
        interpretation q c = interpretation q c := ⟨hs.1, hs.1, hs.2.1, rfl⟩
    simpa only [output, show (1 == 2) = false from rfl, Bool.cond_false,
      BaseTransformation.piCode_eq q v c hh] using he
  · have hs := BaseTransformation.rawPiCode_spec q v c h
    exact ⟨(Bool.and_eq_true.mp h).1,
      ((Comparison.acceptedCode_exact q _).mp hs.1).1,
      ((Comparison.acceptedCode_exact v _).mp hs.2.1).1, hs.2.2⟩

theorem output_normal (tag q v c : Nat) (hi : input tag q v c = true) (ht : tag = 1 ∨ tag = 2) :
    Comparison.acceptedCode v (output tag q v c) = true := by
  rcases ht with rfl | rfl
  · have hh : BaseTransformation.normalInputCheck q v c = true := by simpa [input] using hi
    simpa [output] using BaseTransformation.piCode_normal q v c hh
  · have hh : BaseTransformation.rawInputCheck q v c = true := by simpa [input] using hi
    exact (BaseTransformation.rawPiCode_spec q v c hh).2.1

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

theorem program_exists : ∃ p : Program, ∀ query, p.eval query = evaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp evaluation_partrec)

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

theorem sourceColumn_correct (tag q v c out : Nat) (ho : out ∈ (sourceColumn tag q v).eval c) :
    checkCode q c = true ∧ checkCode q out = true ∧ checkCode v out = true ∧
      interpretation q out = interpretation q c := by
  obtain ⟨hi, rfl⟩ := (sourceColumn_graph tag q v c out).mp ho
  exact output_spec tag q v c hi

theorem sourceColumn_order (tag tag' q v c d out out' : Nat)
    (hc : out ∈ (sourceColumn tag q v).eval c) (hd : out' ∈ (sourceColumn tag' q v).eval d) :
    interpretation q c < interpretation q d ↔ interpretation v out < interpretation v out' := by
  have hs := sourceColumn_correct tag q v c out hc
  have ht := sourceColumn_correct tag' q v d out' hd
  simpa only [Arithmetic.raw_value q out hs.2.1, Arithmetic.raw_value q out' ht.2.1,
    Arithmetic.raw_value v out hs.2.2.1, Arithmetic.raw_value v out' ht.2.2.1, hs.2.2.2, ht.2.2.2] using
      BaseTransformation.raw_less_iff q v _ _ (Arithmetic.raw_checked q out hs.2.1)
        (Arithmetic.raw_checked q out' ht.2.1) (Arithmetic.raw_checked v out hs.2.2.1)
          (Arithmetic.raw_checked v out' ht.2.2.1)

theorem piColumn_domain (q v c : Nat) : (sourceColumn 0 q v).domain c ↔
    checkCode q c = true ∧ baseCheck v = true ∧ base v < base q ∧
      BaseTransformation.ParBounded q v (ThetaCourse.rawTree c) := by
  rw [sourceColumn_domain]
  simpa [input] using BaseTransformation.inputCheck_exact q v c

theorem rawColumn_domain (q v c : Nat) : (sourceColumn 2 q v).domain c ↔
    checkCode q c = true ∧ baseCheck v = true ∧ base v < base q ∧
      BaseTransformation.ParBounded q v (ThetaCourse.rawTree (Normalization.normalizeCode q c)) := by
  rw [sourceColumn_domain]
  simpa [input] using BaseTransformation.rawInputCheck_exact q v c

def inputEvaluation (query : Nat) : Part Nat :=
  let p := data query
  cond (input p.1.1 p.1.2 p.2.1 p.2.2) (Part.some 1) Part.none

theorem inputEvaluation_partrec : Partrec inputEvaluation :=
  Partrec.cond (input_primrec.comp data_primrec).to_comp (Computable.const 1).partrec Partrec.none

theorem inputProgram_exists : ∃ p : Program, ∀ query, p.eval query = inputEvaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp inputEvaluation_partrec)

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

theorem graphProgram_exists : ∃ p : Program, ∀ query, p.eval query = graphEvaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp graphEvaluation_partrec)

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

end Alexander313.HereditaryNativeBaseTransformationProgram
