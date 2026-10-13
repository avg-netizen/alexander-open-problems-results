import Alexander313.Wilken.HereditaryNativeRightSubtraction

/-!
# Actual native source dotted-right-subtraction Programs

Tag zero executes on both original checked native inputs at any genuine
coded epsilon context and every sort. Tag one restricts those inputs to
weak Normal. Both execute the same actual finite ANF-value suffix matcher.
Unknown tags/malformed contexts or trees reject. Every answer is admitted,
normal, has height at most the left input and satisfies the ALL-ordinal
least-solution/source fallback contract. This is a dotminus b, not the
earlier left removal (Mathlib b-a).

The actual finite producer, positive input and complete literal numerical
graph have genuine PR kernels. All Program compiler columns are PR. Graphs
include answer zero and certify the chosen spelling, not every equal-valued
native code. All source candidates remain uncompiled.
-/

namespace Alexander313.HereditaryNativeRightSubtractionProgram

open Wilken.RelativeTerm.Hereditary

abbrev Data := (Nat × Nat) × (Nat × Nat)

def normalInput (q c d : Nat) : Bool :=
  NativeContext.Comparison.acceptedCode q c && NativeContext.Comparison.acceptedCode q d

theorem normalInput_primrec : Primrec
    (fun p : Nat × (Nat × Nat) => normalInput p.1 p.2.1 p.2.2) :=
  Primrec.and.comp (NativeContext.Comparison.acceptedCode_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
    (NativeContext.Comparison.acceptedCode_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd))

def input (tag q c d : Nat) : Bool := cond (tag == 0) (NativeContext.RightSubtraction.inputCheck q c d)
  (cond (tag == 1) (normalInput q c d) false)

theorem input_primrec : Primrec (fun p : Data => input p.1.1 p.1.2 p.2.1 p.2.2) := by
  have ht := Primrec.fst.comp Primrec.fst
  have hp := (Primrec.snd.comp Primrec.fst).pair
    ((Primrec.fst.comp Primrec.snd).pair (Primrec.snd.comp Primrec.snd))
  exact (Primrec.beq.comp ht (Primrec.const 0)).cond (NativeContext.RightSubtraction.inputCheck_primrec.comp hp)
    ((Primrec.beq.comp ht (Primrec.const 1)).cond (normalInput_primrec.comp hp) (Primrec.const false))

theorem input_exact (tag q c d : Nat) : input tag q c d = true ↔
    (tag = 0 ∧ NativeContext.checkCode q c = true ∧ NativeContext.checkCode q d = true) ∨
      (tag = 1 ∧ NativeContext.Comparison.acceptedCode q c = true ∧ NativeContext.Comparison.acceptedCode q d = true) := by
  by_cases h0 : tag = 0
  · subst tag; simp [input, NativeContext.RightSubtraction.inputCheck_exact]
  · by_cases h1 : tag = 1 <;> simp [input, h0, h1, normalInput]

theorem input_raw (tag q c d : Nat) (hi : input tag q c d = true) :
    NativeContext.checkCode q c = true ∧ NativeContext.checkCode q d = true := by
  rcases (input_exact tag q c d).mp hi with ⟨_, hc, hd⟩ | ⟨_, hc, hd⟩
  · exact ⟨hc, hd⟩
  · exact ⟨((NativeContext.Comparison.acceptedCode_exact q c).mp hc).1,
      ((NativeContext.Comparison.acceptedCode_exact q d).mp hd).1⟩

def data (query : Nat) : Data :=
  ((query.unpair.1, query.unpair.2.unpair.1),
    (query.unpair.2.unpair.2.unpair.1, query.unpair.2.unpair.2.unpair.2))

theorem data_primrec : Primrec data := by
  have ht := Primrec.unpair
  have hq := Primrec.unpair.comp (Primrec.snd.comp ht)
  have hp := Primrec.unpair.comp (Primrec.snd.comp hq)
  exact ((Primrec.fst.comp ht).pair (Primrec.fst.comp hq)).pair hp

def output (p : Data) : Nat := NativeContext.RightSubtraction.rightCode p.1.2 p.2.1 p.2.2

theorem output_primrec : Primrec output := NativeContext.RightSubtraction.rightCode_primrec.comp
  ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)

def evaluation (query : Nat) : Part Nat :=
  let p := data query
  cond (input p.1.1 p.1.2 p.2.1 p.2.2) (Part.some (output p)) Part.none

theorem evaluation_partrec : Partrec evaluation :=
  Partrec.cond (input_primrec.comp data_primrec).to_comp (output_primrec.comp data_primrec).to_comp.partrec Partrec.none

theorem program_exists : ∃ p : Program, ∀ query, p.eval query = evaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp evaluation_partrec)

noncomputable def program : Program := Classical.choose program_exists

theorem program_eval (tag q c d : Nat) : program.eval (Nat.pair tag (Nat.pair q (Nat.pair c d))) =
    cond (input tag q c d) (Part.some (NativeContext.RightSubtraction.rightCode q c d)) Part.none := by
  simpa only [evaluation, data, output, Nat.unpair_pair] using
    Classical.choose_spec program_exists (Nat.pair tag (Nat.pair q (Nat.pair c d)))

theorem program_domain (tag q c d : Nat) : program.domain (Nat.pair tag (Nat.pair q (Nat.pair c d))) ↔ input tag q c d = true := by
  rw [Program.domain, program_eval]
  cases hi : input tag q c d <;> simp [hi]

theorem program_graph (tag q c d out : Nat) : out ∈ program.eval (Nat.pair tag (Nat.pair q (Nat.pair c d))) ↔
    input tag q c d = true ∧ out = NativeContext.RightSubtraction.rightCode q c d := by
  rw [program_eval]
  cases hi : input tag q c d <;> simp [hi, eq_comm]

noncomputable def sourceColumn (tag q c : Nat) : Program := ((program.column tag).column q).column c

theorem sourceColumn_primrec : Primrec (fun p : Nat × (Nat × Nat) => sourceColumn p.1 p.2.1 p.2.2) :=
  Program.column_primrec.comp
    (Program.column_primrec.comp (Program.column_primrec.comp (Primrec.const program) Primrec.fst)
      (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)

theorem sourceColumn_eval (tag q c d : Nat) : (sourceColumn tag q c).eval d =
    cond (input tag q c d) (Part.some (NativeContext.RightSubtraction.rightCode q c d)) Part.none := by
  simp only [sourceColumn, Nat.Partrec.Code.eval_curry, program_eval]

theorem sourceColumn_domain (tag q c d : Nat) : (sourceColumn tag q c).domain d ↔ input tag q c d = true := by
  simp only [sourceColumn, Program.column_domain]
  exact program_domain tag q c d

theorem sourceColumn_graph (tag q c d out : Nat) : out ∈ (sourceColumn tag q c).eval d ↔
    input tag q c d = true ∧ out = NativeContext.RightSubtraction.rightCode q c d := by
  simp only [sourceColumn, Nat.Partrec.Code.eval_curry]
  exact program_graph tag q c d out

theorem rawColumn_domain (q c d : Nat) : (sourceColumn 0 q c).domain d ↔
    NativeContext.checkCode q c = true ∧ NativeContext.checkCode q d = true := by
  simp [sourceColumn_domain, input, NativeContext.RightSubtraction.inputCheck_exact]

theorem normalColumn_domain (q c d : Nat) : (sourceColumn 1 q c).domain d ↔
    NativeContext.Comparison.acceptedCode q c = true ∧ NativeContext.Comparison.acceptedCode q d = true := by
  simp [sourceColumn_domain, input, normalInput]

theorem sourceColumn_spec (tag q c d out : Nat) (ho : out ∈ (sourceColumn tag q c).eval d) :
    input tag q c d = true ∧ NativeContext.Comparison.acceptedCode q out = true ∧
      NativeContext.interpretation q out = Wilken.OrdinalRightSubtraction.rightSubtract
        (NativeContext.interpretation q c) (NativeContext.interpretation q d) ∧
      Wilken.RelativeTerm.heightCode out ≤ Wilken.RelativeTerm.heightCode c := by
  obtain ⟨hi, rfl⟩ := (sourceColumn_graph tag q c d out).mp ho
  have hc := input_raw tag q c d hi
  exact ⟨hi, NativeContext.RightSubtraction.rightCode_spec q c d hc.1 hc.2⟩

theorem sourceColumn_source (tag q c d out : Nat) (ho : out ∈ (sourceColumn tag q c).eval d) :
    Wilken.OrdinalRightSubtraction.SourceSpec (NativeContext.interpretation q c) (NativeContext.interpretation q d)
      (NativeContext.interpretation q out) := by
  rw [(sourceColumn_spec tag q c d out ho).2.2.1]
  exact Wilken.OrdinalRightSubtraction.rightSubtract_spec _ _

theorem sourceColumn_fragment (tag q n c d out : Nat)
    (hc : NativeContext.Height.fragmentCheck q n c = true) (ho : out ∈ (sourceColumn tag q c).eval d) :
    NativeContext.Height.fragmentCheck q n out = true := by
  obtain ⟨hi, rfl⟩ := (sourceColumn_graph tag q c d out).mp ho
  exact NativeContext.RightSubtraction.rightCode_fragment q n c d hc (input_raw tag q c d hi).2

theorem sourceColumn_unique (tag q c d : Nat) (hi : input tag q c d = true) :
    ∃! out, out ∈ (sourceColumn tag q c).eval d := by
  refine ⟨NativeContext.RightSubtraction.rightCode q c d, (sourceColumn_graph tag q c d _).mpr ⟨hi, rfl⟩, ?_⟩
  intro out ho
  exact ((sourceColumn_graph tag q c d out).mp ho).2

def inputEvaluation (query : Nat) : Part Nat :=
  let p := data query
  cond (input p.1.1 p.1.2 p.2.1 p.2.2) (Part.some 1) Part.none

theorem inputEvaluation_partrec : Partrec inputEvaluation :=
  Partrec.cond (input_primrec.comp data_primrec).to_comp (Computable.const 1).partrec Partrec.none

theorem inputProgram_exists : ∃ p : Program, ∀ query, p.eval query = inputEvaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp inputEvaluation_partrec)

noncomputable def inputProgram : Program := Classical.choose inputProgram_exists

theorem inputProgram_domain (tag q c d : Nat) : inputProgram.domain (Nat.pair tag (Nat.pair q (Nat.pair c d))) ↔
    input tag q c d = true := by
  rw [Program.domain, Classical.choose_spec inputProgram_exists]
  simp only [inputEvaluation, data, Nat.unpair_pair]
  cases hi : input tag q c d <;> simp [hi]

noncomputable def inputColumn (tag q : Nat) : Program := (inputProgram.column tag).column q

theorem inputColumn_primrec : Primrec₂ inputColumn :=
  (Program.column_primrec.comp (Program.column_primrec.comp (Primrec.const inputProgram) Primrec.fst) Primrec.snd).to₂

theorem inputColumn_domain (tag q c d : Nat) : (inputColumn tag q).domain (Nat.pair c d) ↔ input tag q c d = true := by
  simp only [inputColumn, Program.column_domain]
  exact inputProgram_domain tag q c d

def graph (p : Data) (out : Nat) : Bool := input p.1.1 p.1.2 p.2.1 p.2.2 && (out == output p)

theorem graph_primrec : Primrec₂ graph :=
  (Primrec.and.comp (input_primrec.comp Primrec.fst)
    (Primrec.beq.comp Primrec.snd (output_primrec.comp Primrec.fst))).to₂

theorem graph_exact (p : Data) (out : Nat) : graph p out = true ↔
    input p.1.1 p.1.2 p.2.1 p.2.2 = true ∧ out = output p := by
  simp only [graph, Bool.and_eq_true, beq_iff_eq]

def graphEvaluation (query : Nat) : Part Nat :=
  cond (graph (data query.unpair.1) query.unpair.2) (Part.some 1) Part.none

theorem graphEvaluation_partrec : Partrec graphEvaluation :=
  Partrec.cond (graph_primrec.comp (data_primrec.comp (Primrec.fst.comp Primrec.unpair))
    (Primrec.snd.comp Primrec.unpair)).to_comp (Computable.const 1).partrec Partrec.none

theorem graphProgram_exists : ∃ p : Program, ∀ query, p.eval query = graphEvaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp graphEvaluation_partrec)

noncomputable def graphProgram : Program := Classical.choose graphProgram_exists

theorem graphProgram_domain (tag q c d out : Nat) :
    graphProgram.domain (Nat.pair (Nat.pair tag (Nat.pair q (Nat.pair c d))) out) ↔
      input tag q c d = true ∧ out = NativeContext.RightSubtraction.rightCode q c d := by
  rw [Program.domain, Classical.choose_spec graphProgram_exists]
  simp only [graphEvaluation, data, Nat.unpair_pair]
  cases hg : graph ((tag, q), (c, d)) out with
  | true =>
    have hs : input tag q c d = true ∧ out = NativeContext.RightSubtraction.rightCode q c d :=
      (graph_exact ((tag, q), (c, d)) out).mp hg
    simp [hg, hs]
  | false =>
    have hn : ¬ (input tag q c d = true ∧ out = NativeContext.RightSubtraction.rightCode q c d) := by
      intro he
      have ht := (graph_exact ((tag, q), (c, d)) out).mpr he
      simp only [hg, Bool.false_eq_true] at ht
    simp [hg, hn]

noncomputable def graphColumn (tag q c d : Nat) : Program :=
  graphProgram.column (Nat.pair tag (Nat.pair q (Nat.pair c d)))

theorem graphColumn_primrec : Primrec (fun p : Data => graphColumn p.1.1 p.1.2 p.2.1 p.2.2) :=
  Program.column_primrec.comp (Primrec.const graphProgram)
    (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.fst)
      (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst)
        (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))))

theorem graphColumn_domain (tag q c d out : Nat) : (graphColumn tag q c d).domain out ↔
    input tag q c d = true ∧ out = NativeContext.RightSubtraction.rightCode q c d := by
  rw [graphColumn, Program.column_domain]
  exact graphProgram_domain tag q c d out

theorem graphColumn_execution (tag q c d out : Nat) : (graphColumn tag q c d).domain out ↔
    out ∈ (sourceColumn tag q c).eval d :=
  (graphColumn_domain tag q c d out).trans (sourceColumn_graph tag q c d out).symm

end Alexander313.HereditaryNativeRightSubtractionProgram
