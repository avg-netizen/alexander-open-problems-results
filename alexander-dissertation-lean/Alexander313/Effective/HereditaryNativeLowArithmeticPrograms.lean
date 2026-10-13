import Alexander313.Wilken.HereditaryNativeLowArithmetic

/-!
# Executing low arithmetic in the same positive public epsilon context

Tags 0/1 execute genuine multiplication/general power on both original raw
native LOW inputs; tags 2/3/4/5 execute first log/last log/positive principal
log/omega power on the left input, ignoring the right payload. The principal
tag additionally derives the real positive additive-principal guard. Every
answer returns to contextCode s with original low admission and weak Normal.

The numerical graph executes the actual producer and compares its literal
chosen answer, including zero. Searches and graph execution are Partrec;
finite omega production and all Program column compilers are separately PR.
No full-sort/arbitrary-epsilon arithmetic or native recoding oracle is used.
All proof terms are uncompiled source candidates.
-/

namespace Alexander313.HereditaryNativeLowArithmeticProgram

open Wilken.RelativeTerm.Hereditary

abbrev Data := (Nat × Nat) × (Nat × Nat)

def data (query : Nat) : Data :=
  ((query.unpair.1, query.unpair.2.unpair.1),
    (query.unpair.2.unpair.2.unpair.1, query.unpair.2.unpair.2.unpair.2))

theorem data_primrec : Primrec data := by
  have ht := Primrec.unpair
  have hs := Primrec.unpair.comp (Primrec.snd.comp ht)
  have hp := Primrec.unpair.comp (Primrec.snd.comp hs)
  exact ((Primrec.fst.comp ht).pair (Primrec.fst.comp hs)).pair hp

def evaluation (query : Nat) : Part Nat :=
  let p := data query
  NativeContext.LowArithmetic.operation p.1.1 p.1.2 p.2.1 p.2.2

theorem evaluation_partrec : Partrec evaluation :=
  NativeContext.LowArithmetic.operation_partrec.comp data_primrec.to_comp

theorem program_exists : ∃ p : Program, ∀ query, p.eval query = evaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp evaluation_partrec)

noncomputable def program : Program := Classical.choose program_exists

theorem program_eval (tag s c d : Nat) :
    program.eval (Nat.pair tag (Nat.pair s (Nat.pair c d))) = NativeContext.LowArithmetic.operation tag s c d := by
  simpa only [evaluation, data, Nat.unpair_pair] using
    Classical.choose_spec program_exists (Nat.pair tag (Nat.pair s (Nat.pair c d)))

theorem program_domain (tag s c d : Nat) : program.domain (Nat.pair tag (Nat.pair s (Nat.pair c d))) ↔
    NativeContext.LowArithmetic.input tag s c d = true := by
  rw [Program.domain, program_eval, NativeContext.LowArithmetic.operation_domain]

noncomputable def sourceColumn (tag s c : Nat) : Program := ((program.column tag).column s).column c

theorem sourceColumn_primrec : Primrec (fun p : Nat × (Nat × Nat) => sourceColumn p.1 p.2.1 p.2.2) :=
  Program.column_primrec.comp
    (Program.column_primrec.comp (Program.column_primrec.comp (Primrec.const program) Primrec.fst)
      (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)

theorem sourceColumn_eval (tag s c d : Nat) : (sourceColumn tag s c).eval d =
    NativeContext.LowArithmetic.operation tag s c d := by
  simp only [sourceColumn, Nat.Partrec.Code.eval_curry, program_eval]

theorem sourceColumn_domain (tag s c d : Nat) : (sourceColumn tag s c).domain d ↔
    NativeContext.LowArithmetic.input tag s c d = true := by
  simp only [sourceColumn, Program.column_domain]
  exact program_domain tag s c d

theorem multiplyColumn_domain (s c d : Nat) : (sourceColumn 0 s c).domain d ↔
    NativeContext.lowCheckCode (NativePublicBridge.contextCode s) c = true ∧
      NativeContext.lowCheckCode (NativePublicBridge.contextCode s) d = true := by
  simp [sourceColumn_domain, NativeContext.LowArithmetic.input, NativeContext.LowArithmetic.lowInput]

theorem powerColumn_domain (s c d : Nat) : (sourceColumn 1 s c).domain d ↔
    NativeContext.lowCheckCode (NativePublicBridge.contextCode s) c = true ∧
      NativeContext.lowCheckCode (NativePublicBridge.contextCode s) d = true := by
  simp [sourceColumn_domain, NativeContext.LowArithmetic.input, NativeContext.LowArithmetic.lowInput]

theorem leadingLogColumn_domain (s c d : Nat) : (sourceColumn 2 s c).domain d ↔
    NativeContext.lowCheckCode (NativePublicBridge.contextCode s) c = true := by
  simp [sourceColumn_domain, NativeContext.LowArithmetic.input, NativeContext.LowArithmetic.lowInput]

theorem logendColumn_domain (s c d : Nat) : (sourceColumn 3 s c).domain d ↔
    NativeContext.lowCheckCode (NativePublicBridge.contextCode s) c = true := by
  simp [sourceColumn_domain, NativeContext.LowArithmetic.input, NativeContext.LowArithmetic.lowInput]

theorem principalLogColumn_domain (s c d : Nat) : (sourceColumn 4 s c).domain d ↔
    NativeContext.LowArithmetic.lowInput s c = true ∧
      0 < NativeContext.interpretation (NativePublicBridge.contextCode s) c ∧
      Ordinal.IsPrincipal (· + ·) (NativeContext.interpretation (NativePublicBridge.contextCode s) c) := by
  simp [sourceColumn_domain, NativeContext.LowArithmetic.input, NativeContext.LowArithmetic.principalInput_exact]

theorem omegaColumn_domain (s c d : Nat) : (sourceColumn 5 s c).domain d ↔
    NativeContext.lowCheckCode (NativePublicBridge.contextCode s) c = true := by
  simp [sourceColumn_domain, NativeContext.LowArithmetic.input, NativeContext.LowArithmetic.lowInput]

theorem sourceColumn_spec (tag s c d out : Nat) (ho : out ∈ (sourceColumn tag s c).eval d) :
    NativeContext.LowArithmetic.input tag s c d = true ∧
      NativeContext.lowCheckCode (NativePublicBridge.contextCode s) out = true ∧
      NativeContext.Comparison.acceptedCode (NativePublicBridge.contextCode s) out = true ∧
      NativeContext.interpretation (NativePublicBridge.contextCode s) out < finiteBase ((s + 1) + 1) ∧
      NativeContext.LowArithmetic.ResultSpec tag
        (NativeContext.interpretation (NativePublicBridge.contextCode s) c)
        (NativeContext.interpretation (NativePublicBridge.contextCode s) d)
        (NativeContext.interpretation (NativePublicBridge.contextCode s) out) :=
  NativeContext.LowArithmetic.operation_spec tag s c d out (by simpa only [sourceColumn_eval] using ho)

theorem multiplyColumn_value (s c d out : Nat) (ho : out ∈ (sourceColumn 0 s c).eval d) :
    NativeContext.interpretation (NativePublicBridge.contextCode s) out =
      NativeContext.interpretation (NativePublicBridge.contextCode s) c * NativeContext.interpretation (NativePublicBridge.contextCode s) d := by
  simpa [NativeContext.LowArithmetic.ResultSpec] using (sourceColumn_spec 0 s c d out ho).2.2.2.2

theorem powerColumn_value (s c d out : Nat) (ho : out ∈ (sourceColumn 1 s c).eval d) :
    NativeContext.interpretation (NativePublicBridge.contextCode s) out =
      NativeContext.interpretation (NativePublicBridge.contextCode s) c ^ NativeContext.interpretation (NativePublicBridge.contextCode s) d := by
  simpa [NativeContext.LowArithmetic.ResultSpec] using (sourceColumn_spec 1 s c d out ho).2.2.2.2

theorem leadingLogColumn_value (s c d out : Nat) (ho : out ∈ (sourceColumn 2 s c).eval d) :
    LogEnd.SourceLogSpec false (NativeContext.interpretation (NativePublicBridge.contextCode s) c)
      (NativeContext.interpretation (NativePublicBridge.contextCode s) out) := by
  simpa [NativeContext.LowArithmetic.ResultSpec] using (sourceColumn_spec 2 s c d out ho).2.2.2.2

theorem logendColumn_value (s c d out : Nat) (ho : out ∈ (sourceColumn 3 s c).eval d) :
    LogEnd.SourceLogSpec true (NativeContext.interpretation (NativePublicBridge.contextCode s) c)
      (NativeContext.interpretation (NativePublicBridge.contextCode s) out) := by
  simpa [NativeContext.LowArithmetic.ResultSpec] using (sourceColumn_spec 3 s c d out ho).2.2.2.2

theorem principalLogColumn_value (s c d out : Nat) (ho : out ∈ (sourceColumn 4 s c).eval d) :
    Ordinal.omega0 ^ NativeContext.interpretation (NativePublicBridge.contextCode s) out =
      NativeContext.interpretation (NativePublicBridge.contextCode s) c := by
  simpa [NativeContext.LowArithmetic.ResultSpec] using (sourceColumn_spec 4 s c d out ho).2.2.2.2

theorem omegaColumn_eval (s c d : Nat) : (sourceColumn 5 s c).eval d =
    cond (NativeContext.LowArithmetic.lowInput s c) (Part.some (NativeContext.LowArithmetic.omegaCode s c)) Part.none := by
  rw [sourceColumn_eval, NativeContext.LowArithmetic.operation_omegaCode]

theorem sourceColumn_unique (tag s c d : Nat) (hi : NativeContext.LowArithmetic.input tag s c d = true) :
    ∃! out, out ∈ (sourceColumn tag s c).eval d := by
  rw [sourceColumn_eval]
  exact NativeContext.LowArithmetic.operation_unique tag s c d hi

theorem sourceColumn_invariant (tag s c d c' d' out out' : Nat)
    (ho : out ∈ (sourceColumn tag s c).eval d) (ho' : out' ∈ (sourceColumn tag s c').eval d')
    (hc : NativeContext.interpretation (NativePublicBridge.contextCode s) c = NativeContext.interpretation (NativePublicBridge.contextCode s) c')
    (hd : NativeContext.interpretation (NativePublicBridge.contextCode s) d = NativeContext.interpretation (NativePublicBridge.contextCode s) d') : out = out' :=
  NativeContext.LowArithmetic.operation_invariant tag s c d c' d' out out'
    (by simpa only [sourceColumn_eval] using ho) (by simpa only [sourceColumn_eval] using ho') hc hd

def inputEvaluation (query : Nat) : Part Nat :=
  let p := data query
  cond (NativeContext.LowArithmetic.input p.1.1 p.1.2 p.2.1 p.2.2) (Part.some 1) Part.none

theorem inputEvaluation_partrec : Partrec inputEvaluation :=
  Partrec.cond (NativeContext.LowArithmetic.input_primrec.comp data_primrec).to_comp
    (Computable.const 1).partrec Partrec.none

theorem inputProgram_exists : ∃ p : Program, ∀ query, p.eval query = inputEvaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp inputEvaluation_partrec)

noncomputable def inputProgram : Program := Classical.choose inputProgram_exists

theorem inputProgram_domain (tag s c d : Nat) :
    inputProgram.domain (Nat.pair tag (Nat.pair s (Nat.pair c d))) ↔ NativeContext.LowArithmetic.input tag s c d = true := by
  rw [Program.domain, Classical.choose_spec inputProgram_exists]
  simp only [inputEvaluation, data, Nat.unpair_pair]
  cases hi : NativeContext.LowArithmetic.input tag s c d <;> simp [hi]

noncomputable def inputColumn (tag s : Nat) : Program := (inputProgram.column tag).column s

theorem inputColumn_primrec : Primrec₂ inputColumn :=
  (Program.column_primrec.comp (Program.column_primrec.comp (Primrec.const inputProgram) Primrec.fst) Primrec.snd).to₂

theorem inputColumn_domain (tag s c d : Nat) : (inputColumn tag s).domain (Nat.pair c d) ↔
    NativeContext.LowArithmetic.input tag s c d = true := by
  simp only [inputColumn, Program.column_domain]
  exact inputProgram_domain tag s c d

/-- The complete graph runs the actual search and tests its literal answer.
It certifies answer zero as well as every other natural output. -/
def graphEvaluation (query : Nat) : Part Nat := (evaluation query.unpair.1).bind
  (fun answer => cond (query.unpair.2 == answer) (Part.some 1) Part.none)

theorem graphEvaluation_partrec : Partrec graphEvaluation := by
  have hf := evaluation_partrec.comp (Primrec.fst.comp Primrec.unpair).to_comp
  have hg : Partrec₂ (fun query answer : Nat => cond (query.unpair.2 == answer) (Part.some 1) Part.none) :=
    (Partrec.cond (Primrec.beq.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)) Primrec.snd).to_comp
      (Computable.const 1).partrec Partrec.none).to₂
  exact hf.bind hg

theorem graphEvaluation_domain (query : Nat) : (graphEvaluation query).Dom ↔ query.unpair.2 ∈ evaluation query.unpair.1 := by
  constructor
  · intro h
    obtain ⟨value, hv⟩ := Part.dom_iff_mem.mp h
    obtain ⟨answer, ha, ht⟩ := Part.mem_bind_iff.mp hv
    cases he : query.unpair.2 == answer with
    | false => simp only [he, Bool.cond_false, Part.notMem_none] at ht
    | true => exact (beq_iff_eq.mp he).symm ▸ ha
  · intro ho
    exact Part.dom_iff_mem.mpr ⟨1, Part.mem_bind ho (by simp)⟩

theorem graphProgram_exists : ∃ p : Program, ∀ query, p.eval query = graphEvaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp graphEvaluation_partrec)

noncomputable def graphProgram : Program := Classical.choose graphProgram_exists

theorem graphProgram_domain (tag s c d out : Nat) :
    graphProgram.domain (Nat.pair (Nat.pair tag (Nat.pair s (Nat.pair c d))) out) ↔
      out ∈ NativeContext.LowArithmetic.operation tag s c d := by
  rw [Program.domain, Classical.choose_spec graphProgram_exists, graphEvaluation_domain]
  simp only [evaluation, data, Nat.unpair_pair]

noncomputable def graphColumn (tag s c d : Nat) : Program :=
  graphProgram.column (Nat.pair tag (Nat.pair s (Nat.pair c d)))

theorem graphColumn_primrec : Primrec (fun p : Data => graphColumn p.1.1 p.1.2 p.2.1 p.2.2) :=
  Program.column_primrec.comp (Primrec.const graphProgram)
    (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.fst)
      (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst)
        (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))))

theorem graphColumn_domain (tag s c d out : Nat) : (graphColumn tag s c d).domain out ↔
    out ∈ (sourceColumn tag s c).eval d := by
  rw [graphColumn, Program.column_domain, graphProgram_domain, sourceColumn_eval]

theorem graphColumn_unique (tag s c d : Nat) (hi : NativeContext.LowArithmetic.input tag s c d = true) :
    ∃! out, (graphColumn tag s c d).domain out := by
  simpa only [graphColumn_domain] using sourceColumn_unique tag s c d hi

end Alexander313.HereditaryNativeLowArithmeticProgram
