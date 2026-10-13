import Alexander313.Wilken.HereditaryNativeSourceChiPowers

/-!
# Executing source logend and omega-power indicator Programs

Tags zero and one execute omega power and logend of the ORIGINAL proper
theta-zero input, then run the genuine native indicator on that actual
returned code. The logend producer really runs its terminating search;
there is no primitive-recursive search bound. The proved arithmetic chi
law gives a finite PR numerical graph, including both zero and one.
Original context, argument, weak-normality, theta admission and nonzero
guards are retained. All proof candidates remain uncompiled.
-/

namespace Alexander313.HereditaryNativeSourceChiPowersProgram

open Wilken.RelativeTerm.Hereditary
open Wilken.RelativeTerm.Hereditary.NativeContext
open Wilken.RelativeTerm.Hereditary.NativeContext.SourceChi.Powers

abbrev Data := Nat × (Nat × Nat)

def input (tag s a : Nat) : Bool := ((tag == 0) || (tag == 1)) && sourceInput s a

theorem input_primrec : Primrec (fun p : Data => input p.1 p.2.1 p.2.2) :=
  Primrec.and.comp (Primrec.or.comp (Primrec.beq.comp Primrec.fst (Primrec.const 0))
    (Primrec.beq.comp Primrec.fst (Primrec.const 1)))
    (sourceInput_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))

theorem input_exact (tag s a : Nat) : input tag s a = true ↔
    (tag = 0 ∨ tag = 1) ∧ sourceInput s a = true := by
  simp only [input, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]

def arithmeticTag (tag : Nat) : Nat := cond (tag == 0) 5 3

theorem arithmeticTag_primrec : Primrec arithmeticTag :=
  (Primrec.beq.comp Primrec.id (Primrec.const 0)).cond (Primrec.const 5) (Primrec.const 3)

def sourceOperation (tag s a : Nat) : Part Nat := cond (input tag s a)
  (LowArithmetic.operation (arithmeticTag tag) s (SourceChi.Arithmetic.rightCode a) 0) Part.none

theorem sourceOperation_partrec : Partrec
    (fun p : Data => sourceOperation p.1 p.2.1 p.2.2) := by
  have hp := ((arithmeticTag_primrec.comp Primrec.fst).pair (Primrec.fst.comp Primrec.snd)).pair
    ((SourceChi.Arithmetic.rightCode_primrec.comp (Primrec.snd.comp Primrec.snd)).pair (Primrec.const 0))
  exact Partrec.cond input_primrec.to_comp (LowArithmetic.operation_partrec.comp hp.to_comp) Partrec.none

theorem sourceOperation_domain (tag s a : Nat) : (sourceOperation tag s a).Dom ↔ input tag s a = true := by
  cases hi : input tag s a with
  | false => simp [sourceOperation, hi, Part.none]
  | true =>
    have hs := (input_exact tag s a).mp hi
    have hl := (sourceInput_low s a hs.2).1
    have hd : LowArithmetic.input (arithmeticTag tag) s (SourceChi.Arithmetic.rightCode a) 0 = true := by
      rcases hs.1 with rfl | rfl <;> simp [arithmeticTag, LowArithmetic.input, hl]
    simp only [sourceOperation, hi, Bool.cond_true]
    exact ⟨fun _ => rfl, fun _ => (LowArithmetic.operation_domain _ _ _ _).mpr hd⟩

theorem sourceOperation_spec (tag s a out : Nat) (ho : out ∈ sourceOperation tag s a) :
    input tag s a = true ∧ lowCheckCode (NativePublicBridge.contextCode s) out = true ∧
      SourceChi.inputCheck (NativePublicBridge.contextCode s) out = true ∧
      SourceChi.chiCode (NativePublicBridge.contextCode s) out =
        SourceChi.chiCode (NativePublicBridge.contextCode s) (SourceChi.Arithmetic.rightCode a) := by
  have hi := (sourceOperation_domain tag s a).mp (Part.dom_iff_mem.mpr ⟨out, ho⟩)
  have hs := (input_exact tag s a).mp hi
  have hm : out ∈ LowArithmetic.operation (arithmeticTag tag) s (SourceChi.Arithmetic.rightCode a) 0 := by
    simpa only [sourceOperation, hi, Bool.cond_true] using ho
  have hv := LowArithmetic.operation_spec _ _ _ _ out hm
  refine ⟨hi, hv.2.1, hv.2.2.1, ?_⟩
  rcases hs.1 with rfl | rfl
  · have he : out = LowArithmetic.omegaCode s (SourceChi.Arithmetic.rightCode a) := by
      have hc := LowArithmetic.operation_omegaCode s (SourceChi.Arithmetic.rightCode a) 0
      simpa only [arithmeticTag, beq_self_eq_true, Bool.cond_true, hc,
        (sourceInput_low s a hs.2).1, Bool.cond_true, Part.mem_some_iff, eq_comm] using hm
    rw [he]
    exact source_lemma_3_5_a_omega s a hs.2
  · exact source_lemma_3_5_a_logend s a out hs.2 (by
      simpa [arithmeticTag] using hm)

def numeral (b : Bool) : Nat := cond b 1 0

theorem numeral_primrec : Primrec numeral := Primrec.id.cond (Primrec.const 1) (Primrec.const 0)

def sourceAnswer (s a : Nat) : Nat :=
  numeral (SourceChi.chiCode (NativePublicBridge.contextCode s) (SourceChi.Arithmetic.rightCode a))

theorem sourceAnswer_primrec : Primrec₂ sourceAnswer :=
  (numeral_primrec.comp (SourceChi.chiCode_primrec.comp
    (NativePublicBridge.contextCode_primrec.comp Primrec.fst)
    (SourceChi.Arithmetic.rightCode_primrec.comp Primrec.snd))).to₂

/-- This producer runs the actual arithmetic before inspecting its output. -/
def chiOperation (tag s a : Nat) : Part Nat := (sourceOperation tag s a).map
  (fun out => numeral (SourceChi.chiCode (NativePublicBridge.contextCode s) out))

theorem chiOperation_partrec : Partrec (fun p : Data => chiOperation p.1 p.2.1 p.2.2) := by
  have hv : Primrec₂ (fun p : Data => fun out =>
      numeral (SourceChi.chiCode (NativePublicBridge.contextCode p.2.1) out)) :=
    (numeral_primrec.comp (SourceChi.chiCode_primrec.comp
      (NativePublicBridge.contextCode_primrec.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
      Primrec.snd)).to₂
  exact Partrec.map sourceOperation_partrec hv.to_comp

theorem chiOperation_domain (tag s a : Nat) : (chiOperation tag s a).Dom ↔ input tag s a = true :=
  sourceOperation_domain tag s a

theorem chiOperation_literal (tag s a answer : Nat) : answer ∈ chiOperation tag s a ↔
    ∃ out ∈ sourceOperation tag s a,
      answer = numeral (SourceChi.chiCode (NativePublicBridge.contextCode s) out) := by
  rw [chiOperation, Part.mem_map_iff]
  constructor
  · rintro ⟨out, ho, he⟩
    exact ⟨out, ho, he.symm⟩
  · rintro ⟨out, ho, he⟩
    exact ⟨out, ho, he.symm⟩

theorem chiOperation_graph (tag s a answer : Nat) : answer ∈ chiOperation tag s a ↔
    input tag s a = true ∧ answer = sourceAnswer s a := by
  constructor
  · intro hm
    obtain ⟨out, ho, he⟩ := (chiOperation_literal tag s a answer).mp hm
    have hs := sourceOperation_spec tag s a out ho
    exact ⟨hs.1, by simpa only [sourceAnswer, hs.2.2.2] using he⟩
  · rintro ⟨hi, he⟩
    obtain ⟨out, ho⟩ := Part.dom_iff_mem.mp ((sourceOperation_domain tag s a).mpr hi)
    have hs := sourceOperation_spec tag s a out ho
    apply (chiOperation_literal tag s a answer).mpr
    exact ⟨out, ho, by simpa only [sourceAnswer, hs.2.2.2] using he⟩

def data (query : Nat) : Data :=
  (query.unpair.1, (query.unpair.2.unpair.1, query.unpair.2.unpair.2))

theorem data_primrec : Primrec data :=
  (Primrec.fst.comp Primrec.unpair).pair (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))

def evaluation (query : Nat) : Part Nat :=
  let p := data query
  chiOperation p.1 p.2.1 p.2.2

theorem evaluation_partrec : Partrec evaluation := chiOperation_partrec.comp data_primrec.to_comp

theorem program_exists : ∃ p : Program, ∀ query, p.eval query = evaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp evaluation_partrec)

noncomputable def program : Program := Classical.choose program_exists

theorem program_eval (tag s a : Nat) : program.eval (Nat.pair tag (Nat.pair s a)) = chiOperation tag s a := by
  simpa only [evaluation, data, Nat.unpair_pair] using
    Classical.choose_spec program_exists (Nat.pair tag (Nat.pair s a))

theorem program_domain (tag s a : Nat) : program.domain (Nat.pair tag (Nat.pair s a)) ↔ input tag s a = true := by
  rw [Program.domain, program_eval, chiOperation_domain]

theorem program_graph (tag s a answer : Nat) : answer ∈ program.eval (Nat.pair tag (Nat.pair s a)) ↔
    (tag = 0 ∨ tag = 1) ∧ sourceInput s a = true ∧ answer = sourceAnswer s a := by
  rw [program_eval, chiOperation_graph, input_exact, and_assoc]

noncomputable def sourceColumn (tag s : Nat) : Program := (program.column tag).column s

theorem sourceColumn_primrec : Primrec₂ sourceColumn :=
  (Program.column_primrec.comp (Program.column_primrec.comp (Primrec.const program) Primrec.fst) Primrec.snd).to₂

theorem sourceColumn_eval (tag s a : Nat) : (sourceColumn tag s).eval a = chiOperation tag s a := by
  simp only [sourceColumn, Nat.Partrec.Code.eval_curry, program_eval]

theorem sourceColumn_domain (tag s a : Nat) : (sourceColumn tag s).domain a ↔
    (tag = 0 ∨ tag = 1) ∧ sourceInput s a = true := by
  rw [sourceColumn, Program.column_domain, Program.column_domain, program_domain, input_exact]

theorem sourceColumn_original_domain (tag s a : Nat) : (sourceColumn tag s).domain a ↔
    (tag = 0 ∨ tag = 1) ∧ checkCode (NativePublicBridge.contextCode s) a = true ∧
      Comparison.Normal (NativePublicBridge.contextCode s) (ThetaCourse.rawTree a) ∧
      check (NativePublicBridge.contextCode s) (.theta 0 (ThetaCourse.rawTree a)) = true ∧
      base (NativePublicBridge.contextCode s) <
        denote (NativePublicBridge.contextCode s) (.theta 0 (ThetaCourse.rawTree a)) := by
  rw [sourceColumn_domain, sourceInput_literal]

theorem sourceColumn_literal (tag s a answer : Nat) : answer ∈ (sourceColumn tag s).eval a ↔
    ∃ out ∈ sourceOperation tag s a,
      answer = numeral (SourceChi.chiCode (NativePublicBridge.contextCode s) out) := by
  rw [sourceColumn_eval]
  exact chiOperation_literal tag s a answer

def graph (tag s a answer : Nat) : Bool := input tag s a && (answer == sourceAnswer s a)

theorem graph_primrec : Primrec (fun p : Data × Nat => graph p.1.1 p.1.2.1 p.1.2.2 p.2) :=
  Primrec.and.comp (input_primrec.comp Primrec.fst) (Primrec.beq.comp Primrec.snd
    (sourceAnswer_primrec.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))

theorem graph_exact (tag s a answer : Nat) : graph tag s a answer = true ↔
    answer ∈ chiOperation tag s a := by
  rw [graph, Bool.and_eq_true, beq_iff_eq, chiOperation_graph]

theorem graph_unique (tag s a : Nat) (hi : input tag s a = true) :
    ∃! answer, graph tag s a answer = true := by
  refine ⟨sourceAnswer s a, (graph_exact _ _ _ _).mpr ((chiOperation_graph _ _ _ _).mpr ⟨hi, rfl⟩), ?_⟩
  intro answer ha
  exact ((chiOperation_graph _ _ _ _).mp ((graph_exact _ _ _ _).mp ha)).2

def graphRaw (query : Nat) : Bool :=
  let p := data query.unpair.1
  graph p.1 p.2.1 p.2.2 query.unpair.2

theorem graphRaw_primrec : Primrec graphRaw := graph_primrec.comp
  ((data_primrec.comp (Primrec.fst.comp Primrec.unpair)).pair (Primrec.snd.comp Primrec.unpair))

def graphEvaluation (query : Nat) : Part Nat := cond (graphRaw query) (Part.some 1) Part.none

theorem graphEvaluation_partrec : Partrec graphEvaluation :=
  Partrec.cond graphRaw_primrec.to_comp (Computable.const 1).partrec Partrec.none

theorem graphProgram_exists : ∃ p : Program, ∀ query, p.eval query = graphEvaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp graphEvaluation_partrec)

noncomputable def graphProgram : Program := Classical.choose graphProgram_exists

theorem graphProgram_domain (tag s a answer : Nat) :
    graphProgram.domain (Nat.pair (Nat.pair tag (Nat.pair s a)) answer) ↔
      answer ∈ (sourceColumn tag s).eval a := by
  rw [Program.domain, Classical.choose_spec graphProgram_exists]
  simp only [graphEvaluation, graphRaw, data, Nat.unpair_pair]
  have hc : (cond (graph tag s a answer) (Part.some 1) Part.none).Dom ↔ graph tag s a answer = true := by
    cases h : graph tag s a answer <;> simp [h]
  exact hc.trans ((graph_exact tag s a answer).trans (by rw [sourceColumn_eval]))

noncomputable def graphColumn (tag s a : Nat) : Program :=
  graphProgram.column (Nat.pair tag (Nat.pair s a))

theorem graphColumn_primrec : Primrec (fun p : Data => graphColumn p.1 p.2.1 p.2.2) :=
  Program.column_primrec.comp (Primrec.const graphProgram)
    (Primrec₂.natPair.comp Primrec.fst (Primrec₂.natPair.comp
      (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)))

theorem graphColumn_domain (tag s a answer : Nat) : (graphColumn tag s a).domain answer ↔
    answer ∈ (sourceColumn tag s).eval a := by
  rw [graphColumn, Program.column_domain]
  exact graphProgram_domain tag s a answer

end Alexander313.HereditaryNativeSourceChiPowersProgram
