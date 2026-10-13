import Alexander313.Wilken.HereditaryNativeArithmetic

/-!
# Executing Programs for real native addition and left removal

Tags 0/1 execute addition/total left removal on all original checked pairs;
2/3 restrict them to original weak-normal pairs. Tags 4/5 execute the source
ordered operation -c+d on original raw/weak-normal pairs with c<=d. This is
Mathlib's d-c, not the distinct dotted right subtraction from w2.txt453.
Unknown tags and malformed contexts or trees reject. Every computed result
is originally accepted and obeys genuine ordinal and literal-height laws.

The finite source operations and their complete numerical executing graphs
are primitive recursive. Actual Programs and PR compiler columns are built
from those kernels. Output uniqueness is literal fixed-input execution;
value equivalence of different inputs does not assert native syntax equality.
All proof terms remain uncompiled candidates.
-/

namespace Alexander313.HereditaryNativeArithmeticProgram

open Wilken.RelativeTerm.Hereditary

abbrev Data := (Nat × Nat) × (Nat × Nat)

def normalInput (q c d : Nat) : Bool :=
  NativeContext.Comparison.acceptedCode q c && NativeContext.Comparison.acceptedCode q d

theorem normalInput_primrec : Primrec
    (fun p : Nat × (Nat × Nat) => normalInput p.1 p.2.1 p.2.2) :=
  Primrec.and.comp (NativeContext.Comparison.acceptedCode_primrec.comp Primrec.fst
    (Primrec.fst.comp Primrec.snd)) (NativeContext.Comparison.acceptedCode_primrec.comp Primrec.fst
      (Primrec.snd.comp Primrec.snd))

theorem normalInput_raw (q c d : Nat) (h : normalInput q c d = true) :
    NativeContext.Arithmetic.inputCheck q c d = true := by
  obtain ⟨hc, hd⟩ := Bool.and_eq_true.mp h
  exact (NativeContext.Arithmetic.inputCheck_exact q c d).mpr
    ⟨((NativeContext.Comparison.acceptedCode_exact q c).mp hc).1,
      ((NativeContext.Comparison.acceptedCode_exact q d).mp hd).1⟩

def input (tag q c d : Nat) : Bool :=
  cond (decide (tag < 2)) (NativeContext.Arithmetic.inputCheck q c d)
    (cond (decide (tag < 4)) (normalInput q c d)
      (cond (tag == 4) (NativeContext.Arithmetic.orderedCheck q c d)
        (cond (tag == 5) (normalInput q c d && NativeContext.Arithmetic.leCode q c d) false)))

theorem input_primrec : Primrec (fun p : Data => input p.1.1 p.1.2 p.2.1 p.2.2) := by
  have ht := Primrec.fst.comp Primrec.fst
  have hq := Primrec.snd.comp Primrec.fst
  have hc := Primrec.fst.comp Primrec.snd
  have hd := Primrec.snd.comp Primrec.snd
  have hp := hq.pair (hc.pair hd)
  have hr := NativeContext.Arithmetic.inputCheck_primrec.comp hp
  have hn := normalInput_primrec.comp hp
  have ho := NativeContext.Arithmetic.orderedCheck_primrec.comp hp
  have hl := NativeContext.Arithmetic.leCode_primrec.comp hp
  exact ((Primrec.nat_lt.comp ht (Primrec.const 2)).decide).cond hr
    (((Primrec.nat_lt.comp ht (Primrec.const 4)).decide).cond hn
      ((Primrec.beq.comp ht (Primrec.const 4)).cond ho
        ((Primrec.beq.comp ht (Primrec.const 5)).cond (Primrec.and.comp hn hl) (Primrec.const false))))

@[simp] theorem input_zero (q c d : Nat) : input 0 q c d = NativeContext.Arithmetic.inputCheck q c d := rfl
@[simp] theorem input_one (q c d : Nat) : input 1 q c d = NativeContext.Arithmetic.inputCheck q c d := rfl
@[simp] theorem input_two (q c d : Nat) : input 2 q c d = normalInput q c d := rfl
@[simp] theorem input_three (q c d : Nat) : input 3 q c d = normalInput q c d := rfl
@[simp] theorem input_four (q c d : Nat) : input 4 q c d = NativeContext.Arithmetic.orderedCheck q c d := rfl
@[simp] theorem input_five (q c d : Nat) : input 5 q c d =
    (normalInput q c d && NativeContext.Arithmetic.leCode q c d) := rfl

theorem input_unknown (tag q c d : Nat) (h : 6 ≤ tag) : input tag q c d = false := by
  have h2 : ¬tag < 2 := by omega
  have h4 : ¬tag < 4 := by omega
  have hn4 : tag ≠ 4 := by omega
  have hn5 : tag ≠ 5 := by omega
  have hb4 : (tag == 4) = false := by
    cases hb : tag == 4 with
    | false => rfl
    | true => exact False.elim (hn4 (beq_iff_eq.mp hb))
  have hb5 : (tag == 5) = false := by
    cases hb : tag == 5 with
    | false => rfl
    | true => exact False.elim (hn5 (beq_iff_eq.mp hb))
  simp only [input, h2, h4, decide_false, hb4, hb5, Bool.cond_false]

theorem input_raw (tag q c d : Nat) (h : input tag q c d = true) :
    NativeContext.checkCode q c = true ∧ NativeContext.checkCode q d = true := by
  unfold input at h
  cases h2 : decide (tag < 2) with
  | true =>
    exact (NativeContext.Arithmetic.inputCheck_exact q c d).mp
      (by simpa only [h2, Bool.cond_true] using h)
  | false =>
    simp only [h2, Bool.cond_false] at h
    cases h4 : decide (tag < 4) with
    | true =>
      exact (NativeContext.Arithmetic.inputCheck_exact q c d).mp (normalInput_raw q c d
        (by simpa only [h4, Bool.cond_true] using h))
    | false =>
      simp only [h4, Bool.cond_false] at h
      cases he4 : tag == 4 with
      | true =>
        have ho := (NativeContext.Arithmetic.orderedCheck_exact q c d).mp
          (by simpa only [he4, Bool.cond_true] using h)
        exact ⟨ho.1, ho.2.1⟩
      | false =>
        simp only [he4, Bool.cond_false] at h
        cases he5 : tag == 5 with
        | false => simp only [he5, Bool.cond_false, Bool.false_eq_true] at h
        | true =>
          have hs : (normalInput q c d && NativeContext.Arithmetic.leCode q c d) = true :=
            by simpa only [he5, Bool.cond_true] using h
          have hn : normalInput q c d = true := (Bool.and_eq_true.mp hs).1
          exact (NativeContext.Arithmetic.inputCheck_exact q c d).mp (normalInput_raw q c d hn)

def isAddition (tag : Nat) : Bool := (tag == 0) || (tag == 2)

def output (tag q c d : Nat) : Nat := cond (isAddition tag)
  (NativeContext.Arithmetic.addCode q c d) (NativeContext.Arithmetic.subtractCode q c d)

theorem output_primrec : Primrec (fun p : Data => output p.1.1 p.1.2 p.2.1 p.2.2) := by
  have ht := Primrec.fst.comp Primrec.fst
  have hp := (Primrec.snd.comp Primrec.fst).pair
    ((Primrec.fst.comp Primrec.snd).pair (Primrec.snd.comp Primrec.snd))
  exact (Primrec.or.comp (Primrec.beq.comp ht (Primrec.const 0))
    (Primrec.beq.comp ht (Primrec.const 2))).cond
      (NativeContext.Arithmetic.addCode_primrec.comp hp) (NativeContext.Arithmetic.subtractCode_primrec.comp hp)

theorem output_spec (tag q c d : Nat) (hi : input tag q c d = true) :
    NativeContext.Comparison.acceptedCode q (output tag q c d) = true ∧
      NativeContext.interpretation q (output tag q c d) =
        cond (isAddition tag) (NativeContext.interpretation q c + NativeContext.interpretation q d)
          (NativeContext.interpretation q d - NativeContext.interpretation q c) ∧
      Wilken.RelativeTerm.heightCode (output tag q c d) ≤
        max (Wilken.RelativeTerm.heightCode c) (Wilken.RelativeTerm.heightCode d) := by
  obtain ⟨hc, hd⟩ := input_raw tag q c d hi
  cases h : isAddition tag with
  | true => simpa only [output, h, Bool.cond_true] using NativeContext.Arithmetic.addCode_spec q c d hc hd
  | false =>
    have hs := NativeContext.Arithmetic.subtractCode_spec q c d hc hd
    simpa only [output, h, Bool.cond_false] using ⟨hs.1, hs.2.1, hs.2.2.trans (le_max_right _ _)⟩

def data (query : Nat) : Data :=
  ((query.unpair.1, query.unpair.2.unpair.1),
    (query.unpair.2.unpair.2.unpair.1, query.unpair.2.unpair.2.unpair.2))

theorem data_primrec : Primrec data := by
  have h := Primrec.unpair
  have htail := Primrec.unpair.comp (Primrec.snd.comp h)
  exact ((Primrec.fst.comp h).pair (Primrec.fst.comp htail)).pair
    (Primrec.unpair.comp (Primrec.snd.comp htail))

def evaluation (query : Nat) : Part Nat :=
  let p := data query
  cond (input p.1.1 p.1.2 p.2.1 p.2.2) (Part.some (output p.1.1 p.1.2 p.2.1 p.2.2)) Part.none

theorem evaluation_partrec : Partrec evaluation :=
  Partrec.cond (input_primrec.comp data_primrec).to_comp
    (output_primrec.comp data_primrec).to_comp.partrec Partrec.none

theorem arithmeticProgram_exists : ∃ p : Program, ∀ query, p.eval query = evaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp evaluation_partrec)

noncomputable def arithmeticProgram : Program := Classical.choose arithmeticProgram_exists

theorem arithmeticProgram_eval (tag q c d : Nat) :
    arithmeticProgram.eval (Nat.pair tag (Nat.pair q (Nat.pair c d))) =
      cond (input tag q c d) (Part.some (output tag q c d)) Part.none := by
  simpa only [evaluation, data, Nat.unpair_pair] using
    Classical.choose_spec arithmeticProgram_exists (Nat.pair tag (Nat.pair q (Nat.pair c d)))

theorem arithmeticProgram_domain (tag q c d : Nat) :
    arithmeticProgram.domain (Nat.pair tag (Nat.pair q (Nat.pair c d))) ↔ input tag q c d = true := by
  rw [Program.domain, arithmeticProgram_eval]
  cases h : input tag q c d <;> simp [h]

theorem arithmeticProgram_graph (tag q c d out : Nat) :
    out ∈ arithmeticProgram.eval (Nat.pair tag (Nat.pair q (Nat.pair c d))) ↔
      input tag q c d = true ∧ out = output tag q c d := by
  rw [arithmeticProgram_eval]
  cases h : input tag q c d <;> simp [h, Part.mem_some_iff]

noncomputable def sourceColumn (tag q c : Nat) : Program :=
  ((arithmeticProgram.column tag).column q).column c

theorem sourceColumn_primrec : Primrec (fun p : Nat × (Nat × Nat) => sourceColumn p.1 p.2.1 p.2.2) :=
  Program.column_primrec.comp
    (Program.column_primrec.comp (Program.column_primrec.comp (Primrec.const arithmeticProgram) Primrec.fst)
      (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)

theorem sourceColumn_eval (tag q c d : Nat) : (sourceColumn tag q c).eval d =
    cond (input tag q c d) (Part.some (output tag q c d)) Part.none := by
  simp only [sourceColumn, Nat.Partrec.Code.eval_curry]
  exact arithmeticProgram_eval tag q c d

theorem sourceColumn_domain (tag q c d : Nat) : (sourceColumn tag q c).domain d ↔ input tag q c d = true := by
  simp only [sourceColumn, Program.column_domain]
  exact arithmeticProgram_domain tag q c d

theorem sourceColumn_graph (tag q c d out : Nat) : out ∈ (sourceColumn tag q c).eval d ↔
    input tag q c d = true ∧ out = output tag q c d := by
  simp only [sourceColumn, Nat.Partrec.Code.eval_curry]
  exact arithmeticProgram_graph tag q c d out

theorem sourceColumn_returns (tag q c d : Nat) (hi : input tag q c d = true) :
    (sourceColumn tag q c).eval d = Part.some (output tag q c d) := by
  simp only [sourceColumn_eval, hi, Bool.cond_true]

theorem sourceColumn_correct (tag q c d out : Nat) (ho : out ∈ (sourceColumn tag q c).eval d) :
    NativeContext.checkCode q c = true ∧ NativeContext.checkCode q d = true ∧
      NativeContext.Comparison.acceptedCode q out = true ∧
      NativeContext.interpretation q out =
        cond (isAddition tag) (NativeContext.interpretation q c + NativeContext.interpretation q d)
          (NativeContext.interpretation q d - NativeContext.interpretation q c) ∧
      Wilken.RelativeTerm.heightCode out ≤ max (Wilken.RelativeTerm.heightCode c) (Wilken.RelativeTerm.heightCode d) := by
  obtain ⟨hi, rfl⟩ := (sourceColumn_graph tag q c d out).mp ho
  exact ⟨(input_raw tag q c d hi).1, (input_raw tag q c d hi).2, output_spec tag q c d hi⟩

theorem raw_add_domain (q c d : Nat) : (sourceColumn 0 q c).domain d ↔
    NativeContext.checkCode q c = true ∧ NativeContext.checkCode q d = true := by
  rw [sourceColumn_domain, input_zero, NativeContext.Arithmetic.inputCheck_exact]

theorem raw_subtract_domain (q c d : Nat) : (sourceColumn 1 q c).domain d ↔
    NativeContext.checkCode q c = true ∧ NativeContext.checkCode q d = true := by
  rw [sourceColumn_domain, input_one, NativeContext.Arithmetic.inputCheck_exact]

theorem normal_add_domain (q c d : Nat) : (sourceColumn 2 q c).domain d ↔
    NativeContext.Comparison.acceptedCode q c = true ∧ NativeContext.Comparison.acceptedCode q d = true := by
  rw [sourceColumn_domain, input_two]
  exact Bool.and_eq_true

theorem normal_subtract_domain (q c d : Nat) : (sourceColumn 3 q c).domain d ↔
    NativeContext.Comparison.acceptedCode q c = true ∧ NativeContext.Comparison.acceptedCode q d = true := by
  rw [sourceColumn_domain, input_three]
  exact Bool.and_eq_true

theorem ordered_raw_domain (q c d : Nat) : (sourceColumn 4 q c).domain d ↔
    NativeContext.checkCode q c = true ∧ NativeContext.checkCode q d = true ∧
      NativeContext.interpretation q c ≤ NativeContext.interpretation q d := by
  rw [sourceColumn_domain, input_four, NativeContext.Arithmetic.orderedCheck_exact]

theorem ordered_normal_domain (q c d : Nat) : (sourceColumn 5 q c).domain d ↔
    NativeContext.Comparison.acceptedCode q c = true ∧ NativeContext.Comparison.acceptedCode q d = true ∧
      NativeContext.interpretation q c ≤ NativeContext.interpretation q d := by
  rw [sourceColumn_domain, input_five, Bool.and_eq_true]
  constructor
  · rintro ⟨hn, hl⟩
    obtain ⟨hc, hd⟩ := Bool.and_eq_true.mp hn
    have hi := (NativeContext.Arithmetic.inputCheck_exact q c d).mp (normalInput_raw q c d hn)
    exact ⟨hc, hd, (NativeContext.Arithmetic.leCode_exact q c d hi.1 hi.2).mp hl⟩
  · rintro ⟨hc, hd, hl⟩
    have hn : normalInput q c d = true := Bool.and_eq_true.mpr ⟨hc, hd⟩
    have hi := (NativeContext.Arithmetic.inputCheck_exact q c d).mp (normalInput_raw q c d hn)
    exact ⟨hn, (NativeContext.Arithmetic.leCode_exact q c d hi.1 hi.2).mpr hl⟩

theorem sourceColumn_unknown (tag q c d : Nat) (h : 6 ≤ tag) : ¬ (sourceColumn tag q c).domain d := by
  rw [sourceColumn_domain, input_unknown tag q c d h]
  exact Bool.false_ne_true

def inputEvaluation (query : Nat) : Part Nat :=
  let p := data query
  cond (input p.1.1 p.1.2 p.2.1 p.2.2) (Part.some 1) Part.none

theorem inputEvaluation_partrec : Partrec inputEvaluation :=
  Partrec.cond (input_primrec.comp data_primrec).to_comp (Computable.const 1).partrec Partrec.none

theorem inputProgram_exists : ∃ p : Program, ∀ query, p.eval query = inputEvaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp inputEvaluation_partrec)

noncomputable def inputProgram : Program := Classical.choose inputProgram_exists

theorem inputProgram_domain (tag q c d : Nat) :
    inputProgram.domain (Nat.pair tag (Nat.pair q (Nat.pair c d))) ↔ input tag q c d = true := by
  rw [Program.domain, Classical.choose_spec inputProgram_exists]
  simp only [inputEvaluation, data, Nat.unpair_pair]
  cases h : input tag q c d <;> simp [h]

noncomputable def inputColumn (tag q : Nat) : Program := (inputProgram.column tag).column q

theorem inputColumn_primrec : Primrec₂ inputColumn :=
  (Program.column_primrec.comp (Program.column_primrec.comp (Primrec.const inputProgram) Primrec.fst)
    Primrec.snd).to₂

theorem inputColumn_domain (tag q c d : Nat) : (inputColumn tag q).domain (Nat.pair c d) ↔ input tag q c d = true := by
  simp only [inputColumn, Program.column_domain]
  exact inputProgram_domain tag q c d

def graph (tag q c d out : Nat) : Bool := input tag q c d && (out == output tag q c d)

theorem graph_primrec : Primrec (fun p : Data × Nat => graph p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2 p.2) :=
  Primrec.and.comp (input_primrec.comp Primrec.fst)
    (Primrec.beq.comp Primrec.snd (output_primrec.comp Primrec.fst))

theorem graph_exact (tag q c d out : Nat) : graph tag q c d out = true ↔
    input tag q c d = true ∧ out = output tag q c d := by
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

theorem graphProgram_domain (tag q c d out : Nat) :
    graphProgram.domain (Nat.pair (Nat.pair tag (Nat.pair q (Nat.pair c d))) out) ↔
      input tag q c d = true ∧ out = output tag q c d := by
  rw [Program.domain, Classical.choose_spec graphProgram_exists]
  simp only [graphEvaluation, data, Nat.unpair_pair]
  cases h : graph tag q c d out with
  | true => simp [h, (graph_exact tag q c d out).mp h]
  | false =>
    have hn : ¬(input tag q c d = true ∧ out = output tag q c d) := by
      intro he
      have ht := (graph_exact tag q c d out).mpr he
      simp only [h, Bool.false_eq_true] at ht
    simp [h, hn]

noncomputable def graphColumn (tag q c d : Nat) : Program :=
  graphProgram.column (Nat.pair tag (Nat.pair q (Nat.pair c d)))

theorem graphColumn_primrec : Primrec (fun p : Data => graphColumn p.1.1 p.1.2 p.2.1 p.2.2) :=
  Program.column_primrec.comp (Primrec.const graphProgram)
    (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.fst)
      (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst)
        (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))))

theorem graphColumn_domain (tag q c d out : Nat) : (graphColumn tag q c d).domain out ↔
    input tag q c d = true ∧ out = output tag q c d := by
  rw [graphColumn, Program.column_domain]
  exact graphProgram_domain tag q c d out

theorem graphColumn_execution (tag q c d out : Nat) :
    (graphColumn tag q c d).domain out ↔ out ∈ (sourceColumn tag q c).eval d :=
  (graphColumn_domain tag q c d out).trans (sourceColumn_graph tag q c d out).symm

theorem graphColumn_unique (tag q c d : Nat) (hi : input tag q c d = true) :
    ∃! out, (graphColumn tag q c d).domain out := by
  refine ⟨output tag q c d, (graphColumn_domain tag q c d _).mpr ⟨hi, rfl⟩, ?_⟩
  intro out ho
  exact ((graphColumn_domain tag q c d out).mp ho).2

end Alexander313.HereditaryNativeArithmeticProgram
