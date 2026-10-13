import Alexander313.Wilken.HereditaryNativeFixedPoint

/-!
# Actual fixed-point and strict-supremum Programs

Tags 0/1/2 test the original native sorted domain, actual repaired fixed
residual and literal STRICT residual supremum relation. Tags 3/4/5 expose
the corresponding weak-normal domain and decisions before normalization.
The total decision Program returns the literal guarded Boolean as 0 or 1;
positive Programs and complete graph Programs retain the real domains.
Every column uses the actual PR Program compiler. Unknown tags reject.
No fixed-point classifier or source graph is assumed. Uncompiled.
-/

namespace Alexander313.HereditaryNativeFixedPointProgram

open Wilken.RelativeTerm.Hereditary
open NativeContext.FixedPoint

def kernel (tag q m c : Nat) : Bool :=
  cond (tag == 0) (rawInputCheck q m c)
    (cond (tag == 1) (fixedRawCode q m c)
      (cond (tag == 2) (strictRawCode q m c)
        (cond (tag == 3) (inputCheck q m c)
          (cond (tag == 4) (fixedCode q m c)
            (cond (tag == 5) (strictCode q m c) false)))))

theorem kernel_primrec : Primrec (fun p : Nat × (Nat × (Nat × Nat)) => kernel p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hdata := Primrec.snd
  have ht (k : Nat) := Primrec.beq.comp Primrec.fst (Primrec.const k)
  exact (ht 0).cond (rawInputCheck_primrec.comp hdata)
    ((ht 1).cond (fixedRawCode_primrec.comp hdata)
      ((ht 2).cond (strictRawCode_primrec.comp hdata)
        ((ht 3).cond (inputCheck_primrec.comp hdata)
          ((ht 4).cond (fixedCode_primrec.comp hdata)
            ((ht 5).cond (strictCode_primrec.comp hdata) (Primrec.const false))))))

def raw (query : Nat) : Bool := kernel query.unpair.1 query.unpair.2.unpair.1
  query.unpair.2.unpair.2.unpair.1 query.unpair.2.unpair.2.unpair.2

theorem raw_primrec : Primrec raw := kernel_primrec.comp
  ((Primrec.fst.comp Primrec.unpair).pair ((Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))).pair
    (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))))

def answer (tag q m c : Nat) : Nat := cond (kernel tag q m c) 1 0

def decisionEvaluation (query : Nat) : Part Nat := Part.some (cond (raw query) 1 0)

theorem decisionEvaluation_partrec : Partrec decisionEvaluation :=
  (raw_primrec.cond (Primrec.const 1) (Primrec.const 0)).to_comp.partrec

theorem decisionProgram_exists : ∃ p : Program, ∀ query, p.eval query = decisionEvaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp decisionEvaluation_partrec)

noncomputable def decisionProgram : Program := Classical.choose decisionProgram_exists

theorem decisionProgram_eval (tag q m c : Nat) :
    decisionProgram.eval (Nat.pair tag (Nat.pair q (Nat.pair m c))) = Part.some (answer tag q m c) := by
  simpa only [decisionEvaluation, raw, answer, Nat.unpair_pair] using
    Classical.choose_spec decisionProgram_exists (Nat.pair tag (Nat.pair q (Nat.pair m c)))

theorem decisionProgram_total (query : Nat) : decisionProgram.domain query := by
  rw [Program.domain, Classical.choose_spec decisionProgram_exists]
  exact Part.some_dom _

theorem decisionProgram_graph (tag q m c output : Nat) :
    output ∈ decisionProgram.eval (Nat.pair tag (Nat.pair q (Nat.pair m c))) ↔ output = answer tag q m c := by
  simp only [decisionProgram_eval, Part.mem_some_iff]

theorem decisionProgram_positive (tag q m c : Nat) :
    1 ∈ decisionProgram.eval (Nat.pair tag (Nat.pair q (Nat.pair m c))) ↔ kernel tag q m c = true := by
  rw [decisionProgram_graph]
  cases h : kernel tag q m c <;> simp [answer, h]

noncomputable def decisionColumn (tag q m : Nat) : Program := ((decisionProgram.column tag).column q).column m

theorem decisionColumn_primrec : Primrec (fun p : Nat × (Nat × Nat) => decisionColumn p.1 p.2.1 p.2.2) := by
  have hfirst := Program.column_primrec.comp (Primrec.const decisionProgram) Primrec.fst
  have hsecond := Program.column_primrec.comp hfirst (Primrec.fst.comp Primrec.snd)
  exact Program.column_primrec.comp hsecond (Primrec.snd.comp Primrec.snd)

theorem decisionColumn_eval (tag q m c : Nat) : (decisionColumn tag q m).eval c = Part.some (answer tag q m c) := by
  simp only [decisionColumn, Nat.Partrec.Code.eval_curry, decisionProgram_eval]

def inputEvaluation (query : Nat) : Part Nat := cond (raw query) (Part.some 0) Part.none

theorem inputEvaluation_partrec : Partrec inputEvaluation :=
  Partrec.cond raw_primrec.to_comp (Computable.const 0).partrec Partrec.none

theorem inputProgram_exists : ∃ p : Program, ∀ query, p.eval query = inputEvaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp inputEvaluation_partrec)

noncomputable def inputProgram : Program := Classical.choose inputProgram_exists

theorem inputProgram_domain (tag q m c : Nat) :
    inputProgram.domain (Nat.pair tag (Nat.pair q (Nat.pair m c))) ↔ kernel tag q m c = true := by
  rw [Program.domain, Classical.choose_spec inputProgram_exists]
  cases h : kernel tag q m c <;> simp [inputEvaluation, raw, Nat.unpair_pair, h]

noncomputable def inputColumn (tag q m : Nat) : Program := ((inputProgram.column tag).column q).column m

theorem inputColumn_primrec : Primrec (fun p : Nat × (Nat × Nat) => inputColumn p.1 p.2.1 p.2.2) := by
  have hfirst := Program.column_primrec.comp (Primrec.const inputProgram) Primrec.fst
  have hsecond := Program.column_primrec.comp hfirst (Primrec.fst.comp Primrec.snd)
  exact Program.column_primrec.comp hsecond (Primrec.snd.comp Primrec.snd)

theorem inputColumn_domain (tag q m c : Nat) : (inputColumn tag q m).domain c ↔ kernel tag q m c = true := by
  rw [inputColumn, Program.column_domain, Program.column_domain, Program.column_domain]
  exact inputProgram_domain tag q m c

def Domain (q m c : Nat) : Prop := NativeContext.checkCode q c = true ∧
  NativeContext.interpretation q c < Wilken.omegaSequence (NativeContext.base q) (m + 2)

theorem domainColumn_exact (q m c : Nat) : (inputColumn 0 q m).domain c ↔ Domain q m c := by
  rw [inputColumn_domain]
  change rawInputCheck q m c = true ↔ _
  exact rawInputCheck_exact q m c

theorem fixedColumn_exact (q m c : Nat) : (inputColumn 1 q m).domain c ↔ Domain q m c ∧ SourceFixed q m c := by
  rw [inputColumn_domain]
  change fixedRawCode q m c = true ↔ _
  rw [fixedRawCode_exact]
  simp only [Domain, and_assoc]

theorem strictColumn_exact (q m c : Nat) : (inputColumn 2 q m).domain c ↔ Domain q m c ∧ SourceStrict q m c := by
  rw [inputColumn_domain]
  change strictRawCode q m c = true ↔ _
  rw [strictRawCode_exact]
  simp only [Domain, and_assoc]

theorem normalDomainColumn_exact (q m c : Nat) : (inputColumn 3 q m).domain c ↔
    NativeContext.checkCode q c = true ∧ NativeContext.Comparison.Normal q (ThetaCourse.rawTree c) ∧
      NativeContext.interpretation q c < Wilken.omegaSequence (NativeContext.base q) (m + 2) := by
  rw [inputColumn_domain]
  change inputCheck q m c = true ↔ _
  exact inputCheck_exact q m c

theorem normalFixedColumn_exact (q m c : Nat) : (inputColumn 4 q m).domain c ↔ inputCheck q m c = true ∧ SourceFixed q m c := by
  rw [inputColumn_domain]
  change fixedCode q m c = true ↔ _
  exact fixedCode_exact q m c

theorem normalStrictColumn_exact (q m c : Nat) : (inputColumn 5 q m).domain c ↔ inputCheck q m c = true ∧ SourceStrict q m c := by
  rw [inputColumn_domain]
  change strictCode q m c = true ↔ _
  exact strictCode_exact q m c

theorem inputColumn_unknown (tag q m c : Nat) (h0 : tag ≠ 0) (h1 : tag ≠ 1) (h2 : tag ≠ 2)
    (h3 : tag ≠ 3) (h4 : tag ≠ 4) (h5 : tag ≠ 5) : ¬ (inputColumn tag q m).domain c := by
  rw [inputColumn_domain]
  simp [kernel, h0, h1, h2, h3, h4, h5]

def graphRaw (query : Nat) : Bool := query.unpair.2 == cond (raw query.unpair.1) 1 0

theorem graphRaw_primrec : Primrec graphRaw := Primrec.beq.comp (Primrec.snd.comp Primrec.unpair)
  ((raw_primrec.comp (Primrec.fst.comp Primrec.unpair)).cond (Primrec.const 1) (Primrec.const 0))

def graphEvaluation (query : Nat) : Part Nat := cond (graphRaw query) (Part.some 0) Part.none

theorem graphEvaluation_partrec : Partrec graphEvaluation :=
  Partrec.cond graphRaw_primrec.to_comp (Computable.const 0).partrec Partrec.none

theorem graphProgram_exists : ∃ p : Program, ∀ query, p.eval query = graphEvaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp graphEvaluation_partrec)

noncomputable def graphProgram : Program := Classical.choose graphProgram_exists

theorem graphProgram_domain (tag q m c output : Nat) :
    graphProgram.domain (Nat.pair (Nat.pair tag (Nat.pair q (Nat.pair m c))) output) ↔ output = answer tag q m c := by
  rw [Program.domain, Classical.choose_spec graphProgram_exists]
  simp only [graphEvaluation, graphRaw, raw, Nat.unpair_pair]
  change (cond (output == answer tag q m c) (Part.some 0) Part.none).Dom ↔ output = answer tag q m c
  cases h : output == answer tag q m c <;> simp [h, ← beq_iff_eq]

noncomputable def graphColumn (tag q m c : Nat) : Program := graphProgram.column (Nat.pair tag (Nat.pair q (Nat.pair m c)))

theorem graphColumn_primrec : Primrec (fun p : Nat × (Nat × (Nat × Nat)) => graphColumn p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  Program.column_primrec.comp (Primrec.const graphProgram) (Primrec₂.natPair.comp Primrec.fst
    (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd) (Primrec₂.natPair.comp
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))

theorem graphColumn_domain (tag q m c output : Nat) : (graphColumn tag q m c).domain output ↔ output = answer tag q m c := by
  rw [graphColumn, Program.column_domain]
  exact graphProgram_domain tag q m c output

theorem graphColumn_execution (tag q m c output : Nat) : (graphColumn tag q m c).domain output ↔
    output ∈ decisionProgram.eval (Nat.pair tag (Nat.pair q (Nat.pair m c))) :=
  (graphColumn_domain tag q m c output).trans (decisionProgram_graph tag q m c output).symm

theorem graphColumn_unique (tag q m c : Nat) : ∃! output, (graphColumn tag q m c).domain output := by
  refine ⟨answer tag q m c, (graphColumn_domain tag q m c _).mpr rfl, ?_⟩
  intro output ho
  exact (graphColumn_domain tag q m c output).mp ho

end Alexander313.HereditaryNativeFixedPointProgram
