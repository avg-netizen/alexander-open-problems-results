import Alexander313.Wilken.HereditaryNativeComparison

/-!
# Executing order Programs for admitted weak-normal native terms

The real PR native comparator and constructed normality check determine the
kernel. Tag 0 admits both native inputs, tags 1/2/3 recognize actual less,
equal and greater on that exact domain. Unknown tags reject. A total decision
Program returns the literal guarded 0/1 answer; positive Programs recognize
the source domain/relations and the complete numerical output graph. Every
column specializes an actual fixed Program by the genuine PR compiler.
No raw native normalization, cross-base conversion or translation is asserted.
All terms remain uncompiled proof candidates.
-/

namespace Alexander313.HereditaryNativeComparisonProgram

open Wilken.RelativeTerm.Hereditary

def kernel (tag q c d : Nat) : Bool :=
  cond (tag == 0) (NativeContext.Comparison.acceptedCode q c && NativeContext.Comparison.acceptedCode q d)
    (cond (tag == 1) (NativeContext.Comparison.lessCode q c d)
      (cond (tag == 2) (NativeContext.Comparison.equalCode q c d)
        (cond (tag == 3) (NativeContext.Comparison.lessCode q d c) false)))

theorem kernel_primrec : Primrec (fun p : Nat × (Nat × (Nat × Nat)) => kernel p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hq : Primrec (fun p : Nat × (Nat × (Nat × Nat)) => p.2.1) := Primrec.fst.comp Primrec.snd
  have hc : Primrec (fun p : Nat × (Nat × (Nat × Nat)) => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hd : Primrec (fun p : Nat × (Nat × (Nat × Nat)) => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have ht (k : Nat) : Primrec (fun p : Nat × (Nat × (Nat × Nat)) => p.1 == k) :=
    Primrec.beq.comp Primrec.fst (Primrec.const k)
  exact (ht 0).cond (Primrec.and.comp (NativeContext.Comparison.acceptedCode_primrec.comp hq hc)
    (NativeContext.Comparison.acceptedCode_primrec.comp hq hd))
    ((ht 1).cond (NativeContext.Comparison.lessCode_primrec.comp (hq.pair (hc.pair hd)))
      ((ht 2).cond (NativeContext.Comparison.equalCode_primrec.comp (hq.pair (hc.pair hd)))
        ((ht 3).cond (NativeContext.Comparison.lessCode_primrec.comp (hq.pair (hd.pair hc))) (Primrec.const false))))

def raw (query : Nat) : Bool := kernel query.unpair.1 query.unpair.2.unpair.1
  query.unpair.2.unpair.2.unpair.1 query.unpair.2.unpair.2.unpair.2

theorem raw_primrec : Primrec raw := kernel_primrec.comp
  ((Primrec.fst.comp Primrec.unpair).pair ((Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))).pair
    (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))))

def answer (tag q c d : Nat) : Nat := cond (kernel tag q c d) 1 0

def decisionEvaluation (query : Nat) : Part Nat := Part.some (cond (raw query) 1 0)

theorem decisionEvaluation_partrec : Partrec decisionEvaluation :=
  (raw_primrec.cond (Primrec.const 1) (Primrec.const 0)).to_comp.partrec

theorem decisionProgram_exists : ∃ p : Program, ∀ query, p.eval query = decisionEvaluation query :=
  by
    obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp decisionEvaluation_partrec)
    exact ⟨p, fun query => congrFun hp query⟩

noncomputable def decisionProgram : Program := Classical.choose decisionProgram_exists

theorem decisionProgram_eval (tag q c d : Nat) :
    decisionProgram.eval (Nat.pair tag (Nat.pair q (Nat.pair c d))) = Part.some (answer tag q c d) := by
  simpa only [decisionProgram, decisionEvaluation, raw, answer, Nat.unpair_pair] using
    Classical.choose_spec decisionProgram_exists (Nat.pair tag (Nat.pair q (Nat.pair c d)))

theorem decisionProgram_total (query : Nat) : decisionProgram.domain query := by
  rw [Program.domain, decisionProgram, Classical.choose_spec decisionProgram_exists]
  exact Part.some_dom _

theorem decisionProgram_graph (tag q c d output : Nat) :
    output ∈ decisionProgram.eval (Nat.pair tag (Nat.pair q (Nat.pair c d))) ↔ output = answer tag q c d := by
  simp only [decisionProgram_eval, Part.mem_some_iff]

theorem decisionProgram_positive (tag q c d : Nat) :
    1 ∈ decisionProgram.eval (Nat.pair tag (Nat.pair q (Nat.pair c d))) ↔ kernel tag q c d = true := by
  rw [decisionProgram_graph]
  cases h : kernel tag q c d <;> simp [answer, h]

noncomputable def decisionColumn (tag q : Nat) : Program := (decisionProgram.column tag).column q

theorem decisionColumn_primrec : Primrec₂ decisionColumn := by
  have hfirst : Primrec (fun p : Nat × Nat => decisionProgram.column p.1) :=
    Program.column_primrec.comp (Primrec.const decisionProgram) Primrec.fst
  exact (Program.column_primrec.comp hfirst Primrec.snd).to₂

theorem decisionColumn_eval (tag q c d : Nat) :
    (decisionColumn tag q).eval (Nat.pair c d) = Part.some (answer tag q c d) := by
  simp only [decisionColumn, Program.column, Nat.Partrec.Code.eval_curry, decisionProgram_eval]

def inputEvaluation (query : Nat) : Part Nat := cond (raw query) (Part.some 0) Part.none

theorem inputEvaluation_partrec : Partrec inputEvaluation :=
  Partrec.cond raw_primrec.to_comp (Computable.const 0).partrec Partrec.none

theorem inputProgram_exists : ∃ p : Program, ∀ query, p.eval query = inputEvaluation query :=
  by
    obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp inputEvaluation_partrec)
    exact ⟨p, fun query => congrFun hp query⟩

noncomputable def inputProgram : Program := Classical.choose inputProgram_exists

theorem inputProgram_domain (tag q c d : Nat) :
    inputProgram.domain (Nat.pair tag (Nat.pair q (Nat.pair c d))) ↔ kernel tag q c d = true := by
  rw [Program.domain, inputProgram, Classical.choose_spec inputProgram_exists]
  cases h : kernel tag q c d <;> simp [inputEvaluation, raw, Nat.unpair_pair, h]

noncomputable def inputColumn (tag q : Nat) : Program := (inputProgram.column tag).column q

theorem inputColumn_primrec : Primrec₂ inputColumn := by
  have hfirst : Primrec (fun p : Nat × Nat => inputProgram.column p.1) :=
    Program.column_primrec.comp (Primrec.const inputProgram) Primrec.fst
  exact (Program.column_primrec.comp hfirst Primrec.snd).to₂

theorem inputColumn_domain (tag q c d : Nat) : (inputColumn tag q).domain (Nat.pair c d) ↔ kernel tag q c d = true := by
  rw [inputColumn, Program.column_domain, Program.column_domain]
  exact inputProgram_domain tag q c d

def Domain (q c d : Nat) : Prop := NativeContext.checkCode q c = true ∧
  NativeContext.Comparison.Normal q (ThetaCourse.rawTree c) ∧ NativeContext.checkCode q d = true ∧
    NativeContext.Comparison.Normal q (ThetaCourse.rawTree d)

theorem domainColumn_exact (q c d : Nat) : (inputColumn 0 q).domain (Nat.pair c d) ↔ Domain q c d := by
  rw [inputColumn_domain]
  change (NativeContext.Comparison.acceptedCode q c && NativeContext.Comparison.acceptedCode q d) = true ↔ _
  simp only [Bool.and_eq_true, NativeContext.Comparison.acceptedCode_exact, Domain, and_assoc]

theorem lessColumn_exact (q c d : Nat) : (inputColumn 1 q).domain (Nat.pair c d) ↔
    Domain q c d ∧ NativeContext.interpretation q c < NativeContext.interpretation q d := by
  rw [inputColumn_domain]
  change NativeContext.Comparison.lessCode q c d = true ↔ _
  rw [NativeContext.Comparison.lessCode_exact]
  simp only [Domain, and_assoc]

theorem equalColumn_exact (q c d : Nat) : (inputColumn 2 q).domain (Nat.pair c d) ↔
    Domain q c d ∧ NativeContext.interpretation q c = NativeContext.interpretation q d := by
  rw [inputColumn_domain]
  change NativeContext.Comparison.equalCode q c d = true ↔ _
  rw [NativeContext.Comparison.equalCode_exact]
  simp only [Domain, and_assoc]

theorem greaterColumn_exact (q c d : Nat) : (inputColumn 3 q).domain (Nat.pair c d) ↔
    Domain q c d ∧ NativeContext.interpretation q d < NativeContext.interpretation q c := by
  rw [inputColumn_domain]
  change NativeContext.Comparison.lessCode q d c = true ↔ _
  rw [NativeContext.Comparison.lessCode_exact]
  simp only [Domain]
  tauto

theorem orderColumn_trichotomy (q c d : Nat) (h : Domain q c d) :
    (inputColumn 1 q).domain (Nat.pair c d) ∨ (inputColumn 2 q).domain (Nat.pair c d) ∨
      (inputColumn 3 q).domain (Nat.pair c d) := by
  rcases lt_trichotomy (NativeContext.interpretation q c) (NativeContext.interpretation q d) with hlt | he | hgt
  · exact Or.inl ((lessColumn_exact q c d).mpr ⟨h, hlt⟩)
  · exact Or.inr (Or.inl ((equalColumn_exact q c d).mpr ⟨h, he⟩))
  · exact Or.inr (Or.inr ((greaterColumn_exact q c d).mpr ⟨h, hgt⟩))

theorem inputColumn_unknown (tag q c d : Nat) (h0 : tag ≠ 0) (h1 : tag ≠ 1) (h2 : tag ≠ 2) (h3 : tag ≠ 3) :
    ¬ (inputColumn tag q).domain (Nat.pair c d) := by
  rw [inputColumn_domain]
  simp [kernel, h0, h1, h2, h3]

noncomputable def rightColumn (tag q c : Nat) : Program := (inputColumn tag q).column c

theorem rightColumn_primrec : Primrec (fun p : Nat × (Nat × Nat) => rightColumn p.1 p.2.1 p.2.2) :=
  Program.column_primrec.comp (inputColumn_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
    (Primrec.snd.comp Primrec.snd)

theorem rightColumn_domain (tag q c d : Nat) : (rightColumn tag q c).domain d ↔ kernel tag q c d = true := by
  rw [rightColumn, Program.column_domain]
  exact inputColumn_domain tag q c d

def graphRaw (query : Nat) : Bool := query.unpair.2 == cond (raw query.unpair.1) 1 0

theorem graphRaw_primrec : Primrec graphRaw := Primrec.beq.comp (Primrec.snd.comp Primrec.unpair)
  ((raw_primrec.comp (Primrec.fst.comp Primrec.unpair)).cond (Primrec.const 1) (Primrec.const 0))

def graphEvaluation (query : Nat) : Part Nat := cond (graphRaw query) (Part.some 0) Part.none

theorem graphEvaluation_partrec : Partrec graphEvaluation :=
  Partrec.cond graphRaw_primrec.to_comp (Computable.const 0).partrec Partrec.none

theorem graphProgram_exists : ∃ p : Program, ∀ query, p.eval query = graphEvaluation query :=
  by
    obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp graphEvaluation_partrec)
    exact ⟨p, fun query => congrFun hp query⟩

noncomputable def graphProgram : Program := Classical.choose graphProgram_exists

theorem graphProgram_domain (tag q c d output : Nat) :
    graphProgram.domain (Nat.pair (Nat.pair tag (Nat.pair q (Nat.pair c d))) output) ↔ output = answer tag q c d := by
  rw [Program.domain, graphProgram, Classical.choose_spec graphProgram_exists]
  simp only [graphEvaluation, graphRaw, raw, Nat.unpair_pair]
  change (cond (output == answer tag q c d) (Part.some 0) Part.none).Dom ↔ output = answer tag q c d
  cases h : output == answer tag q c d <;> simp [h, ← beq_iff_eq]

noncomputable def graphColumn (tag q c d : Nat) : Program := graphProgram.column (Nat.pair tag (Nat.pair q (Nat.pair c d)))

theorem graphColumn_primrec : Primrec (fun p : Nat × (Nat × (Nat × Nat)) => graphColumn p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  Program.column_primrec.comp (Primrec.const graphProgram) (Primrec₂.natPair.comp Primrec.fst
    (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd) (Primrec₂.natPair.comp
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))

theorem graphColumn_domain (tag q c d output : Nat) : (graphColumn tag q c d).domain output ↔ output = answer tag q c d := by
  rw [graphColumn, Program.column_domain]
  exact graphProgram_domain tag q c d output

theorem graphColumn_execution (tag q c d output : Nat) : (graphColumn tag q c d).domain output ↔
    output ∈ decisionProgram.eval (Nat.pair tag (Nat.pair q (Nat.pair c d))) :=
  (graphColumn_domain tag q c d output).trans (decisionProgram_graph tag q c d output).symm

theorem graphColumn_unique (tag q c d : Nat) : ∃! output, (graphColumn tag q c d).domain output := by
  refine ⟨answer tag q c d, (graphColumn_domain tag q c d _).mpr rfl, ?_⟩
  intro output ho
  exact (graphColumn_domain tag q c d output).mp ho

end Alexander313.HereditaryNativeComparisonProgram
