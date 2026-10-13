import Alexander313.Wilken.HereditaryNativeDecomposition

/-!
# Actual Programs for native principal words and cardinal pieces

Tags 0/1/2 execute the whole/high/low encoded native atom lists. Tags 3/4
execute the original native high/low codes, tag 5 the paired codes, and tag 6
the actual native ANF reconstruction. Every operation retains the original
checked weak-normal input domain; unknown tags reject. Positive input and
complete computed-output graph Programs specialize by genuine PR compilers.
Numerical uniqueness refers to this executing finite algorithm. Arbitrary
native spellings of equal ordinal values are not identified syntactically.
All proof candidates remain uncompiled.
-/

namespace Alexander313.HereditaryNativeDecompositionProgram

open Wilken.RelativeTerm.Hereditary.NativeContext

def output (tag m c : Nat) : Nat :=
  cond (tag == 0) (Encodable.encode (Decomposition.word c))
    (cond (tag == 1) (Encodable.encode (Decomposition.highWord m c))
      (cond (tag == 2) (Encodable.encode (Decomposition.lowWord m c))
        (cond (tag == 3) (Decomposition.highCode m c)
          (cond (tag == 4) (Decomposition.lowCode m c)
            (cond (tag == 5) (Nat.pair (Decomposition.highCode m c) (Decomposition.lowCode m c))
              (cond (tag == 6) (Decomposition.rebuildCode c) 0))))))

theorem output_primrec : Primrec (fun p : Nat × (Nat × Nat) => output p.1 p.2.1 p.2.2) := by
  have hm := Primrec.fst.comp Primrec.snd
  have hc := Primrec.snd.comp Primrec.snd
  have hword := Primrec.encode.comp (Decomposition.word_primrec.comp hc)
  have hhighWord := Primrec.encode.comp (Decomposition.highWord_primrec.comp hm hc)
  have hlowWord := Primrec.encode.comp (Decomposition.lowWord_primrec.comp hm hc)
  have hhigh := Decomposition.highCode_primrec.comp hm hc
  have hlow := Decomposition.lowCode_primrec.comp hm hc
  have hpair := Primrec₂.natPair.comp hhigh hlow
  have hrebuild := Decomposition.rebuildCode_primrec.comp hc
  have ht (i : Nat) := Primrec.beq.comp Primrec.fst (Primrec.const i)
  exact (ht 0).cond hword ((ht 1).cond hhighWord ((ht 2).cond hlowWord
    ((ht 3).cond hhigh ((ht 4).cond hlow ((ht 5).cond hpair ((ht 6).cond hrebuild (Primrec.const 0)))))))

def valid (tag q c : Nat) : Bool := decide (tag ≤ 6) && Decomposition.inputCheck q c

theorem valid_primrec : Primrec (fun p : Nat × (Nat × Nat) => valid p.1 p.2.1 p.2.2) :=
  Primrec.and.comp ((Primrec.nat_le.comp Primrec.fst (Primrec.const 6)).decide)
    (Decomposition.inputCheck_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))

theorem valid_exact (tag q c : Nat) : valid tag q c = true ↔ tag ≤ 6 ∧ Decomposition.inputCheck q c = true := by
  simp only [valid, Bool.and_eq_true, decide_eq_true_eq]

def validRaw (query : Nat) : Bool := valid query.unpair.1 query.unpair.2.unpair.1
  query.unpair.2.unpair.2.unpair.2

def outputRaw (query : Nat) : Nat := output query.unpair.1 query.unpair.2.unpair.2.unpair.1
  query.unpair.2.unpair.2.unpair.2

theorem validRaw_primrec : Primrec validRaw := by
  have hr := Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)
  have hp := Primrec.unpair.comp (Primrec.snd.comp hr)
  exact valid_primrec.comp ((Primrec.fst.comp Primrec.unpair).pair
    ((Primrec.fst.comp hr).pair (Primrec.snd.comp hp)))

theorem outputRaw_primrec : Primrec outputRaw := by
  have hr := Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)
  have hp := Primrec.unpair.comp (Primrec.snd.comp hr)
  exact output_primrec.comp ((Primrec.fst.comp Primrec.unpair).pair hp)

def evaluation (query : Nat) : Part Nat := cond (validRaw query) (Part.some (outputRaw query)) Part.none

theorem evaluation_partrec : Partrec evaluation :=
  Partrec.cond validRaw_primrec.to_comp outputRaw_primrec.to_comp.partrec Partrec.none

theorem program_exists : ∃ p : Program, ∀ query, p.eval query = evaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp evaluation_partrec)

noncomputable def program : Program := Classical.choose program_exists

theorem program_eval (tag q m c : Nat) :
    program.eval (Nat.pair tag (Nat.pair q (Nat.pair m c))) =
      cond (valid tag q c) (Part.some (output tag m c)) Part.none := by
  simpa only [evaluation, validRaw, outputRaw, Nat.unpair_pair] using
    Classical.choose_spec program_exists (Nat.pair tag (Nat.pair q (Nat.pair m c)))

theorem program_domain (tag q m c : Nat) :
    program.domain (Nat.pair tag (Nat.pair q (Nat.pair m c))) ↔
      tag ≤ 6 ∧ Decomposition.inputCheck q c = true := by
  rw [Program.domain, program_eval]
  cases h : valid tag q c <;> simp [h, ← valid_exact]

theorem program_graph (tag q m c value : Nat) :
    value ∈ program.eval (Nat.pair tag (Nat.pair q (Nat.pair m c))) ↔
      (tag ≤ 6 ∧ Decomposition.inputCheck q c = true) ∧ value = output tag m c := by
  rw [program_eval]
  cases h : valid tag q c <;> simp [h, ← valid_exact]

noncomputable def sourceColumn (tag q m : Nat) : Program := ((program.column tag).column q).column m

theorem sourceColumn_primrec : Primrec (fun p : Nat × (Nat × Nat) => sourceColumn p.1 p.2.1 p.2.2) := by
  have ht := Program.column_primrec.comp (Primrec.const program) Primrec.fst
  have hq := Program.column_primrec.comp ht (Primrec.fst.comp Primrec.snd)
  exact Program.column_primrec.comp hq (Primrec.snd.comp Primrec.snd)

theorem sourceColumn_eval (tag q m c : Nat) :
    (sourceColumn tag q m).eval c = cond (valid tag q c) (Part.some (output tag m c)) Part.none := by
  simp only [sourceColumn, Nat.Partrec.Code.eval_curry, program_eval]

theorem sourceColumn_domain (tag q m c : Nat) :
    (sourceColumn tag q m).domain c ↔ tag ≤ 6 ∧ Decomposition.inputCheck q c = true := by
  rw [sourceColumn, Program.column_domain, Program.column_domain, Program.column_domain]
  exact program_domain tag q m c

theorem sourceColumn_graph (tag q m c value : Nat) : value ∈ (sourceColumn tag q m).eval c ↔
    (tag ≤ 6 ∧ Decomposition.inputCheck q c = true) ∧ value = output tag m c := by
  simp only [sourceColumn, Nat.Partrec.Code.eval_curry]
  exact program_graph tag q m c value

theorem sourceColumn_original (tag q m c : Nat) (htag : tag ≤ 6) :
    (sourceColumn tag q m).domain c ↔ checkCode q c = true ∧ Comparison.Normal q (Wilken.RelativeTerm.Hereditary.ThetaCourse.rawTree c) := by
  simp only [sourceColumn_domain, htag, true_and, Decomposition.inputCheck_exact]

theorem wordColumn_eval (q m c : Nat) (hc : Decomposition.inputCheck q c = true) :
    (sourceColumn 0 q m).eval c = Part.some (Encodable.encode (Decomposition.word c)) := by
  simp [sourceColumn_eval, valid, output, hc]

theorem highWordColumn_eval (q m c : Nat) (hc : Decomposition.inputCheck q c = true) :
    (sourceColumn 1 q m).eval c = Part.some (Encodable.encode (Decomposition.highWord m c)) := by
  simp [sourceColumn_eval, valid, output, hc]

theorem lowWordColumn_eval (q m c : Nat) (hc : Decomposition.inputCheck q c = true) :
    (sourceColumn 2 q m).eval c = Part.some (Encodable.encode (Decomposition.lowWord m c)) := by
  simp [sourceColumn_eval, valid, output, hc]

theorem highColumn_eval (q m c : Nat) (hc : Decomposition.inputCheck q c = true) :
    (sourceColumn 3 q m).eval c = Part.some (Decomposition.highCode m c) := by
  simp [sourceColumn_eval, valid, output, hc]

theorem lowColumn_eval (q m c : Nat) (hc : Decomposition.inputCheck q c = true) :
    (sourceColumn 4 q m).eval c = Part.some (Decomposition.lowCode m c) := by
  simp [sourceColumn_eval, valid, output, hc]

theorem partsColumn_eval (q m c : Nat) (hc : Decomposition.inputCheck q c = true) :
    (sourceColumn 5 q m).eval c = Part.some (Nat.pair (Decomposition.highCode m c) (Decomposition.lowCode m c)) := by
  simp [sourceColumn_eval, valid, output, hc]

theorem rebuildColumn_eval (q m c : Nat) (hc : Decomposition.inputCheck q c = true) :
    (sourceColumn 6 q m).eval c = Part.some (Decomposition.rebuildCode c) := by
  simp [sourceColumn_eval, valid, output, hc]

theorem partsColumn_value (q m c : Nat) (hc : Decomposition.inputCheck q c = true) :
    Comparison.acceptedCode q (Decomposition.highCode m c) = true ∧
      Comparison.acceptedCode q (Decomposition.lowCode m c) = true ∧
      interpretation q (Decomposition.highCode m c) = Wilken.omegaSequence (base q) (m + 1) *
        (interpretation q c / Wilken.omegaSequence (base q) (m + 1)) ∧
      interpretation q (Decomposition.lowCode m c) = interpretation q c % Wilken.omegaSequence (base q) (m + 1) := by
  have ha := Decomposition.parts_accepted q m c hc
  have hv := Decomposition.parts_code_value q m c hc
  exact ⟨ha.1, ha.2, hv.1, hv.2⟩

theorem sourceColumn_unique (tag q m c : Nat) (htag : tag ≤ 6) (hc : Decomposition.inputCheck q c = true) :
    ∃! value, value ∈ (sourceColumn tag q m).eval c := by
  refine ⟨output tag m c, (sourceColumn_graph tag q m c _).mpr ⟨⟨htag, hc⟩, rfl⟩, ?_⟩
  intro value hv
  exact ((sourceColumn_graph tag q m c value).mp hv).2

def inputEvaluation (query : Nat) : Part Nat := cond (validRaw query) (Part.some 0) Part.none

theorem inputEvaluation_partrec : Partrec inputEvaluation :=
  Partrec.cond validRaw_primrec.to_comp (Computable.const 0).partrec Partrec.none

theorem inputProgram_exists : ∃ p : Program, ∀ query, p.eval query = inputEvaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp inputEvaluation_partrec)

noncomputable def inputProgram : Program := Classical.choose inputProgram_exists

theorem inputProgram_domain (tag q m c : Nat) :
    inputProgram.domain (Nat.pair tag (Nat.pair q (Nat.pair m c))) ↔
      tag ≤ 6 ∧ Decomposition.inputCheck q c = true := by
  rw [Program.domain, Classical.choose_spec inputProgram_exists]
  cases h : valid tag q c <;> simp [inputEvaluation, validRaw, Nat.unpair_pair, h, ← valid_exact]

noncomputable def inputColumn (tag q m : Nat) : Program := ((inputProgram.column tag).column q).column m

theorem inputColumn_primrec : Primrec (fun p : Nat × (Nat × Nat) => inputColumn p.1 p.2.1 p.2.2) := by
  have ht := Program.column_primrec.comp (Primrec.const inputProgram) Primrec.fst
  have hq := Program.column_primrec.comp ht (Primrec.fst.comp Primrec.snd)
  exact Program.column_primrec.comp hq (Primrec.snd.comp Primrec.snd)

theorem inputColumn_domain (tag q m c : Nat) :
    (inputColumn tag q m).domain c ↔ tag ≤ 6 ∧ Decomposition.inputCheck q c = true := by
  rw [inputColumn, Program.column_domain, Program.column_domain, Program.column_domain]
  exact inputProgram_domain tag q m c

def graphRaw (query : Nat) : Bool := validRaw query.unpair.1 && query.unpair.2 == outputRaw query.unpair.1

theorem graphRaw_primrec : Primrec graphRaw :=
  Primrec.and.comp (validRaw_primrec.comp (Primrec.fst.comp Primrec.unpair))
    (Primrec.beq.comp (Primrec.snd.comp Primrec.unpair) (outputRaw_primrec.comp (Primrec.fst.comp Primrec.unpair)))

def graphEvaluation (query : Nat) : Part Nat := cond (graphRaw query) (Part.some 0) Part.none

theorem graphEvaluation_partrec : Partrec graphEvaluation :=
  Partrec.cond graphRaw_primrec.to_comp (Computable.const 0).partrec Partrec.none

theorem graphProgram_exists : ∃ p : Program, ∀ query, p.eval query = graphEvaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp graphEvaluation_partrec)

noncomputable def graphProgram : Program := Classical.choose graphProgram_exists

theorem graphProgram_domain (tag q m c value : Nat) :
    graphProgram.domain (Nat.pair (Nat.pair tag (Nat.pair q (Nat.pair m c))) value) ↔
      (tag ≤ 6 ∧ Decomposition.inputCheck q c = true) ∧ value = output tag m c := by
  rw [Program.domain, Classical.choose_spec graphProgram_exists]
  simp only [graphEvaluation, graphRaw, validRaw, outputRaw, Nat.unpair_pair]
  cases h : valid tag q c <;> cases he : value == output tag m c <;> simp [h, he, ← valid_exact, ← beq_iff_eq]

noncomputable def graphColumn (tag q m c : Nat) : Program :=
  graphProgram.column (Nat.pair tag (Nat.pair q (Nat.pair m c)))

theorem graphColumn_primrec : Primrec (fun p : Nat × (Nat × (Nat × Nat)) => graphColumn p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  Program.column_primrec.comp (Primrec.const graphProgram) (Primrec₂.natPair.comp Primrec.fst
    (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd) (Primrec₂.natPair.comp
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))

theorem graphColumn_domain (tag q m c value : Nat) :
    (graphColumn tag q m c).domain value ↔ (tag ≤ 6 ∧ Decomposition.inputCheck q c = true) ∧ value = output tag m c := by
  rw [graphColumn, Program.column_domain]
  exact graphProgram_domain tag q m c value

theorem graphColumn_execution (tag q m c value : Nat) :
    (graphColumn tag q m c).domain value ↔ value ∈ (sourceColumn tag q m).eval c :=
  (graphColumn_domain tag q m c value).trans (sourceColumn_graph tag q m c value).symm

end Alexander313.HereditaryNativeDecompositionProgram
