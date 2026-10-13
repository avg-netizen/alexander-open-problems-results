import Alexander313.Wilken.HereditarySourceDecomposition

/-!
# Actual Programs for original hereditary principal words and cardinal pieces

Tags 0/1/2 execute the whole/high/low encoded source atom lists. Tags 3/4
execute the original hereditary high/low codes, tag 5 the paired codes, and tag 6
the actual original ANF reconstruction. Every operation retains the original
checked recursively normal input domain at every level, including zero; unknown tags reject. Positive input and
complete computed-output graph Programs specialize by genuine PR compilers.
Numerical uniqueness refers to this executing finite algorithm. Arbitrary
source spellings of equal ordinal values are not identified syntactically.
All proof candidates remain uncompiled.
-/

namespace Alexander313.HereditarySourceDecompositionProgram

open Wilken.RelativeTerm.Hereditary

def output (tag r m c : Nat) : Nat :=
  cond (tag == 0) (Encodable.encode (SourceDecomposition.word r c))
    (cond (tag == 1) (Encodable.encode (SourceDecomposition.highWord r m c))
      (cond (tag == 2) (Encodable.encode (SourceDecomposition.lowWord r m c))
        (cond (tag == 3) (SourceDecomposition.highCode r m c)
          (cond (tag == 4) (SourceDecomposition.lowCode r m c)
            (cond (tag == 5) (Nat.pair (SourceDecomposition.highCode r m c) (SourceDecomposition.lowCode r m c))
              (cond (tag == 6) (SourceDecomposition.rebuildCode r c) 0))))))

theorem output_primrec : Primrec (fun p : Nat × (Nat × (Nat × Nat)) => output p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hr := Primrec.fst.comp Primrec.snd
  have hm := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hc := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hword := Primrec.encode.comp (SourceDecomposition.word_primrec.comp hr hc)
  have hp := hr.pair (hm.pair hc)
  have hhighWord := Primrec.encode.comp (SourceDecomposition.highWord_primrec.comp hp)
  have hlowWord := Primrec.encode.comp (SourceDecomposition.lowWord_primrec.comp hp)
  have hhigh := SourceDecomposition.highCode_primrec.comp hp
  have hlow := SourceDecomposition.lowCode_primrec.comp hp
  have hpair := Primrec₂.natPair.comp hhigh hlow
  have hrebuild := SourceDecomposition.rebuildCode_primrec.comp hr hc
  have ht (i : Nat) := Primrec.beq.comp Primrec.fst (Primrec.const i)
  exact (ht 0).cond hword ((ht 1).cond hhighWord ((ht 2).cond hlowWord
    ((ht 3).cond hhigh ((ht 4).cond hlow ((ht 5).cond hpair ((ht 6).cond hrebuild (Primrec.const 0)))))))

def valid (tag r c : Nat) : Bool := decide (tag ≤ 6) && SourceDecomposition.inputCheck r c

theorem valid_primrec : Primrec (fun p : Nat × (Nat × Nat) => valid p.1 p.2.1 p.2.2) :=
  Primrec.and.comp ((Primrec.nat_le.comp Primrec.fst (Primrec.const 6)).decide)
    (SourceDecomposition.inputCheck_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))

theorem valid_exact (tag r c : Nat) : valid tag r c = true ↔ tag ≤ 6 ∧ SourceDecomposition.inputCheck r c = true := by
  simp only [valid, Bool.and_eq_true, decide_eq_true_eq]

def validRaw (query : Nat) : Bool := valid query.unpair.1 query.unpair.2.unpair.1
  query.unpair.2.unpair.2.unpair.2

def outputRaw (query : Nat) : Nat := output query.unpair.1 query.unpair.2.unpair.1
  query.unpair.2.unpair.2.unpair.1 query.unpair.2.unpair.2.unpair.2

theorem validRaw_primrec : Primrec validRaw := by
  have hr := Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)
  have hp := Primrec.unpair.comp (Primrec.snd.comp hr)
  exact valid_primrec.comp ((Primrec.fst.comp Primrec.unpair).pair
    ((Primrec.fst.comp hr).pair (Primrec.snd.comp hp)))

theorem outputRaw_primrec : Primrec outputRaw := by
  have hr := Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)
  have hp := Primrec.unpair.comp (Primrec.snd.comp hr)
  exact output_primrec.comp ((Primrec.fst.comp Primrec.unpair).pair
    ((Primrec.fst.comp hr).pair hp))

def evaluation (query : Nat) : Part Nat := cond (validRaw query) (Part.some (outputRaw query)) Part.none

theorem evaluation_partrec : Partrec evaluation :=
  Partrec.cond validRaw_primrec.to_comp outputRaw_primrec.to_comp.partrec Partrec.none

theorem program_exists : ∃ p : Program, ∀ query, p.eval query = evaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp evaluation_partrec)

noncomputable def program : Program := Classical.choose program_exists

theorem program_eval (tag r m c : Nat) :
    program.eval (Nat.pair tag (Nat.pair r (Nat.pair m c))) =
      cond (valid tag r c) (Part.some (output tag r m c)) Part.none := by
  simpa only [evaluation, validRaw, outputRaw, Nat.unpair_pair] using
    Classical.choose_spec program_exists (Nat.pair tag (Nat.pair r (Nat.pair m c)))

theorem program_domain (tag r m c : Nat) :
    program.domain (Nat.pair tag (Nat.pair r (Nat.pair m c))) ↔
      tag ≤ 6 ∧ SourceDecomposition.inputCheck r c = true := by
  rw [Program.domain, program_eval]
  cases h : valid tag r c <;> simp [h, ← valid_exact]

theorem program_graph (tag r m c value : Nat) :
    value ∈ program.eval (Nat.pair tag (Nat.pair r (Nat.pair m c))) ↔
      (tag ≤ 6 ∧ SourceDecomposition.inputCheck r c = true) ∧ value = output tag r m c := by
  rw [program_eval]
  cases h : valid tag r c <;> simp [h, ← valid_exact]

noncomputable def sourceColumn (tag r m : Nat) : Program := ((program.column tag).column r).column m

theorem sourceColumn_primrec : Primrec (fun p : Nat × (Nat × Nat) => sourceColumn p.1 p.2.1 p.2.2) := by
  have ht := Program.column_primrec.comp (Primrec.const program) Primrec.fst
  have hq := Program.column_primrec.comp ht (Primrec.fst.comp Primrec.snd)
  exact Program.column_primrec.comp hq (Primrec.snd.comp Primrec.snd)

theorem sourceColumn_eval (tag r m c : Nat) :
    (sourceColumn tag r m).eval c = cond (valid tag r c) (Part.some (output tag r m c)) Part.none := by
  simp only [sourceColumn, Nat.Partrec.Code.eval_curry, program_eval]

theorem sourceColumn_domain (tag r m c : Nat) :
    (sourceColumn tag r m).domain c ↔ tag ≤ 6 ∧ SourceDecomposition.inputCheck r c = true := by
  rw [sourceColumn, Program.column_domain, Program.column_domain, Program.column_domain]
  exact program_domain tag r m c

theorem sourceColumn_graph (tag r m c value : Nat) : value ∈ (sourceColumn tag r m).eval c ↔
    (tag ≤ 6 ∧ SourceDecomposition.inputCheck r c = true) ∧ value = output tag r m c := by
  simp only [sourceColumn, Nat.Partrec.Code.eval_curry]
  exact program_graph tag r m c value

theorem sourceColumn_original (tag r m c : Nat) (htag : tag ≤ 6) :
    (sourceColumn tag r m).domain c ↔ checkCode r c = true ∧ Theta.Normal r (Wilken.RelativeTerm.Hereditary.ThetaCourse.rawTree c) := by
  simp only [sourceColumn_domain, htag, true_and, SourceDecomposition.inputCheck_exact]

theorem wordColumn_eval (r m c : Nat) (hc : SourceDecomposition.inputCheck r c = true) :
    (sourceColumn 0 r m).eval c = Part.some (Encodable.encode (SourceDecomposition.word r c)) := by
  simp [sourceColumn_eval, valid, output, hc]

theorem highWordColumn_eval (r m c : Nat) (hc : SourceDecomposition.inputCheck r c = true) :
    (sourceColumn 1 r m).eval c = Part.some (Encodable.encode (SourceDecomposition.highWord r m c)) := by
  simp [sourceColumn_eval, valid, output, hc]

theorem lowWordColumn_eval (r m c : Nat) (hc : SourceDecomposition.inputCheck r c = true) :
    (sourceColumn 2 r m).eval c = Part.some (Encodable.encode (SourceDecomposition.lowWord r m c)) := by
  simp [sourceColumn_eval, valid, output, hc]

theorem highColumn_eval (r m c : Nat) (hc : SourceDecomposition.inputCheck r c = true) :
    (sourceColumn 3 r m).eval c = Part.some (SourceDecomposition.highCode r m c) := by
  simp [sourceColumn_eval, valid, output, hc]

theorem lowColumn_eval (r m c : Nat) (hc : SourceDecomposition.inputCheck r c = true) :
    (sourceColumn 4 r m).eval c = Part.some (SourceDecomposition.lowCode r m c) := by
  simp [sourceColumn_eval, valid, output, hc]

theorem partsColumn_eval (r m c : Nat) (hc : SourceDecomposition.inputCheck r c = true) :
    (sourceColumn 5 r m).eval c = Part.some (Nat.pair (SourceDecomposition.highCode r m c) (SourceDecomposition.lowCode r m c)) := by
  simp [sourceColumn_eval, valid, output, hc]

theorem rebuildColumn_eval (r m c : Nat) (hc : SourceDecomposition.inputCheck r c = true) :
    (sourceColumn 6 r m).eval c = Part.some (SourceDecomposition.rebuildCode r c) := by
  simp [sourceColumn_eval, valid, output, hc]

theorem partsColumn_value (r m c : Nat) (hc : SourceDecomposition.inputCheck r c = true) :
    Theta.acceptedCode r (SourceDecomposition.highCode r m c) = true ∧
      Theta.acceptedCode r (SourceDecomposition.lowCode r m c) = true ∧
      interpretation r (SourceDecomposition.highCode r m c) = Wilken.omegaSequence (finiteBase r) (m + 1) *
        (interpretation r c / Wilken.omegaSequence (finiteBase r) (m + 1)) ∧
      interpretation r (SourceDecomposition.lowCode r m c) = interpretation r c % Wilken.omegaSequence (finiteBase r) (m + 1) := by
  have ha := SourceDecomposition.parts_accepted r m c hc
  have hv := SourceDecomposition.parts_code_value r m c hc
  exact ⟨ha.1, ha.2, hv.1, hv.2⟩

theorem sourceColumn_unique (tag r m c : Nat) (htag : tag ≤ 6) (hc : SourceDecomposition.inputCheck r c = true) :
    ∃! value, value ∈ (sourceColumn tag r m).eval c := by
  refine ⟨output tag r m c, (sourceColumn_graph tag r m c _).mpr ⟨⟨htag, hc⟩, rfl⟩, ?_⟩
  intro value hv
  exact ((sourceColumn_graph tag r m c value).mp hv).2

def inputEvaluation (query : Nat) : Part Nat := cond (validRaw query) (Part.some 0) Part.none

theorem inputEvaluation_partrec : Partrec inputEvaluation :=
  Partrec.cond validRaw_primrec.to_comp (Computable.const 0).partrec Partrec.none

theorem inputProgram_exists : ∃ p : Program, ∀ query, p.eval query = inputEvaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp inputEvaluation_partrec)

noncomputable def inputProgram : Program := Classical.choose inputProgram_exists

theorem inputProgram_domain (tag r m c : Nat) :
    inputProgram.domain (Nat.pair tag (Nat.pair r (Nat.pair m c))) ↔
      tag ≤ 6 ∧ SourceDecomposition.inputCheck r c = true := by
  rw [Program.domain, Classical.choose_spec inputProgram_exists]
  cases h : valid tag r c <;> simp [inputEvaluation, validRaw, Nat.unpair_pair, h, ← valid_exact]

noncomputable def inputColumn (tag r m : Nat) : Program := ((inputProgram.column tag).column r).column m

theorem inputColumn_primrec : Primrec (fun p : Nat × (Nat × Nat) => inputColumn p.1 p.2.1 p.2.2) := by
  have ht := Program.column_primrec.comp (Primrec.const inputProgram) Primrec.fst
  have hq := Program.column_primrec.comp ht (Primrec.fst.comp Primrec.snd)
  exact Program.column_primrec.comp hq (Primrec.snd.comp Primrec.snd)

theorem inputColumn_domain (tag r m c : Nat) :
    (inputColumn tag r m).domain c ↔ tag ≤ 6 ∧ SourceDecomposition.inputCheck r c = true := by
  rw [inputColumn, Program.column_domain, Program.column_domain, Program.column_domain]
  exact inputProgram_domain tag r m c

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

theorem graphProgram_domain (tag r m c value : Nat) :
    graphProgram.domain (Nat.pair (Nat.pair tag (Nat.pair r (Nat.pair m c))) value) ↔
      (tag ≤ 6 ∧ SourceDecomposition.inputCheck r c = true) ∧ value = output tag r m c := by
  rw [Program.domain, Classical.choose_spec graphProgram_exists]
  simp only [graphEvaluation, graphRaw, validRaw, outputRaw, Nat.unpair_pair]
  cases h : valid tag r c <;> cases he : value == output tag r m c <;> simp [h, he, ← valid_exact, ← beq_iff_eq]

noncomputable def graphColumn (tag r m c : Nat) : Program :=
  graphProgram.column (Nat.pair tag (Nat.pair r (Nat.pair m c)))

theorem graphColumn_primrec : Primrec (fun p : Nat × (Nat × (Nat × Nat)) => graphColumn p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  Program.column_primrec.comp (Primrec.const graphProgram) (Primrec₂.natPair.comp Primrec.fst
    (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd) (Primrec₂.natPair.comp
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))

theorem graphColumn_domain (tag r m c value : Nat) :
    (graphColumn tag r m c).domain value ↔ (tag ≤ 6 ∧ SourceDecomposition.inputCheck r c = true) ∧ value = output tag r m c := by
  rw [graphColumn, Program.column_domain]
  exact graphProgram_domain tag r m c value

theorem graphColumn_execution (tag r m c value : Nat) :
    (graphColumn tag r m c).domain value ↔ value ∈ (sourceColumn tag r m).eval c :=
  (graphColumn_domain tag r m c value).trans (sourceColumn_graph tag r m c value).symm

end Alexander313.HereditarySourceDecompositionProgram
