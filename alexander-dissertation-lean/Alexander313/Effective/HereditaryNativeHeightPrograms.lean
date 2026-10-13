import Alexander313.Wilken.HereditaryNativeHeight

/-!
# Guarded native literal-height Programs

Tags 0 and 1 return original weak-normal and original raw written heights.
Tag 2 returns the actual normalized raw height. Tags 3, 4 and 5 return the
actual high-part, low-part and rebuilt ANF heights on the original normal
domain. Every domain retains original coded-epsilon admission; invalid tags
reject. Actual output-code admission, literal height nonincrease and least
finite-fragment admission are derived. Complete numerical graphs and the
executing fragment recognizer use real PR kernels and compiler columns.
These heights are attached to the written or constructed native terms;
ordinal spelling invariance and source 2.22/2.46/3.7 are not asserted.
All proof candidates remain uncompiled.
-/

namespace Alexander313.HereditaryNativeHeightProgram

open Wilken.RelativeTerm.Hereditary.NativeContext

def input (tag q c : Nat) : Bool :=
  cond (tag == 0) (Comparison.acceptedCode q c)
    (cond (tag == 1) (checkCode q c)
      (cond (tag == 2) (checkCode q c)
        (cond (tag == 3) (Comparison.acceptedCode q c)
          (cond (tag == 4) (Comparison.acceptedCode q c)
            (cond (tag == 5) (Comparison.acceptedCode q c) false)))))

theorem input_primrec : Primrec (fun p : Nat × (Nat × Nat) => input p.1 p.2.1 p.2.2) := by
  have ht (k : Nat) := Primrec.beq.comp Primrec.fst (Primrec.const k)
  have hq := Primrec.fst.comp Primrec.snd
  have hc := Primrec.snd.comp Primrec.snd
  have hn := Comparison.acceptedCode_primrec.comp hq hc
  have hr := checkCode_primrec.comp hq hc
  exact (ht 0).cond hn ((ht 1).cond hr ((ht 2).cond hr
    ((ht 3).cond hn ((ht 4).cond hn ((ht 5).cond hn (Primrec.const false))))))

theorem input_exact (tag q c : Nat) : input tag q c = true ↔
    ((tag = 1 ∨ tag = 2) ∧ checkCode q c = true) ∨
      ((tag = 0 ∨ tag = 3 ∨ tag = 4 ∨ tag = 5) ∧ Comparison.acceptedCode q c = true) := by
  by_cases h0 : tag = 0
  · subst tag; simp [input]
  · by_cases h1 : tag = 1
    · subst tag; simp [input]
    · by_cases h2 : tag = 2
      · subst tag; simp [input]
      · by_cases h3 : tag = 3
        · subst tag; simp [input]
        · by_cases h4 : tag = 4
          · subst tag; simp [input]
          · by_cases h5 : tag = 5 <;> simp [input, h0, h1, h2, h3, h4, h5]

def outputCode (tag q m c : Nat) : Nat := cond (tag == 2) (Normalization.normalizeCode q c)
  (cond (tag == 3) (Decomposition.highCode m c)
    (cond (tag == 4) (Decomposition.lowCode m c)
      (cond (tag == 5) (Decomposition.rebuildCode c) c)))

theorem outputCode_primrec : Primrec
    (fun p : Nat × (Nat × (Nat × Nat)) => outputCode p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have ht (k : Nat) := Primrec.beq.comp Primrec.fst (Primrec.const k)
  have hq := Primrec.fst.comp Primrec.snd
  have hm := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hc := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact (ht 2).cond (Normalization.Effective.normalizeCode_primrec.comp hq hc)
    ((ht 3).cond (Decomposition.highCode_primrec.comp hm hc)
      ((ht 4).cond (Decomposition.lowCode_primrec.comp hm hc)
        ((ht 5).cond (Decomposition.rebuildCode_primrec.comp hc) hc)))

def answer (tag q m c : Nat) : Nat :=
  Wilken.RelativeTerm.heightCode (outputCode tag q m c)

theorem answer_primrec : Primrec
    (fun p : Nat × (Nat × (Nat × Nat)) => answer p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  Wilken.RelativeTerm.heightCode_primrec.comp outputCode_primrec

theorem outputCode_spec (tag q m c : Nat) (hc : input tag q c = true) :
    checkCode q (outputCode tag q m c) = true ∧
      Wilken.RelativeTerm.heightCode (outputCode tag q m c) ≤ Wilken.RelativeTerm.heightCode c := by
  rcases (input_exact tag q c).mp hc with ⟨h, hc⟩ | ⟨h, hc⟩
  · rcases h with rfl | rfl
    · simp [outputCode, hc]
    · simpa [outputCode] using And.intro (Normalization.normalizeCode_checked q c hc).1
        (Height.normalizeCode_height q c hc)
  · have hi := ((Comparison.acceptedCode_exact q c).mp hc).1
    have hd : Decomposition.inputCheck q c = true := hc
    rcases h with rfl | rfl | rfl | rfl
    · simp [outputCode, hi]
    · have hs := Decomposition.parts_accepted q m c hd
      simpa [outputCode] using And.intro ((Comparison.acceptedCode_exact q _).mp hs.1).1
        (Height.parts_code_height q m c hi).1
    · have hs := Decomposition.parts_accepted q m c hd
      simpa [outputCode] using And.intro ((Comparison.acceptedCode_exact q _).mp hs.2).1
        (Height.parts_code_height q m c hi).2
    · have hs := Decomposition.rebuild_spec q c hd
      simpa [outputCode] using And.intro ((Comparison.acceptedCode_exact q _).mp hs.1).1
        (Height.rebuildCode_height q c hi)

theorem outputCode_at_answer (tag q m c : Nat) (hc : input tag q c = true) :
    Height.fragmentCheck q (answer tag q m c) (outputCode tag q m c) = true :=
  Height.fragmentCheck_at_height q _ (outputCode_spec tag q m c hc).1

def evaluation (query : Nat) : Part Nat :=
  cond (input query.unpair.1 query.unpair.2.unpair.1 query.unpair.2.unpair.2.unpair.2)
    (Part.some (answer query.unpair.1 query.unpair.2.unpair.1
      query.unpair.2.unpair.2.unpair.1 query.unpair.2.unpair.2.unpair.2)) Part.none

theorem evaluation_partrec : Partrec evaluation := by
  have ht := Primrec.fst.comp Primrec.unpair
  have hp := Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)
  have hq := Primrec.fst.comp hp
  have hmc := Primrec.unpair.comp (Primrec.snd.comp hp)
  have hm := Primrec.fst.comp hmc
  have hc := Primrec.snd.comp hmc
  exact Partrec.cond (input_primrec.comp (ht.pair (hq.pair hc))).to_comp
    (answer_primrec.comp (ht.pair (hq.pair (hm.pair hc)))).to_comp.partrec Partrec.none

theorem program_exists : ∃ p : Program, ∀ query, p.eval query = evaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp evaluation_partrec)

noncomputable def program : Program := Classical.choose program_exists

theorem program_eval (tag q m c : Nat) :
    program.eval (Nat.pair tag (Nat.pair q (Nat.pair m c))) =
      cond (input tag q c) (Part.some (answer tag q m c)) Part.none := by
  simpa only [evaluation, Nat.unpair_pair] using
    Classical.choose_spec program_exists (Nat.pair tag (Nat.pair q (Nat.pair m c)))

theorem program_domain (tag q m c : Nat) :
    program.domain (Nat.pair tag (Nat.pair q (Nat.pair m c))) ↔ input tag q c = true := by
  rw [Program.domain, program_eval]
  cases h : input tag q c <;> simp [h]

theorem program_graph (tag q m c output : Nat) :
    output ∈ program.eval (Nat.pair tag (Nat.pair q (Nat.pair m c))) ↔
      input tag q c = true ∧ output = answer tag q m c := by
  rw [program_eval]
  cases h : input tag q c <;> simp [h]

noncomputable def sourceColumn (tag q m : Nat) : Program := ((program.column tag).column q).column m

theorem sourceColumn_primrec : Primrec (fun p : Nat × (Nat × Nat) => sourceColumn p.1 p.2.1 p.2.2) := by
  have ht := Program.column_primrec.comp (Primrec.const program) Primrec.fst
  exact Program.column_primrec.comp
    (Program.column_primrec.comp ht (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)

theorem sourceColumn_eval (tag q m c : Nat) : (sourceColumn tag q m).eval c =
    cond (input tag q c) (Part.some (answer tag q m c)) Part.none := by
  simp only [sourceColumn, Nat.Partrec.Code.eval_curry, program_eval]

theorem sourceColumn_domain (tag q m c : Nat) : (sourceColumn tag q m).domain c ↔ input tag q c = true := by
  rw [sourceColumn, Program.column_domain, Program.column_domain, Program.column_domain]
  exact program_domain tag q m c

theorem sourceColumn_graph (tag q m c output : Nat) : output ∈ (sourceColumn tag q m).eval c ↔
    input tag q c = true ∧ output = answer tag q m c := by
  simp only [sourceColumn, Nat.Partrec.Code.eval_curry]
  exact program_graph tag q m c output

theorem sourceColumn_height_bound (tag q m c output : Nat)
    (ho : output ∈ (sourceColumn tag q m).eval c) :
    output ≤ Wilken.RelativeTerm.heightCode c := by
  obtain ⟨hc, rfl⟩ := (sourceColumn_graph tag q m c output).mp ho
  exact (outputCode_spec tag q m c hc).2

theorem sourceColumn_fragment (tag q m c output : Nat)
    (ho : output ∈ (sourceColumn tag q m).eval c) :
    Height.fragmentCheck q output (outputCode tag q m c) = true := by
  obtain ⟨hc, rfl⟩ := (sourceColumn_graph tag q m c output).mp ho
  exact outputCode_at_answer tag q m c hc

theorem normalColumn_domain (q m c : Nat) : (sourceColumn 0 q m).domain c ↔
    checkCode q c = true ∧ Comparison.Normal q (Wilken.RelativeTerm.Hereditary.ThetaCourse.rawTree c) := by
  simp [sourceColumn_domain, input, Comparison.acceptedCode_exact]

theorem rawColumn_domain (q m c : Nat) : (sourceColumn 1 q m).domain c ↔ checkCode q c = true := by
  simp [sourceColumn_domain, input]

theorem normalizedColumn_domain (q m c : Nat) : (sourceColumn 2 q m).domain c ↔ checkCode q c = true := by
  simp [sourceColumn_domain, input]

theorem normalColumn_height (q m c : Nat) (hc : Comparison.acceptedCode q c = true) :
    (sourceColumn 0 q m).eval c =
      Part.some (Wilken.RelativeTerm.Hereditary.ThetaCourse.rawTree c).height := by
  have hi := ((Comparison.acceptedCode_exact q c).mp hc).1
  simp [sourceColumn_eval, input, hc, answer, outputCode, Height.input_heightCode q c hi]

theorem rawColumn_height (q m c : Nat) (hc : checkCode q c = true) :
    (sourceColumn 1 q m).eval c =
      Part.some (Wilken.RelativeTerm.Hereditary.ThetaCourse.rawTree c).height := by
  simp [sourceColumn_eval, input, hc, answer, outputCode, Height.input_heightCode q c hc]

theorem normalizedColumn_height (q m c : Nat) (hc : checkCode q c = true) :
    (sourceColumn 2 q m).eval c =
      Part.some (Normalization.normalize q (Wilken.RelativeTerm.Hereditary.ThetaCourse.rawTree c)).height := by
  simp [sourceColumn_eval, input, hc, answer, outputCode, Normalization.normalizeCode,
    Wilken.RelativeTerm.heightCode_code]

/-- Complete numerical output certificate, including height zero. -/
def graphCheck (tag q m c output : Nat) : Bool := input tag q c && (output == answer tag q m c)

theorem graphCheck_primrec : Primrec
    (fun p : (Nat × (Nat × (Nat × Nat))) × Nat => graphCheck p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2) := by
  have ht := Primrec.fst.comp Primrec.fst
  have hq := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hc := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  exact Primrec.and.comp (input_primrec.comp (ht.pair (hq.pair hc)))
    (Primrec.beq.comp Primrec.snd (answer_primrec.comp Primrec.fst))

def graphEvaluation (query : Nat) : Part Nat :=
  let source := query.unpair.1
  cond (graphCheck source.unpair.1 source.unpair.2.unpair.1
    source.unpair.2.unpair.2.unpair.1 source.unpair.2.unpair.2.unpair.2 query.unpair.2)
    (Part.some 0) Part.none

theorem graphEvaluation_partrec : Partrec graphEvaluation := by
  have hs := Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)
  have hp := Primrec.unpair.comp (Primrec.snd.comp hs)
  have hmc := Primrec.unpair.comp (Primrec.snd.comp hp)
  have hsource := (Primrec.fst.comp hs).pair ((Primrec.fst.comp hp).pair hmc)
  have hg := graphCheck_primrec.comp (hsource.pair (Primrec.snd.comp Primrec.unpair))
  exact Partrec.cond hg.to_comp (Computable.const 0).partrec Partrec.none

theorem graphProgram_exists : ∃ p : Program, ∀ query, p.eval query = graphEvaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp graphEvaluation_partrec)

noncomputable def graphProgram : Program := Classical.choose graphProgram_exists

theorem graphProgram_domain (tag q m c output : Nat) :
    graphProgram.domain (Nat.pair (Nat.pair tag (Nat.pair q (Nat.pair m c))) output) ↔
      input tag q c = true ∧ output = answer tag q m c := by
  rw [Program.domain, Classical.choose_spec graphProgram_exists]
  simp only [graphEvaluation, Nat.unpair_pair, graphCheck]
  cases hi : input tag q c <;> cases ho : output == answer tag q m c <;>
    simp [hi, ho, ← beq_iff_eq]

noncomputable def graphColumn (tag q m c : Nat) : Program :=
  graphProgram.column (Nat.pair tag (Nat.pair q (Nat.pair m c)))

theorem graphColumn_primrec : Primrec
    (fun p : Nat × (Nat × (Nat × Nat)) => graphColumn p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  Program.column_primrec.comp (Primrec.const graphProgram) (Primrec₂.natPair.comp Primrec.fst
    (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd)
      (Primrec₂.natPair.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))

theorem graphColumn_domain (tag q m c output : Nat) : (graphColumn tag q m c).domain output ↔
    input tag q c = true ∧ output = answer tag q m c := by
  rw [graphColumn, Program.column_domain]
  exact graphProgram_domain tag q m c output

theorem graphColumn_executed (tag q m c output : Nat) : (graphColumn tag q m c).domain output ↔
    output ∈ (sourceColumn tag q m).eval c := by
  rw [graphColumn_domain, sourceColumn_graph]

theorem graphColumn_unique (tag q m c : Nat) (hc : input tag q c = true) :
    ∃! output, (graphColumn tag q m c).domain output := by
  refine ⟨answer tag q m c, (graphColumn_domain tag q m c _).mpr ⟨hc, rfl⟩, ?_⟩
  intro output ho
  exact ((graphColumn_domain tag q m c output).mp ho).2

/-- This positive recognizer executes the ORIGINAL finite native parser. -/
def fragmentEvaluation (query : Nat) : Part Nat :=
  cond (Height.fragmentCheck query.unpair.1 query.unpair.2.unpair.1 query.unpair.2.unpair.2)
    (Part.some 0) Part.none

theorem fragmentEvaluation_partrec : Partrec fragmentEvaluation := by
  have hp := Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)
  have h := Height.fragmentCheck_primrec.comp
    (((Primrec.fst.comp Primrec.unpair).pair (Primrec.fst.comp hp)).pair (Primrec.snd.comp hp))
  exact Partrec.cond h.to_comp (Computable.const 0).partrec Partrec.none

theorem fragmentProgram_exists : ∃ p : Program, ∀ query, p.eval query = fragmentEvaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp fragmentEvaluation_partrec)

noncomputable def fragmentProgram : Program := Classical.choose fragmentProgram_exists

theorem fragmentProgram_domain (q n c : Nat) : fragmentProgram.domain (Nat.pair q (Nat.pair n c)) ↔
    checkCode q c = true ∧ Wilken.RelativeTerm.heightCode c ≤ n := by
  rw [Program.domain, Classical.choose_spec fragmentProgram_exists]
  simp only [fragmentEvaluation, Nat.unpair_pair]
  cases h : Height.fragmentCheck q n c <;> simp [h, ← Height.fragmentCheck_exact]

noncomputable def fragmentColumn (q n : Nat) : Program := (fragmentProgram.column q).column n

theorem fragmentColumn_primrec : Primrec₂ fragmentColumn :=
  (Program.column_primrec.comp
    (Program.column_primrec.comp (Primrec.const fragmentProgram) Primrec.fst) Primrec.snd).to₂

theorem fragmentColumn_domain (q n c : Nat) : (fragmentColumn q n).domain c ↔
    checkCode q c = true ∧ Wilken.RelativeTerm.heightCode c ≤ n := by
  rw [fragmentColumn, Program.column_domain, Program.column_domain]
  exact fragmentProgram_domain q n c

end Alexander313.HereditaryNativeHeightProgram
