import Alexander313.Wilken.HereditaryNativeNormalizationPrimitive

/-!
# Actual Programs for native normalization

The constructed PR normalizer executes on exactly the original native
epsilon-context domain. Its output is admitted and weak normal with the
same actual ordinal. Positive input and literal executing-output graph
Programs have exact guards; their columns are genuine PR specializations.
Uniqueness concerns the actual computed code, not all weak-normal spellings.
Uncompiled proof candidates.
-/

namespace Alexander313.HereditaryNativeNormalizationProgram

open Wilken.RelativeTerm.Hereditary

def evaluation (query : Nat) : Part Nat := cond (NativeContext.checkCode query.unpair.1 query.unpair.2)
  (Part.some (NativeContext.Normalization.normalizeCode query.unpair.1 query.unpair.2)) Part.none

theorem evaluation_partrec : Partrec evaluation := by
  have hq := Primrec.fst.comp Primrec.unpair
  have hc := Primrec.snd.comp Primrec.unpair
  exact Partrec.cond (NativeContext.checkCode_primrec.comp hq hc).to_comp
    (NativeContext.Normalization.Effective.normalizeCode_primrec.comp hq hc).to_comp.partrec Partrec.none

theorem normalizeProgram_exists : ∃ p : Program, ∀ query, p.eval query = evaluation query :=
  by
    obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp evaluation_partrec)
    exact ⟨p, fun query => congrFun hp query⟩

noncomputable def normalizeProgram : Program := Classical.choose normalizeProgram_exists

theorem normalizeProgram_eval (q c : Nat) : normalizeProgram.eval (Nat.pair q c) =
    cond (NativeContext.checkCode q c) (Part.some (NativeContext.Normalization.normalizeCode q c)) Part.none := by
  simpa only [normalizeProgram, evaluation, Nat.unpair_pair] using Classical.choose_spec normalizeProgram_exists (Nat.pair q c)

theorem normalizeProgram_domain (q c : Nat) : normalizeProgram.domain (Nat.pair q c) ↔
    NativeContext.checkCode q c = true := by
  rw [Program.domain, normalizeProgram_eval]
  cases h : NativeContext.checkCode q c <;> simp [h]

theorem normalizeProgram_graph (q c output : Nat) : output ∈ normalizeProgram.eval (Nat.pair q c) ↔
    NativeContext.checkCode q c = true ∧ output = NativeContext.Normalization.normalizeCode q c := by
  rw [normalizeProgram_eval]
  cases h : NativeContext.checkCode q c <;> simp [h, Part.mem_some_iff]

theorem normalizeProgram_returns (q c : Nat) (hc : NativeContext.checkCode q c = true) :
    normalizeProgram.eval (Nat.pair q c) = Part.some (NativeContext.Normalization.normalizeCode q c) := by
  simp only [normalizeProgram_eval, hc, Bool.cond_true]

noncomputable def normalizeColumn (q : Nat) : Program := normalizeProgram.column q

theorem normalizeColumn_primrec : Primrec normalizeColumn :=
  Program.column_primrec.comp (Primrec.const normalizeProgram) Primrec.id

theorem normalizeColumn_eval (q c : Nat) : (normalizeColumn q).eval c =
    cond (NativeContext.checkCode q c) (Part.some (NativeContext.Normalization.normalizeCode q c)) Part.none := by
  rw [normalizeColumn, Program.column, Nat.Partrec.Code.eval_curry]
  exact normalizeProgram_eval q c

theorem normalizeColumn_domain (q c : Nat) : (normalizeColumn q).domain c ↔ NativeContext.checkCode q c = true := by
  rw [normalizeColumn, Program.column_domain]
  exact normalizeProgram_domain q c

theorem normalizeColumn_graph (q c output : Nat) : output ∈ (normalizeColumn q).eval c ↔
    NativeContext.checkCode q c = true ∧ output = NativeContext.Normalization.normalizeCode q c := by
  rw [normalizeColumn, Program.column, Nat.Partrec.Code.eval_curry]
  exact normalizeProgram_graph q c output

theorem normalizeColumn_correct (q c output : Nat) (ho : output ∈ (normalizeColumn q).eval c) :
    NativeContext.checkCode q c = true ∧ NativeContext.Comparison.acceptedCode q output = true ∧
      NativeContext.interpretation q output = NativeContext.interpretation q c := by
  obtain ⟨hc, rfl⟩ := (normalizeColumn_graph q c output).mp ho
  have hs := NativeContext.Normalization.normalizeCode_accepted q c hc
  exact ⟨hc, hs.1, hs.2⟩

theorem normalizeColumn_total_original (q c : Nat) (hc : NativeContext.checkCode q c = true) :
    ∃! output, output ∈ (normalizeColumn q).eval c := by
  refine ⟨NativeContext.Normalization.normalizeCode q c,
    (normalizeColumn_graph q c _).mpr ⟨hc, rfl⟩, ?_⟩
  intro output ho
  exact ((normalizeColumn_graph q c output).mp ho).2

def inputEvaluation (query : Nat) : Part Nat :=
  cond (NativeContext.checkCode query.unpair.1 query.unpair.2) (Part.some 0) Part.none

theorem inputEvaluation_partrec : Partrec inputEvaluation :=
  Partrec.cond (NativeContext.checkCode_primrec.comp (Primrec.fst.comp Primrec.unpair)
    (Primrec.snd.comp Primrec.unpair)).to_comp (Computable.const 0).partrec Partrec.none

theorem inputProgram_exists : ∃ p : Program, ∀ query, p.eval query = inputEvaluation query :=
  by
    obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp inputEvaluation_partrec)
    exact ⟨p, fun query => congrFun hp query⟩

noncomputable def inputProgram : Program := Classical.choose inputProgram_exists

theorem inputProgram_domain (q c : Nat) : inputProgram.domain (Nat.pair q c) ↔ NativeContext.checkCode q c = true := by
  rw [Program.domain, inputProgram, Classical.choose_spec inputProgram_exists]
  cases h : NativeContext.checkCode q c <;> simp [inputEvaluation, Nat.unpair_pair, h]

noncomputable def inputColumn (q : Nat) : Program := inputProgram.column q

theorem inputColumn_primrec : Primrec inputColumn :=
  Program.column_primrec.comp (Primrec.const inputProgram) Primrec.id

theorem inputColumn_domain (q c : Nat) : (inputColumn q).domain c ↔ NativeContext.checkCode q c = true := by
  rw [inputColumn, Program.column_domain]
  exact inputProgram_domain q c

def graphRaw (query : Nat) : Bool := NativeContext.Normalization.graph
  query.unpair.1.unpair.1 query.unpair.1.unpair.2 query.unpair.2

theorem graphRaw_primrec : Primrec graphRaw := by
  have h := NativeContext.Normalization.Effective.graph_primrec.comp
    ((Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))).pair
      ((Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))).pair
        (Primrec.snd.comp Primrec.unpair)))
  exact h.of_eq (fun _ => rfl)

def graphEvaluation (query : Nat) : Part Nat := cond (graphRaw query) (Part.some 0) Part.none

theorem graphEvaluation_partrec : Partrec graphEvaluation :=
  Partrec.cond graphRaw_primrec.to_comp (Computable.const 0).partrec Partrec.none

theorem graphProgram_exists : ∃ p : Program, ∀ query, p.eval query = graphEvaluation query :=
  by
    obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp graphEvaluation_partrec)
    exact ⟨p, fun query => congrFun hp query⟩

noncomputable def graphProgram : Program := Classical.choose graphProgram_exists

theorem graphProgram_domain (q c output : Nat) : graphProgram.domain (Nat.pair (Nat.pair q c) output) ↔
    NativeContext.checkCode q c = true ∧ output = NativeContext.Normalization.normalizeCode q c := by
  rw [Program.domain, graphProgram, Classical.choose_spec graphProgram_exists]
  simp only [graphEvaluation, graphRaw, Nat.unpair_pair]
  cases h : NativeContext.Normalization.graph q c output with
  | false =>
    have hn : ¬ (NativeContext.checkCode q c = true ∧ output = NativeContext.Normalization.normalizeCode q c) := by
      intro hs
      have he := (NativeContext.Normalization.graph_exact q c output).mpr hs
      simp only [h, Bool.false_eq_true] at he
    simp [h, hn]
  | true => simp [h, (NativeContext.Normalization.graph_exact q c output).mp h]

noncomputable def graphColumn (q c : Nat) : Program := graphProgram.column (Nat.pair q c)

theorem graphColumn_primrec : Primrec₂ graphColumn :=
  (Program.column_primrec.comp (Primrec.const graphProgram) Primrec₂.natPair).to₂

theorem graphColumn_domain (q c output : Nat) : (graphColumn q c).domain output ↔
    NativeContext.checkCode q c = true ∧ output = NativeContext.Normalization.normalizeCode q c := by
  rw [graphColumn, Program.column_domain]
  exact graphProgram_domain q c output

theorem graphColumn_execution (q c output : Nat) : (graphColumn q c).domain output ↔ output ∈ (normalizeColumn q).eval c :=
  (graphColumn_domain q c output).trans (normalizeColumn_graph q c output).symm

theorem graphColumn_spec (q c output : Nat) (ho : (graphColumn q c).domain output) :
    NativeContext.checkCode q c = true ∧ NativeContext.Comparison.acceptedCode q output = true ∧
      NativeContext.interpretation q output = NativeContext.interpretation q c :=
  normalizeColumn_correct q c output ((graphColumn_execution q c output).mp ho)

theorem graphColumn_unique (q c : Nat) (hc : NativeContext.checkCode q c = true) :
    ∃! output, (graphColumn q c).domain output := by
  refine ⟨NativeContext.Normalization.normalizeCode q c, (graphColumn_domain q c _).mpr ⟨hc, rfl⟩, ?_⟩
  intro output ho
  exact ((graphColumn_domain q c output).mp ho).2

end Alexander313.HereditaryNativeNormalizationProgram
