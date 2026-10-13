import Alexander313.Wilken.HereditaryLocalization

/-!
# Executing full-depth source localization Programs

The actual guarded Program computes the finite greatest-argument walk over
full P_0 support and emits its complete canonical path. It halts exactly on
literal originally admitted normal theta-zero roots. Positive input and output
Programs test the actual PR guard and complete literal computed graph. Column
compilers specialize these genuine fixed kernels. This does not assume native
spelling uniqueness, path invariance under arbitrary alternate spellings, or
the unconstructed fixed-point refinements. All terms remain uncompiled.
-/

namespace Alexander313.HereditaryLocalizationProgram

open Wilken.RelativeTerm.Hereditary

def evaluation (query : Nat) : Part Nat := Localization.localization query.unpair.1 query.unpair.2

theorem evaluation_partrec : Partrec evaluation :=
  Localization.localization_partrec.comp (Primrec.fst.comp Primrec.unpair).to_comp
    (Primrec.snd.comp Primrec.unpair).to_comp

theorem operationProgram_exists : ∃ p : Program, ∀ query, p.eval query = evaluation query := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp evaluation_partrec)
  exact ⟨p, fun query => congrFun hp query⟩

noncomputable def operationProgram : Program := Classical.choose operationProgram_exists

theorem operationProgram_eval (r c : Nat) : operationProgram.eval (Nat.pair r c) = Localization.localization r c := by
  simpa only [operationProgram, evaluation, Nat.unpair_pair] using Classical.choose_spec operationProgram_exists (Nat.pair r c)

theorem operationProgram_domain (r c : Nat) : operationProgram.domain (Nat.pair r c) ↔ Localization.Node r c := by
  simp only [Program.domain, operationProgram_eval, Localization.localization_domain]

noncomputable def operationColumn (r : Nat) : Program := operationProgram.column r

theorem operationColumn_primrec : Primrec operationColumn :=
  Program.column_primrec.comp (Primrec.const operationProgram) Primrec.id

theorem operationColumn_eval (r c : Nat) : (operationColumn r).eval c = Localization.localization r c := by
  simp only [operationColumn, Program.column, Nat.Partrec.Code.eval_curry, operationProgram_eval]

theorem operationColumn_domain (r c : Nat) : (operationColumn r).domain c ↔ Localization.Node r c := by
  rw [operationColumn, Program.column_domain]
  exact operationProgram_domain r c

theorem operationProgram_returns (r c : Nat) (hc : Localization.inputCheck r c = true) :
    Encodable.encode (Localization.word r c) ∈ operationProgram.eval (Nat.pair r c) := by
  rw [operationProgram_eval]
  exact Localization.localization_returns r c hc

theorem operationProgram_unique (r c : Nat) (hc : Localization.inputCheck r c = true) :
    ∃! output, output ∈ operationProgram.eval (Nat.pair r c) := by
  rw [operationProgram_eval]
  exact Localization.localization_unique r c hc

theorem operationProgram_graph_iff (r c output : Nat) : output ∈ operationProgram.eval (Nat.pair r c) ↔
    Localization.Node r c ∧ output = Encodable.encode (Localization.word r c) := by
  rw [operationProgram_eval, Localization.localization_graph_iff, Localization.graph_exact]

theorem operationProgram_word (r c : Nat) (rs : List Nat)
    (hr : Encodable.encode rs ∈ operationProgram.eval (Nat.pair r c)) :
    rs = Localization.word r c ∧ (∀ d ∈ rs, Canonical.check d = true) ∧
      ((rs.map unionInterpretation).Pairwise (· < ·)) ∧ rs.length ≤ (Localization.support c).length + 1 := by
  rw [operationProgram_eval] at hr
  exact Localization.localization_word r c rs hr

theorem operationProgram_end (r c : Nat) (rs : List Nat)
    (hr : Encodable.encode rs ∈ operationProgram.eval (Nat.pair r c)) :
    unionInterpretation (Localization.endpoint rs) = interpretation r c := by
  have hs := (operationProgram_graph_iff r c _).mp hr
  have he : rs = Localization.word r c := Encodable.encode_injective hs.2
  rw [he]
  exact Localization.word_end r c ((Localization.inputCheck_exact r c).mpr hs.1)

theorem operationProgram_source (r c output : Nat) (hc : output ∈ operationProgram.eval (Nat.pair r c)) :
    ∃ path : List Nat, Localization.SourcePath r (Localization.support c) path ∧
      Localization.value r (Localization.endpoint path) = Localization.value r c ∧
      output = Encodable.encode (path.map (Localization.emit r)) ∧
      (∀ d ∈ path, Localization.Node r d) ∧ ((path.map (Localization.value r)).Pairwise (· < ·)) := by
  rw [operationProgram_eval] at hc
  exact Localization.localization_source r c output hc

def inputRaw (query : Nat) : Bool := Localization.inputCheck query.unpair.1 query.unpair.2

theorem inputRaw_primrec : Primrec inputRaw :=
  Localization.inputCheck_primrec.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)

def inputEvaluation (query : Nat) : Part Nat := cond (inputRaw query) (Part.some 0) Part.none

theorem inputEvaluation_partrec : Partrec inputEvaluation :=
  Partrec.cond inputRaw_primrec.to_comp (Computable.const 0).partrec Partrec.none

theorem inputProgram_exists : ∃ p : Program, ∀ query, p.eval query = inputEvaluation query := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp inputEvaluation_partrec)
  exact ⟨p, fun query => congrFun hp query⟩

noncomputable def inputProgram : Program := Classical.choose inputProgram_exists

theorem inputProgram_domain (r c : Nat) : inputProgram.domain (Nat.pair r c) ↔ Localization.Node r c := by
  rw [Program.domain, inputProgram, Classical.choose_spec inputProgram_exists]
  cases h : Localization.inputCheck r c <;>
    simp [inputEvaluation, inputRaw, Nat.unpair_pair, h, ← Localization.inputCheck_exact]

noncomputable def inputColumn (r : Nat) : Program := inputProgram.column r

theorem inputColumn_primrec : Primrec inputColumn :=
  Program.column_primrec.comp (Primrec.const inputProgram) Primrec.id

theorem inputColumn_domain (r c : Nat) : (inputColumn r).domain c ↔ Localization.Node r c := by
  rw [inputColumn, Program.column_domain]
  exact inputProgram_domain r c

def graphRaw (query : Nat) : Bool := Localization.graph query.unpair.1.unpair.1 query.unpair.1.unpair.2 query.unpair.2

theorem graphRaw_primrec : Primrec graphRaw :=
  Localization.graph_primrec.comp ((Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)).pair
    (Primrec.snd.comp Primrec.unpair))

def graphEvaluation (query : Nat) : Part Nat := cond (graphRaw query) (Part.some 0) Part.none

theorem graphEvaluation_partrec : Partrec graphEvaluation :=
  Partrec.cond graphRaw_primrec.to_comp (Computable.const 0).partrec Partrec.none

theorem graphProgram_exists : ∃ p : Program, ∀ query, p.eval query = graphEvaluation query := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp graphEvaluation_partrec)
  exact ⟨p, fun query => congrFun hp query⟩

noncomputable def graphProgram : Program := Classical.choose graphProgram_exists

theorem graphProgram_domain (r c output : Nat) : graphProgram.domain (Nat.pair (Nat.pair r c) output) ↔
    Localization.Node r c ∧ output = Encodable.encode (Localization.word r c) := by
  rw [Program.domain, graphProgram, Classical.choose_spec graphProgram_exists, ← Localization.graph_exact]
  cases h : Localization.graph r c output <;>
    simp [graphEvaluation, graphRaw, Nat.unpair_pair, h]

noncomputable def graphColumn (r c : Nat) : Program := graphProgram.column (Nat.pair r c)

theorem graphColumn_primrec : Primrec₂ graphColumn :=
  (Program.column_primrec.comp (Primrec.const graphProgram) Primrec₂.natPair).to₂

theorem graphColumn_domain (r c output : Nat) : (graphColumn r c).domain output ↔
    Localization.Node r c ∧ output = Encodable.encode (Localization.word r c) := by
  rw [graphColumn, Program.column_domain]
  exact graphProgram_domain r c output

theorem graphColumn_execution (r c output : Nat) : (graphColumn r c).domain output ↔
    output ∈ operationProgram.eval (Nat.pair r c) :=
  (graphColumn_domain r c output).trans (operationProgram_graph_iff r c output).symm

theorem graphColumn_unique (r c : Nat) (hc : Localization.inputCheck r c = true) :
    ∃! output, (graphColumn r c).domain output := by
  obtain ⟨output, hout, hu⟩ := operationProgram_unique r c hc
  exact ⟨output, (graphColumn_execution r c output).mpr hout,
    fun d hd => hu d ((graphColumn_execution r c d).mp hd)⟩

end Alexander313.HereditaryLocalizationProgram
