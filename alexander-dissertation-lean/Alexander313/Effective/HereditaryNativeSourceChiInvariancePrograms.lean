import Alexander313.Wilken.HereditaryNativeSourceChiInvariance

/-!
# Executing same-positive-public return-indicator Programs

The real native-to-public return is followed by the actual PUBLIC normalizer
and source chi. The derived same-q invariant proves agreement with the
independently executed native raw chi. Its original native coded epsilon,
payload and full-sort check is the exact source Program domain.

The actual finite adapter, original input, both numerical answers and the
complete graph are PR. Source, total decision and positive literal graph
Programs and fixed-column compilers are constructed from those kernels.
No normalizer spelling identity, return oracle or cross-base Lemma 3.4 is
assumed. Same-q mathematical invariance itself has the full original coded
epsilon scope; this return operation uses contextCode s. Uncompiled candidates.
-/

namespace Alexander313.HereditaryNativeSourceChiInvarianceProgram

open Wilken.RelativeTerm.Hereditary
open NativeContext.SourceChi.Invariance

def input (s c : Nat) : Bool := NativeContext.checkCode (NativePublicBridge.contextCode s) c

theorem input_primrec : Primrec₂ input :=
  (NativeContext.checkCode_primrec.comp (NativePublicBridge.contextCode_primrec.comp Primrec.fst) Primrec.snd).to₂

def answer (s c : Nat) : Nat := cond (returnChi s c) 1 0

theorem answer_primrec : Primrec₂ answer :=
  (returnChi_primrec.cond (Primrec.const 1) (Primrec.const 0)).to₂

def rawInput (query : Nat) : Bool := input query.unpair.1 query.unpair.2

def rawAnswer (query : Nat) : Nat := answer query.unpair.1 query.unpair.2

theorem rawInput_primrec : Primrec rawInput := input_primrec.comp
  (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)

theorem rawAnswer_primrec : Primrec rawAnswer := answer_primrec.comp
  (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)

def valueEvaluation (query : Nat) : Part Nat := cond (rawInput query) (Part.some (rawAnswer query)) Part.none

theorem valueEvaluation_partrec : Partrec valueEvaluation :=
  Partrec.cond rawInput_primrec.to_comp rawAnswer_primrec.to_comp.partrec Partrec.none

theorem valueProgram_exists : ∃ p : Program, ∀ query, p.eval query = valueEvaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp valueEvaluation_partrec)

noncomputable def valueProgram : Program := Classical.choose valueProgram_exists

theorem valueProgram_eval (s c : Nat) : valueProgram.eval (Nat.pair s c) =
    cond (input s c) (Part.some (answer s c)) Part.none := by
  simpa only [valueEvaluation, rawInput, rawAnswer, Nat.unpair_pair] using
    Classical.choose_spec valueProgram_exists (Nat.pair s c)

theorem valueProgram_domain (s c : Nat) : valueProgram.domain (Nat.pair s c) ↔ input s c = true := by
  rw [Program.domain, valueProgram_eval]
  cases h : input s c <;> simp [h]

theorem valueProgram_graph (s c output : Nat) : output ∈ valueProgram.eval (Nat.pair s c) ↔
    input s c = true ∧ output = answer s c := by
  rw [valueProgram_eval]
  cases h : input s c <;> simp [h]

noncomputable def valueColumn (s : Nat) : Program := valueProgram.column s

theorem valueColumn_primrec : Primrec valueColumn :=
  Program.column_primrec.comp (Primrec.const valueProgram) Primrec.id

theorem valueColumn_eval (s c : Nat) : (valueColumn s).eval c =
    cond (input s c) (Part.some (answer s c)) Part.none := by
  simp only [valueColumn, Nat.Partrec.Code.eval_curry, valueProgram_eval]

theorem valueColumn_domain (s c : Nat) : (valueColumn s).domain c ↔
    NativeContext.checkCode (NativePublicBridge.contextCode s) c = true := by
  rw [valueColumn, Program.column_domain, valueProgram_domain]
  rfl

/-- Literal computation returns public chi AFTER actual return and public
normalization. Its agreement with native raw chi is a proved source result. -/
theorem valueColumn_return_source (s c : Nat) (hc : input s c = true) :
    (valueColumn s).eval c = Part.some
      (cond (SourceChi.chiCode (s + 1) (NativePublicReturn.rawReturnCode s c)) 1 0) := by
  simp only [valueColumn_eval, hc, Bool.cond_true, answer, returnChi,
    show NativeContext.checkCode (NativePublicBridge.contextCode s) c = true from hc, Bool.true_and]

theorem valueColumn_native_source (s c : Nat) (hc : input s c = true) :
    (valueColumn s).eval c = Part.some
      (cond (NativeContext.SourceChi.rawChiCode (NativePublicBridge.contextCode s) c) 1 0) := by
  rw [valueColumn_eval, hc]
  simp only [Bool.cond_true, answer, returnChi_agreement]

/-- Two originally admitted equal-valued raw inputs give equal actual
return-indicator outputs, even when their independent normal spellings differ. -/
theorem valueColumn_invariant (s c d : Nat) (hc : input s c = true) (hd : input s d = true)
    (hv : NativeContext.interpretation (NativePublicBridge.contextCode s) c =
      NativeContext.interpretation (NativePublicBridge.contextCode s) d) :
    (valueColumn s).eval c = (valueColumn s).eval d := by
  rw [valueColumn_eval, valueColumn_eval, hc, hd]
  simp only [Bool.cond_true, answer, returnChi_invariant s c d hc hd hv]

def decisionEvaluation (query : Nat) : Part Nat := Part.some (rawAnswer query)

theorem decisionEvaluation_partrec : Partrec decisionEvaluation := rawAnswer_primrec.to_comp.partrec

theorem decisionProgram_exists : ∃ p : Program, ∀ query, p.eval query = decisionEvaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp decisionEvaluation_partrec)

noncomputable def decisionProgram : Program := Classical.choose decisionProgram_exists

theorem decisionProgram_eval (s c : Nat) : decisionProgram.eval (Nat.pair s c) = Part.some (answer s c) := by
  simpa only [decisionEvaluation, rawAnswer, Nat.unpair_pair] using
    Classical.choose_spec decisionProgram_exists (Nat.pair s c)

theorem decisionProgram_total (query : Nat) : decisionProgram.domain query := by
  rw [Program.domain, Classical.choose_spec decisionProgram_exists]
  exact Part.some_dom _

theorem decisionProgram_positive (s c : Nat) : 1 ∈ decisionProgram.eval (Nat.pair s c) ↔
    NativeContext.SourceChi.rawChiCode (NativePublicBridge.contextCode s) c = true := by
  rw [decisionProgram_eval, ← returnChi_agreement]
  cases h : returnChi s c <;> simp [answer, h]

noncomputable def decisionColumn (s : Nat) : Program := decisionProgram.column s

theorem decisionColumn_primrec : Primrec decisionColumn :=
  Program.column_primrec.comp (Primrec.const decisionProgram) Primrec.id

theorem decisionColumn_eval (s c : Nat) : (decisionColumn s).eval c = Part.some (answer s c) := by
  simp only [decisionColumn, Nat.Partrec.Code.eval_curry, decisionProgram_eval]

def graph (s c output : Nat) : Bool := input s c && (output == answer s c)

theorem graph_primrec : Primrec (fun p : (Nat × Nat) × Nat => graph p.1.1 p.1.2 p.2) :=
  Primrec.and.comp (input_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst))
    (Primrec.beq.comp Primrec.snd (answer_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)))

theorem graph_exact (s c output : Nat) : graph s c output = true ↔ input s c = true ∧ output = answer s c := by
  simp only [graph, Bool.and_eq_true, beq_iff_eq]

theorem graph_unique (s c : Nat) (hc : input s c = true) : ∃! output, graph s c output = true := by
  refine ⟨answer s c, (graph_exact s c _).mpr ⟨hc, rfl⟩, ?_⟩
  intro output ho
  exact ((graph_exact s c output).mp ho).2

def graphRaw (query : Nat) : Bool := graph query.unpair.1.unpair.1 query.unpair.1.unpair.2 query.unpair.2

theorem graphRaw_primrec : Primrec graphRaw := graph_primrec.comp
  ((Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)).pair (Primrec.snd.comp Primrec.unpair))

def graphEvaluation (query : Nat) : Part Nat := cond (graphRaw query) (Part.some 1) Part.none

theorem graphEvaluation_partrec : Partrec graphEvaluation :=
  Partrec.cond graphRaw_primrec.to_comp (Computable.const 1).partrec Partrec.none

theorem graphProgram_exists : ∃ p : Program, ∀ query, p.eval query = graphEvaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp graphEvaluation_partrec)

noncomputable def graphProgram : Program := Classical.choose graphProgram_exists

theorem graphProgram_domain (s c output : Nat) : graphProgram.domain (Nat.pair (Nat.pair s c) output) ↔
    input s c = true ∧ output = answer s c := by
  rw [Program.domain, Classical.choose_spec graphProgram_exists]
  change (cond (graph s c output) (Part.some 1) Part.none).Dom ↔ _
  have he : (cond (graph s c output) (Part.some 1) Part.none).Dom ↔ graph s c output = true := by
    cases h : graph s c output <;> simp [h, Part.some, Part.none]
  exact he.trans (graph_exact s c output)

noncomputable def graphColumn (s c : Nat) : Program := graphProgram.column (Nat.pair s c)

theorem graphColumn_primrec : Primrec₂ graphColumn :=
  (Program.column_primrec.comp (Primrec.const graphProgram) Primrec₂.natPair).to₂

theorem graphColumn_domain (s c output : Nat) : (graphColumn s c).domain output ↔
    NativeContext.checkCode (NativePublicBridge.contextCode s) c = true ∧ output = answer s c := by
  rw [graphColumn, Program.column_domain, graphProgram_domain]
  rfl

theorem graphColumn_matches_value (s c output : Nat) : (graphColumn s c).domain output ↔
    output ∈ (valueColumn s).eval c := by
  rw [graphColumn_domain, valueColumn_eval]
  change (input s c = true ∧ output = answer s c) ↔
    output ∈ cond (input s c) (Part.some (answer s c)) Part.none
  cases h : input s c <;> simp [h]

end Alexander313.HereditaryNativeSourceChiInvarianceProgram
