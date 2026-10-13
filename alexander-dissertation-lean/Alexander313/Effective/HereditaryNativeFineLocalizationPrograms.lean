import Alexander313.Wilken.HereditaryNativeFineLocalization

/-!
# Executing same-epsilon native fine localization Programs

Tag0 executes the original weak-normal literal theta-zero domain including
the base singleton. Tag1 executes the original RAW proper-root domain. The
actual public fine search and finite canonical-node return map produce the
literal native word. Its values satisfy the proved source2.40 order law.

Positive input tests use genuine PR guards. The complete numerical graph runs
the actual Partrec producer and compares the literal answer, including zero;
no PR graph or global search bound is asserted. Every fixed Program column
compiler is PR. Unknown tags reject. No arbitrary-context recoder, independent
normalizer equality or native spelling/support recurrence is assumed. These
source candidates remain uncompiled.
-/

namespace Alexander313.HereditaryNativeFineLocalizationProgram

open Wilken.RelativeTerm.Hereditary

def input (tag s c : Nat) : Bool := cond (tag == 0) (NativeContext.FineLocalization.inputCheck s c)
  (cond (tag == 1) (NativeContext.FineLocalization.rawInputCheck s c) false)

theorem input_primrec : Primrec (fun p : Nat × (Nat × Nat) => input p.1 p.2.1 p.2.2) :=
  (Primrec.beq.comp Primrec.fst (Primrec.const 0)).cond
    (NativeContext.FineLocalization.inputCheck_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
    ((Primrec.beq.comp Primrec.fst (Primrec.const 1)).cond
      (NativeContext.FineLocalization.rawInputCheck_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
      (Primrec.const false))

theorem input_exact (tag s c : Nat) : input tag s c = true ↔
    (tag = 0 ∧ NativeContext.FineLocalization.inputCheck s c = true) ∨
      (tag = 1 ∧ NativeContext.FineLocalization.rawInputCheck s c = true) := by
  by_cases h0 : tag = 0
  · subst tag; simp [input]
  · by_cases h1 : tag = 1 <;> simp [input, h0, h1]

def evaluation (query : Nat) : Part Nat := cond (query.unpair.1 == 0)
  (NativeContext.FineLocalization.fineLocalization query.unpair.2.unpair.1 query.unpair.2.unpair.2)
    (cond (query.unpair.1 == 1)
      (NativeContext.FineLocalization.rawFineLocalization query.unpair.2.unpair.1 query.unpair.2.unpair.2) Part.none)

theorem evaluation_partrec : Partrec evaluation := by
  have ht := Primrec.fst.comp Primrec.unpair
  have hp := Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)
  have hs := Primrec.fst.comp hp
  have hc := Primrec.snd.comp hp
  exact Partrec.cond (Primrec.beq.comp ht (Primrec.const 0)).to_comp
    (NativeContext.FineLocalization.fineLocalization_partrec.comp hs.to_comp hc.to_comp)
    (Partrec.cond (Primrec.beq.comp ht (Primrec.const 1)).to_comp
      (NativeContext.FineLocalization.rawFineLocalization_partrec.comp hs.to_comp hc.to_comp) Partrec.none)

theorem program_exists : ∃ p : Program, ∀ query, p.eval query = evaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp evaluation_partrec)

noncomputable def program : Program := Classical.choose program_exists

theorem program_eval (tag s c : Nat) : program.eval (Nat.pair tag (Nat.pair s c)) =
    cond (tag == 0) (NativeContext.FineLocalization.fineLocalization s c)
      (cond (tag == 1) (NativeContext.FineLocalization.rawFineLocalization s c) Part.none) := by
  simpa only [evaluation, Nat.unpair_pair] using
    Classical.choose_spec program_exists (Nat.pair tag (Nat.pair s c))

theorem program_domain (tag s c : Nat) : program.domain (Nat.pair tag (Nat.pair s c)) ↔ input tag s c = true := by
  rw [Program.domain, program_eval]
  by_cases h0 : tag = 0
  · subst tag; simp [input, NativeContext.FineLocalization.fineLocalization_domain]
  · by_cases h1 : tag = 1 <;> simp [input, h0, h1, NativeContext.FineLocalization.rawFineLocalization_domain, Part.not_none_dom]

noncomputable def sourceColumn (tag s : Nat) : Program := (program.column tag).column s

theorem sourceColumn_primrec : Primrec₂ sourceColumn :=
  (Program.column_primrec.comp (Program.column_primrec.comp (Primrec.const program) Primrec.fst) Primrec.snd).to₂

theorem sourceColumn_eval (tag s c : Nat) : (sourceColumn tag s).eval c =
    cond (tag == 0) (NativeContext.FineLocalization.fineLocalization s c)
      (cond (tag == 1) (NativeContext.FineLocalization.rawFineLocalization s c) Part.none) := by
  simp only [sourceColumn, Nat.Partrec.Code.eval_curry, program_eval]

theorem sourceColumn_domain (tag s c : Nat) : (sourceColumn tag s).domain c ↔ input tag s c = true := by
  rw [sourceColumn, Program.column_domain, Program.column_domain]
  exact program_domain tag s c

theorem normalColumn_domain (s c : Nat) : (sourceColumn 0 s).domain c ↔
    ∃ a : Wilken.RelativeTerm Nat, c = (.theta 0 a).code ∧
      NativeContext.check (NativePublicBridge.contextCode s) (.theta 0 a) = true ∧
      NativeContext.Comparison.Normal (NativePublicBridge.contextCode s) (.theta 0 a) := by
  simp [sourceColumn_domain, input, NativeContext.FineLocalization.inputCheck_exact]

theorem rawColumn_domain (s c : Nat) : (sourceColumn 1 s).domain c ↔
    (∃ a : Wilken.RelativeTerm Nat, c = (.theta 0 a).code ∧ NativeContext.check (NativePublicBridge.contextCode s) (.theta 0 a) = true) ∧
      NativeContext.base (NativePublicBridge.contextCode s) < NativeContext.interpretation (NativePublicBridge.contextCode s) c := by
  simp [sourceColumn_domain, input, NativeContext.FineLocalization.rawInputCheck_exact]

theorem sourceColumn_source (tag s c output : Nat) (ho : output ∈ (sourceColumn tag s).eval c) :
    input tag s c = true ∧ NativeContext.FineLocalization.OutputSpec s
      (if tag = 0 then NativeContext.FineLocalization.publicCode s c else NativeContext.FineLocalization.rawPublicCode s c) output := by
  rw [sourceColumn_eval] at ho
  by_cases h0 : tag = 0
  · subst tag
    have hs := NativeContext.FineLocalization.fineLocalization_source s c output (by simpa using ho)
    simpa [input] using hs
  · by_cases h1 : tag = 1
    · subst tag
      have hs := NativeContext.FineLocalization.rawFineLocalization_source s c output (by simpa using ho)
      simpa [input] using hs
    · simp [h0, h1, Part.notMem_none] at ho

theorem sourceColumn_original (tag s c output : Nat) (ho : output ∈ (sourceColumn tag s).eval c) :
    ∀ d ∈ NativeContext.FineLocalization.decodedWord output,
      NativeContext.Comparison.acceptedCode (NativePublicBridge.contextCode s) d = true ∧
        NativeContext.lowCheckCode (NativePublicBridge.contextCode s) d = true :=
  (sourceColumn_source tag s c output ho).2.nodes

theorem sourceColumn_strict (tag s c output : Nat) (ho : output ∈ (sourceColumn tag s).eval c) :
    (NativeContext.FineLocalization.outputValues s output).Pairwise (· < ·) :=
  (sourceColumn_source tag s c output ho).2.strict

theorem sourceColumn_endpoints (tag s c output : Nat) (ho : output ∈ (sourceColumn tag s).eval c) :
    ∃ middle, NativeContext.FineLocalization.outputValues s output = NativeContext.base (NativePublicBridge.contextCode s) :: middle ∧
      ∃ pre, NativeContext.FineLocalization.outputValues s output = pre ++ [NativeContext.interpretation (NativePublicBridge.contextCode s) c] := by
  have hs := sourceColumn_source tag s c output ho
  have he := hs.2.endpoints
  rcases (input_exact tag s c).mp hs.1 with ⟨rfl, hc⟩ | ⟨rfl, hc⟩
  · simpa only [if_pos rfl, NativeContext.FineLocalization.publicCode_value s c hc,
      NativePublicBridge.contextCode_value] using he
  · simpa only [show (1 : Nat) ≠ 0 by decide, if_false, NativeContext.FineLocalization.rawPublicCode_value s c hc,
      NativePublicBridge.contextCode_value] using he

theorem sourceColumn_unique (tag s c : Nat) (hc : input tag s c = true) : ∃! output, output ∈ (sourceColumn tag s).eval c := by
  obtain ⟨output, ho⟩ := Part.dom_iff_mem.mp ((sourceColumn_domain tag s c).mpr hc)
  exact ⟨output, ho, fun other ht => Part.mem_unique ht ho⟩

theorem normalColumn_invariant (s c d output second : Nat)
    (ho : output ∈ (sourceColumn 0 s).eval c) (hv : second ∈ (sourceColumn 0 s).eval d)
    (he : NativeContext.interpretation (NativePublicBridge.contextCode s) c = NativeContext.interpretation (NativePublicBridge.contextCode s) d) : output = second :=
  NativeContext.FineLocalization.fineLocalization_invariant s c d output second
    (by simpa [sourceColumn_eval] using ho) (by simpa [sourceColumn_eval] using hv) he

theorem rawColumn_invariant (s c d output second : Nat)
    (ho : output ∈ (sourceColumn 1 s).eval c) (hv : second ∈ (sourceColumn 1 s).eval d)
    (he : NativeContext.interpretation (NativePublicBridge.contextCode s) c = NativeContext.interpretation (NativePublicBridge.contextCode s) d) : output = second :=
  NativeContext.FineLocalization.rawFineLocalization_invariant s c d output second
    (by simpa [sourceColumn_eval] using ho) (by simpa [sourceColumn_eval] using hv) he

theorem normalColumn_lex_iff (s c d output second : Nat)
    (ho : output ∈ (sourceColumn 0 s).eval c) (hv : second ∈ (sourceColumn 0 s).eval d) :
    List.Lex (· < ·) (NativeContext.FineLocalization.outputValues s output) (NativeContext.FineLocalization.outputValues s second) ↔
      NativeContext.interpretation (NativePublicBridge.contextCode s) c < NativeContext.interpretation (NativePublicBridge.contextCode s) d :=
  NativeContext.FineLocalization.fineLocalization_lex_iff s c d output second
    (by simpa [sourceColumn_eval] using ho) (by simpa [sourceColumn_eval] using hv)

theorem rawColumn_lex_iff (s c d output second : Nat)
    (ho : output ∈ (sourceColumn 1 s).eval c) (hv : second ∈ (sourceColumn 1 s).eval d) :
    List.Lex (· < ·) (NativeContext.FineLocalization.outputValues s output) (NativeContext.FineLocalization.outputValues s second) ↔
      NativeContext.interpretation (NativePublicBridge.contextCode s) c < NativeContext.interpretation (NativePublicBridge.contextCode s) d :=
  NativeContext.FineLocalization.rawFineLocalization_lex_iff s c d output second
    (by simpa [sourceColumn_eval] using ho) (by simpa [sourceColumn_eval] using hv)

theorem normalColumn_base (s c : Nat) (hc : NativeContext.FineLocalization.inputCheck s c = true)
    (hb : NativeContext.interpretation (NativePublicBridge.contextCode s) c = NativeContext.base (NativePublicBridge.contextCode s)) :
    Encodable.encode [NativeContext.FineLocalization.nodeCode s (NativeContext.FineLocalization.publicCode s c)] ∈ (sourceColumn 0 s).eval c := by
  simpa [sourceColumn_eval] using NativeContext.FineLocalization.fineLocalization_base s c hc hb

def inputEvaluation (query : Nat) : Part Nat := cond
  (input query.unpair.1 query.unpair.2.unpair.1 query.unpair.2.unpair.2) (Part.some 1) Part.none

theorem inputEvaluation_partrec : Partrec inputEvaluation := by
  have hp := (Primrec.fst.comp Primrec.unpair).pair (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  exact Partrec.cond (input_primrec.comp hp).to_comp (Computable.const 1).partrec Partrec.none

theorem inputProgram_exists : ∃ p : Program, ∀ query, p.eval query = inputEvaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp inputEvaluation_partrec)

noncomputable def inputProgram : Program := Classical.choose inputProgram_exists

theorem inputProgram_domain (tag s c : Nat) : inputProgram.domain (Nat.pair tag (Nat.pair s c)) ↔ input tag s c = true := by
  rw [Program.domain, Classical.choose_spec inputProgram_exists]
  simp only [inputEvaluation, Nat.unpair_pair]
  cases hi : input tag s c <;> simp [hi]

noncomputable def inputColumn (tag s : Nat) : Program := (inputProgram.column tag).column s

theorem inputColumn_primrec : Primrec₂ inputColumn :=
  (Program.column_primrec.comp (Program.column_primrec.comp (Primrec.const inputProgram) Primrec.fst) Primrec.snd).to₂

theorem inputColumn_domain (tag s c : Nat) : (inputColumn tag s).domain c ↔ input tag s c = true := by
  rw [inputColumn, Program.column_domain, Program.column_domain]
  exact inputProgram_domain tag s c

/-- Complete literal numerical graph: execute the search and test its answer.
The queried natural is unrestricted; zero is never discarded by tagging. -/
def graphEvaluation (query : Nat) : Part Nat := (evaluation query.unpair.1).bind
  (fun answer => cond (query.unpair.2 == answer) (Part.some 1) Part.none)

theorem graphEvaluation_partrec : Partrec graphEvaluation := by
  have hf := evaluation_partrec.comp (Primrec.fst.comp Primrec.unpair).to_comp
  have hg : Partrec₂ (fun query answer : Nat => cond (query.unpair.2 == answer) (Part.some 1) Part.none) :=
    (Partrec.cond (Primrec.beq.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)) Primrec.snd).to_comp
      (Computable.const 1).partrec Partrec.none).to₂
  exact hf.bind hg

theorem graphEvaluation_domain (query : Nat) : (graphEvaluation query).Dom ↔ query.unpair.2 ∈ evaluation query.unpair.1 := by
  constructor
  · intro h
    obtain ⟨out, ho⟩ := Part.dom_iff_mem.mp h
    obtain ⟨answer, ha, ht⟩ := Part.mem_bind_iff.mp ho
    cases he : query.unpair.2 == answer with
    | false => simp only [he, Bool.cond_false, Part.notMem_none] at ht
    | true => exact (beq_iff_eq.mp he).symm ▸ ha
  · intro ho
    exact Part.dom_iff_mem.mpr ⟨1, Part.mem_bind ho (by simp)⟩

theorem graphProgram_exists : ∃ p : Program, ∀ query, p.eval query = graphEvaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp graphEvaluation_partrec)

noncomputable def graphProgram : Program := Classical.choose graphProgram_exists

theorem graphProgram_domain (tag s c output : Nat) :
    graphProgram.domain (Nat.pair (Nat.pair tag (Nat.pair s c)) output) ↔ output ∈ (sourceColumn tag s).eval c := by
  rw [Program.domain, Classical.choose_spec graphProgram_exists, graphEvaluation_domain]
  simp only [sourceColumn, Nat.Partrec.Code.eval_curry, Classical.choose_spec program_exists, Nat.unpair_pair]

noncomputable def graphColumn (tag s c : Nat) : Program := graphProgram.column (Nat.pair tag (Nat.pair s c))

theorem graphColumn_primrec : Primrec (fun p : Nat × (Nat × Nat) => graphColumn p.1 p.2.1 p.2.2) :=
  Program.column_primrec.comp (Primrec.const graphProgram)
    (Primrec₂.natPair.comp Primrec.fst (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)))

theorem graphColumn_domain (tag s c output : Nat) : (graphColumn tag s c).domain output ↔ output ∈ (sourceColumn tag s).eval c := by
  rw [graphColumn, Program.column_domain, graphProgram_domain]

theorem graphColumn_unique (tag s c : Nat) (hc : input tag s c = true) : ∃! output, (graphColumn tag s c).domain output := by
  simpa only [graphColumn_domain] using sourceColumn_unique tag s c hc

end Alexander313.HereditaryNativeFineLocalizationProgram
