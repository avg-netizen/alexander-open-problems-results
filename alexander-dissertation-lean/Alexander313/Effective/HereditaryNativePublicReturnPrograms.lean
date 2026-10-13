import Alexander313.Wilken.HereditaryNativePublicReturn

/-!
# Exact Programs for the genuine same-epsilon native/public return

Tags 0 and 1 return original weak-normal and original raw native inputs.
Tags 2 and 3 retain the additional ORIGINAL native low guard. The actual
finite payload converter, mapParameters and public normalizer are PR; whole
outputs are checked public terms at level s+1. Low outputs additionally admit
the real original public union tag. Unknown tags reject. Numerical graphs
specify the literal executing output, including zero, not all equal-valued
public spellings. Programs and their compiler columns are constructed from
these finite kernels, with no recoding/effectivity oracle. Uncompiled.
-/

namespace Alexander313.HereditaryNativePublicReturnProgram

open Wilken.RelativeTerm.Hereditary
open NativePublicBridge (contextCode contextCode_primrec)

def input (tag s c : Nat) : Bool :=
  cond (tag == 0) (NativeContext.Comparison.acceptedCode (contextCode s) c)
    (cond (tag == 1) (NativeContext.checkCode (contextCode s) c)
      (cond (tag == 2) (NativeContext.Comparison.acceptedCode (contextCode s) c &&
        NativeContext.lowCheckCode (contextCode s) c)
        (cond (tag == 3) (NativeContext.lowCheckCode (contextCode s) c) false)))

theorem input_primrec : Primrec (fun p : Nat × (Nat × Nat) => input p.1 p.2.1 p.2.2) := by
  have ht (k : Nat) := Primrec.beq.comp Primrec.fst (Primrec.const k)
  have hq := contextCode_primrec.comp (Primrec.fst.comp Primrec.snd)
  have hc := Primrec.snd.comp Primrec.snd
  have hn := NativeContext.Comparison.acceptedCode_primrec.comp hq hc
  have hr := NativeContext.checkCode_primrec.comp hq hc
  have hl := NativeContext.lowCheckCode_primrec.comp hq hc
  exact (ht 0).cond hn ((ht 1).cond hr ((ht 2).cond (Primrec.and.comp hn hl)
    ((ht 3).cond hl (Primrec.const false))))

theorem input_exact (tag s c : Nat) : input tag s c = true ↔
    (tag = 0 ∧ NativeContext.Comparison.acceptedCode (contextCode s) c = true) ∨
    (tag = 1 ∧ NativeContext.checkCode (contextCode s) c = true) ∨
    (tag = 2 ∧ NativeContext.Comparison.acceptedCode (contextCode s) c = true ∧
      NativeContext.lowCheckCode (contextCode s) c = true) ∨
    (tag = 3 ∧ NativeContext.lowCheckCode (contextCode s) c = true) := by
  by_cases h0 : tag = 0
  · subst tag; simp [input]
  · by_cases h1 : tag = 1
    · subst tag; simp [input]
    · by_cases h2 : tag = 2
      · subst tag; simp [input]
      · by_cases h3 : tag = 3 <;> simp [input, h0, h1, h2, h3]

def answer (tag s c : Nat) : Nat := cond ((tag == 1) || (tag == 3))
  (NativePublicReturn.rawReturnCode s c) (NativePublicReturn.returnedCode s c)

theorem answer_primrec : Primrec (fun p : Nat × (Nat × Nat) => answer p.1 p.2.1 p.2.2) := by
  have h := Primrec.or.comp (Primrec.beq.comp Primrec.fst (Primrec.const 1))
    (Primrec.beq.comp Primrec.fst (Primrec.const 3))
  exact h.cond (NativePublicReturn.rawReturnCode_primrec.comp (Primrec.fst.comp Primrec.snd)
    (Primrec.snd.comp Primrec.snd))
    (NativePublicReturn.returnedCode_primrec.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd))

theorem answer_spec (tag s c : Nat) (hc : input tag s c = true) :
    Theta.acceptedCode (s + 1) (answer tag s c) = true ∧
      interpretation (s + 1) (answer tag s c) = NativeContext.interpretation (contextCode s) c := by
  rcases (input_exact tag s c).mp hc with ⟨rfl, hc⟩ | ⟨rfl, hc⟩ | ⟨rfl, hc, hl⟩ | ⟨rfl, hl⟩
  · simpa [answer] using NativePublicReturn.returnedCode_normal_spec s c hc
  · simpa [answer] using NativePublicReturn.rawReturnCode_spec s c hc
  · simpa [answer] using NativePublicReturn.returnedCode_normal_spec s c hc
  · have hi := (Bool.and_eq_true.mp hl).1
    simpa [answer] using NativePublicReturn.rawReturnCode_spec s c hi

theorem answer_low_spec (tag s c : Nat) (hc : input tag s c = true) (ht : tag = 2 ∨ tag = 3) :
    Theta.acceptedLowCode (s + 1) (answer tag s c) = true ∧
      interpretation (s + 1) (answer tag s c) = NativeContext.interpretation (contextCode s) c := by
  rcases ht with rfl | rfl
  · have hs : NativeContext.Comparison.acceptedCode (contextCode s) c = true ∧
        NativeContext.lowCheckCode (contextCode s) c = true := by simpa [input] using hc
    simpa [answer] using NativePublicReturn.returnedCode_normal_low_spec s c hs.1 hs.2
  · have hs : NativeContext.lowCheckCode (contextCode s) c = true := by simpa [input] using hc
    simpa [answer] using NativePublicReturn.rawReturnCode_low_spec s c hs

theorem answer_low_union (tag s c : Nat) (hc : input tag s c = true) (ht : tag = 2 ∨ tag = 3) :
    unionCheck (Nat.pair (s + 1) (answer tag s c)) = true ∧
      unionInterpretation (Nat.pair (s + 1) (answer tag s c)) = NativeContext.interpretation (contextCode s) c := by
  have hs := answer_low_spec tag s c hc ht
  simpa only [unionCheck_pair, unionInterpretation_pair] using
    And.intro ((Theta.acceptedLowCode_iff _ _).mp hs.1).1 hs.2

def evaluation (query : Nat) : Part Nat :=
  cond (input query.unpair.1 query.unpair.2.unpair.1 query.unpair.2.unpair.2)
    (Part.some (answer query.unpair.1 query.unpair.2.unpair.1 query.unpair.2.unpair.2)) Part.none

theorem evaluation_partrec : Partrec evaluation := by
  have ht := Primrec.fst.comp Primrec.unpair
  have hp := Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)
  have hquery := ht.pair hp
  exact Partrec.cond (input_primrec.comp hquery).to_comp
    (answer_primrec.comp hquery).to_comp.partrec Partrec.none

theorem program_exists : ∃ p : Program, ∀ query, p.eval query = evaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp evaluation_partrec)

noncomputable def program : Program := Classical.choose program_exists

theorem program_eval (tag s c : Nat) : program.eval (Nat.pair tag (Nat.pair s c)) =
    cond (input tag s c) (Part.some (answer tag s c)) Part.none := by
  simpa only [evaluation, Nat.unpair_pair] using
    Classical.choose_spec program_exists (Nat.pair tag (Nat.pair s c))

theorem program_domain (tag s c : Nat) : program.domain (Nat.pair tag (Nat.pair s c)) ↔
    input tag s c = true := by
  rw [Program.domain, program_eval]
  cases h : input tag s c <;> simp [h]

theorem program_graph (tag s c output : Nat) : output ∈ program.eval (Nat.pair tag (Nat.pair s c)) ↔
    input tag s c = true ∧ output = answer tag s c := by
  rw [program_eval]
  cases h : input tag s c <;> simp [h]

noncomputable def sourceColumn (tag s : Nat) : Program := (program.column tag).column s

theorem sourceColumn_primrec : Primrec₂ sourceColumn :=
  (Program.column_primrec.comp (Program.column_primrec.comp (Primrec.const program) Primrec.fst)
    Primrec.snd).to₂

theorem sourceColumn_eval (tag s c : Nat) : (sourceColumn tag s).eval c =
    cond (input tag s c) (Part.some (answer tag s c)) Part.none := by
  simp only [sourceColumn, Nat.Partrec.Code.eval_curry, program_eval]

theorem sourceColumn_domain (tag s c : Nat) : (sourceColumn tag s).domain c ↔ input tag s c = true := by
  rw [sourceColumn, Program.column_domain, Program.column_domain]
  exact program_domain tag s c

theorem sourceColumn_graph (tag s c output : Nat) : output ∈ (sourceColumn tag s).eval c ↔
    input tag s c = true ∧ output = answer tag s c := by
  simp only [sourceColumn, Nat.Partrec.Code.eval_curry]
  exact program_graph tag s c output

theorem sourceColumn_output (tag s c output : Nat) (ho : output ∈ (sourceColumn tag s).eval c) :
    Theta.acceptedCode (s + 1) output = true ∧
      interpretation (s + 1) output = NativeContext.interpretation (contextCode s) c := by
  obtain ⟨hc, rfl⟩ := (sourceColumn_graph tag s c output).mp ho
  exact answer_spec tag s c hc

theorem sourceColumn_low_output (tag s c output : Nat)
    (ho : output ∈ (sourceColumn tag s).eval c) (ht : tag = 2 ∨ tag = 3) :
    Theta.acceptedLowCode (s + 1) output = true ∧
      unionInterpretation (Nat.pair (s + 1) output) = NativeContext.interpretation (contextCode s) c := by
  obtain ⟨hc, rfl⟩ := (sourceColumn_graph tag s c output).mp ho
  have hs := answer_low_spec tag s c hc ht
  exact ⟨hs.1, by simpa only [unionInterpretation_pair] using hs.2⟩

theorem normalColumn_domain (s c : Nat) : (sourceColumn 0 s).domain c ↔
    NativeContext.checkCode (contextCode s) c = true ∧
      NativeContext.Comparison.Normal (contextCode s) (Wilken.RelativeTerm.Hereditary.ThetaCourse.rawTree c) := by
  simp [sourceColumn_domain, input, NativeContext.Comparison.acceptedCode_exact]

theorem rawColumn_domain (s c : Nat) : (sourceColumn 1 s).domain c ↔
    NativeContext.checkCode (contextCode s) c = true := by simp [sourceColumn_domain, input]

theorem normalLowColumn_domain (s c : Nat) : (sourceColumn 2 s).domain c ↔
    NativeContext.Comparison.acceptedCode (contextCode s) c = true ∧
      NativeContext.lowCheckCode (contextCode s) c = true := by simp [sourceColumn_domain, input]

theorem rawLowColumn_domain (s c : Nat) : (sourceColumn 3 s).domain c ↔
    NativeContext.lowCheckCode (contextCode s) c = true := by simp [sourceColumn_domain, input]

/-- The actual finite kernel's complete literal numerical graph. -/
def graphCheck (tag s c output : Nat) : Bool := input tag s c && (output == answer tag s c)

theorem graphCheck_primrec : Primrec
    (fun p : (Nat × (Nat × Nat)) × Nat => graphCheck p.1.1 p.1.2.1 p.1.2.2 p.2) :=
  Primrec.and.comp (input_primrec.comp Primrec.fst)
    (Primrec.beq.comp Primrec.snd (answer_primrec.comp Primrec.fst))

def graphEvaluation (query : Nat) : Part Nat :=
  let source := query.unpair.1
  cond (graphCheck source.unpair.1 source.unpair.2.unpair.1 source.unpair.2.unpair.2 query.unpair.2)
    (Part.some 0) Part.none

theorem graphEvaluation_partrec : Partrec graphEvaluation := by
  have hs := Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)
  have hsc := Primrec.unpair.comp (Primrec.snd.comp hs)
  have hsource := (Primrec.fst.comp hs).pair hsc
  have h := graphCheck_primrec.comp (hsource.pair (Primrec.snd.comp Primrec.unpair))
  exact Partrec.cond h.to_comp (Computable.const 0).partrec Partrec.none

theorem graphProgram_exists : ∃ p : Program, ∀ query, p.eval query = graphEvaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp graphEvaluation_partrec)

noncomputable def graphProgram : Program := Classical.choose graphProgram_exists

theorem graphProgram_domain (tag s c output : Nat) :
    graphProgram.domain (Nat.pair (Nat.pair tag (Nat.pair s c)) output) ↔
      input tag s c = true ∧ output = answer tag s c := by
  rw [Program.domain, Classical.choose_spec graphProgram_exists]
  simp only [graphEvaluation, Nat.unpair_pair, graphCheck]
  cases hi : input tag s c <;> cases ho : output == answer tag s c <;>
    simp [hi, ho, ← beq_iff_eq]

noncomputable def graphColumn (tag s c : Nat) : Program := graphProgram.column (Nat.pair tag (Nat.pair s c))

theorem graphColumn_primrec : Primrec (fun p : Nat × (Nat × Nat) => graphColumn p.1 p.2.1 p.2.2) :=
  Program.column_primrec.comp (Primrec.const graphProgram)
    (Primrec₂.natPair.comp Primrec.fst (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)))

theorem graphColumn_domain (tag s c output : Nat) : (graphColumn tag s c).domain output ↔
    input tag s c = true ∧ output = answer tag s c := by
  rw [graphColumn, Program.column_domain]
  exact graphProgram_domain tag s c output

theorem graphColumn_executed (tag s c output : Nat) : (graphColumn tag s c).domain output ↔
    output ∈ (sourceColumn tag s).eval c := by rw [graphColumn_domain, sourceColumn_graph]

theorem graphColumn_unique (tag s c : Nat) (hc : input tag s c = true) :
    ∃! output, (graphColumn tag s c).domain output := by
  refine ⟨answer tag s c, (graphColumn_domain tag s c _).mpr ⟨hc, rfl⟩, ?_⟩
  intro output ho
  exact ((graphColumn_domain tag s c output).mp ho).2

end Alexander313.HereditaryNativePublicReturnProgram
