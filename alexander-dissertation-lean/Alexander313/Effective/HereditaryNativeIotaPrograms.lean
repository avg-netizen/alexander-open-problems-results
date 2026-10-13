import Alexander313.Wilken.HereditaryNativeIota
import Alexander313.Computability

/-!
# Actual Programs for native iota syntax and its target normalizer

Tags0/1 execute literal/target-normalized iota on the original weak-normal
source-star domain. Tags2/3 first execute the genuine source normalizer on
original raw admitted inputs, then test its actual source restriction.
Unknown tags reject. The kernels, exact original guards and complete literal
numerical graphs are PR, including an output of zero. Fixed Program columns
are constructed by the existing genuine compiler. No isomorphism, image
coverage, shifted-collapse equation or source canonical-height claim is made.
All proofs remain uncompiled candidates.
-/

namespace Alexander313.HereditaryNativeIotaProgram

open Wilken.RelativeTerm.Hereditary
open NativeContext

abbrev Data := (Nat × Nat) × (Nat × Nat)

def input (tag s a c : Nat) : Bool := cond (tag == 0) (Iota.inputCheck s a c)
  (cond (tag == 1) (Iota.inputCheck s a c)
    (cond (tag == 2) (Iota.rawInputCheck s a c)
      (cond (tag == 3) (Iota.rawInputCheck s a c) false)))

theorem input_primrec : Primrec (fun p : Data => input p.1.1 p.1.2 p.2.1 p.2.2) := by
  have ht : Primrec (fun p : Data => p.1.1) := Primrec.fst.comp Primrec.fst
  have hp : Primrec (fun p : Data => ((p.1.2, p.2.1), p.2.2)) :=
    ((Primrec.snd.comp Primrec.fst).pair (Primrec.fst.comp Primrec.snd)).pair
      (Primrec.snd.comp Primrec.snd)
  have hn := Iota.inputCheck_primrec.comp hp
  have hr := Iota.rawInputCheck_primrec.comp hp
  exact (Primrec.beq.comp ht (Primrec.const 0)).cond hn
    ((Primrec.beq.comp ht (Primrec.const 1)).cond hn
      ((Primrec.beq.comp ht (Primrec.const 2)).cond hr
        ((Primrec.beq.comp ht (Primrec.const 3)).cond hr (Primrec.const false))))

theorem input_exact (tag s a c : Nat) : input tag s a c = true ↔
    ((tag = 0 ∨ tag = 1) ∧ Iota.inputCheck s a c = true) ∨
      ((tag = 2 ∨ tag = 3) ∧ Iota.rawInputCheck s a c = true) := by
  by_cases h0 : tag = 0
  · subst tag; simp [input]
  · by_cases h1 : tag = 1
    · subst tag; simp [input]
    · by_cases h2 : tag = 2
      · subst tag; simp [input]
      · by_cases h3 : tag = 3 <;> simp [input, h0, h1, h2, h3]

theorem input_unknown (tag s a c : Nat) (h : 4 ≤ tag) : input tag s a c = false := by
  have h0 : tag ≠ 0 := by omega
  have h1 : tag ≠ 1 := by omega
  have h2 : tag ≠ 2 := by omega
  have h3 : tag ≠ 3 := by omega
  simp [input, h0, h1, h2, h3]

def output (tag s a c : Nat) : Nat := cond (tag == 0) (Iota.literalCode s a c)
  (cond (tag == 1) (Iota.normalizeCode s a c)
    (cond (tag == 2) (Iota.rawLiteralCode s a c) (Iota.rawNormalizeCode s a c)))

theorem output_primrec : Primrec (fun p : Data => output p.1.1 p.1.2 p.2.1 p.2.2) := by
  have ht : Primrec (fun p : Data => p.1.1) := Primrec.fst.comp Primrec.fst
  have hp : Primrec (fun p : Data => ((p.1.2, p.2.1), p.2.2)) :=
    ((Primrec.snd.comp Primrec.fst).pair (Primrec.fst.comp Primrec.snd)).pair
      (Primrec.snd.comp Primrec.snd)
  exact (Primrec.beq.comp ht (Primrec.const 0)).cond (Iota.literalCode_primrec.comp hp)
    ((Primrec.beq.comp ht (Primrec.const 1)).cond (Iota.normalizeCode_primrec.comp hp)
      ((Primrec.beq.comp ht (Primrec.const 2)).cond (Iota.rawLiteralCode_primrec.comp hp)
        (Iota.rawNormalizeCode_primrec.comp hp)))

theorem output_checked (tag s a c : Nat) (hi : input tag s a c = true) :
    checkCode (Iota.alphaCode s a) (output tag s a c) = true := by
  have literal (d : Nat) (hd : Iota.inputCheck s a d = true) :
      checkCode (Iota.alphaCode s a) (Iota.literalCode s a d) = true := by
    obtain ⟨t, ht, he, hc, hh⟩ := Iota.literalCode_spec s a d hd
    simpa only [he, checkCode_code] using hc
  rcases (input_exact tag s a c).mp hi with ⟨htag, hc⟩ | ⟨htag, hc⟩
  · rcases htag with rfl | rfl
    · simpa [output] using literal c hc
    · simpa [output] using ((Comparison.acceptedCode_exact _ _).mp
        (Iota.normalizeCode_spec s a c hc).1).1
  · have hs := Bool.and_eq_true.mp hc
    rcases htag with rfl | rfl
    · simpa only [output, show (2 == 0) = false from rfl, show (2 == 1) = false from rfl,
        show (2 == 2) = true from rfl, Bool.cond_false, Bool.cond_true,
        Iota.rawLiteralCode, hc] using literal _ hs.2
    · simpa [output] using ((Comparison.acceptedCode_exact _ _).mp
        (Iota.rawNormalizeCode_spec s a c hc).2.1).1

def data (query : Nat) : Data :=
  ((query.unpair.1, query.unpair.2.unpair.1), query.unpair.2.unpair.2.unpair)

theorem data_primrec : Primrec data := by
  have h := Primrec.unpair
  have hp := Primrec.unpair.comp (Primrec.snd.comp h)
  exact ((Primrec.fst.comp h).pair (Primrec.fst.comp hp)).pair
    (Primrec.unpair.comp (Primrec.snd.comp hp))

def evaluation (query : Nat) : Part Nat :=
  let p := data query
  cond (input p.1.1 p.1.2 p.2.1 p.2.2) (Part.some (output p.1.1 p.1.2 p.2.1 p.2.2)) Part.none

theorem evaluation_partrec : Partrec evaluation :=
  Partrec.cond (input_primrec.comp data_primrec).to_comp
    (output_primrec.comp data_primrec).to_comp.partrec Partrec.none

theorem program_exists : ∃ p : Program, ∀ query, p.eval query = evaluation query := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp evaluation_partrec)
  exact ⟨p, fun query => congrFun hp query⟩

noncomputable def program : Program := Classical.choose program_exists

theorem program_eval (tag s a c : Nat) : program.eval (Nat.pair tag (Nat.pair s (Nat.pair a c))) =
    cond (input tag s a c) (Part.some (output tag s a c)) Part.none := by
  simpa only [evaluation, data, Nat.unpair_pair] using
    Classical.choose_spec program_exists (Nat.pair tag (Nat.pair s (Nat.pair a c)))

theorem program_domain (tag s a c : Nat) : program.domain (Nat.pair tag (Nat.pair s (Nat.pair a c))) ↔
    input tag s a c = true := by
  rw [Program.domain, program_eval]
  cases h : input tag s a c <;> simp [h]

theorem program_graph (tag s a c out : Nat) : out ∈ program.eval (Nat.pair tag (Nat.pair s (Nat.pair a c))) ↔
    input tag s a c = true ∧ out = output tag s a c := by
  rw [program_eval]
  cases h : input tag s a c <;> simp [h]

noncomputable def sourceColumn (tag s a : Nat) : Program := ((program.column tag).column s).column a

theorem sourceColumn_primrec : Primrec (fun p : Nat × (Nat × Nat) => sourceColumn p.1 p.2.1 p.2.2) :=
  Program.column_primrec.comp (Program.column_primrec.comp
    (Program.column_primrec.comp (Primrec.const program) Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)

theorem sourceColumn_domain (tag s a c : Nat) : (sourceColumn tag s a).domain c ↔ input tag s a c = true := by
  simp only [sourceColumn, Program.column_domain]
  exact program_domain tag s a c

theorem sourceColumn_graph (tag s a c out : Nat) : out ∈ (sourceColumn tag s a).eval c ↔
    input tag s a c = true ∧ out = output tag s a c := by
  simp only [sourceColumn, Nat.Partrec.Code.eval_curry]
  exact program_graph tag s a c out

theorem sourceColumn_checked (tag s a c out : Nat) (ho : out ∈ (sourceColumn tag s a).eval c) :
    checkCode (Iota.alphaCode s a) out = true := by
  obtain ⟨hi, rfl⟩ := (sourceColumn_graph tag s a c out).mp ho
  exact output_checked tag s a c hi

def graphBool (query : Nat) : Bool :=
  let p := data query.unpair.1
  input p.1.1 p.1.2 p.2.1 p.2.2 && (query.unpair.2 == output p.1.1 p.1.2 p.2.1 p.2.2)

theorem graphBool_primrec : Primrec graphBool := by
  have hd := data_primrec.comp (Primrec.fst.comp Primrec.unpair)
  exact Primrec.and.comp (input_primrec.comp hd)
    (Primrec.beq.comp (Primrec.snd.comp Primrec.unpair) (output_primrec.comp hd))

def graphEvaluation (query : Nat) : Part Nat := cond (graphBool query) (Part.some 0) Part.none

theorem graphEvaluation_partrec : Partrec graphEvaluation :=
  Partrec.cond graphBool_primrec.to_comp (Computable.const 0).partrec Partrec.none

theorem graphProgram_exists : ∃ p : Program, ∀ query, p.eval query = graphEvaluation query := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp graphEvaluation_partrec)
  exact ⟨p, fun query => congrFun hp query⟩

noncomputable def graphProgram : Program := Classical.choose graphProgram_exists

theorem graphProgram_domain (tag s a c out : Nat) : graphProgram.domain
    (Nat.pair (Nat.pair tag (Nat.pair s (Nat.pair a c))) out) ↔
      input tag s a c = true ∧ out = output tag s a c := by
  rw [Program.domain, Classical.choose_spec graphProgram_exists]
  simp only [graphEvaluation, graphBool, data, Nat.unpair_pair]
  cases h : input tag s a c <;> cases he : out == output tag s a c <;>
    simp [h, he, Bool.eq_iff_iff, beq_iff_eq] at *

noncomputable def graphColumn (tag s a c : Nat) : Program :=
  graphProgram.column (Nat.pair tag (Nat.pair s (Nat.pair a c)))

theorem graphColumn_primrec : Primrec (fun p : Data => graphColumn p.1.1 p.1.2 p.2.1 p.2.2) :=
  Program.column_primrec.comp (Primrec.const graphProgram)
    (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.fst)
      (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst)
        (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))))

theorem graphColumn_domain (tag s a c out : Nat) : (graphColumn tag s a c).domain out ↔
    out ∈ (sourceColumn tag s a).eval c := by
  rw [graphColumn, Program.column_domain, graphProgram_domain, sourceColumn_graph]

def inputEvaluation (query : Nat) : Part Nat :=
  let p := data query
  cond (input p.1.1 p.1.2 p.2.1 p.2.2) (Part.some 0) Part.none

theorem inputEvaluation_partrec : Partrec inputEvaluation :=
  Partrec.cond (input_primrec.comp data_primrec).to_comp
    (Computable.const 0).partrec Partrec.none

theorem inputProgram_exists : ∃ p : Program, ∀ query, p.eval query = inputEvaluation query := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp inputEvaluation_partrec)
  exact ⟨p, fun query => congrFun hp query⟩

noncomputable def inputProgram : Program := Classical.choose inputProgram_exists

theorem inputProgram_domain (tag s a c : Nat) : inputProgram.domain
    (Nat.pair tag (Nat.pair s (Nat.pair a c))) ↔ input tag s a c = true := by
  rw [Program.domain, Classical.choose_spec inputProgram_exists]
  simp only [inputEvaluation, data, Nat.unpair_pair]
  cases h : input tag s a c <;> simp [h]

noncomputable def inputColumn (tag s a : Nat) : Program :=
  ((inputProgram.column tag).column s).column a

theorem inputColumn_primrec : Primrec (fun p : Nat × (Nat × Nat) => inputColumn p.1 p.2.1 p.2.2) :=
  Program.column_primrec.comp (Program.column_primrec.comp
    (Program.column_primrec.comp (Primrec.const inputProgram) Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)

theorem inputColumn_domain (tag s a c : Nat) : (inputColumn tag s a).domain c ↔
    input tag s a c = true := by
  simp only [inputColumn, Program.column_domain]
  exact inputProgram_domain tag s a c

end Alexander313.HereditaryNativeIotaProgram
