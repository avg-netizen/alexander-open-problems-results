import Alexander313.Wilken.HereditaryNativeIotaBaseChange
import Alexander313.Effective.HereditaryNativeIotaPrograms

/-!
# Programs executing the original-domain iota/pi equation

Tags0/1 execute actual pi after literal/normalized iota_alpha on the original
weak-normal source-star restriction to gamma. Tags2/3 normalize the original
raw input first. The only guards concern original roots, source base < gamma
< alpha, original source admission/normality, and source-star restriction.
Target pi admission and Par are derived. Program outputs are proved equal to
the actual iota_gamma outputs. Input and complete numerical graph Programs
include output zero; unknown tags reject. All proofs are uncompiled candidates.
-/

namespace Alexander313.HereditaryNativeIotaBaseChangeProgram

open Wilken.RelativeTerm.Hereditary
open NativeContext

abbrev Data := (Nat × Nat) × ((Nat × Nat) × Nat)

def input (tag s g a c : Nat) : Bool := cond (tag == 0) (Iota.BaseChange.inputCheck s g a c)
  (cond (tag == 1) (Iota.BaseChange.inputCheck s g a c)
    (cond (tag == 2) (Iota.BaseChange.rawInputCheck s g a c)
      (cond (tag == 3) (Iota.BaseChange.rawInputCheck s g a c) false)))

theorem input_primrec : Primrec (fun p : Data => input p.1.1 p.1.2 p.2.1.1 p.2.1.2 p.2.2) := by
  have ht : Primrec (fun p : Data => p.1.1) := Primrec.fst.comp Primrec.fst
  have hp : Primrec (fun p : Data => ((p.1.2, (p.2.1.1, p.2.1.2)), p.2.2)) :=
    ((Primrec.snd.comp Primrec.fst).pair (Primrec.fst.comp Primrec.snd)).pair
      (Primrec.snd.comp Primrec.snd)
  have hn := Iota.BaseChange.inputCheck_primrec.comp hp
  have hr := Iota.BaseChange.rawInputCheck_primrec.comp hp
  exact (Primrec.beq.comp ht (Primrec.const 0)).cond hn
    ((Primrec.beq.comp ht (Primrec.const 1)).cond hn
      ((Primrec.beq.comp ht (Primrec.const 2)).cond hr
        ((Primrec.beq.comp ht (Primrec.const 3)).cond hr (Primrec.const false))))

theorem input_exact (tag s g a c : Nat) : input tag s g a c = true ↔
    ((tag = 0 ∨ tag = 1) ∧ Iota.BaseChange.inputCheck s g a c = true) ∨
      ((tag = 2 ∨ tag = 3) ∧ Iota.BaseChange.rawInputCheck s g a c = true) := by
  by_cases h0 : tag = 0
  · subst tag; simp [input]
  · by_cases h1 : tag = 1
    · subst tag; simp [input]
    · by_cases h2 : tag = 2
      · subst tag; simp [input]
      · by_cases h3 : tag = 3 <;> simp [input, h0, h1, h2, h3]

theorem input_unknown (tag s g a c : Nat) (h : 4 ≤ tag) : input tag s g a c = false := by
  have h0 : tag ≠ 0 := by omega
  have h1 : tag ≠ 1 := by omega
  have h2 : tag ≠ 2 := by omega
  have h3 : tag ≠ 3 := by omega
  simp [input, h0, h1, h2, h3]

/-- Execute the genuine original pi kernel on the actual alpha-iota output. -/
def output (tag s g a c : Nat) : Nat := BaseTransformation.piCode (Iota.alphaCode s a)
  (Iota.alphaCode s g) (HereditaryNativeIotaProgram.output tag s a c)

theorem output_primrec : Primrec (fun p : Data => output p.1.1 p.1.2 p.2.1.1 p.2.1.2 p.2.2) := by
  have hs : Primrec (fun p : Data => p.1.2) := Primrec.snd.comp Primrec.fst
  have hg : Primrec (fun p : Data => p.2.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have ha : Primrec (fun p : Data => p.2.1.2) := Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have hp : Primrec (fun p : Data => ((p.1.1, p.1.2), (p.2.1.2, p.2.2))) :=
    Primrec.fst.pair (ha.pair (Primrec.snd.comp Primrec.snd))
  exact BaseTransformation.piCode_primrec.comp ((Iota.alphaCode_primrec.comp hs ha).pair
    ((Iota.alphaCode_primrec.comp hs hg).pair (HereditaryNativeIotaProgram.output_primrec.comp hp)))

theorem output_pi_caller (tag s g a c : Nat) (hi : input tag s g a c = true) :
    BaseTransformation.inputCheck (Iota.alphaCode s a) (Iota.alphaCode s g)
      (HereditaryNativeIotaProgram.output tag s a c) = true := by
  rcases (input_exact tag s g a c).mp hi with ⟨htag, hc⟩ | ⟨htag, hc⟩
  · rcases htag with rfl | rfl
    · simpa [HereditaryNativeIotaProgram.output] using Iota.BaseChange.literal_pi_caller s g a c hc
    · simpa [HereditaryNativeIotaProgram.output] using
        (Bool.and_eq_true.mp (Iota.BaseChange.normalized_pi_caller s g a c hc)).1
  · rcases htag with rfl | rfl
    · simpa [HereditaryNativeIotaProgram.output] using Iota.BaseChange.raw_literal_pi_caller s g a c hc
    · simpa [HereditaryNativeIotaProgram.output] using
        (Bool.and_eq_true.mp (Iota.BaseChange.raw_normalized_pi_caller s g a c hc)).1

theorem output_commutes (tag s g a c : Nat) (hi : input tag s g a c = true) :
    output tag s g a c = HereditaryNativeIotaProgram.output tag s g c := by
  rcases (input_exact tag s g a c).mp hi with ⟨htag, hc⟩ | ⟨htag, hc⟩
  · rcases htag with rfl | rfl
    · simpa [output, HereditaryNativeIotaProgram.output] using Iota.BaseChange.literal_commutes s g a c hc
    · simpa [output, HereditaryNativeIotaProgram.output] using Iota.BaseChange.normalized_commutes s g a c hc
  · rcases htag with rfl | rfl
    · simpa [output, HereditaryNativeIotaProgram.output] using Iota.BaseChange.raw_literal_commutes s g a c hc
    · simpa [output, HereditaryNativeIotaProgram.output] using Iota.BaseChange.raw_normalized_commutes s g a c hc

theorem output_checked (tag s g a c : Nat) (hi : input tag s g a c = true) :
    checkCode (Iota.alphaCode s g) (output tag s g a c) = true :=
  BaseTransformation.piCode_checked _ _ _ (output_pi_caller tag s g a c hi)

theorem output_accepted (tag s g a c : Nat) (hi : input tag s g a c = true)
    (htag : tag = 1 ∨ tag = 3) : Comparison.acceptedCode (Iota.alphaCode s g) (output tag s g a c) = true := by
  rcases htag with rfl | rfl
  · have hc : Iota.BaseChange.inputCheck s g a c = true := by simpa [input] using hi
    simpa [output, HereditaryNativeIotaProgram.output] using
      BaseTransformation.piCode_normal _ _ _ (Iota.BaseChange.normalized_pi_caller s g a c hc)
  · have hc : Iota.BaseChange.rawInputCheck s g a c = true := by simpa [input] using hi
    simpa [output, HereditaryNativeIotaProgram.output] using
      BaseTransformation.piCode_normal _ _ _ (Iota.BaseChange.raw_normalized_pi_caller s g a c hc)

def data (query : Nat) : Data :=
  ((query.unpair.1, query.unpair.2.unpair.1),
    ((query.unpair.2.unpair.2.unpair.1, query.unpair.2.unpair.2.unpair.2.unpair.1),
      query.unpair.2.unpair.2.unpair.2.unpair.2))

theorem data_primrec : Primrec data := by
  have h0 := Primrec.unpair
  have h1 := Primrec.unpair.comp (Primrec.snd.comp h0)
  have h2 := Primrec.unpair.comp (Primrec.snd.comp h1)
  have h3 := Primrec.unpair.comp (Primrec.snd.comp h2)
  exact ((Primrec.fst.comp h0).pair (Primrec.fst.comp h1)).pair
    (((Primrec.fst.comp h2).pair (Primrec.fst.comp h3)).pair (Primrec.snd.comp h3))

def evaluation (query : Nat) : Part Nat :=
  let p := data query
  cond (input p.1.1 p.1.2 p.2.1.1 p.2.1.2 p.2.2)
    (Part.some (output p.1.1 p.1.2 p.2.1.1 p.2.1.2 p.2.2)) Part.none

theorem evaluation_partrec : Partrec evaluation :=
  Partrec.cond (input_primrec.comp data_primrec).to_comp
    (output_primrec.comp data_primrec).to_comp.partrec Partrec.none

theorem program_exists : ∃ p : Program, ∀ query, p.eval query = evaluation query := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp evaluation_partrec)
  exact ⟨p, fun query => congrFun hp query⟩

noncomputable def program : Program := Classical.choose program_exists

theorem program_eval (tag s g a c : Nat) :
    program.eval (Nat.pair tag (Nat.pair s (Nat.pair g (Nat.pair a c)))) =
      cond (input tag s g a c) (Part.some (output tag s g a c)) Part.none := by
  simpa only [evaluation, data, Nat.unpair_pair] using
    Classical.choose_spec program_exists (Nat.pair tag (Nat.pair s (Nat.pair g (Nat.pair a c))))

theorem program_domain (tag s g a c : Nat) :
    program.domain (Nat.pair tag (Nat.pair s (Nat.pair g (Nat.pair a c)))) ↔ input tag s g a c = true := by
  rw [Program.domain, program_eval]
  cases h : input tag s g a c <;> simp [h]

theorem program_graph (tag s g a c out : Nat) :
    out ∈ program.eval (Nat.pair tag (Nat.pair s (Nat.pair g (Nat.pair a c)))) ↔
      input tag s g a c = true ∧ out = output tag s g a c := by
  rw [program_eval]
  cases h : input tag s g a c <;> simp [h]

theorem program_graph_commutes (tag s g a c out : Nat) :
    out ∈ program.eval (Nat.pair tag (Nat.pair s (Nat.pair g (Nat.pair a c)))) ↔
      input tag s g a c = true ∧ out = HereditaryNativeIotaProgram.output tag s g c := by
  rw [program_graph]
  exact ⟨fun ⟨hi, he⟩ => ⟨hi, he.trans (output_commutes tag s g a c hi)⟩,
    fun ⟨hi, he⟩ => ⟨hi, he.trans (output_commutes tag s g a c hi).symm⟩⟩

noncomputable def sourceColumn (tag s g a : Nat) : Program := (((program.column tag).column s).column g).column a

theorem sourceColumn_primrec : Primrec
    (fun p : (Nat × Nat) × (Nat × Nat) => sourceColumn p.1.1 p.1.2 p.2.1 p.2.2) :=
  Program.column_primrec.comp (Program.column_primrec.comp (Program.column_primrec.comp
    (Program.column_primrec.comp (Primrec.const program) (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp Primrec.fst)) (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)

theorem sourceColumn_domain (tag s g a c : Nat) : (sourceColumn tag s g a).domain c ↔ input tag s g a c = true := by
  simp only [sourceColumn, Program.column_domain]
  exact program_domain tag s g a c

theorem sourceColumn_graph (tag s g a c out : Nat) : out ∈ (sourceColumn tag s g a).eval c ↔
    input tag s g a c = true ∧ out = output tag s g a c := by
  simp only [sourceColumn, Nat.Partrec.Code.eval_curry]
  exact program_graph tag s g a c out

theorem sourceColumn_commutes (tag s g a c out : Nat) (ho : out ∈ (sourceColumn tag s g a).eval c) :
    out = HereditaryNativeIotaProgram.output tag s g c := by
  obtain ⟨hi, he⟩ := (sourceColumn_graph tag s g a c out).mp ho
  exact he.trans (output_commutes tag s g a c hi)

theorem sourceColumn_checked (tag s g a c out : Nat) (ho : out ∈ (sourceColumn tag s g a).eval c) :
    checkCode (Iota.alphaCode s g) out = true := by
  obtain ⟨hi, rfl⟩ := (sourceColumn_graph tag s g a c out).mp ho
  exact output_checked tag s g a c hi

def graphBool (query : Nat) : Bool :=
  let p := data query.unpair.1
  input p.1.1 p.1.2 p.2.1.1 p.2.1.2 p.2.2 &&
    (query.unpair.2 == output p.1.1 p.1.2 p.2.1.1 p.2.1.2 p.2.2)

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

theorem graphProgram_domain (tag s g a c out : Nat) : graphProgram.domain
    (Nat.pair (Nat.pair tag (Nat.pair s (Nat.pair g (Nat.pair a c)))) out) ↔
      input tag s g a c = true ∧ out = output tag s g a c := by
  rw [Program.domain, Classical.choose_spec graphProgram_exists]
  simp only [graphEvaluation, graphBool, data, Nat.unpair_pair]
  cases h : input tag s g a c <;> cases he : out == output tag s g a c <;>
    simp [h, he, Bool.eq_iff_iff, beq_iff_eq] at *

noncomputable def graphColumn (tag s g a c : Nat) : Program :=
  graphProgram.column (Nat.pair tag (Nat.pair s (Nat.pair g (Nat.pair a c))))

theorem graphColumn_primrec : Primrec (fun p : Data => graphColumn p.1.1 p.1.2 p.2.1.1 p.2.1.2 p.2.2) :=
  Program.column_primrec.comp (Primrec.const graphProgram)
    (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.fst)
      (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst)
        (Primrec₂.natPair.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
          (Primrec₂.natPair.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
            (Primrec.snd.comp Primrec.snd)))))

theorem graphColumn_domain (tag s g a c out : Nat) : (graphColumn tag s g a c).domain out ↔
    out ∈ (sourceColumn tag s g a).eval c := by
  rw [graphColumn, Program.column_domain, graphProgram_domain, sourceColumn_graph]

def inputEvaluation (query : Nat) : Part Nat :=
  let p := data query
  cond (input p.1.1 p.1.2 p.2.1.1 p.2.1.2 p.2.2) (Part.some 0) Part.none

theorem inputEvaluation_partrec : Partrec inputEvaluation :=
  Partrec.cond (input_primrec.comp data_primrec).to_comp (Computable.const 0).partrec Partrec.none

theorem inputProgram_exists : ∃ p : Program, ∀ query, p.eval query = inputEvaluation query := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp inputEvaluation_partrec)
  exact ⟨p, fun query => congrFun hp query⟩

noncomputable def inputProgram : Program := Classical.choose inputProgram_exists

theorem inputProgram_domain (tag s g a c : Nat) : inputProgram.domain
    (Nat.pair tag (Nat.pair s (Nat.pair g (Nat.pair a c)))) ↔ input tag s g a c = true := by
  rw [Program.domain, Classical.choose_spec inputProgram_exists]
  simp only [inputEvaluation, data, Nat.unpair_pair]
  cases h : input tag s g a c <;> simp [h]

noncomputable def inputColumn (tag s g a : Nat) : Program := (((inputProgram.column tag).column s).column g).column a

theorem inputColumn_primrec : Primrec
    (fun p : (Nat × Nat) × (Nat × Nat) => inputColumn p.1.1 p.1.2 p.2.1 p.2.2) :=
  Program.column_primrec.comp (Program.column_primrec.comp (Program.column_primrec.comp
    (Program.column_primrec.comp (Primrec.const inputProgram) (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp Primrec.fst)) (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)

theorem inputColumn_domain (tag s g a c : Nat) : (inputColumn tag s g a).domain c ↔ input tag s g a c = true := by
  simp only [inputColumn, Program.column_domain]
  exact inputProgram_domain tag s g a c

end Alexander313.HereditaryNativeIotaBaseChangeProgram
