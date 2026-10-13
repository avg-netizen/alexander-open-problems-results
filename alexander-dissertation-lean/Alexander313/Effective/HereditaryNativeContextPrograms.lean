import Alexander313.Wilken.HereditaryNativeContexts

/-!
# Executing native epsilon-context admission Programs

The total decision Program computes the actual native admission kernels.
Tags 0 and 1 select full and low native syntax, tag 2 selects an original
public parameter below the actual epsilon base, and tag 3 selects a finite
fragment with its literal (fragment,term-code) payload. Every tag retains
the actual epsilon-context guard; unknown tags reject. Positive input and
complete Boolean output-graph Programs specialize genuine fixed PR kernels.
They do not evaluate, compare or translate native ordinal values.
All proof candidates are uncompiled.
-/

namespace Alexander313.HereditaryNativeContextProgram

open Wilken.RelativeTerm
open Wilken.RelativeTerm.Hereditary

def kernel (tag q payload : Nat) : Bool :=
  cond (tag == 0) (NativeContext.checkCode q payload)
    (cond (tag == 1) (NativeContext.lowCheckCode q payload)
      (cond (tag == 2) (NativeContext.baseCheck q && NativeContext.parameterCheck q payload)
        (cond (tag == 3) (NativeContext.baseCheck q &&
          NativeContext.finiteCheckCode q payload.unpair.1 payload.unpair.2) false)))

theorem kernel_primrec : Primrec (fun p : Nat × (Nat × Nat) => kernel p.1 p.2.1 p.2.2) := by
  have hq : Primrec (fun p : Nat × (Nat × Nat) => p.2.1) := Primrec.fst.comp Primrec.snd
  have hp : Primrec (fun p : Nat × (Nat × Nat) => p.2.2) := Primrec.snd.comp Primrec.snd
  have hg := NativeContext.baseCheck_primrec.comp hq
  have hf := NativeContext.finiteCheckCode_primrec.comp
    ((hq.pair (Primrec.fst.comp (Primrec.unpair.comp hp))).pair
      (Primrec.snd.comp (Primrec.unpair.comp hp)))
  have ht (k : Nat) : Primrec (fun p : Nat × (Nat × Nat) => p.1 == k) :=
    Primrec.beq.comp Primrec.fst (Primrec.const k)
  exact (ht 0).cond (NativeContext.checkCode_primrec.comp hq hp)
    ((ht 1).cond (NativeContext.lowCheckCode_primrec.comp hq hp)
      ((ht 2).cond (Primrec.and.comp hg (NativeContext.parameterCheck_primrec.comp hq hp))
        ((ht 3).cond (Primrec.and.comp hg hf) (Primrec.const false))))

@[simp] theorem kernel_full (q c : Nat) : kernel 0 q c = NativeContext.checkCode q c := rfl

@[simp] theorem kernel_low (q c : Nat) : kernel 1 q c = NativeContext.lowCheckCode q c := rfl

@[simp] theorem kernel_parameter (q p : Nat) :
    kernel 2 q p = (NativeContext.baseCheck q && NativeContext.parameterCheck q p) := rfl

@[simp] theorem kernel_finite (q n c : Nat) : kernel 3 q (Nat.pair n c) =
    (NativeContext.baseCheck q && NativeContext.finiteCheckCode q n c) := by
  simp [kernel, Nat.unpair_pair]

theorem kernel_unknown (tag q payload : Nat) (h0 : tag ≠ 0) (h1 : tag ≠ 1)
    (h2 : tag ≠ 2) (h3 : tag ≠ 3) : kernel tag q payload = false := by
  simp [kernel, h0, h1, h2, h3]

def raw (query : Nat) : Bool := kernel query.unpair.1 query.unpair.2.unpair.1 query.unpair.2.unpair.2

theorem raw_primrec : Primrec raw := kernel_primrec.comp
  ((Primrec.fst.comp Primrec.unpair).pair
    (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))

def answer (tag q payload : Nat) : Nat := cond (kernel tag q payload) 1 0

def decisionEvaluation (query : Nat) : Part Nat := Part.some (cond (raw query) 1 0)

theorem decisionEvaluation_partrec : Partrec decisionEvaluation :=
  (raw_primrec.cond (Primrec.const 1) (Primrec.const 0)).to_comp.partrec

theorem decisionProgram_exists : ∃ p : Program, ∀ query, p.eval query = decisionEvaluation query :=
  by
    obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp decisionEvaluation_partrec)
    exact ⟨p, fun query => congrFun hp query⟩

noncomputable def decisionProgram : Program := Classical.choose decisionProgram_exists

theorem decisionProgram_eval (tag q payload : Nat) :
    decisionProgram.eval (Nat.pair tag (Nat.pair q payload)) = Part.some (answer tag q payload) := by
  simpa only [decisionProgram, decisionEvaluation, raw, answer, Nat.unpair_pair] using
    Classical.choose_spec decisionProgram_exists (Nat.pair tag (Nat.pair q payload))

theorem decisionProgram_total (query : Nat) : decisionProgram.domain query := by
  rw [Program.domain, decisionProgram, Classical.choose_spec decisionProgram_exists]
  exact Part.some_dom _

theorem decisionProgram_graph (tag q payload output : Nat) :
    output ∈ decisionProgram.eval (Nat.pair tag (Nat.pair q payload)) ↔ output = answer tag q payload := by
  simp only [decisionProgram_eval, Part.mem_some_iff]

theorem decisionProgram_positive (tag q payload : Nat) :
    1 ∈ decisionProgram.eval (Nat.pair tag (Nat.pair q payload)) ↔ kernel tag q payload = true := by
  rw [decisionProgram_graph]
  cases h : kernel tag q payload <;> simp [answer, h]

noncomputable def decisionColumn (tag q : Nat) : Program := (decisionProgram.column tag).column q

theorem decisionColumn_primrec : Primrec₂ decisionColumn := by
  have hfirst : Primrec (fun p : Nat × Nat => decisionProgram.column p.1) :=
    Program.column_primrec.comp (Primrec.const decisionProgram) Primrec.fst
  exact (Program.column_primrec.comp hfirst Primrec.snd).to₂

theorem decisionColumn_eval (tag q payload : Nat) :
    (decisionColumn tag q).eval payload = Part.some (answer tag q payload) := by
  simp only [decisionColumn, Program.column, Nat.Partrec.Code.eval_curry, decisionProgram_eval]

def inputEvaluation (query : Nat) : Part Nat := cond (raw query) (Part.some 0) Part.none

theorem inputEvaluation_partrec : Partrec inputEvaluation :=
  Partrec.cond raw_primrec.to_comp (Computable.const 0).partrec Partrec.none

theorem inputProgram_exists : ∃ p : Program, ∀ query, p.eval query = inputEvaluation query :=
  by
    obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp inputEvaluation_partrec)
    exact ⟨p, fun query => congrFun hp query⟩

noncomputable def inputProgram : Program := Classical.choose inputProgram_exists

theorem inputProgram_domain (tag q payload : Nat) :
    inputProgram.domain (Nat.pair tag (Nat.pair q payload)) ↔ kernel tag q payload = true := by
  rw [Program.domain, inputProgram, Classical.choose_spec inputProgram_exists]
  cases h : kernel tag q payload <;> simp [inputEvaluation, raw, Nat.unpair_pair, h]

noncomputable def inputColumn (tag q : Nat) : Program := (inputProgram.column tag).column q

theorem inputColumn_primrec : Primrec₂ inputColumn := by
  have hfirst : Primrec (fun p : Nat × Nat => inputProgram.column p.1) :=
    Program.column_primrec.comp (Primrec.const inputProgram) Primrec.fst
  exact (Program.column_primrec.comp hfirst Primrec.snd).to₂

theorem inputColumn_domain (tag q payload : Nat) :
    (inputColumn tag q).domain payload ↔ kernel tag q payload = true := by
  rw [inputColumn, Program.column_domain, Program.column_domain]
  exact inputProgram_domain tag q payload

theorem fullColumn_domain (q c : Nat) : (inputColumn 0 q).domain c ↔
    ∃ t : Wilken.RelativeTerm Nat, t.code = c ∧ NativeContext.check q t = true := by
  rw [inputColumn_domain, kernel_full]
  exact NativeContext.checkCode_exact q c

theorem fullColumn_source (q c : Nat) : (inputColumn 0 q).domain c ↔
    NativeContext.baseCheck q = true ∧ ∃ t : Wilken.RelativeTerm Nat,
      t.code = c ∧ ∃ n, NativeContext.admissible q n t := by
  rw [fullColumn_domain]
  constructor
  · rintro ⟨t, ht, hc⟩
    have hs := (NativeContext.check_exact q t).mp hc
    exact ⟨hs.1, t, ht, hs.2⟩
  · rintro ⟨hq, t, ht, hs⟩
    exact ⟨t, ht, (NativeContext.check_exact q t).mpr ⟨hq, hs⟩⟩

theorem lowColumn_domain (q c : Nat) : (inputColumn 1 q).domain c ↔
    ∃ t : Wilken.RelativeTerm Nat, t.code = c ∧ NativeContext.lowCheck q t = true := by
  rw [inputColumn_domain, kernel_low]
  exact NativeContext.lowCheckCode_exact q c

theorem parameterColumn_domain (q p : Nat) : (inputColumn 2 q).domain p ↔
    NativeContext.baseCheck q = true ∧ unionCheck p = true ∧ NativeContext.parameters p < NativeContext.base q := by
  rw [inputColumn_domain, kernel_parameter, Bool.and_eq_true, NativeContext.parameterCheck_exact]
  constructor
  · rintro ⟨hq, hp, hv, hlt⟩; exact ⟨hq, hp, hlt⟩
  · rintro ⟨hq, hp, hlt⟩
    exact ⟨hq, hp, ((NativeContext.baseCheck_exact q).mp hq).1, hlt⟩

theorem finiteColumn_domain (q n c : Nat) : (inputColumn 3 q).domain (Nat.pair n c) ↔
    NativeContext.baseCheck q = true ∧ ∃ t : Wilken.RelativeTerm Nat,
      t.code = c ∧ NativeContext.admissible q n t := by
  rw [inputColumn_domain, kernel_finite, Bool.and_eq_true]
  exact and_congr Iff.rfl (NativeContext.finiteCheckCode_exact q n c)

theorem fullColumn_global (q c : Nat) (hc : (inputColumn 0 q).domain c) :
    Wilken.GlobalNotation (NativeContext.base q) 0 (NativeContext.interpretation q c) := by
  obtain ⟨t, ht, hct⟩ := (fullColumn_domain q c).mp hc
  rw [← ht, NativeContext.interpretation_code]
  exact NativeContext.checked_globalNotation q t hct

theorem lowColumn_bound (q c : Nat) (hc : (inputColumn 1 q).domain c) :
    NativeContext.interpretation q c < Wilken.globalBoundary (NativeContext.base q) 0 :=
  NativeContext.checked_low_bound q c ((inputColumn_domain 1 q c).mp hc)

theorem fullColumn_coverage (q : Nat) (hq : NativeContext.baseCheck q = true) (ξ : Ordinal.{0}) :
    Wilken.GlobalNotation (NativeContext.base q) 0 ξ ↔
      ∃ c, (inputColumn 0 q).domain c ∧ NativeContext.interpretation q c = ξ := by
  simpa only [inputColumn_domain, kernel_full] using NativeContext.globalNotation_iff_code q hq ξ

theorem lowColumn_coverage (q : Nat) (hq : NativeContext.baseCheck q = true) (ξ : Ordinal.{0}) :
    ξ < Wilken.globalBoundary (NativeContext.base q) 0 ↔
      ∃ c, (inputColumn 1 q).domain c ∧ NativeContext.interpretation q c = ξ := by
  simpa only [inputColumn_domain, kernel_low] using NativeContext.lt_boundary_iff_code q hq ξ

theorem inputColumn_unknown (tag q payload : Nat) (h0 : tag ≠ 0) (h1 : tag ≠ 1)
    (h2 : tag ≠ 2) (h3 : tag ≠ 3) : ¬ (inputColumn tag q).domain payload := by
  rw [inputColumn_domain, kernel_unknown tag q payload h0 h1 h2 h3]
  decide

def graphRaw (query : Nat) : Bool :=
  query.unpair.2 == cond (raw query.unpair.1) 1 0

theorem graphRaw_primrec : Primrec graphRaw :=
  Primrec.beq.comp (Primrec.snd.comp Primrec.unpair)
    ((raw_primrec.comp (Primrec.fst.comp Primrec.unpair)).cond (Primrec.const 1) (Primrec.const 0))

def graphEvaluation (query : Nat) : Part Nat := cond (graphRaw query) (Part.some 0) Part.none

theorem graphEvaluation_partrec : Partrec graphEvaluation :=
  Partrec.cond graphRaw_primrec.to_comp (Computable.const 0).partrec Partrec.none

theorem graphProgram_exists : ∃ p : Program, ∀ query, p.eval query = graphEvaluation query :=
  by
    obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp graphEvaluation_partrec)
    exact ⟨p, fun query => congrFun hp query⟩

noncomputable def graphProgram : Program := Classical.choose graphProgram_exists

theorem graphProgram_domain (tag q payload output : Nat) :
    graphProgram.domain (Nat.pair (Nat.pair tag (Nat.pair q payload)) output) ↔ output = answer tag q payload := by
  rw [Program.domain, graphProgram, Classical.choose_spec graphProgram_exists]
  simp only [graphEvaluation, graphRaw, raw, Nat.unpair_pair]
  change (cond (output == answer tag q payload) (Part.some 0) Part.none).Dom ↔ output = answer tag q payload
  cases h : output == answer tag q payload <;>
    simp [h, ← beq_iff_eq]

noncomputable def graphColumn (tag q payload : Nat) : Program :=
  graphProgram.column (Nat.pair tag (Nat.pair q payload))

theorem graphColumn_primrec : Primrec (fun p : Nat × (Nat × Nat) => graphColumn p.1 p.2.1 p.2.2) :=
  Program.column_primrec.comp (Primrec.const graphProgram)
    (Primrec₂.natPair.comp Primrec.fst (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)))

theorem graphColumn_domain (tag q payload output : Nat) :
    (graphColumn tag q payload).domain output ↔ output = answer tag q payload := by
  rw [graphColumn, Program.column_domain]
  exact graphProgram_domain tag q payload output

theorem graphColumn_execution (tag q payload output : Nat) :
    (graphColumn tag q payload).domain output ↔
      output ∈ decisionProgram.eval (Nat.pair tag (Nat.pair q payload)) :=
  (graphColumn_domain tag q payload output).trans (decisionProgram_graph tag q payload output).symm

theorem graphColumn_unique (tag q payload : Nat) : ∃! output, (graphColumn tag q payload).domain output := by
  refine ⟨answer tag q payload, (graphColumn_domain tag q payload _).mpr rfl, ?_⟩
  intro output ho
  exact (graphColumn_domain tag q payload output).mp ho

end Alexander313.HereditaryNativeContextProgram
