import Alexander313.Wilken.HereditarySourceZeta

/-!
# Actual source-zeta Programs and complete positive graphs

Tags zero and one execute zeta on the original normal and original raw
literal theta-zero domains, respectively, at every public level. Unknown
tags reject. The strict branch executes the real partial-recursive last
logarithm; the other branch returns canonical zero. The independently
derived finite logarithm graph supplies the genuinely PR complete output
test. Positive domain/graph Programs and all compiler columns specialize
actual constructed kernels. No primitive-recursive logarithm search bound
or same-level output recoding is asserted. Uncompiled source candidates.
-/

namespace Alexander313.HereditarySourceZetaProgram

open Wilken.RelativeTerm.Hereditary

def input (tag r c : Nat) : Bool := cond (tag == 0) (SourceZeta.inputCheck r c)
  (cond (tag == 1) (SourceZeta.rawInputCheck r c) false)

theorem input_primrec : Primrec (fun p : Nat × (Nat × Nat) => input p.1 p.2.1 p.2.2) :=
  (Primrec.beq.comp Primrec.fst (Primrec.const 0)).cond
    (SourceZeta.inputCheck_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
    ((Primrec.beq.comp Primrec.fst (Primrec.const 1)).cond
      (SourceZeta.rawInputCheck_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
      (Primrec.const false))

theorem input_exact (tag r c : Nat) : input tag r c = true ↔
    (tag = 0 ∧ SourceZeta.inputCheck r c = true) ∨
      (tag = 1 ∧ SourceZeta.rawInputCheck r c = true) := by
  by_cases h0 : tag = 0
  · subst tag; simp [input]
  · by_cases h1 : tag = 1 <;> simp [input, h0, h1]

def evaluation (query : Nat) : Part Nat :=
  cond (query.unpair.1 == 0) (SourceZeta.zeta query.unpair.2.unpair.1 query.unpair.2.unpair.2)
    (cond (query.unpair.1 == 1) (SourceZeta.rawZeta query.unpair.2.unpair.1 query.unpair.2.unpair.2) Part.none)

theorem evaluation_partrec : Partrec evaluation := by
  have ht := Primrec.fst.comp Primrec.unpair
  have hp := Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)
  have hr := Primrec.fst.comp hp
  have hc := Primrec.snd.comp hp
  exact Partrec.cond (Primrec.beq.comp ht (Primrec.const 0)).to_comp
    (SourceZeta.zeta_partrec.comp hr.to_comp hc.to_comp)
    (Partrec.cond (Primrec.beq.comp ht (Primrec.const 1)).to_comp
      (SourceZeta.rawZeta_partrec.comp hr.to_comp hc.to_comp) Partrec.none)

theorem program_exists : ∃ p : Program, ∀ query, p.eval query = evaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp evaluation_partrec)

noncomputable def program : Program := Classical.choose program_exists

theorem program_eval (tag r c : Nat) : program.eval (Nat.pair tag (Nat.pair r c)) =
    cond (tag == 0) (SourceZeta.zeta r c) (cond (tag == 1) (SourceZeta.rawZeta r c) Part.none) := by
  simpa only [evaluation, Nat.unpair_pair] using
    Classical.choose_spec program_exists (Nat.pair tag (Nat.pair r c))

theorem program_domain (tag r c : Nat) : program.domain (Nat.pair tag (Nat.pair r c)) ↔ input tag r c = true := by
  rw [Program.domain, program_eval]
  by_cases h0 : tag = 0
  · subst tag; simp [input, Bool.cond_true, SourceZeta.zeta_domain]
  · by_cases h1 : tag = 1 <;>
      simp [input, h0, h1, SourceZeta.rawZeta_domain, Part.not_none_dom]

def graphCheck (tag r c d : Nat) : Bool := cond (tag == 0) (SourceZeta.graph r c d)
  (cond (tag == 1) (SourceZeta.rawGraph r c d) false)

theorem graphCheck_primrec : Primrec (fun p : Nat × (Nat × (Nat × Nat)) => graphCheck p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  (Primrec.beq.comp Primrec.fst (Primrec.const 0)).cond
    (SourceZeta.graph_primrec.comp Primrec.snd)
    ((Primrec.beq.comp Primrec.fst (Primrec.const 1)).cond
      (SourceZeta.rawGraph_primrec.comp Primrec.snd) (Primrec.const false))

theorem graphCheck_exact (tag r c d : Nat) : graphCheck tag r c d = true ↔
    input tag r c = true ∧ Canonical.check d = true ∧ unionInterpretation d = SourceZeta.sourceValue r c := by
  by_cases h0 : tag = 0
  · subst tag; simp [graphCheck, input, Bool.cond_true, SourceZeta.graph_exact]
  · by_cases h1 : tag = 1 <;>
      simp [graphCheck, input, h0, h1, SourceZeta.rawGraph_exact]

theorem program_graph (tag r c d : Nat) : d ∈ program.eval (Nat.pair tag (Nat.pair r c)) ↔
    graphCheck tag r c d = true := by
  rw [program_eval]
  by_cases h0 : tag = 0
  · subst tag; simp [graphCheck, Bool.cond_true, SourceZeta.zeta_graph_iff]
  · by_cases h1 : tag = 1 <;>
      simp [graphCheck, h0, h1, SourceZeta.rawZeta_graph_iff, Part.notMem_none]

noncomputable def sourceColumn (tag r : Nat) : Program := (program.column tag).column r

theorem sourceColumn_primrec : Primrec₂ sourceColumn :=
  (Program.column_primrec.comp (Program.column_primrec.comp (Primrec.const program) Primrec.fst) Primrec.snd).to₂

theorem sourceColumn_eval (tag r c : Nat) : (sourceColumn tag r).eval c =
    cond (tag == 0) (SourceZeta.zeta r c) (cond (tag == 1) (SourceZeta.rawZeta r c) Part.none) := by
  simp only [sourceColumn, Nat.Partrec.Code.eval_curry, program_eval]

theorem sourceColumn_domain (tag r c : Nat) : (sourceColumn tag r).domain c ↔ input tag r c = true := by
  rw [sourceColumn, Program.column_domain, Program.column_domain]
  exact program_domain tag r c

theorem sourceColumn_graph (tag r c d : Nat) : d ∈ (sourceColumn tag r).eval c ↔
    input tag r c = true ∧ Canonical.check d = true ∧ unionInterpretation d = SourceZeta.sourceValue r c := by
  simp only [sourceColumn, Nat.Partrec.Code.eval_curry]
  exact (program_graph tag r c d).trans (graphCheck_exact tag r c d)

theorem normalColumn_domain (r c : Nat) : (sourceColumn 0 r).domain c ↔ Localization.Node r c := by
  simp [sourceColumn_domain, input, Bool.cond_true, SourceZeta.inputCheck_exact]

theorem rawColumn_domain (r c : Nat) : (sourceColumn 1 r).domain c ↔
    ∃ a : Wilken.RelativeTerm Nat, c = (.theta 0 a).code ∧ check r (.theta 0 a) = true := by
  simp [sourceColumn_domain, input, Bool.cond_false, Bool.cond_true,
    SourceZeta.rawInputCheck_exact]

theorem sourceColumn_original (tag r c d : Nat) (hd : d ∈ (sourceColumn tag r).eval c) :
    unionCheck d = true ∧ Theta.Normal d.unpair.1 (ThetaCourse.rawTree d.unpair.2) := by
  have hs := ((sourceColumn_graph tag r c d).mp hd).2.1
  exact ⟨Canonical.check_original hs, Canonical.check_normal hs⟩

theorem sourceColumn_bound (tag r c d : Nat) (hd : d ∈ (sourceColumn tag r).eval c) :
    unionInterpretation d < interpretation r c := by
  rw [sourceColumn_eval] at hd
  by_cases h0 : tag = 0
  · subst tag
    simp [Bool.cond_true] at hd
    exact SourceZeta.zeta_bound r c d hd
  · by_cases h1 : tag = 1
    · subst tag
      simp [Bool.cond_true, Bool.cond_false] at hd
      exact SourceZeta.rawZeta_bound r c d hd
    · simp [h0, h1, Part.notMem_none] at hd

theorem sourceColumn_unique (tag r c : Nat) (hc : input tag r c = true) :
    ∃! d, d ∈ (sourceColumn tag r).eval c := by
  obtain ⟨d, hd⟩ := Part.dom_iff_mem.mp ((sourceColumn_domain tag r c).mpr hc)
  exact ⟨d, hd, fun e he => Part.mem_unique he hd⟩

theorem normalColumn_base (r : Nat) : (sourceColumn 0 r).eval (Localization.baseRaw r) = Part.some LogEnd.zeroCode := by
  simp [sourceColumn_eval, Bool.cond_true, SourceZeta.zeta_base]

/-- Positive tags 0/1 recognize input domains. Tags 2/3 recognize the
complete normal/raw output graph. Input payloads are pair(r,c); graph
payloads are pair(r,pair(c,d)). -/
def positiveCheck (tag payload : Nat) : Bool :=
  cond (tag == 0) (SourceZeta.inputCheck payload.unpair.1 payload.unpair.2)
    (cond (tag == 1) (SourceZeta.rawInputCheck payload.unpair.1 payload.unpair.2)
      (cond (tag == 2) (SourceZeta.graph payload.unpair.1 payload.unpair.2.unpair.1 payload.unpair.2.unpair.2)
        (cond (tag == 3) (SourceZeta.rawGraph payload.unpair.1 payload.unpair.2.unpair.1 payload.unpair.2.unpair.2) false)))

theorem positiveCheck_primrec : Primrec₂ positiveCheck := by
  have hp := Primrec.unpair.comp Primrec.snd
  have hg := (Primrec.fst.comp hp).pair (Primrec.unpair.comp (Primrec.snd.comp hp))
  have ht (k : Nat) := Primrec.beq.comp Primrec.fst (Primrec.const k)
  exact ((ht 0).cond (SourceZeta.inputCheck_primrec.comp (Primrec.fst.comp hp) (Primrec.snd.comp hp))
    ((ht 1).cond (SourceZeta.rawInputCheck_primrec.comp (Primrec.fst.comp hp) (Primrec.snd.comp hp))
      ((ht 2).cond (SourceZeta.graph_primrec.comp hg)
        ((ht 3).cond (SourceZeta.rawGraph_primrec.comp hg) (Primrec.const false))))).to₂

private def positiveConstant (query : Nat) (_ : Nat) : Bool := positiveCheck query.unpair.1 query.unpair.2

private theorem positiveConstant_primrec : Primrec₂ positiveConstant :=
  (positiveCheck_primrec.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst))
    (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst))).to₂

def positiveEvaluation (query : Nat) : Part Nat := Nat.rfind (fun witness => Part.some (positiveConstant query witness))

theorem positiveEvaluation_partrec : Partrec positiveEvaluation :=
  Partrec.rfind positiveConstant_primrec.to_comp.partrec.to₂

theorem positiveEvaluation_domain (query : Nat) : (positiveEvaluation query).Dom ↔
    positiveCheck query.unpair.1 query.unpair.2 = true := by
  simp [positiveEvaluation, positiveConstant, Nat.rfind_dom, eq_comm]

theorem positiveProgram_exists : ∃ p : Program, ∀ query,
    p.domain query ↔ positiveCheck query.unpair.1 query.unpair.2 = true := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp positiveEvaluation_partrec)
  refine ⟨p, fun query => ?_⟩
  simpa only [Program.domain, hp] using positiveEvaluation_domain query

noncomputable def positiveProgram : Program := Classical.choose positiveProgram_exists

theorem positiveProgram_domain (query : Nat) : positiveProgram.domain query ↔
    positiveCheck query.unpair.1 query.unpair.2 = true :=
  Classical.choose_spec positiveProgram_exists query

noncomputable def inputColumn (tag r : Nat) : Program := (positiveProgram.column tag).column r

theorem inputColumn_primrec : Primrec₂ inputColumn :=
  (Program.column_primrec.comp (Program.column_primrec.comp (Primrec.const positiveProgram) Primrec.fst) Primrec.snd).to₂

theorem inputColumn_normal (r c : Nat) : (inputColumn 0 r).domain c ↔ Localization.Node r c := by
  simp [inputColumn, Program.column_domain, positiveProgram_domain, Nat.unpair_pair,
    positiveCheck, Bool.cond_true, SourceZeta.inputCheck_exact]

theorem inputColumn_raw (r c : Nat) : (inputColumn 1 r).domain c ↔
    ∃ a : Wilken.RelativeTerm Nat, c = (.theta 0 a).code ∧ check r (.theta 0 a) = true := by
  simp [inputColumn, Program.column_domain, positiveProgram_domain, Nat.unpair_pair,
    positiveCheck, Bool.cond_true, Bool.cond_false, SourceZeta.rawInputCheck_exact]

noncomputable def graphColumn (tag r c : Nat) : Program :=
  ((positiveProgram.column (tag + 2)).column r).column c

theorem graphColumn_primrec : Primrec (fun p : Nat × (Nat × Nat) => graphColumn p.1 p.2.1 p.2.2) := by
  have ht := Program.column_primrec.comp (Primrec.const positiveProgram)
    (Primrec.nat_add.comp Primrec.fst (Primrec.const 2))
  exact Program.column_primrec.comp
    (Program.column_primrec.comp ht (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)

theorem graphColumn_normal (r c d : Nat) : (graphColumn 0 r c).domain d ↔
    Localization.Node r c ∧ Canonical.check d = true ∧ unionInterpretation d = SourceZeta.sourceValue r c := by
  simp [graphColumn, Program.column_domain, positiveProgram_domain, Nat.unpair_pair,
    positiveCheck, Bool.cond_true, Bool.cond_false,
    SourceZeta.graph_exact, SourceZeta.inputCheck_exact]

theorem graphColumn_raw (r c d : Nat) : (graphColumn 1 r c).domain d ↔
    (∃ a : Wilken.RelativeTerm Nat, c = (.theta 0 a).code ∧ check r (.theta 0 a) = true) ∧
      Canonical.check d = true ∧ unionInterpretation d = SourceZeta.sourceValue r c := by
  simp [graphColumn, Program.column_domain, positiveProgram_domain, Nat.unpair_pair,
    positiveCheck, Bool.cond_true, Bool.cond_false,
    SourceZeta.rawGraph_exact, SourceZeta.rawInputCheck_exact]

theorem graphColumn_executed (tag r c d : Nat) (htag : tag = 0 ∨ tag = 1) :
    (graphColumn tag r c).domain d ↔ d ∈ (sourceColumn tag r).eval c := by
  rcases htag with rfl | rfl
  · rw [graphColumn_normal, sourceColumn_graph]
    simp [input, Bool.cond_true, SourceZeta.inputCheck_exact]
  · rw [graphColumn_raw, sourceColumn_graph]
    simp [input, Bool.cond_true, Bool.cond_false, SourceZeta.rawInputCheck_exact]

theorem graphColumn_unique (tag r c : Nat) (htag : tag = 0 ∨ tag = 1) (hc : input tag r c = true) :
    ∃! d, (graphColumn tag r c).domain d := by
  obtain ⟨d, hd, hu⟩ := sourceColumn_unique tag r c hc
  exact ⟨d, (graphColumn_executed tag r c d htag).mpr hd,
    fun e he => hu e ((graphColumn_executed tag r c e htag).mp he)⟩

end Alexander313.HereditarySourceZetaProgram
