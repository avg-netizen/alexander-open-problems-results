import Alexander313.Wilken.HereditaryNativeSourceZeta

/-!
# Actual same-epsilon native zeta Programs and complete finite graphs

Tags zero and one execute the originally guarded normal and raw literal
native theta-zero producers at contextCode s. The actual public producer
and finite same-epsilon return supply original native low normal outputs.
Both complete numerical graphs, including zero, have genuine PR kernels.
Positive exact-domain and graph Programs and their PR compiler columns
specialize those real routines. Unknown tags reject. No arbitrary-base
conversion, PR logarithm search or spelling uniqueness is assumed.
All candidates remain uncompiled.
-/

namespace Alexander313.HereditaryNativeSourceZetaProgram

open Wilken.RelativeTerm.Hereditary

def input (tag s c : Nat) : Bool := cond (tag == 0) (NativeContext.SourceZeta.inputCheck s c)
  (cond (tag == 1) (NativeContext.SourceZeta.rawInputCheck s c) false)

theorem input_primrec : Primrec (fun p : Nat × (Nat × Nat) => input p.1 p.2.1 p.2.2) :=
  (Primrec.beq.comp Primrec.fst (Primrec.const 0)).cond
    (NativeContext.SourceZeta.inputCheck_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
    ((Primrec.beq.comp Primrec.fst (Primrec.const 1)).cond
      (NativeContext.SourceZeta.rawInputCheck_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
      (Primrec.const false))

theorem input_exact (tag s c : Nat) : input tag s c = true ↔
    (tag = 0 ∧ NativeContext.SourceZeta.inputCheck s c = true) ∨
      (tag = 1 ∧ NativeContext.SourceZeta.rawInputCheck s c = true) := by
  by_cases h0 : tag = 0
  · subst tag; simp [input]
  · by_cases h1 : tag = 1 <;> simp [input, h0, h1]

def evaluation (query : Nat) : Part Nat :=
  cond (query.unpair.1 == 0) (NativeContext.SourceZeta.zeta query.unpair.2.unpair.1 query.unpair.2.unpair.2)
    (cond (query.unpair.1 == 1) (NativeContext.SourceZeta.rawZeta query.unpair.2.unpair.1 query.unpair.2.unpair.2) Part.none)

theorem evaluation_partrec : Partrec evaluation := by
  have ht := Primrec.fst.comp Primrec.unpair
  have hp := Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)
  have hr := Primrec.fst.comp hp
  have hc := Primrec.snd.comp hp
  exact Partrec.cond (Primrec.beq.comp ht (Primrec.const 0)).to_comp
    (NativeContext.SourceZeta.zeta_partrec.comp hr.to_comp hc.to_comp)
    (Partrec.cond (Primrec.beq.comp ht (Primrec.const 1)).to_comp
      (NativeContext.SourceZeta.rawZeta_partrec.comp hr.to_comp hc.to_comp) Partrec.none)

theorem program_exists : ∃ p : Program, ∀ query, p.eval query = evaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp evaluation_partrec)

noncomputable def program : Program := Classical.choose program_exists

theorem program_eval (tag s c : Nat) : program.eval (Nat.pair tag (Nat.pair s c)) =
    cond (tag == 0) (NativeContext.SourceZeta.zeta s c) (cond (tag == 1) (NativeContext.SourceZeta.rawZeta s c) Part.none) := by
  simpa only [evaluation, Nat.unpair_pair] using
    Classical.choose_spec program_exists (Nat.pair tag (Nat.pair s c))

theorem program_domain (tag s c : Nat) : program.domain (Nat.pair tag (Nat.pair s c)) ↔ input tag s c = true := by
  rw [Program.domain, program_eval]
  by_cases h0 : tag = 0
  · subst tag; simp [input, NativeContext.SourceZeta.zeta_domain]
  · by_cases h1 : tag = 1 <;> simp [input, h0, h1, NativeContext.SourceZeta.rawZeta_domain, Part.not_none_dom]

def graphCheck (tag s c d : Nat) : Bool := cond (tag == 0) (NativeContext.SourceZeta.graph s c d)
  (cond (tag == 1) (NativeContext.SourceZeta.rawGraph s c d) false)

theorem graphCheck_primrec : Primrec (fun p : Nat × (Nat × (Nat × Nat)) => graphCheck p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  (Primrec.beq.comp Primrec.fst (Primrec.const 0)).cond
    (NativeContext.SourceZeta.graph_primrec.comp Primrec.snd)
    ((Primrec.beq.comp Primrec.fst (Primrec.const 1)).cond
      (NativeContext.SourceZeta.rawGraph_primrec.comp Primrec.snd) (Primrec.const false))

theorem program_graph (tag s c d : Nat) : d ∈ program.eval (Nat.pair tag (Nat.pair s c)) ↔
    graphCheck tag s c d = true := by
  rw [program_eval]
  by_cases h0 : tag = 0
  · subst tag; simp [graphCheck, NativeContext.SourceZeta.zeta_graph_iff]
  · by_cases h1 : tag = 1 <;> simp [graphCheck, h0, h1, NativeContext.SourceZeta.rawZeta_graph_iff, Part.notMem_none]

noncomputable def sourceColumn (tag s : Nat) : Program := (program.column tag).column s

theorem sourceColumn_primrec : Primrec₂ sourceColumn :=
  (Program.column_primrec.comp (Program.column_primrec.comp (Primrec.const program) Primrec.fst) Primrec.snd).to₂

theorem sourceColumn_eval (tag s c : Nat) : (sourceColumn tag s).eval c =
    cond (tag == 0) (NativeContext.SourceZeta.zeta s c) (cond (tag == 1) (NativeContext.SourceZeta.rawZeta s c) Part.none) := by
  simp only [sourceColumn, Nat.Partrec.Code.eval_curry, program_eval]

theorem sourceColumn_domain (tag s c : Nat) : (sourceColumn tag s).domain c ↔ input tag s c = true := by
  rw [sourceColumn, Program.column_domain, Program.column_domain]
  exact program_domain tag s c

theorem sourceColumn_graph (tag s c d : Nat) : d ∈ (sourceColumn tag s).eval c ↔ graphCheck tag s c d = true := by
  simp only [sourceColumn, Nat.Partrec.Code.eval_curry]
  exact program_graph tag s c d

theorem normalColumn_domain (s c : Nat) : (sourceColumn 0 s).domain c ↔ ∃ a : Wilken.RelativeTerm Nat, c = (.theta 0 a).code ∧
      NativeContext.check (NativePublicBridge.contextCode s) (.theta 0 a) = true ∧
      NativeContext.Comparison.Normal (NativePublicBridge.contextCode s) (.theta 0 a) := by
  simp [sourceColumn_domain, input, NativeContext.SourceZeta.inputCheck_exact]

theorem rawColumn_domain (s c : Nat) : (sourceColumn 1 s).domain c ↔
    ∃ a : Wilken.RelativeTerm Nat, c = (.theta 0 a).code ∧ NativeContext.check (NativePublicBridge.contextCode s) (.theta 0 a) = true := by
  simp [sourceColumn_domain, input, NativeContext.SourceZeta.rawInputCheck_exact]

theorem sourceColumn_spec (tag s c d : Nat) (hd : d ∈ (sourceColumn tag s).eval c) :
    input tag s c = true ∧ NativeContext.Comparison.acceptedCode (NativePublicBridge.contextCode s) d = true ∧
      NativeContext.lowCheckCode (NativePublicBridge.contextCode s) d = true ∧
      NativeContext.interpretation (NativePublicBridge.contextCode s) d = NativeContext.SourceZeta.sourceValue s c ∧ NativeContext.interpretation (NativePublicBridge.contextCode s) d < NativeContext.interpretation (NativePublicBridge.contextCode s) c := by
  rw [sourceColumn_eval] at hd
  by_cases h0 : tag = 0
  · subst tag
    have hs := NativeContext.SourceZeta.zeta_spec s c d (by simpa using hd)
    simpa [input] using hs
  · by_cases h1 : tag = 1
    · subst tag
      have hs := NativeContext.SourceZeta.rawZeta_spec s c d (by simpa using hd)
      simpa [input] using hs
    · simp [h0, h1, Part.notMem_none] at hd

theorem sourceColumn_original (tag s c d : Nat) (hd : d ∈ (sourceColumn tag s).eval c) :
    NativeContext.lowCheckCode (NativePublicBridge.contextCode s) d = true ∧
      NativeContext.Comparison.Normal (NativePublicBridge.contextCode s) (ThetaCourse.rawTree d) := by
  have hs := sourceColumn_spec tag s c d hd
  exact ⟨hs.2.2.1, ((NativeContext.Comparison.acceptedCode_exact _ _).mp hs.2.1).2⟩

theorem sourceColumn_unique (tag s c : Nat) (hc : input tag s c = true) :
    ∃! d, d ∈ (sourceColumn tag s).eval c := by
  obtain ⟨d, hd⟩ := Part.dom_iff_mem.mp ((sourceColumn_domain tag s c).mpr hc)
  exact ⟨d, hd, fun e he => Part.mem_unique he hd⟩

theorem normalColumn_invariant (s c v d e : Nat)
    (hd : d ∈ (sourceColumn 0 s).eval c) (he : e ∈ (sourceColumn 0 s).eval v)
    (hv : NativeContext.interpretation (NativePublicBridge.contextCode s) c = NativeContext.interpretation (NativePublicBridge.contextCode s) v) : d = e :=
  NativeContext.SourceZeta.zeta_output_invariant s c v d e (by simpa [sourceColumn_eval] using hd)
    (by simpa [sourceColumn_eval] using he) hv

theorem rawColumn_invariant (s c v d e : Nat)
    (hd : d ∈ (sourceColumn 1 s).eval c) (he : e ∈ (sourceColumn 1 s).eval v)
    (hv : NativeContext.interpretation (NativePublicBridge.contextCode s) c = NativeContext.interpretation (NativePublicBridge.contextCode s) v) : d = e :=
  NativeContext.SourceZeta.rawZeta_output_invariant s c v d e (by simpa [sourceColumn_eval] using hd)
    (by simpa [sourceColumn_eval] using he) hv

/-- Input tags 0/1 consume pair(s,c). Complete graph tags 2/3 consume
pair(s,pair(c,d)); all other tags reject. -/
def positiveCheck (tag payload : Nat) : Bool :=
  cond (tag == 0) (NativeContext.SourceZeta.inputCheck payload.unpair.1 payload.unpair.2)
    (cond (tag == 1) (NativeContext.SourceZeta.rawInputCheck payload.unpair.1 payload.unpair.2)
      (cond (tag == 2) (NativeContext.SourceZeta.graph payload.unpair.1 payload.unpair.2.unpair.1 payload.unpair.2.unpair.2)
        (cond (tag == 3) (NativeContext.SourceZeta.rawGraph payload.unpair.1 payload.unpair.2.unpair.1 payload.unpair.2.unpair.2) false)))

theorem positiveCheck_primrec : Primrec₂ positiveCheck := by
  have hp := Primrec.unpair.comp Primrec.snd
  have hg := (Primrec.fst.comp hp).pair (Primrec.unpair.comp (Primrec.snd.comp hp))
  have ht (k : Nat) := Primrec.beq.comp Primrec.fst (Primrec.const k)
  exact ((ht 0).cond (NativeContext.SourceZeta.inputCheck_primrec.comp (Primrec.fst.comp hp) (Primrec.snd.comp hp))
    ((ht 1).cond (NativeContext.SourceZeta.rawInputCheck_primrec.comp (Primrec.fst.comp hp) (Primrec.snd.comp hp))
      ((ht 2).cond (NativeContext.SourceZeta.graph_primrec.comp hg)
        ((ht 3).cond (NativeContext.SourceZeta.rawGraph_primrec.comp hg) (Primrec.const false))))).to₂

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

noncomputable def inputColumn (tag s : Nat) : Program := (positiveProgram.column tag).column s

theorem inputColumn_primrec : Primrec₂ inputColumn :=
  (Program.column_primrec.comp (Program.column_primrec.comp (Primrec.const positiveProgram) Primrec.fst) Primrec.snd).to₂

theorem inputColumn_normal (s c : Nat) : (inputColumn 0 s).domain c ↔ ∃ a : Wilken.RelativeTerm Nat, c = (.theta 0 a).code ∧
      NativeContext.check (NativePublicBridge.contextCode s) (.theta 0 a) = true ∧
      NativeContext.Comparison.Normal (NativePublicBridge.contextCode s) (.theta 0 a) := by
  simp [inputColumn, Program.column_domain, positiveProgram_domain, Nat.unpair_pair,
    positiveCheck, NativeContext.SourceZeta.inputCheck_exact]

theorem inputColumn_raw (s c : Nat) : (inputColumn 1 s).domain c ↔
    ∃ a : Wilken.RelativeTerm Nat, c = (.theta 0 a).code ∧ NativeContext.check (NativePublicBridge.contextCode s) (.theta 0 a) = true := by
  simp [inputColumn, Program.column_domain, positiveProgram_domain, Nat.unpair_pair,
    positiveCheck, NativeContext.SourceZeta.rawInputCheck_exact]

noncomputable def graphColumn (tag s c : Nat) : Program :=
  ((positiveProgram.column (tag + 2)).column s).column c

theorem graphColumn_primrec : Primrec (fun p : Nat × (Nat × Nat) => graphColumn p.1 p.2.1 p.2.2) := by
  have ht := Program.column_primrec.comp (Primrec.const positiveProgram)
    (Primrec.nat_add.comp Primrec.fst (Primrec.const 2))
  exact Program.column_primrec.comp
    (Program.column_primrec.comp ht (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)

theorem graphColumn_normal (s c d : Nat) : (graphColumn 0 s c).domain d ↔ NativeContext.SourceZeta.graph s c d = true := by
  simp [graphColumn, Program.column_domain, positiveProgram_domain, Nat.unpair_pair, positiveCheck]

theorem graphColumn_raw (s c d : Nat) : (graphColumn 1 s c).domain d ↔ NativeContext.SourceZeta.rawGraph s c d = true := by
  simp [graphColumn, Program.column_domain, positiveProgram_domain, Nat.unpair_pair, positiveCheck]

theorem graphColumn_executed (tag s c d : Nat) (htag : tag = 0 ∨ tag = 1) :
    (graphColumn tag s c).domain d ↔ d ∈ (sourceColumn tag s).eval c := by
  rcases htag with rfl | rfl
  · rw [graphColumn_normal, sourceColumn_graph]
    simp [graphCheck]
  · rw [graphColumn_raw, sourceColumn_graph]
    simp [graphCheck]

theorem graphColumn_spec (tag s c d : Nat) (htag : tag = 0 ∨ tag = 1)
    (hd : (graphColumn tag s c).domain d) :
    input tag s c = true ∧ NativeContext.lowCheckCode (NativePublicBridge.contextCode s) d = true ∧
      NativeContext.Comparison.Normal (NativePublicBridge.contextCode s) (ThetaCourse.rawTree d) ∧
      NativeContext.interpretation (NativePublicBridge.contextCode s) d = NativeContext.SourceZeta.sourceValue s c ∧ NativeContext.interpretation (NativePublicBridge.contextCode s) d < NativeContext.interpretation (NativePublicBridge.contextCode s) c := by
  have hm := (graphColumn_executed tag s c d htag).mp hd
  have hs := sourceColumn_spec tag s c d hm
  have hn := sourceColumn_original tag s c d hm
  exact ⟨hs.1, hn.1, hn.2, hs.2.2.2.1, hs.2.2.2.2⟩

theorem graphColumn_unique (tag s c : Nat) (htag : tag = 0 ∨ tag = 1) (hc : input tag s c = true) :
    ∃! d, (graphColumn tag s c).domain d := by
  obtain ⟨d, hd, hu⟩ := sourceColumn_unique tag s c hc
  exact ⟨d, (graphColumn_executed tag s c d htag).mpr hd,
    fun e he => hu e ((graphColumn_executed tag s c e htag).mp he)⟩

end Alexander313.HereditaryNativeSourceZetaProgram
