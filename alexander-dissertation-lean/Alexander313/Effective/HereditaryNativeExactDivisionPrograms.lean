import Alexander313.Wilken.HereditaryNativeExactDivision

/-!
# Actual same-context native exact-division Programs

Tag 0 accepts the original raw low source domain; tag 1 additionally requires
weak-Normal inputs. Tag 2 is the real positive principal factor <= principal
dividend caller, whose quotient existence is derived. Every source domain
retains factor positivity and actual quotient existence. Unknown tags reject.

The producer executes the public certificate search and the genuine native
return. The positive complete-input Program executes this search too. The
complete numerical graph executes the chosen producer and checks its literal
answer, including zero; it is Partrec. No PR divisibility decision or search
bound is asserted. Finite guards and all actual compiler columns are PR.
All source candidates remain uncompiled.
-/

namespace Alexander313.HereditaryNativeExactDivisionProgram

open Wilken.RelativeTerm.Hereditary

abbrev Data := (Nat × Nat) × (Nat × Nat)

def normalInput (s c d : Nat) : Bool :=
  NativeContext.Comparison.acceptedCode (NativePublicBridge.contextCode s) c &&
    NativeContext.Comparison.acceptedCode (NativePublicBridge.contextCode s) d

theorem normalInput_primrec : Primrec
    (fun p : Nat × (Nat × Nat) => normalInput p.1 p.2.1 p.2.2) := by
  have hq := NativePublicBridge.contextCode_primrec.comp Primrec.fst
  exact Primrec.and.comp
    (NativeContext.Comparison.acceptedCode_primrec.comp hq (Primrec.fst.comp Primrec.snd))
    (NativeContext.Comparison.acceptedCode_primrec.comp hq (Primrec.snd.comp Primrec.snd))

/-- Only the finite original caller guard; complete divisibility is below. -/
def caller (tag s c d : Nat) : Bool := cond (tag == 0) (NativeContext.ExactDivision.callerCheck s c d)
  (cond (tag == 1) (NativeContext.ExactDivision.callerCheck s c d && normalInput s c d)
    (cond (tag == 2) (NativeContext.ExactDivision.principalCaller s c d) false))

theorem caller_primrec : Primrec (fun p : Data => caller p.1.1 p.1.2 p.2.1 p.2.2) := by
  have ht := Primrec.fst.comp Primrec.fst
  have hp := (Primrec.snd.comp Primrec.fst).pair Primrec.snd
  have hc := NativeContext.ExactDivision.callerCheck_primrec.comp hp
  exact (Primrec.beq.comp ht (Primrec.const 0)).cond hc
    ((Primrec.beq.comp ht (Primrec.const 1)).cond
      (Primrec.and.comp hc (normalInput_primrec.comp hp))
      ((Primrec.beq.comp ht (Primrec.const 2)).cond
        (NativeContext.ExactDivision.principalCaller_primrec.comp hp) (Primrec.const false)))

def SourceDomain (tag s c d : Nat) : Prop := caller tag s c d = true ∧
  NativeContext.ExactDivision.SourceDomain s c d

def data (query : Nat) : Data :=
  ((query.unpair.1, query.unpair.2.unpair.1),
    (query.unpair.2.unpair.2.unpair.1, query.unpair.2.unpair.2.unpair.2))

theorem data_primrec : Primrec data := by
  have ht := Primrec.unpair
  have hs := Primrec.unpair.comp (Primrec.snd.comp ht)
  have hp := Primrec.unpair.comp (Primrec.snd.comp hs)
  exact ((Primrec.fst.comp ht).pair (Primrec.fst.comp hs)).pair hp

def evaluation (query : Nat) : Part Nat :=
  let p := data query
  cond (caller p.1.1 p.1.2 p.2.1 p.2.2) (NativeContext.ExactDivision.divide p.1.2 p.2.1 p.2.2) Part.none

theorem evaluation_partrec : Partrec evaluation :=
  Partrec.cond (caller_primrec.comp data_primrec).to_comp
    (NativeContext.ExactDivision.divide_partrec.comp
      (((Primrec.snd.comp Primrec.fst).pair Primrec.snd).comp data_primrec).to_comp) Partrec.none

theorem evaluation_domain (tag s c d : Nat) :
    (evaluation (Nat.pair tag (Nat.pair s (Nat.pair c d)))).Dom ↔ SourceDomain tag s c d := by
  simp only [evaluation, data, Nat.unpair_pair]
  cases h : caller tag s c d <;> simp [h, SourceDomain, NativeContext.ExactDivision.divide_domain]

theorem evaluation_graph (tag s c d out : Nat) :
    out ∈ evaluation (Nat.pair tag (Nat.pair s (Nat.pair c d))) ↔
      caller tag s c d = true ∧ out ∈ NativeContext.ExactDivision.divide s c d := by
  simp only [evaluation, data, Nat.unpair_pair]
  cases h : caller tag s c d <;> simp [h]

theorem program_exists : ∃ p : Program, ∀ query, p.eval query = evaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp evaluation_partrec)

noncomputable def program : Program := Classical.choose program_exists

theorem program_eval (query : Nat) : program.eval query = evaluation query :=
  Classical.choose_spec program_exists query

noncomputable def sourceColumn (tag s c : Nat) : Program := ((program.column tag).column s).column c

theorem sourceColumn_primrec : Primrec (fun p : Nat × (Nat × Nat) => sourceColumn p.1 p.2.1 p.2.2) :=
  Program.column_primrec.comp
    (Program.column_primrec.comp (Program.column_primrec.comp (Primrec.const program) Primrec.fst)
      (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)

theorem sourceColumn_eval (tag s c d : Nat) : (sourceColumn tag s c).eval d =
    cond (caller tag s c d) (NativeContext.ExactDivision.divide s c d) Part.none := by
  simp only [sourceColumn, Nat.Partrec.Code.eval_curry, program_eval, evaluation, data, Nat.unpair_pair]

theorem sourceColumn_domain (tag s c d : Nat) : (sourceColumn tag s c).domain d ↔ SourceDomain tag s c d := by
  simp only [sourceColumn, Program.column_domain, Program.domain, program_eval]
  exact evaluation_domain tag s c d

theorem sourceColumn_graph (tag s c d out : Nat) : out ∈ (sourceColumn tag s c).eval d ↔
    caller tag s c d = true ∧ out ∈ NativeContext.ExactDivision.divide s c d := by
  simp only [sourceColumn, Nat.Partrec.Code.eval_curry, program_eval]
  exact evaluation_graph tag s c d out

theorem rawColumn_domain (s c d : Nat) : (sourceColumn 0 s c).domain d ↔
    NativeContext.ExactDivision.SourceDomain s c d := by
  rw [sourceColumn_domain]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨by simpa [caller] using NativeContext.ExactDivision.sourceDomain_caller s c d h, h⟩

theorem normalColumn_domain (s c d : Nat) : (sourceColumn 1 s c).domain d ↔
    normalInput s c d = true ∧ NativeContext.ExactDivision.SourceDomain s c d := by
  rw [sourceColumn_domain]
  constructor
  · intro h
    have hc : NativeContext.ExactDivision.callerCheck s c d && normalInput s c d = true :=
      by simpa [caller] using h.1
    exact ⟨(Bool.and_eq_true.mp hc).2, h.2⟩
  · rintro ⟨hn, h⟩
    exact ⟨by simp [caller, hn, NativeContext.ExactDivision.sourceDomain_caller s c d h], h⟩

/-- This finite principal caller has derived existence, without a supplied quotient. -/
theorem principalColumn_domain (s c d : Nat) : (sourceColumn 2 s c).domain d ↔
    NativeContext.ExactDivision.principalCaller s c d = true := by
  rw [sourceColumn_domain]
  constructor
  · intro h; simpa [caller] using h.1
  · intro h
    exact ⟨by simpa [caller] using h, NativeContext.ExactDivision.principalCaller_sourceDomain s c d h⟩

theorem unknownColumn_domain (tag s c d : Nat) (h0 : tag ≠ 0) (h1 : tag ≠ 1) (h2 : tag ≠ 2) :
    ¬(sourceColumn tag s c).domain d := by
  rw [sourceColumn_domain]
  simp [SourceDomain, caller, h0, h1, h2]

theorem sourceColumn_spec (tag s c d out : Nat) (ho : out ∈ (sourceColumn tag s c).eval d) :
    SourceDomain tag s c d ∧ NativeContext.LowArithmetic.lowInput s out = true ∧
      NativeContext.Comparison.acceptedCode (NativePublicBridge.contextCode s) out = true ∧
      NativeContext.interpretation (NativePublicBridge.contextCode s) c *
          NativeContext.interpretation (NativePublicBridge.contextCode s) out =
        NativeContext.interpretation (NativePublicBridge.contextCode s) d ∧
      NativeContext.interpretation (NativePublicBridge.contextCode s) out ≤
        NativeContext.interpretation (NativePublicBridge.contextCode s) d := by
  obtain ⟨hc, hm⟩ := (sourceColumn_graph tag s c d out).mp ho
  have hs := NativeContext.ExactDivision.divide_spec s c d out hm
  exact ⟨⟨hc, hs.1⟩, hs.2⟩

theorem sourceColumn_least (tag s c d out : Nat) (ho : out ∈ (sourceColumn tag s c).eval d) :
    ∀ δ : Ordinal.{0}, NativeContext.interpretation (NativePublicBridge.contextCode s) c * δ =
      NativeContext.interpretation (NativePublicBridge.contextCode s) d →
        NativeContext.interpretation (NativePublicBridge.contextCode s) out ≤ δ :=
  (NativeContext.ExactDivision.divide_least s c d out ((sourceColumn_graph tag s c d out).mp ho).2).2

theorem sourceColumn_unique (tag s c d : Nat) (h : SourceDomain tag s c d) :
    ∃! out, out ∈ (sourceColumn tag s c).eval d := by
  obtain ⟨out, ho, _⟩ := NativeContext.ExactDivision.divide_returns s c d h.2
  refine ⟨out, (sourceColumn_graph tag s c d out).mpr ⟨h.1, ho⟩, ?_⟩
  intro z hz
  exact Part.mem_unique hz ((sourceColumn_graph tag s c d out).mpr ⟨h.1, ho⟩)

/-- Recognition of the COMPLETE original source domain executes the real search. -/
def inputEvaluation (query : Nat) : Part Nat := (evaluation query).map (fun _ => 1)

theorem inputEvaluation_partrec : Partrec inputEvaluation :=
  Partrec.map evaluation_partrec (Computable.const 1).to₂

theorem inputProgram_exists : ∃ p : Program, ∀ query, p.eval query = inputEvaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp inputEvaluation_partrec)

noncomputable def inputProgram : Program := Classical.choose inputProgram_exists

theorem inputProgram_eval (query : Nat) : inputProgram.eval query = inputEvaluation query :=
  Classical.choose_spec inputProgram_exists query

noncomputable def inputColumn (tag s : Nat) : Program := (inputProgram.column tag).column s

theorem inputColumn_primrec : Primrec₂ inputColumn :=
  (Program.column_primrec.comp (Program.column_primrec.comp (Primrec.const inputProgram) Primrec.fst) Primrec.snd).to₂

theorem inputColumn_domain (tag s c d : Nat) : (inputColumn tag s).domain (Nat.pair c d) ↔ SourceDomain tag s c d := by
  simp only [inputColumn, Program.column_domain, Program.domain, inputProgram_eval, inputEvaluation]
  exact evaluation_domain tag s c d

theorem inputColumn_positive (tag s c d : Nat) :
    1 ∈ (inputColumn tag s).eval (Nat.pair c d) ↔ SourceDomain tag s c d := by
  simp only [inputColumn, Nat.Partrec.Code.eval_curry, inputProgram_eval, inputEvaluation]
  rw [Part.mem_map_iff]
  constructor
  · rintro ⟨out, ho, _⟩
    exact (evaluation_domain tag s c d).mp (Part.dom_iff_mem.mpr ⟨out, ho⟩)
  · intro h
    obtain ⟨out, ho⟩ := Part.dom_iff_mem.mp ((evaluation_domain tag s c d).mpr h)
    exact ⟨out, ho, rfl⟩

/-- The graph runs the source producer, preserving its actual selected spelling. -/
def graphEvaluation (query : Nat) : Part Nat :=
  (evaluation query.unpair.1).bind (fun out => cond (out == query.unpair.2) (Part.some 1) Part.none)

theorem graphEvaluation_partrec : Partrec graphEvaluation := by
  have hc : Primrec (fun p : Nat × Nat => p.2 == p.1.unpair.2) :=
    Primrec.beq.comp Primrec.snd ((Primrec.snd.comp Primrec.unpair).comp Primrec.fst)
  exact Partrec.bind (evaluation_partrec.comp (Primrec.fst.comp Primrec.unpair).to_comp)
    (Partrec.cond hc.to_comp (Computable.const 1).partrec Partrec.none).to₂

theorem graphEvaluation_domain (query out : Nat) :
    (graphEvaluation (Nat.pair query out)).Dom ↔ out ∈ evaluation query := by
  constructor
  · intro h
    obtain ⟨answer, ha⟩ := Part.dom_iff_mem.mp h
    have hm : answer ∈ (evaluation query).bind (fun v => cond (v == out) (Part.some 1) Part.none) :=
      by simpa only [graphEvaluation, Nat.unpair_pair] using ha
    obtain ⟨v, hv, hn⟩ := Part.mem_bind_iff.mp hm
    cases he : v == out with
    | false => simp only [he, Bool.cond_false, Part.notMem_none] at hn
    | true =>
      have hvo : v = out := beq_iff_eq.mp he
      exact hvo ▸ hv
  · intro h
    apply Part.dom_iff_mem.mpr
    refine ⟨1, ?_⟩
    simp only [graphEvaluation, Nat.unpair_pair]
    exact Part.mem_bind_iff.mpr ⟨out, h, by simp⟩

theorem graphProgram_exists : ∃ p : Program, ∀ query, p.eval query = graphEvaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp graphEvaluation_partrec)

noncomputable def graphProgram : Program := Classical.choose graphProgram_exists

theorem graphProgram_eval (query : Nat) : graphProgram.eval query = graphEvaluation query :=
  Classical.choose_spec graphProgram_exists query

noncomputable def graphColumn (tag s c d : Nat) : Program :=
  graphProgram.column (Nat.pair tag (Nat.pair s (Nat.pair c d)))

theorem graphColumn_primrec : Primrec (fun p : Data => graphColumn p.1.1 p.1.2 p.2.1 p.2.2) :=
  Program.column_primrec.comp (Primrec.const graphProgram)
    (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.fst)
      (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst)
        (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))))

theorem graphColumn_domain (tag s c d out : Nat) : (graphColumn tag s c d).domain out ↔
    out ∈ (sourceColumn tag s c).eval d := by
  simp only [graphColumn, Program.column_domain, Program.domain, graphProgram_eval, graphEvaluation_domain]
  simp only [sourceColumn, Nat.Partrec.Code.eval_curry, program_eval]

theorem graphColumn_unique (tag s c d : Nat) (h : SourceDomain tag s c d) :
    ∃! out, (graphColumn tag s c d).domain out := by
  obtain ⟨out, ho, hu⟩ := sourceColumn_unique tag s c d h
  exact ⟨out, (graphColumn_domain tag s c d out).mpr ho,
    fun z hz => hu z ((graphColumn_domain tag s c d z).mp hz)⟩

end Alexander313.HereditaryNativeExactDivisionProgram
