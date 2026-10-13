import Alexander313.Wilken.HereditaryNativeCanonicalHeight

/-!
# Executing native canonical VALUE-height Programs

Tag 0 computes canonical height by genuine normalization on every original
raw native input. Tag 1 reads the height of an original weak-normal input;
the value-invariance theorem identifies it with that canonical height.
Tags 2 and 3 return the actual high and low component heights on the same
original weak-normal domain. Constructed outputs are originally admitted
and normal, and their heights do not exceed the input's canonical height.

Complete numerical graphs include height zero. The positive fragment
Program recognizes existence of ANY original representation in fragment n,
using the real normalizer and finite height test. All kernels are PR; all
Programs and their compiler columns are constructed from those kernels.
No canonical source endpoint-height characterization or ordinal oracle is
assumed. All proof candidates remain uncompiled.
-/

namespace Alexander313.HereditaryNativeCanonicalHeightProgram

open Wilken.RelativeTerm.Hereditary.NativeContext

def input (tag q c : Nat) : Bool :=
  cond (tag == 0) (checkCode q c)
    (cond (tag == 1) (Comparison.acceptedCode q c)
      (cond (tag == 2) (Comparison.acceptedCode q c)
        (cond (tag == 3) (Comparison.acceptedCode q c) false)))

theorem input_primrec : Primrec (fun p : Nat × (Nat × Nat) => input p.1 p.2.1 p.2.2) := by
  have ht (k : Nat) := Primrec.beq.comp Primrec.fst (Primrec.const k)
  have hq := Primrec.fst.comp Primrec.snd
  have hc := Primrec.snd.comp Primrec.snd
  have hn := Comparison.acceptedCode_primrec.comp hq hc
  exact (ht 0).cond (checkCode_primrec.comp hq hc)
    ((ht 1).cond hn ((ht 2).cond hn ((ht 3).cond hn (Primrec.const false))))

theorem input_exact (tag q c : Nat) : input tag q c = true ↔
    (tag = 0 ∧ checkCode q c = true) ∨
      ((tag = 1 ∨ tag = 2 ∨ tag = 3) ∧ Comparison.acceptedCode q c = true) := by
  by_cases h0 : tag = 0
  · subst tag; simp [input]
  · by_cases h1 : tag = 1
    · subst tag; simp [input]
    · by_cases h2 : tag = 2
      · subst tag; simp [input]
      · by_cases h3 : tag = 3 <;> simp [input, h0, h1, h2, h3]

def outputCode (tag q m c : Nat) : Nat :=
  cond (tag == 0) (Normalization.normalizeCode q c)
    (cond (tag == 2) (Decomposition.highCode m c)
      (cond (tag == 3) (Decomposition.lowCode m c) c))

theorem outputCode_primrec : Primrec
    (fun p : Nat × (Nat × (Nat × Nat)) => outputCode p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have ht (k : Nat) := Primrec.beq.comp Primrec.fst (Primrec.const k)
  have hq := Primrec.fst.comp Primrec.snd
  have hm := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hc := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact (ht 0).cond (Normalization.Effective.normalizeCode_primrec.comp hq hc)
    ((ht 2).cond (Decomposition.highCode_primrec.comp hm hc)
      ((ht 3).cond (Decomposition.lowCode_primrec.comp hm hc) hc))

def answer (tag q m c : Nat) : Nat := Wilken.RelativeTerm.heightCode (outputCode tag q m c)

theorem answer_primrec : Primrec
    (fun p : Nat × (Nat × (Nat × Nat)) => answer p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  Wilken.RelativeTerm.heightCode_primrec.comp outputCode_primrec

theorem outputCode_spec (tag q m c : Nat) (hc : input tag q c = true) :
    Comparison.acceptedCode q (outputCode tag q m c) = true ∧
      answer tag q m c ≤ CanonicalHeight.canonicalHeightCode q c := by
  rcases (input_exact tag q c).mp hc with ⟨rfl, hc⟩ | ⟨h, hc⟩
  · have hs := Normalization.normalizeCode_accepted q c hc
    exact ⟨by simpa [outputCode] using hs.1, by simp [answer, outputCode, CanonicalHeight.canonicalHeightCode]⟩
  · have hd : Decomposition.inputCheck q c = true := hc
    have hh := CanonicalHeight.canonicalHeightCode_parts q m c hd
    have hs := Decomposition.parts_accepted q m c hd
    rcases h with rfl | rfl | rfl
    · exact ⟨by simpa [outputCode] using hc,
        by simpa [answer, outputCode, CanonicalHeight.canonicalHeightCode_normal q c hc]⟩
    · exact ⟨by simpa [outputCode] using hs.1,
        by simpa [answer, outputCode, CanonicalHeight.canonicalHeightCode_normal q _ hs.1] using hh.1⟩
    · exact ⟨by simpa [outputCode] using hs.2,
        by simpa [answer, outputCode, CanonicalHeight.canonicalHeightCode_normal q _ hs.2] using hh.2⟩

/-- The actual answer is the least fragment of the constructed output VALUE. -/
theorem answer_fragment_iff (tag q m c n : Nat) (hc : input tag q c = true) :
    answer tag q m c ≤ n ↔ ∃ t : Wilken.RelativeTerm Nat,
      admissible q n t ∧ denote q t = interpretation q (outputCode tag q m c) := by
  have hs := (Comparison.acceptedCode_exact q _).mp (outputCode_spec tag q m c hc).1
  change Wilken.RelativeTerm.heightCode (outputCode tag q m c) ≤ n ↔ _
  rw [← CanonicalHeight.canonicalHeightCode_normal q _ (outputCode_spec tag q m c hc).1]
  exact CanonicalHeight.canonicalHeightCode_fragment_iff q n _ hs.1

theorem raw_answer (q m c : Nat) : answer 0 q m c = CanonicalHeight.canonicalHeightCode q c := by
  simp [answer, outputCode, CanonicalHeight.canonicalHeightCode]

theorem raw_answer_zero_iff (q m c : Nat) (hc : checkCode q c = true) :
    answer 0 q m c = 0 ↔ interpretation q c < base q := by
  rw [raw_answer]
  exact CanonicalHeight.canonicalHeightCode_zero_iff_below_base q c hc

theorem raw_answer_invariant (q m c d : Nat) (hc : checkCode q c = true) (hd : checkCode q d = true)
    (hv : interpretation q c = interpretation q d) : answer 0 q m c = answer 0 q m d := by
  rw [raw_answer, raw_answer]
  exact CanonicalHeight.canonicalHeightCode_invariant q c d hc hd hv

theorem raw_answer_context (q v m c : Nat) (hq : checkCode q c = true) (hv : checkCode v c = true) :
    answer 0 q m c = answer 0 v m c := by
  rw [raw_answer, raw_answer]
  exact CanonicalHeight.canonicalHeightCode_context q v c hq hv

theorem normal_answer_invariant (tag q m c d : Nat)
    (hc : Comparison.acceptedCode q c = true) (hd : Comparison.acceptedCode q d = true)
    (hv : interpretation q c = interpretation q d) : answer tag q m c = answer tag q m d := by
  have hi := (Comparison.acceptedCode_exact q c).mp hc
  have hj := (Comparison.acceptedCode_exact q d).mp hd
  have hp := Decomposition.parts_values_invariant q m c d hc hd hv
  have hs := Decomposition.parts_accepted q m c hc
  have hr := Decomposition.parts_accepted q m d hd
  by_cases h0 : tag = 0
  · subst tag; exact raw_answer_invariant q m c d hi.1 hj.1 hv
  · by_cases h2 : tag = 2
    · subst tag
      simpa [answer, outputCode] using CanonicalHeight.normalCode_height_invariant q _ _ hs.1 hr.1 hp.1
    · by_cases h3 : tag = 3
      · subst tag
        simpa [answer, outputCode] using CanonicalHeight.normalCode_height_invariant q _ _ hs.2 hr.2 hp.2
      · simpa [answer, outputCode, h0, h2, h3] using
          CanonicalHeight.normalCode_height_invariant q c d hc hd hv

def evaluation (query : Nat) : Part Nat :=
  cond (input query.unpair.1 query.unpair.2.unpair.1 query.unpair.2.unpair.2.unpair.2)
    (Part.some (answer query.unpair.1 query.unpair.2.unpair.1
      query.unpair.2.unpair.2.unpair.1 query.unpair.2.unpair.2.unpair.2)) Part.none

theorem evaluation_partrec : Partrec evaluation := by
  have ht := Primrec.fst.comp Primrec.unpair
  have hp := Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)
  have hq := Primrec.fst.comp hp
  have hmc := Primrec.unpair.comp (Primrec.snd.comp hp)
  have hm := Primrec.fst.comp hmc
  have hc := Primrec.snd.comp hmc
  exact Partrec.cond (input_primrec.comp (ht.pair (hq.pair hc))).to_comp
    (answer_primrec.comp (ht.pair (hq.pair (hm.pair hc)))).to_comp.partrec Partrec.none

theorem program_exists : ∃ p : Program, ∀ query, p.eval query = evaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp evaluation_partrec)

noncomputable def program : Program := Classical.choose program_exists

theorem program_eval (tag q m c : Nat) :
    program.eval (Nat.pair tag (Nat.pair q (Nat.pair m c))) =
      cond (input tag q c) (Part.some (answer tag q m c)) Part.none := by
  simpa only [evaluation, Nat.unpair_pair] using
    Classical.choose_spec program_exists (Nat.pair tag (Nat.pair q (Nat.pair m c)))

theorem program_domain (tag q m c : Nat) :
    program.domain (Nat.pair tag (Nat.pair q (Nat.pair m c))) ↔ input tag q c = true := by
  rw [Program.domain, program_eval]
  cases h : input tag q c <;> simp [h]

theorem program_graph (tag q m c output : Nat) :
    output ∈ program.eval (Nat.pair tag (Nat.pair q (Nat.pair m c))) ↔
      input tag q c = true ∧ output = answer tag q m c := by
  rw [program_eval]
  cases h : input tag q c <;> simp [h]

noncomputable def sourceColumn (tag q m : Nat) : Program := ((program.column tag).column q).column m

theorem sourceColumn_primrec : Primrec (fun p : Nat × (Nat × Nat) => sourceColumn p.1 p.2.1 p.2.2) := by
  have ht := Program.column_primrec.comp (Primrec.const program) Primrec.fst
  exact Program.column_primrec.comp
    (Program.column_primrec.comp ht (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)

theorem sourceColumn_eval (tag q m c : Nat) : (sourceColumn tag q m).eval c =
    cond (input tag q c) (Part.some (answer tag q m c)) Part.none := by
  simp only [sourceColumn, Nat.Partrec.Code.eval_curry, program_eval]

theorem sourceColumn_domain (tag q m c : Nat) : (sourceColumn tag q m).domain c ↔ input tag q c = true := by
  rw [sourceColumn, Program.column_domain, Program.column_domain, Program.column_domain]
  exact program_domain tag q m c

theorem sourceColumn_graph (tag q m c output : Nat) : output ∈ (sourceColumn tag q m).eval c ↔
    input tag q c = true ∧ output = answer tag q m c := by
  simp only [sourceColumn, Nat.Partrec.Code.eval_curry]
  exact program_graph tag q m c output

theorem rawColumn_domain (q m c : Nat) : (sourceColumn 0 q m).domain c ↔ checkCode q c = true := by
  simp only [sourceColumn_domain, input, beq_self_eq_true, Bool.cond_true]

theorem rawColumn_zero_iff (q m c : Nat) : 0 ∈ (sourceColumn 0 q m).eval c ↔
    checkCode q c = true ∧ interpretation q c < base q := by
  rw [sourceColumn_graph]
  simp only [input, beq_self_eq_true, Bool.cond_true]
  constructor
  · rintro ⟨hc, hh⟩; exact ⟨hc, (raw_answer_zero_iff q m c hc).mp hh.symm⟩
  · rintro ⟨hc, hh⟩; exact ⟨hc, ((raw_answer_zero_iff q m c hc).mpr hh).symm⟩

theorem sourceColumn_minimal_fragment (tag q m c output n : Nat)
    (ho : output ∈ (sourceColumn tag q m).eval c) : output ≤ n ↔
    ∃ t : Wilken.RelativeTerm Nat, admissible q n t ∧
      denote q t = interpretation q (outputCode tag q m c) := by
  obtain ⟨hc, rfl⟩ := (sourceColumn_graph tag q m c output).mp ho
  exact answer_fragment_iff tag q m c n hc

theorem sourceColumn_bound (tag q m c output : Nat) (ho : output ∈ (sourceColumn tag q m).eval c) :
    output ≤ CanonicalHeight.canonicalHeightCode q c := by
  obtain ⟨hc, rfl⟩ := (sourceColumn_graph tag q m c output).mp ho
  exact (outputCode_spec tag q m c hc).2

/-- The finite complete graph tests the actual chosen numeral, including zero. -/
def graphCheck (tag q m c output : Nat) : Bool := input tag q c && (output == answer tag q m c)

theorem graphCheck_primrec : Primrec
    (fun p : (Nat × (Nat × (Nat × Nat))) × Nat => graphCheck p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2) := by
  have ht := Primrec.fst.comp Primrec.fst
  have hq := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hc := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  exact Primrec.and.comp (input_primrec.comp (ht.pair (hq.pair hc)))
    (Primrec.beq.comp Primrec.snd (answer_primrec.comp Primrec.fst))

def graphEvaluation (query : Nat) : Part Nat :=
  let source := query.unpair.1
  cond (graphCheck source.unpair.1 source.unpair.2.unpair.1
    source.unpair.2.unpair.2.unpair.1 source.unpair.2.unpair.2.unpair.2 query.unpair.2)
    (Part.some 0) Part.none

theorem graphEvaluation_partrec : Partrec graphEvaluation := by
  have hs := Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)
  have hp := Primrec.unpair.comp (Primrec.snd.comp hs)
  have hmc := Primrec.unpair.comp (Primrec.snd.comp hp)
  have hsource := (Primrec.fst.comp hs).pair ((Primrec.fst.comp hp).pair hmc)
  have hg := graphCheck_primrec.comp (hsource.pair (Primrec.snd.comp Primrec.unpair))
  exact Partrec.cond hg.to_comp (Computable.const 0).partrec Partrec.none

theorem graphProgram_exists : ∃ p : Program, ∀ query, p.eval query = graphEvaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp graphEvaluation_partrec)

noncomputable def graphProgram : Program := Classical.choose graphProgram_exists

theorem graphProgram_domain (tag q m c output : Nat) :
    graphProgram.domain (Nat.pair (Nat.pair tag (Nat.pair q (Nat.pair m c))) output) ↔
      input tag q c = true ∧ output = answer tag q m c := by
  rw [Program.domain, Classical.choose_spec graphProgram_exists]
  simp only [graphEvaluation, Nat.unpair_pair, graphCheck]
  cases hi : input tag q c <;> cases ho : output == answer tag q m c <;>
    simp [hi, ho, ← beq_iff_eq]

noncomputable def graphColumn (tag q m c : Nat) : Program :=
  graphProgram.column (Nat.pair tag (Nat.pair q (Nat.pair m c)))

theorem graphColumn_primrec : Primrec
    (fun p : Nat × (Nat × (Nat × Nat)) => graphColumn p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  Program.column_primrec.comp (Primrec.const graphProgram) (Primrec₂.natPair.comp Primrec.fst
    (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd)
      (Primrec₂.natPair.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))

theorem graphColumn_domain (tag q m c output : Nat) : (graphColumn tag q m c).domain output ↔
    input tag q c = true ∧ output = answer tag q m c := by
  rw [graphColumn, Program.column_domain]
  exact graphProgram_domain tag q m c output

theorem graphColumn_executed (tag q m c output : Nat) : (graphColumn tag q m c).domain output ↔
    output ∈ (sourceColumn tag q m).eval c := by
  rw [graphColumn_domain, sourceColumn_graph]

theorem graphColumn_unique (tag q m c : Nat) (hc : input tag q c = true) :
    ∃! output, (graphColumn tag q m c).domain output := by
  refine ⟨answer tag q m c, (graphColumn_domain tag q m c _).mpr ⟨hc, rfl⟩, ?_⟩
  intro output ho
  exact ((graphColumn_domain tag q m c output).mp ho).2

def fragmentEvaluation (query : Nat) : Part Nat :=
  cond (CanonicalHeight.canonicalFragmentCheck query.unpair.1 query.unpair.2.unpair.1 query.unpair.2.unpair.2)
    (Part.some 0) Part.none

theorem fragmentEvaluation_partrec : Partrec fragmentEvaluation := by
  have hp := Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)
  have h := CanonicalHeight.canonicalFragmentCheck_primrec.comp
    (((Primrec.fst.comp Primrec.unpair).pair (Primrec.fst.comp hp)).pair (Primrec.snd.comp hp))
  exact Partrec.cond h.to_comp (Computable.const 0).partrec Partrec.none

theorem fragmentProgram_exists : ∃ p : Program, ∀ query, p.eval query = fragmentEvaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp fragmentEvaluation_partrec)

noncomputable def fragmentProgram : Program := Classical.choose fragmentProgram_exists

theorem fragmentProgram_domain (q n c : Nat) : fragmentProgram.domain (Nat.pair q (Nat.pair n c)) ↔
    checkCode q c = true ∧ ∃ t : Wilken.RelativeTerm Nat,
      admissible q n t ∧ denote q t = interpretation q c := by
  rw [Program.domain, Classical.choose_spec fragmentProgram_exists]
  simp only [fragmentEvaluation, Nat.unpair_pair]
  have he := CanonicalHeight.canonicalFragmentCheck_exact q n c
  cases h : CanonicalHeight.canonicalFragmentCheck q n c <;> simp_all

noncomputable def fragmentColumn (q n : Nat) : Program := (fragmentProgram.column q).column n

theorem fragmentColumn_primrec : Primrec₂ fragmentColumn :=
  (Program.column_primrec.comp
    (Program.column_primrec.comp (Primrec.const fragmentProgram) Primrec.fst) Primrec.snd).to₂

theorem fragmentColumn_domain (q n c : Nat) : (fragmentColumn q n).domain c ↔
    checkCode q c = true ∧ ∃ t : Wilken.RelativeTerm Nat,
      admissible q n t ∧ denote q t = interpretation q c := by
  rw [fragmentColumn, Program.column_domain, Program.column_domain]
  exact fragmentProgram_domain q n c

theorem fragmentColumn_invariant (q n c d : Nat) (hc : checkCode q c = true) (hd : checkCode q d = true)
    (hv : interpretation q c = interpretation q d) :
    (fragmentColumn q n).domain c ↔ (fragmentColumn q n).domain d := by
  rw [fragmentColumn_domain, fragmentColumn_domain, ← CanonicalHeight.canonicalFragmentCheck_exact,
    ← CanonicalHeight.canonicalFragmentCheck_exact, CanonicalHeight.canonicalFragmentCheck_invariant q n c d hc hd hv]

theorem fragmentColumn_context (q v n c : Nat) (hq : checkCode q c = true) (hv : checkCode v c = true) :
    (fragmentColumn q n).domain c ↔ (fragmentColumn v n).domain c := by
  rw [fragmentColumn_domain, fragmentColumn_domain, ← CanonicalHeight.canonicalFragmentCheck_exact,
    ← CanonicalHeight.canonicalFragmentCheck_exact, CanonicalHeight.canonicalFragmentCheck_context q v n c hq hv]

end Alexander313.HereditaryNativeCanonicalHeightProgram
