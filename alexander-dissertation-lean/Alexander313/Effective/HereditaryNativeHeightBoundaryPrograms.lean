import Alexander313.Wilken.HereditaryNativeHeightBoundary

/-!
# Executing actual source endpoint and height Programs

Every source tag retains the ORIGINAL native low parser, including the
original coded-epsilon base guard. Tag 0 computes the least actual source
endpoint index. Tag 1 returns the complete 0/1 decision for value below
endpoint n; tag 2 decides the exact canonical height n. The last two tags
execute finite PR predicates whose actual ordinal meanings were proved
from genuine finite source coverage, not supplied by a semantic oracle.

The source Program, complete numerical graph (including output zero),
positive recognizers, and uniform compiler columns are constructed from
these genuine PR kernels. Unknown tags are rejected. All candidates
remain uncompiled.
-/

namespace Alexander313.HereditaryNativeHeightBoundaryProgram

open Wilken.RelativeTerm.Hereditary.NativeContext

def input (tag q c : Nat) : Bool :=
  ((tag == 0) || (tag == 1) || (tag == 2)) && lowCheckCode q c

theorem input_primrec : Primrec (fun p : Nat × (Nat × Nat) => input p.1 p.2.1 p.2.2) := by
  have ht (k : Nat) := Primrec.beq.comp Primrec.fst (Primrec.const k)
  exact Primrec.and.comp (Primrec.or.comp (Primrec.or.comp (ht 0) (ht 1)) (ht 2))
    (lowCheckCode_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))

theorem input_exact (tag q c : Nat) : input tag q c = true ↔
    (tag = 0 ∨ tag = 1 ∨ tag = 2) ∧ lowCheckCode q c = true := by
  simp only [input, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, or_assoc]

def answer (tag q n c : Nat) : Nat :=
  cond (tag == 0) (CanonicalHeight.canonicalHeightCode q c)
    (cond (tag == 1) (cond (HeightBoundary.belowEndpointCheck q n c) 1 0)
      (cond (HeightBoundary.exactHeightCheck q n c) 1 0))

theorem answer_primrec : Primrec
    (fun p : Nat × (Nat × (Nat × Nat)) => answer p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hq := Primrec.fst.comp Primrec.snd
  have hn := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hc := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hp := (hq.pair hn).pair hc
  have hb := (HeightBoundary.belowEndpointCheck_primrec.comp hp).cond (Primrec.const 1) (Primrec.const 0)
  have he := (HeightBoundary.exactHeightCheck_primrec.comp hp).cond (Primrec.const 1) (Primrec.const 0)
  exact (Primrec.beq.comp Primrec.fst (Primrec.const 0)).cond
    (CanonicalHeight.canonicalHeightCode_primrec.comp hq hc)
    ((Primrec.beq.comp Primrec.fst (Primrec.const 1)).cond hb he)

theorem answer_height (q n c : Nat) : answer 0 q n c = CanonicalHeight.canonicalHeightCode q c := by
  simp [answer]

theorem answer_height_source (q n c : Nat) (hc : lowCheckCode q c = true) :
    IsLeast {m : Nat | interpretation q c < HeightBoundary.endpoint q m} (answer 0 q n c) := by
  rw [answer_height]
  exact HeightBoundary.source_lemma_2_22 q c hc

theorem answer_endpoint_one_iff (q n c : Nat) : answer 1 q n c = 1 ↔
    lowCheckCode q c = true ∧ interpretation q c < HeightBoundary.endpoint q n := by
  change cond (HeightBoundary.belowEndpointCheck q n c) 1 0 = 1 ↔ _
  rw [← HeightBoundary.belowEndpointCheck_exact q n c]
  cases HeightBoundary.belowEndpointCheck q n c <;> decide

theorem answer_exact_one_iff (q n c : Nat) : answer 2 q n c = 1 ↔
    lowCheckCode q c = true ∧ CanonicalHeight.canonicalHeightCode q c = n := by
  change cond (HeightBoundary.exactHeightCheck q n c) 1 0 = 1 ↔ _
  have he : HeightBoundary.exactHeightCheck q n c = true ↔
      lowCheckCode q c = true ∧ CanonicalHeight.canonicalHeightCode q c = n := by
    simp only [HeightBoundary.exactHeightCheck, Bool.and_eq_true, beq_iff_eq]
  rw [← he]
  cases HeightBoundary.exactHeightCheck q n c <;> decide

theorem answer_endpoint_bool (q n c : Nat) : answer 1 q n c = 0 ∨ answer 1 q n c = 1 := by
  cases h : HeightBoundary.belowEndpointCheck q n c <;> simp [answer, h]

theorem answer_exact_bool (q n c : Nat) : answer 2 q n c = 0 ∨ answer 2 q n c = 1 := by
  cases h : HeightBoundary.exactHeightCheck q n c <;> simp [answer, h]

theorem answer_endpoint_zero_iff (q n c : Nat) (hc : lowCheckCode q c = true) :
    answer 1 q n c = 0 ↔ HeightBoundary.endpoint q n ≤ interpretation q c := by
  have h1 := answer_endpoint_one_iff q n c
  rcases answer_endpoint_bool q n c with h0 | h0
  · constructor
    · intro _
      exact le_of_not_gt (fun hv => by have hbad := h1.mpr ⟨hc, hv⟩; omega)
    · intro _; exact h0
  · constructor
    · intro hz; omega
    · intro hv
      exact False.elim (((h1.mp h0).2).not_ge hv)

theorem answer_invariant (tag q n c d : Nat) (hc : lowCheckCode q c = true)
    (hd : lowCheckCode q d = true) (hv : interpretation q c = interpretation q d) :
    answer tag q n c = answer tag q n d := by
  simp only [answer, CanonicalHeight.canonicalHeightCode_invariant q c d
    (HeightBoundary.input_spec q c hc).1 (HeightBoundary.input_spec q d hd).1 hv,
    HeightBoundary.belowEndpointCheck_invariant q n c d hc hd hv,
    HeightBoundary.exactHeightCheck_invariant q n c d hc hd hv]

def evaluation (query : Nat) : Part Nat :=
  cond (input query.unpair.1 query.unpair.2.unpair.1 query.unpair.2.unpair.2.unpair.2)
    (Part.some (answer query.unpair.1 query.unpair.2.unpair.1
      query.unpair.2.unpair.2.unpair.1 query.unpair.2.unpair.2.unpair.2)) Part.none

theorem evaluation_partrec : Partrec evaluation := by
  have ht := Primrec.fst.comp Primrec.unpair
  have hp := Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)
  have hq := Primrec.fst.comp hp
  have hnc := Primrec.unpair.comp (Primrec.snd.comp hp)
  have hn := Primrec.fst.comp hnc
  have hc := Primrec.snd.comp hnc
  exact Partrec.cond (input_primrec.comp (ht.pair (hq.pair hc))).to_comp
    (answer_primrec.comp (ht.pair (hq.pair (hn.pair hc)))).to_comp.partrec Partrec.none

theorem program_exists : ∃ p : Program, ∀ query, p.eval query = evaluation query := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp evaluation_partrec)
  exact ⟨p, fun query => congrFun hp query⟩

noncomputable def program : Program := Classical.choose program_exists

theorem program_eval (tag q n c : Nat) :
    program.eval (Nat.pair tag (Nat.pair q (Nat.pair n c))) =
      cond (input tag q c) (Part.some (answer tag q n c)) Part.none := by
  simpa only [evaluation, Nat.unpair_pair] using
    Classical.choose_spec program_exists (Nat.pair tag (Nat.pair q (Nat.pair n c)))

theorem program_domain (tag q n c : Nat) :
    program.domain (Nat.pair tag (Nat.pair q (Nat.pair n c))) ↔
      (tag = 0 ∨ tag = 1 ∨ tag = 2) ∧ lowCheckCode q c = true := by
  rw [Program.domain, program_eval, ← input_exact]
  cases h : input tag q c <;> simp [h]

theorem program_graph (tag q n c output : Nat) :
    output ∈ program.eval (Nat.pair tag (Nat.pair q (Nat.pair n c))) ↔
      input tag q c = true ∧ output = answer tag q n c := by
  rw [program_eval]
  cases h : input tag q c <;> simp [h]

noncomputable def sourceColumn (tag q n : Nat) : Program := ((program.column tag).column q).column n

theorem sourceColumn_primrec : Primrec (fun p : Nat × (Nat × Nat) => sourceColumn p.1 p.2.1 p.2.2) := by
  have ht := Program.column_primrec.comp (Primrec.const program) Primrec.fst
  exact Program.column_primrec.comp
    (Program.column_primrec.comp ht (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)

theorem sourceColumn_eval (tag q n c : Nat) : (sourceColumn tag q n).eval c =
    cond (input tag q c) (Part.some (answer tag q n c)) Part.none := by
  simp only [sourceColumn, Nat.Partrec.Code.eval_curry, program_eval]

theorem sourceColumn_domain (tag q n c : Nat) : (sourceColumn tag q n).domain c ↔
    (tag = 0 ∨ tag = 1 ∨ tag = 2) ∧ lowCheckCode q c = true := by
  rw [sourceColumn, Program.column_domain, Program.column_domain, Program.column_domain]
  exact program_domain tag q n c

theorem sourceColumn_graph (tag q n c output : Nat) : output ∈ (sourceColumn tag q n).eval c ↔
    input tag q c = true ∧ output = answer tag q n c := by
  simp only [sourceColumn, Nat.Partrec.Code.eval_curry]
  exact program_graph tag q n c output

theorem heightColumn_source (q n c output : Nat) (ho : output ∈ (sourceColumn 0 q n).eval c) :
    IsLeast {m : Nat | interpretation q c < HeightBoundary.endpoint q m} output := by
  obtain ⟨hc, rfl⟩ := (sourceColumn_graph 0 q n c output).mp ho
  exact answer_height_source q n c ((input_exact 0 q c).mp hc).2

theorem endpointColumn_one_iff (q n c : Nat) : 1 ∈ (sourceColumn 1 q n).eval c ↔
    lowCheckCode q c = true ∧ interpretation q c < HeightBoundary.endpoint q n := by
  rw [sourceColumn_graph]
  constructor
  · rintro ⟨_, hv⟩; exact (answer_endpoint_one_iff q n c).mp hv.symm
  · intro hv
    exact ⟨(input_exact 1 q c).mpr ⟨Or.inr (Or.inl rfl), hv.1⟩,
      ((answer_endpoint_one_iff q n c).mpr hv).symm⟩

theorem exactColumn_succ_one_iff (q n c : Nat) : 1 ∈ (sourceColumn 2 q (n + 1)).eval c ↔
    lowCheckCode q c = true ∧ HeightBoundary.endpoint q n ≤ interpretation q c ∧
      interpretation q c < HeightBoundary.endpoint q (n + 1) := by
  rw [sourceColumn_graph]
  constructor
  · rintro ⟨hc, hv⟩
    have hh := (answer_exact_one_iff q (n + 1) c).mp hv.symm
    exact ⟨hh.1, (HeightBoundary.canonicalHeightCode_eq_succ_iff_strip q n c hh.1).mp hh.2⟩
  · rintro ⟨hc, hs⟩
    have hh := (HeightBoundary.canonicalHeightCode_eq_succ_iff_strip q n c hc).mpr hs
    exact ⟨(input_exact 2 q c).mpr ⟨Or.inr (Or.inr rfl), hc⟩,
      ((answer_exact_one_iff q (n + 1) c).mpr ⟨hc, hh⟩).symm⟩

/-- This complete graph checks the exact emitted numeral, including 0. -/
def graphCheck (tag q n c output : Nat) : Bool := input tag q c && (output == answer tag q n c)

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
  have hnc := Primrec.unpair.comp (Primrec.snd.comp hp)
  have hsource := (Primrec.fst.comp hs).pair ((Primrec.fst.comp hp).pair hnc)
  have hg := graphCheck_primrec.comp (hsource.pair (Primrec.snd.comp Primrec.unpair))
  exact Partrec.cond hg.to_comp (Computable.const 0).partrec Partrec.none

theorem graphProgram_exists : ∃ p : Program, ∀ query, p.eval query = graphEvaluation query := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp graphEvaluation_partrec)
  exact ⟨p, fun query => congrFun hp query⟩

noncomputable def graphProgram : Program := Classical.choose graphProgram_exists

theorem graphProgram_domain (tag q n c output : Nat) :
    graphProgram.domain (Nat.pair (Nat.pair tag (Nat.pair q (Nat.pair n c))) output) ↔
      input tag q c = true ∧ output = answer tag q n c := by
  rw [Program.domain, Classical.choose_spec graphProgram_exists]
  simp only [graphEvaluation, Nat.unpair_pair, graphCheck]
  cases hi : input tag q c <;> cases ho : output == answer tag q n c <;>
    simp [hi, ho, ← beq_iff_eq]

noncomputable def graphColumn (tag q n c : Nat) : Program :=
  graphProgram.column (Nat.pair tag (Nat.pair q (Nat.pair n c)))

theorem graphColumn_primrec : Primrec
    (fun p : Nat × (Nat × (Nat × Nat)) => graphColumn p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hp := Primrec₂.natPair.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hq := Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd) hp
  exact Program.column_primrec.comp (Primrec.const graphProgram)
    (Primrec₂.natPair.comp Primrec.fst hq)

theorem graphColumn_domain (tag q n c output : Nat) : (graphColumn tag q n c).domain output ↔
    input tag q c = true ∧ output = answer tag q n c := by
  rw [graphColumn, Program.column_domain]
  exact graphProgram_domain tag q n c output

end Alexander313.HereditaryNativeHeightBoundaryProgram
