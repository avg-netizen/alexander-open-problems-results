import Alexander313.Wilken.HereditaryLogEnd

/-!
# Actual component and first/last logarithm Programs

A total Program executes the real PR head/end selection. A separate partial
Program executes original admission, the explicit zero branch and the genuine
principal logarithm. Its first/last columns halt exactly on all original
admitted union inputs, with canonical output and literal source CNF semantics.
Positive graph kernels retain original admission and unique canonical output.
Their column maps are genuinely PR instances of the existing s-m-n compiler.
No arithmetic Program, output semantics or halting oracle is assumed.
All terms remain uncompiled; the inherited rfind output signature has been
verified against the exact pinned local Mathlib source.
-/

namespace Alexander313.HereditaryLogEndProgram

open Wilken.RelativeTerm.Hereditary

def componentEvaluation (query : Nat) : Part Nat :=
  Part.some (LogEnd.componentCode (query.unpair.1 == 1) query.unpair.2)

theorem componentEvaluation_partrec : Partrec componentEvaluation :=
  (LogEnd.componentCode_primrec.comp
    (Primrec.beq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 1))
    (Primrec.snd.comp Primrec.unpair)).to_comp.partrec

theorem componentProgram_exists : ∃ p : Program, ∀ query, p.eval query = componentEvaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp componentEvaluation_partrec)

noncomputable def componentProgram : Program := Classical.choose componentProgram_exists

theorem componentProgram_eval (query : Nat) : componentProgram.eval query = componentEvaluation query :=
  Classical.choose_spec componentProgram_exists query

noncomputable def componentColumn (tag : Nat) : Program := componentProgram.column tag

theorem componentColumn_primrec : Primrec componentColumn :=
  Program.column_primrec.comp (Primrec.const componentProgram) Primrec.id

theorem componentColumn_eval (tag q : Nat) :
    (componentColumn tag).eval q = Part.some (LogEnd.componentCode (tag == 1) q) := by
  simp only [componentColumn, Program.column, Nat.Partrec.Code.eval_curry, componentProgram_eval,
    componentEvaluation, Nat.unpair_pair]

theorem componentColumn_total (tag q : Nat) : (componentColumn tag).domain q := by
  change ((componentColumn tag).eval q).Dom
  rw [componentColumn_eval]
  trivial

theorem componentColumn_original (tag q : Nat) (hq : unionCheck q = true) :
    Canonical.check (LogEnd.componentCode (tag == 1) q) = true ∧
      unionCheck (LogEnd.componentCode (tag == 1) q) = true ∧
      Theta.Normal (LogEnd.componentCode (tag == 1) q).unpair.1
        (ThetaCourse.rawTree (LogEnd.componentCode (tag == 1) q).unpair.2) ∧
      unionInterpretation (LogEnd.componentCode (tag == 1) q) = LogEnd.componentValue (tag == 1) (unionInterpretation q) :=
  ⟨LogEnd.componentCode_checked _ q hq, LogEnd.componentCode_original _ q hq,
    LogEnd.componentCode_normal _ q hq, LogEnd.componentCode_value _ q hq⟩

def logarithmEvaluation (query : Nat) : Part Nat :=
  LogEnd.componentLog (query.unpair.1 == 1) query.unpair.2

theorem logarithmEvaluation_partrec : Partrec logarithmEvaluation :=
  LogEnd.componentLog_partrec.comp
    (Primrec.beq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 1)).to_comp
    (Primrec.snd.comp Primrec.unpair).to_comp

theorem logarithmProgram_exists : ∃ p : Program, ∀ query, p.eval query = logarithmEvaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp logarithmEvaluation_partrec)

noncomputable def logarithmProgram : Program := Classical.choose logarithmProgram_exists

theorem logarithmProgram_eval (query : Nat) : logarithmProgram.eval query = logarithmEvaluation query :=
  Classical.choose_spec logarithmProgram_exists query

noncomputable def logarithmColumn (tag : Nat) : Program := logarithmProgram.column tag

theorem logarithmColumn_primrec : Primrec logarithmColumn :=
  Program.column_primrec.comp (Primrec.const logarithmProgram) Primrec.id

theorem logarithmColumn_eval (tag q : Nat) :
    (logarithmColumn tag).eval q = LogEnd.componentLog (tag == 1) q := by
  simp only [logarithmColumn, Program.column, Nat.Partrec.Code.eval_curry, logarithmProgram_eval,
    logarithmEvaluation, Nat.unpair_pair]

theorem logarithmColumn_domain (tag q : Nat) : (logarithmColumn tag).domain q ↔ unionCheck q = true := by
  simp only [Program.domain, logarithmColumn_eval, LogEnd.componentLog_domain]

theorem logarithmColumn_original (tag q c : Nat) (hc : c ∈ (logarithmColumn tag).eval q) :
    unionCheck q = true ∧ Canonical.check c = true ∧
      LogEnd.SourceLogSpec (tag == 1) (unionInterpretation q) (unionInterpretation c) := by
  rw [logarithmColumn_eval] at hc
  exact LogEnd.componentLog_value _ q c hc

theorem logarithmColumn_output_original (tag q c : Nat) (hc : c ∈ (logarithmColumn tag).eval q) :
    unionCheck c = true ∧ Theta.Normal c.unpair.1 (ThetaCourse.rawTree c.unpair.2) := by
  rw [logarithmColumn_eval] at hc
  exact LogEnd.componentLog_original _ q c hc

theorem logarithmColumn_returns (tag q : Nat) (hq : unionCheck q = true) :
    ∃ c : Nat, c ∈ (logarithmColumn tag).eval q ∧ Canonical.check c = true ∧
      LogEnd.SourceLogSpec (tag == 1) (unionInterpretation q) (unionInterpretation c) := by
  rw [logarithmColumn_eval]
  exact LogEnd.componentLog_returns _ q hq

theorem logarithmColumn_output_invariant (tag q v c d : Nat)
    (hc : c ∈ (logarithmColumn tag).eval q) (hd : d ∈ (logarithmColumn tag).eval v)
    (he : unionInterpretation q = unionInterpretation v) : c = d := by
  rw [logarithmColumn_eval] at hc hd
  exact LogEnd.componentLog_output_invariant _ q v c d hc hd he

noncomputable def leadingLogProgram : Program := logarithmColumn 0

noncomputable def logendProgram : Program := logarithmColumn 1

theorem leadingLogProgram_eval (q : Nat) : leadingLogProgram.eval q = LogEnd.leadingLog q := by
  simpa only [leadingLogProgram, LogEnd.leadingLog] using logarithmColumn_eval 0 q

theorem logendProgram_eval (q : Nat) : logendProgram.eval q = LogEnd.logend q := by
  simpa only [logendProgram, LogEnd.logend] using logarithmColumn_eval 1 q

theorem leadingLogProgram_domain (q : Nat) : leadingLogProgram.domain q ↔ unionCheck q = true :=
  logarithmColumn_domain 0 q

theorem logendProgram_domain (q : Nat) : logendProgram.domain q ↔ unionCheck q = true :=
  logarithmColumn_domain 1 q

theorem leadingLogProgram_power (q c : Nat) (hc : c ∈ leadingLogProgram.eval q)
    (hp : 0 < unionInterpretation q) : Ordinal.omega0 ^ unionInterpretation c = unionInterpretation (LogEnd.mcCode q) := by
  rw [leadingLogProgram_eval] at hc
  exact LogEnd.leadingLog_power q c hc hp

theorem logendProgram_power (q c : Nat) (hc : c ∈ logendProgram.eval q)
    (hp : 0 < unionInterpretation q) : Ordinal.omega0 ^ unionInterpretation c = unionInterpretation (LogEnd.endCode q) := by
  rw [logendProgram_eval] at hc
  exact LogEnd.logend_power q c hc hp

theorem leadingLogProgram_zero (q : Nat) (hq : unionCheck q = true) (hz : unionInterpretation q = 0) :
    leadingLogProgram.eval q = Part.some LogEnd.zeroCode := by
  rw [leadingLogProgram_eval]
  exact LogEnd.leadingLog_zero q hq hz

theorem logendProgram_zero (q : Nat) (hq : unionCheck q = true) (hz : unionInterpretation q = 0) :
    logendProgram.eval q = Part.some LogEnd.zeroCode := by
  rw [logendProgram_eval]
  exact LogEnd.logend_zero q hq hz

theorem logendProgram_cnf (q c : Nat) (hc : c ∈ logendProgram.eval q)
    (xs : List Ordinal.{0}) (hx : xs.Pairwise (fun a b => b ≤ a))
    (hv : unionInterpretation q = Wilken.principalSum (xs.map (fun a => Ordinal.omega0 ^ a))) :
    unionInterpretation c = xs.reverse[0]?.getD 0 := by
  rw [logendProgram_eval] at hc
  exact LogEnd.logend_cnf q c hc xs hx hv

/-- Tags 0/1 are mc/end graphs; 2/3 are first/last logarithm graphs. -/
def positiveCheck (tag payload : Nat) : Bool :=
  cond (tag == 0) (LogEnd.componentGraph false payload.unpair.1 payload.unpair.2)
    (cond (tag == 1) (LogEnd.componentGraph true payload.unpair.1 payload.unpair.2)
      (cond (tag == 2) (LogEnd.logGraph false payload.unpair.1 payload.unpair.2)
        (cond (tag == 3) (LogEnd.logGraph true payload.unpair.1 payload.unpair.2) false)))

theorem positiveCheck_primrec : Primrec₂ positiveCheck := by
  have hp := Primrec.unpair.comp Primrec.snd
  have hg (last : Bool) := LogEnd.componentGraph_primrec.comp ((Primrec.const last).pair hp)
  have hl (last : Bool) := LogEnd.logGraph_primrec.comp ((Primrec.const last).pair hp)
  exact ((Primrec.beq.comp Primrec.fst (Primrec.const 0)).cond (hg false)
    ((Primrec.beq.comp Primrec.fst (Primrec.const 1)).cond (hg true)
      ((Primrec.beq.comp Primrec.fst (Primrec.const 2)).cond (hl false)
        ((Primrec.beq.comp Primrec.fst (Primrec.const 3)).cond (hl true) (Primrec.const false))))).to₂

private def positiveConstant (query : Nat) (_ : Nat) : Bool := positiveCheck query.unpair.1 query.unpair.2

private theorem positiveConstant_primrec : Primrec₂ positiveConstant :=
  (positiveCheck_primrec.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst))
    (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst))).to₂

def positiveEvaluation (query : Nat) : Part Nat := Nat.rfind (fun witness => Part.some (positiveConstant query witness))

theorem positiveEvaluation_partrec : Partrec positiveEvaluation := Partrec.rfind positiveConstant_primrec.to_comp.partrec.to₂

theorem positiveEvaluation_domain (query : Nat) : (positiveEvaluation query).Dom ↔ positiveCheck query.unpair.1 query.unpair.2 = true := by
  simp [positiveEvaluation, positiveConstant, Nat.rfind_dom, eq_comm]

theorem positiveProgram_exists : ∃ p : Program, ∀ query,
    p.domain query ↔ positiveCheck query.unpair.1 query.unpair.2 = true := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp positiveEvaluation_partrec)
  refine ⟨p, fun query => ?_⟩
  simpa only [Program.domain, hp] using positiveEvaluation_domain query

noncomputable def positiveProgram : Program := Classical.choose positiveProgram_exists

theorem positiveProgram_domain (query : Nat) : positiveProgram.domain query ↔ positiveCheck query.unpair.1 query.unpair.2 = true :=
  Classical.choose_spec positiveProgram_exists query

noncomputable def componentGraphColumn (last : Bool) (q : Nat) : Program :=
  (positiveProgram.column (cond last 1 0)).column q

noncomputable def logGraphColumn (last : Bool) (q : Nat) : Program :=
  (positiveProgram.column (cond last 3 2)).column q

theorem componentGraphColumn_primrec : Primrec₂ componentGraphColumn :=
  (Program.column_primrec.comp
    (Program.column_primrec.comp (Primrec.const positiveProgram)
      (Primrec.fst.cond (Primrec.const 1) (Primrec.const 0))) Primrec.snd).to₂

theorem logGraphColumn_primrec : Primrec₂ logGraphColumn :=
  (Program.column_primrec.comp
    (Program.column_primrec.comp (Primrec.const positiveProgram)
      (Primrec.fst.cond (Primrec.const 3) (Primrec.const 2))) Primrec.snd).to₂

theorem componentGraphColumn_domain (last : Bool) (q c : Nat) : (componentGraphColumn last q).domain c ↔
    unionCheck q = true ∧ Canonical.check c = true ∧
      unionInterpretation c = LogEnd.componentValue last (unionInterpretation q) := by
  cases last <;> simp [componentGraphColumn, Program.column_domain, positiveProgram_domain,
    positiveCheck, LogEnd.componentGraph_exact]

theorem logGraphColumn_domain (last : Bool) (q c : Nat) : (logGraphColumn last q).domain c ↔
    unionCheck q = true ∧ Canonical.check c = true ∧
      LogEnd.SourceLogSpec last (unionInterpretation q) (unionInterpretation c) := by
  cases last <;> simp [logGraphColumn, Program.column_domain, positiveProgram_domain,
    positiveCheck, LogEnd.logGraph_exact]

theorem componentGraphColumn_unique (last : Bool) (q : Nat) (hq : unionCheck q = true) :
    ∃! c : Nat, (componentGraphColumn last q).domain c := by
  obtain ⟨c, hc, hu⟩ := LogEnd.componentGraph_unique last q hq
  refine ⟨c, (componentGraphColumn_domain last q c).mpr ((LogEnd.componentGraph_exact last q c).mp hc), ?_⟩
  intro d hd
  exact hu d ((LogEnd.componentGraph_exact last q d).mpr ((componentGraphColumn_domain last q d).mp hd))

theorem logGraphColumn_unique (last : Bool) (q : Nat) (hq : unionCheck q = true) :
    ∃! c : Nat, (logGraphColumn last q).domain c := by
  obtain ⟨c, hc, hu⟩ := LogEnd.logGraph_unique last q hq
  refine ⟨c, (logGraphColumn_domain last q c).mpr ((LogEnd.logGraph_exact last q c).mp hc), ?_⟩
  intro d hd
  exact hu d ((LogEnd.logGraph_exact last q d).mpr ((logGraphColumn_domain last q d).mp hd))

theorem logGraphColumn_returned (tag q c : Nat) (hc : c ∈ (logarithmColumn tag).eval q) :
    (logGraphColumn (tag == 1) q).domain c :=
  (logGraphColumn_domain _ q c).mpr (logarithmColumn_original tag q c hc)

theorem logGraphColumn_eval_iff (tag q c : Nat) :
    c ∈ (logarithmColumn tag).eval q ↔ (logGraphColumn (tag == 1) q).domain c := by
  rw [logarithmColumn_eval, LogEnd.componentLog_graph_iff, logGraphColumn_domain, LogEnd.logGraph_exact]

end Alexander313.HereditaryLogEndProgram
