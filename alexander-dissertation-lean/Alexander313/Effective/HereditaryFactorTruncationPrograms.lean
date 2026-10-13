import Alexander313.Wilken.HereditaryFactorTruncation

/-!
# Executing overlined truncation and retained-word Programs

The actual operation kernel executes the guarded principal-logarithm maps.
Tag one returns the complete retained word; other operation tags return its
canonical product. Both halt exactly on an original positive additive
principal and an original threshold. The positive graph kernel searches real
PR logarithm certificates, retaining literal output equality. Graph tags zero
and one select product and word; other graph tags reject. Fixed Program
specializations are PR, without claiming PR logarithm or truncation execution.
All terms remain uncompiled candidates.
-/

namespace Alexander313.HereditaryFactorTruncationProgram

open Wilken.RelativeTerm.Hereditary

def evaluation (query : Nat) : Part Nat :=
  let input := query.unpair.2.unpair
  cond (query.unpair.1 == 1) (FactorTruncation.retainedForm input.1 input.2)
    (FactorTruncation.truncate input.1 input.2)

theorem evaluation_partrec : Partrec evaluation := by
  have hp := Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)
  exact Partrec.cond
    (Primrec.beq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 1)).to_comp
    (FactorTruncation.retainedForm_partrec.comp (Primrec.fst.comp hp).to_comp (Primrec.snd.comp hp).to_comp)
    (FactorTruncation.truncate_partrec.comp (Primrec.fst.comp hp).to_comp (Primrec.snd.comp hp).to_comp)

theorem operationProgram_exists : ∃ p : Program, ∀ query, p.eval query = evaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp evaluation_partrec)

noncomputable def operationProgram : Program := Classical.choose operationProgram_exists

theorem operationProgram_eval (query : Nat) : operationProgram.eval query = evaluation query :=
  Classical.choose_spec operationProgram_exists query

noncomputable def operationColumn (tag : Nat) : Program := operationProgram.column tag

theorem operationColumn_primrec : Primrec operationColumn :=
  Program.column_primrec.comp (Primrec.const operationProgram) Primrec.id

theorem operationColumn_eval (tag q b : Nat) : (operationColumn tag).eval (Nat.pair q b) =
    cond (tag == 1) (FactorTruncation.retainedForm q b) (FactorTruncation.truncate q b) := by
  simp only [operationColumn, Nat.Partrec.Code.eval_curry, operationProgram_eval,
    evaluation, Nat.unpair_pair]

theorem operationColumn_domain (tag q b : Nat) : (operationColumn tag).domain (Nat.pair q b) ↔
    Principal.unionPrincipalCheck q = true ∧ unionCheck b = true := by
  change ((operationColumn tag).eval (Nat.pair q b)).Dom ↔ _
  rw [operationColumn_eval]
  cases ht : (tag == 1) <;> simp only [Bool.cond_false, Bool.cond_true,
    FactorTruncation.truncate_domain, FactorTruncation.retainedForm_domain]

noncomputable def sourceColumn (tag q : Nat) : Program := (operationColumn tag).column q

theorem sourceColumn_primrec : Primrec₂ sourceColumn :=
  (Program.column_primrec.comp (operationColumn_primrec.comp Primrec.fst) Primrec.snd).to₂

theorem sourceColumn_eval (tag q b : Nat) : (sourceColumn tag q).eval b =
    cond (tag == 1) (FactorTruncation.retainedForm q b) (FactorTruncation.truncate q b) := by
  simp only [sourceColumn, Nat.Partrec.Code.eval_curry, operationColumn_eval]

theorem sourceColumn_domain (tag q b : Nat) : (sourceColumn tag q).domain b ↔
    unionCheck q = true ∧ 0 < unionInterpretation q ∧
      Ordinal.IsPrincipal (· + ·) (unionInterpretation q) ∧ unionCheck b = true := by
  rw [sourceColumn, Program.column_domain, operationColumn_domain, Principal.unionPrincipalCheck_exact]
  simp only [and_assoc]

noncomputable def truncateProgram : Program := operationColumn 0

noncomputable def retainedFormProgram : Program := operationColumn 1

theorem truncateProgram_eval (q b : Nat) : truncateProgram.eval (Nat.pair q b) = FactorTruncation.truncate q b := by
  simpa only [truncateProgram] using operationColumn_eval 0 q b

theorem retainedFormProgram_eval (q b : Nat) : retainedFormProgram.eval (Nat.pair q b) = FactorTruncation.retainedForm q b := by
  simpa only [retainedFormProgram] using operationColumn_eval 1 q b

theorem truncateProgram_spec (q b c : Nat) (hc : c ∈ truncateProgram.eval (Nat.pair q b)) :
    FactorTruncation.TruncateSpec q b c := by
  rw [truncateProgram_eval] at hc
  exact FactorTruncation.truncate_value q b c hc

theorem retainedFormProgram_spec (q b : Nat) (rs : List Nat)
    (hr : Encodable.encode rs ∈ retainedFormProgram.eval (Nat.pair q b)) : FactorTruncation.RetainedSpec q b rs := by
  rw [retainedFormProgram_eval] at hr
  exact FactorTruncation.retainedForm_spec q b rs hr

theorem truncateProgram_graph_iff (q b c : Nat) : c ∈ truncateProgram.eval (Nat.pair q b) ↔
    FactorTruncation.TruncateSpec q b c := by
  rw [truncateProgram_eval]
  exact FactorTruncation.truncate_graph_iff q b c

theorem retainedFormProgram_graph_iff (q b c : Nat) : c ∈ retainedFormProgram.eval (Nat.pair q b) ↔
    ∃ rs : List Nat, c = Encodable.encode rs ∧ FactorTruncation.RetainedSpec q b rs := by
  rw [retainedFormProgram_eval]
  exact FactorTruncation.retainedForm_graph_iff q b c

theorem truncateProgram_returns (q b : Nat) (hq : Principal.unionPrincipalCheck q = true) (hb : unionCheck b = true) :
    ∃ c, c ∈ truncateProgram.eval (Nat.pair q b) ∧ FactorTruncation.TruncateSpec q b c := by
  rw [truncateProgram_eval]
  exact FactorTruncation.truncate_returns q b hq hb

theorem retainedFormProgram_returns (q b : Nat) (hq : Principal.unionPrincipalCheck q = true) (hb : unionCheck b = true) :
    ∃ rs : List Nat, Encodable.encode rs ∈ retainedFormProgram.eval (Nat.pair q b) ∧ FactorTruncation.RetainedSpec q b rs := by
  rw [retainedFormProgram_eval]
  exact FactorTruncation.retainedForm_returns q b hq hb

theorem truncateProgram_unique (q b : Nat) (hq : Principal.unionPrincipalCheck q = true) (hb : unionCheck b = true) :
    ∃! c, c ∈ truncateProgram.eval (Nat.pair q b) := by
  rw [truncateProgram_eval]
  exact FactorTruncation.truncate_unique q b hq hb

theorem retainedFormProgram_unique (q b : Nat) (hq : Principal.unionPrincipalCheck q = true) (hb : unionCheck b = true) :
    ∃! c, c ∈ retainedFormProgram.eval (Nat.pair q b) := by
  rw [retainedFormProgram_eval]
  exact FactorTruncation.retainedForm_unique q b hq hb

theorem truncateProgram_bounds (q b c : Nat) (hc : c ∈ truncateProgram.eval (Nat.pair q b)) :
    1 ≤ unionInterpretation c ∧ unionInterpretation c ≤ unionInterpretation q := by
  rw [truncateProgram_eval] at hc
  exact FactorTruncation.truncate_bounds q b c hc

theorem truncateProgram_idempotent (q b c : Nat) (hc : c ∈ truncateProgram.eval (Nat.pair q b)) :
    truncateProgram.eval (Nat.pair c b) = Part.some c := by
  rw [truncateProgram_eval] at hc ⊢
  exact FactorTruncation.truncate_idempotent q b c hc

theorem truncateProgram_invariant (q v b t c d : Nat) (hc : c ∈ truncateProgram.eval (Nat.pair q b))
    (hd : d ∈ truncateProgram.eval (Nat.pair v t)) (hqv : unionInterpretation q = unionInterpretation v)
    (hbt : unionInterpretation b = unionInterpretation t) : c = d := by
  rw [truncateProgram_eval] at hc hd
  exact FactorTruncation.truncate_invariant q v b t c d hc hd hqv hbt

theorem retainedFormProgram_invariant (q v b t c d : Nat) (hc : c ∈ retainedFormProgram.eval (Nat.pair q b))
    (hd : d ∈ retainedFormProgram.eval (Nat.pair v t)) (hqv : unionInterpretation q = unionInterpretation v)
    (hbt : unionInterpretation b = unionInterpretation t) : c = d := by
  rw [retainedFormProgram_eval] at hc hd
  exact FactorTruncation.retainedForm_invariant q v b t c d hc hd hqv hbt

def positiveCheck (query d : Nat) : Bool :=
  let tag := query.unpair.1
  (tag == 0 || tag == 1) && FactorTruncation.certificateCheck (tag == 1) query.unpair.2 d

theorem positiveCheck_primrec : Primrec₂ positiveCheck := by
  have hp := Primrec.unpair.comp Primrec.fst
  have ht := Primrec.fst.comp hp
  have hw := Primrec.beq.comp ht (Primrec.const 1)
  exact (Primrec.and.comp (Primrec.or.comp (Primrec.beq.comp ht (Primrec.const 0)) hw)
    (FactorTruncation.certificateCheck_primrec.comp
      (hw.pair ((Primrec.snd.comp hp).pair Primrec.snd)))).to₂

def positiveEvaluation (query : Nat) : Part Nat := Nat.rfind (fun d => Part.some (positiveCheck query d))

theorem positiveEvaluation_partrec : Partrec positiveEvaluation :=
  Partrec.rfind positiveCheck_primrec.to_comp.partrec.to₂

theorem positiveEvaluation_domain (query : Nat) : (positiveEvaluation query).Dom ↔
    ∃ d, positiveCheck query d = true := by
  simp [positiveEvaluation, Nat.rfind_dom, eq_comm]

theorem graphProgram_exists : ∃ p : Program, ∀ query, p.domain query ↔ ∃ d, positiveCheck query d = true := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp positiveEvaluation_partrec)
  exact ⟨p, fun query => by simpa only [Program.domain, hp] using positiveEvaluation_domain query⟩

noncomputable def graphProgram : Program := Classical.choose graphProgram_exists

theorem graphProgram_domain (query : Nat) : graphProgram.domain query ↔ ∃ d, positiveCheck query d = true :=
  Classical.choose_spec graphProgram_exists query

noncomputable def graphColumn (tag input : Nat) : Program := (graphProgram.column tag).column input

theorem graphColumn_primrec : Primrec₂ graphColumn :=
  (Program.column_primrec.comp
    (Program.column_primrec.comp (Primrec.const graphProgram) Primrec.fst) Primrec.snd).to₂

theorem truncateGraphColumn_domain (q b c : Nat) : (graphColumn 0 (Nat.pair q b)).domain c ↔
    FactorTruncation.TruncateSpec q b c := by
  simpa only [graphColumn, Program.column_domain, graphProgram_domain, positiveCheck,
    Nat.unpair_pair, beq_self_eq_true, Bool.true_or, Bool.true_and] using
    FactorTruncation.truncateCertificate_exists_iff q b c

theorem retainedGraphColumn_domain (q b c : Nat) : (graphColumn 1 (Nat.pair q b)).domain c ↔
    ∃ rs : List Nat, c = Encodable.encode rs ∧ FactorTruncation.RetainedSpec q b rs := by
  simpa only [graphColumn, Program.column_domain, graphProgram_domain, positiveCheck,
    Nat.unpair_pair, beq_self_eq_true, Bool.or_true, Bool.true_and] using
    FactorTruncation.retainedCertificate_exists_iff q b c

theorem truncateGraphColumn_execution (q b c : Nat) : (graphColumn 0 (Nat.pair q b)).domain c ↔
    c ∈ truncateProgram.eval (Nat.pair q b) :=
  (truncateGraphColumn_domain q b c).trans (truncateProgram_graph_iff q b c).symm

theorem retainedGraphColumn_execution (q b c : Nat) : (graphColumn 1 (Nat.pair q b)).domain c ↔
    c ∈ retainedFormProgram.eval (Nat.pair q b) :=
  (retainedGraphColumn_domain q b c).trans (retainedFormProgram_graph_iff q b c).symm

theorem truncateGraphColumn_unique (q b : Nat) (hq : Principal.unionPrincipalCheck q = true) (hb : unionCheck b = true) :
    ∃! c, (graphColumn 0 (Nat.pair q b)).domain c := by
  obtain ⟨c, hc, hu⟩ := truncateProgram_unique q b hq hb
  exact ⟨c, (truncateGraphColumn_execution q b c).mpr hc,
    fun d hd => hu d ((truncateGraphColumn_execution q b d).mp hd)⟩

theorem retainedGraphColumn_unique (q b : Nat) (hq : Principal.unionPrincipalCheck q = true) (hb : unionCheck b = true) :
    ∃! c, (graphColumn 1 (Nat.pair q b)).domain c := by
  obtain ⟨c, hc, hu⟩ := retainedFormProgram_unique q b hq hb
  exact ⟨c, (retainedGraphColumn_execution q b c).mpr hc,
    fun d hd => hu d ((retainedGraphColumn_execution q b d).mp hd)⟩

end Alexander313.HereditaryFactorTruncationProgram
