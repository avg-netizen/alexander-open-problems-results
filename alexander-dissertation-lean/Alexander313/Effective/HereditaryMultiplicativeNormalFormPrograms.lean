import Alexander313.Wilken.HereditaryMultiplicativeNormalForm

/-!
# Executing reduced factor-word and literal last-factor Programs

One actual partial kernel maps the genuine principal logarithm to its PR
factor-word or last-factor output. Tag one selects the last factor; other
tags select the encoded complete reduced word. These executions halt exactly
on originally admitted positive additive principals. The graph kernel uses
PR certificates of the actual logarithm graph, with tag zero for the whole
word and tag one for its last factor. Other graph tags reject. Canonical
heads, real reduced MNF/product semantics and unique literal outputs follow
from the source construction. All column maps specialize actual fixed
Programs primitive recursively. No output, parser, graph, effectivity or
termination oracle is an input. All proof terms remain uncompiled.
-/

namespace Alexander313.HereditaryMultiplicativeNormalFormProgram

open Wilken.RelativeTerm.Hereditary

def evaluation (query : Nat) : Part Nat :=
  cond (query.unpair.1 == 1) (MultiplicativeNormalForm.lastFactor query.unpair.2)
    (MultiplicativeNormalForm.normalForm query.unpair.2)

theorem evaluation_partrec : Partrec evaluation :=
  Partrec.cond
    (Primrec.beq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 1)).to_comp
    (MultiplicativeNormalForm.lastFactor_partrec.comp (Primrec.snd.comp Primrec.unpair).to_comp)
    (MultiplicativeNormalForm.normalForm_partrec.comp (Primrec.snd.comp Primrec.unpair).to_comp)

theorem operationProgram_exists : ∃ p : Program, ∀ query, p.eval query = evaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp evaluation_partrec)

noncomputable def operationProgram : Program := Classical.choose operationProgram_exists

theorem operationProgram_eval (query : Nat) : operationProgram.eval query = evaluation query :=
  Classical.choose_spec operationProgram_exists query

noncomputable def operationColumn (tag : Nat) : Program := operationProgram.column tag

theorem operationColumn_primrec : Primrec operationColumn :=
  Program.column_primrec.comp (Primrec.const operationProgram) Primrec.id

theorem operationColumn_eval (tag q : Nat) : (operationColumn tag).eval q =
    cond (tag == 1) (MultiplicativeNormalForm.lastFactor q) (MultiplicativeNormalForm.normalForm q) := by
  simp only [operationColumn, Nat.Partrec.Code.eval_curry, operationProgram_eval, evaluation, Nat.unpair_pair]

theorem operationColumn_domain (tag q : Nat) : (operationColumn tag).domain q ↔
    Principal.unionPrincipalCheck q = true := by
  change ((operationColumn tag).eval q).Dom ↔ _
  rw [operationColumn_eval]
  cases ht : (tag == 1) <;> simp only [Bool.cond_false, Bool.cond_true,
    MultiplicativeNormalForm.normalForm_domain, MultiplicativeNormalForm.lastFactor_domain]

noncomputable def normalFormProgram : Program := operationColumn 0

noncomputable def lastFactorProgram : Program := operationColumn 1

theorem normalFormProgram_eval (q : Nat) : normalFormProgram.eval q = MultiplicativeNormalForm.normalForm q := by
  simpa only [normalFormProgram] using operationColumn_eval 0 q

theorem lastFactorProgram_eval (q : Nat) : lastFactorProgram.eval q = MultiplicativeNormalForm.lastFactor q := by
  simpa only [lastFactorProgram] using operationColumn_eval 1 q

theorem normalFormProgram_domain (q : Nat) : normalFormProgram.domain q ↔
    unionCheck q = true ∧ 0 < unionInterpretation q ∧ Ordinal.IsPrincipal (· + ·) (unionInterpretation q) := by
  simp only [normalFormProgram, operationColumn_domain, Principal.unionPrincipalCheck_exact]

theorem lastFactorProgram_domain (q : Nat) : lastFactorProgram.domain q ↔
    unionCheck q = true ∧ 0 < unionInterpretation q ∧ Ordinal.IsPrincipal (· + ·) (unionInterpretation q) := by
  simp only [lastFactorProgram, operationColumn_domain, Principal.unionPrincipalCheck_exact]

theorem normalFormProgram_spec (q : Nat) (rs : List Nat) (hc : Encodable.encode rs ∈ normalFormProgram.eval q) :
    MultiplicativeNormalForm.FormSpec q rs := by
  rw [normalFormProgram_eval] at hc
  exact MultiplicativeNormalForm.normalForm_spec q rs hc

theorem normalFormProgram_product (q : Nat) (rs : List Nat) (hc : Encodable.encode rs ∈ normalFormProgram.eval q) :
    Wilken.MultiplicativeNormalForm.factorProduct (rs.map unionInterpretation) = unionInterpretation q :=
  (normalFormProgram_spec q rs hc).2.2.2

theorem normalFormProgram_values (q : Nat) (rs : List Nat) (hc : Encodable.encode rs ∈ normalFormProgram.eval q) :
    rs.map unionInterpretation = Wilken.MultiplicativeNormalForm.canonicalMNF (unionInterpretation q) :=
  MultiplicativeNormalForm.formSpec_values q rs (normalFormProgram_spec q rs hc)

theorem normalFormProgram_head (q : Nat) (rs : List Nat) (hr : Encodable.encode rs ∈ normalFormProgram.eval q)
    (c : Nat) (hc : c ∈ rs) : Canonical.check c = true ∧ 1 < unionInterpretation c ∧
      Wilken.MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation c) := by
  rw [normalFormProgram_eval] at hr
  exact MultiplicativeNormalForm.normalForm_head_spec q rs hr c hc

theorem normalFormProgram_graph_iff (q c : Nat) : c ∈ normalFormProgram.eval q ↔
    ∃ rs : List Nat, c = Encodable.encode rs ∧ MultiplicativeNormalForm.FormSpec q rs := by
  rw [normalFormProgram_eval]
  exact MultiplicativeNormalForm.normalForm_graph_iff q c

theorem normalFormProgram_returns (q : Nat) (hq : Principal.unionPrincipalCheck q = true) :
    ∃ rs : List Nat, Encodable.encode rs ∈ normalFormProgram.eval q ∧ MultiplicativeNormalForm.FormSpec q rs := by
  rw [normalFormProgram_eval]
  exact MultiplicativeNormalForm.normalForm_returns q hq

theorem normalFormProgram_unique (q : Nat) (hq : Principal.unionPrincipalCheck q = true) :
    ∃! c, c ∈ normalFormProgram.eval q := by
  rw [normalFormProgram_eval]
  exact MultiplicativeNormalForm.normalForm_unique q hq

theorem normalFormProgram_invariant (q v c d : Nat) (hc : c ∈ normalFormProgram.eval q)
    (hd : d ∈ normalFormProgram.eval v) (he : unionInterpretation q = unionInterpretation v) : c = d := by
  rw [normalFormProgram_eval] at hc hd
  exact MultiplicativeNormalForm.normalForm_invariant q v c d hc hd he

theorem lastFactorProgram_spec (q c : Nat) (hc : c ∈ lastFactorProgram.eval q) :
    MultiplicativeNormalForm.LastFactorSpec q c := by
  rw [lastFactorProgram_eval] at hc
  exact MultiplicativeNormalForm.lastFactor_value q c hc

theorem lastFactorProgram_original (q c : Nat) (hc : c ∈ lastFactorProgram.eval q) :
    unionCheck c = true ∧ Theta.Normal c.unpair.1 (ThetaCourse.rawTree c.unpair.2) := by
  rw [lastFactorProgram_eval] at hc
  exact MultiplicativeNormalForm.lastFactor_original q c hc

theorem lastFactorProgram_literal (q : Nat) (rs : List Nat) (hr : Encodable.encode rs ∈ normalFormProgram.eval q)
    (c : Nat) (hc : c ∈ lastFactorProgram.eval q) : c = rs.reverse[0]?.getD MultiplicativeNormalForm.oneCode := by
  rw [normalFormProgram_eval] at hr
  rw [lastFactorProgram_eval] at hc
  exact MultiplicativeNormalForm.lastFactor_literal q rs hr c hc

theorem lastFactorProgram_source (q c : Nat) (hc : c ∈ lastFactorProgram.eval q) : unionInterpretation c =
    Wilken.MultiplicativeNormalForm.lastFactor (Wilken.MultiplicativeNormalForm.canonicalMNF (unionInterpretation q)) := by
  rw [lastFactorProgram_eval] at hc
  exact MultiplicativeNormalForm.lastFactor_source q c hc

theorem lastFactorProgram_lf (q c : Nat) (hc : c ∈ lastFactorProgram.eval q) :
    unionInterpretation c = Wilken.MultiplicativeNormalForm.lf (unionInterpretation q) := by
  rw [lastFactorProgram_eval] at hc
  exact MultiplicativeNormalForm.lastFactor_lf q c hc

theorem lastFactorProgram_class (q c : Nat) (hc : c ∈ lastFactorProgram.eval q) :
    Wilken.MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation c) := by
  rw [lastFactorProgram_eval] at hc
  exact MultiplicativeNormalForm.lastFactor_class q c hc

theorem lastFactorProgram_invariant (q v c d : Nat) (hc : c ∈ lastFactorProgram.eval q)
    (hd : d ∈ lastFactorProgram.eval v) (he : unionInterpretation q = unionInterpretation v) : c = d := by
  rw [lastFactorProgram_eval] at hc hd
  exact MultiplicativeNormalForm.lastFactor_invariant q v c d hc hd he

theorem lastFactorProgram_unique (q : Nat) (hq : Principal.unionPrincipalCheck q = true) :
    ∃! c, c ∈ lastFactorProgram.eval q := by
  rw [lastFactorProgram_eval]
  exact MultiplicativeNormalForm.lastFactor_unique q hq

theorem normalFormProgram_unit (q : Nat) (hq : Principal.unionPrincipalCheck q = true)
    (hv : unionInterpretation q = 1) : normalFormProgram.eval q = Part.some (Encodable.encode ([] : List Nat)) := by
  rw [normalFormProgram_eval]
  exact MultiplicativeNormalForm.normalForm_unit q hq hv

theorem lastFactorProgram_unit (q : Nat) (hq : Principal.unionPrincipalCheck q = true)
    (hv : unionInterpretation q = 1) : lastFactorProgram.eval q = Part.some MultiplicativeNormalForm.oneCode := by
  rw [lastFactorProgram_eval]
  exact MultiplicativeNormalForm.lastFactor_unit q hq hv

def positiveCheck (query d : Nat) : Bool :=
  let tag := query.unpair.1
  (tag == 0 || tag == 1) &&
    MultiplicativeNormalForm.certificateCheck (tag == 1) query.unpair.2 d

theorem positiveCheck_primrec : Primrec₂ positiveCheck := by
  have hp := Primrec.unpair.comp Primrec.fst
  have ht := Primrec.fst.comp hp
  have hl := Primrec.beq.comp ht (Primrec.const 1)
  exact (Primrec.and.comp
    (Primrec.or.comp (Primrec.beq.comp ht (Primrec.const 0)) hl)
    (MultiplicativeNormalForm.certificateCheck_primrec.comp
      (hl.pair ((Primrec.snd.comp hp).pair Primrec.snd)))).to₂

def positiveEvaluation (query : Nat) : Part Nat :=
  Nat.rfind (fun d => Part.some (positiveCheck query d))

theorem positiveEvaluation_partrec : Partrec positiveEvaluation :=
  Partrec.rfind positiveCheck_primrec.to_comp.partrec.to₂

theorem positiveEvaluation_domain (query : Nat) : (positiveEvaluation query).Dom ↔
    ∃ d, positiveCheck query d = true := by
  simp [positiveEvaluation, Nat.rfind_dom, eq_comm]

theorem graphProgram_exists : ∃ p : Program, ∀ query,
    p.domain query ↔ ∃ d, positiveCheck query d = true := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp positiveEvaluation_partrec)
  exact ⟨p, fun query => by simpa only [Program.domain, hp] using positiveEvaluation_domain query⟩

noncomputable def graphProgram : Program := Classical.choose graphProgram_exists

theorem graphProgram_domain (query : Nat) : graphProgram.domain query ↔
    ∃ d, positiveCheck query d = true := Classical.choose_spec graphProgram_exists query

noncomputable def graphColumn (tag q : Nat) : Program := (graphProgram.column tag).column q

theorem graphColumn_primrec : Primrec₂ graphColumn :=
  (Program.column_primrec.comp
    (Program.column_primrec.comp (Primrec.const graphProgram) Primrec.fst) Primrec.snd).to₂

theorem formGraphColumn_domain (q c : Nat) : (graphColumn 0 q).domain c ↔
    ∃ rs : List Nat, c = Encodable.encode rs ∧ MultiplicativeNormalForm.FormSpec q rs := by
  simpa only [graphColumn, Program.column_domain, graphProgram_domain, positiveCheck,
    Nat.unpair_pair, beq_self_eq_true, Bool.true_or, Bool.true_and] using
    MultiplicativeNormalForm.formCertificate_exists_iff q c

theorem lastGraphColumn_domain (q c : Nat) : (graphColumn 1 q).domain c ↔
    MultiplicativeNormalForm.LastFactorSpec q c := by
  simpa only [graphColumn, Program.column_domain, graphProgram_domain, positiveCheck,
    Nat.unpair_pair, beq_self_eq_true, Bool.or_true, Bool.true_and] using
    MultiplicativeNormalForm.lastCertificate_exists_iff q c

theorem formGraphColumn_execution (q c : Nat) : (graphColumn 0 q).domain c ↔ c ∈ normalFormProgram.eval q :=
  (formGraphColumn_domain q c).trans (normalFormProgram_graph_iff q c).symm

theorem lastGraphColumn_execution (q c : Nat) : (graphColumn 1 q).domain c ↔ c ∈ lastFactorProgram.eval q := by
  rw [lastGraphColumn_domain, lastFactorProgram_eval, MultiplicativeNormalForm.lastFactor_graph_iff]

theorem formGraphColumn_unique (q : Nat) (hq : Principal.unionPrincipalCheck q = true) :
    ∃! c, (graphColumn 0 q).domain c := by
  obtain ⟨c, hc, hu⟩ := normalFormProgram_unique q hq
  exact ⟨c, (formGraphColumn_execution q c).mpr hc,
    fun d hd => hu d ((formGraphColumn_execution q d).mp hd)⟩

theorem lastGraphColumn_unique (q : Nat) (hq : Principal.unionPrincipalCheck q = true) :
    ∃! c, (graphColumn 1 q).domain c := by
  obtain ⟨c, hc, hu⟩ := lastFactorProgram_unique q hq
  exact ⟨c, (lastGraphColumn_execution q c).mpr hc,
    fun d hd => hu d ((lastGraphColumn_execution q d).mp hd)⟩

end Alexander313.HereditaryMultiplicativeNormalFormProgram
