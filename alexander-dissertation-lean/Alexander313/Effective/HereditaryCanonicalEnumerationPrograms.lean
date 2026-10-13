import Alexander313.Wilken.HereditaryCanonicalEnumeration
import Alexander313.Computability

/-!
# Actual enumeration and genuine Nat ordinal-order Programs

The genuine total rank search is compiled to an actual mathlib Program. Its
COMPLETE numerical graph has a PR checker, including every accepted code
and every natural enumeration query. A second total Program executes the
real strict/non-strict/equality ordinal comparisons of enumerated labels;
all other modes return zero. Its complete graph retains zero and one outputs.
Concrete PR columns specialize that actual chosen Program. No enumeration,
ordinal comparison, compilation or R1/R2 decision oracle is a premise.
Uncompiled source candidates, retained outside the checkpoint until review.
-/

noncomputable section

namespace Alexander313.HereditaryCanonicalEnumeration.Programs

/-- Every natural query executes the genuine derived total enumeration. -/
def enumerationEvaluation (n : Nat) : Part Nat := Part.some (enumCode n)

theorem enumerationEvaluation_partrec : Partrec enumerationEvaluation := enumCode_computable.partrec

theorem enumerationProgram_exists : ∃ p : Program, ∀ n, p.eval n = enumerationEvaluation n := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp
    (Partrec.nat_iff.mp enumerationEvaluation_partrec)
  exact ⟨p, fun n => congrFun hp n⟩

def enumerationProgram : Program := Classical.choose enumerationProgram_exists

theorem enumerationProgram_eval (n : Nat) :
    enumerationProgram.eval n = Part.some (enumCode n) :=
  Classical.choose_spec enumerationProgram_exists n

theorem enumerationProgram_total (n : Nat) : enumerationProgram.domain n := by
  rw [Program.domain, enumerationProgram_eval]
  exact Part.some_dom _

/-- The COMPLETE graph is PR even though no PR time bound on the unbounded
actual enumeration search is claimed. The checker is its bounded inverse. -/
theorem enumerationProgram_graph (n q : Nat) : q ∈ enumerationProgram.eval n ↔
    searchTest n q = true := by
  rw [enumerationProgram_eval, Part.mem_some_iff, searchTest_exact]
  constructor
  · rintro rfl
    exact enumCode_spec n
  · rintro ⟨hq, hr⟩
    exact (enumCode_rank q hq).symm.trans (congrArg enumCode hr)

def enumerationGraphEvaluation (query : Nat) : Part Nat :=
  cond (searchTest query.unpair.1 query.unpair.2) (Part.some 0) Part.none

theorem enumerationGraphEvaluation_partrec : Partrec enumerationGraphEvaluation :=
  Partrec.cond
    (searchTest_primrec.comp (Primrec.fst.comp Primrec.unpair)
      (Primrec.snd.comp Primrec.unpair)).to_comp
    (Computable.const 0).partrec Partrec.none

theorem enumerationGraphProgram_exists : ∃ p : Program, ∀ query,
    p.eval query = enumerationGraphEvaluation query := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp
    (Partrec.nat_iff.mp enumerationGraphEvaluation_partrec)
  exact ⟨p, fun query => congrFun hp query⟩

def enumerationGraphProgram : Program := Classical.choose enumerationGraphProgram_exists

theorem enumerationGraphProgram_domain (n q : Nat) :
    enumerationGraphProgram.domain (Nat.pair n q) ↔ q ∈ enumerationProgram.eval n := by
  rw [Program.domain, enumerationGraphProgram, Classical.choose_spec enumerationGraphProgram_exists,
    enumerationProgram_graph]
  simp only [enumerationGraphEvaluation, Nat.unpair_pair]
  cases h : searchTest n q <;> simp [h]

/-- The named public dictionary is the genuine executing ordinal label
order. Only modes0/1/2 recognize strict/non-strict/equality respectively. -/
def Relation (mode n m : Nat) : Prop :=
  (mode = 0 ∧ @LT.lt Nat publicLinearOrder.toLT n m) ∨
  (mode = 1 ∧ @LE.le Nat publicLinearOrder.toLE n m) ∨ (mode = 2 ∧ n = m)

def answer (query : Nat) : Bool := cond (query.unpair.1 == 0)
  (less query.unpair.2.unpair.1 query.unpair.2.unpair.2)
  (cond (query.unpair.1 == 1)
    (leCheck query.unpair.2.unpair.1 query.unpair.2.unpair.2)
    (cond (query.unpair.1 == 2) (query.unpair.2.unpair.1 == query.unpair.2.unpair.2) false))

theorem answer_computable : Computable answer := by
  have hm := Primrec.fst.comp Primrec.unpair
  have hn := Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  have hk := Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  exact (Primrec.beq.comp hm (Primrec.const 0)).to_comp.cond
    (less_computable.comp hn.to_comp hk.to_comp)
    ((Primrec.beq.comp hm (Primrec.const 1)).to_comp.cond
      (leCheck_computable.comp hn.to_comp hk.to_comp)
      ((Primrec.beq.comp hm (Primrec.const 2)).to_comp.cond
        (Primrec.beq.comp hn hk).to_comp (Computable.const false)))

theorem answer_exact (mode n m : Nat) :
    answer (Nat.pair mode (Nat.pair n m)) = true ↔ Relation mode n m := by
  by_cases h0 : mode = 0
  · subst mode
    simp [answer, Relation, Nat.unpair_pair, publicLinearOrder_lt_check]
  · by_cases h1 : mode = 1
    · subst mode
      simp [answer, Relation, Nat.unpair_pair, publicLinearOrder_le_check]
    · by_cases h2 : mode = 2
      · subst mode
        simp [answer, Relation, Nat.unpair_pair]
      · simp [answer, Relation, Nat.unpair_pair, h0, h1, h2]

def answerValue (query : Nat) : Nat := cond (answer query) 1 0

theorem answerValue_computable : Computable answerValue :=
  answer_computable.cond (Computable.const 1) (Computable.const 0)

def orderEvaluation (query : Nat) : Part Nat := Part.some (answerValue query)

theorem orderEvaluation_partrec : Partrec orderEvaluation := answerValue_computable.partrec

theorem orderProgram_exists : ∃ p : Program, ∀ query, p.eval query = orderEvaluation query := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp orderEvaluation_partrec)
  exact ⟨p, fun query => congrFun hp query⟩

def orderProgram : Program := Classical.choose orderProgram_exists

theorem orderProgram_eval (mode n m : Nat) : orderProgram.eval (Nat.pair mode (Nat.pair n m)) =
    Part.some (answerValue (Nat.pair mode (Nat.pair n m))) :=
  Classical.choose_spec orderProgram_exists _

theorem orderProgram_total (query : Nat) : orderProgram.domain query := by
  rw [Program.domain, orderProgram, Classical.choose_spec orderProgram_exists]
  exact Part.some_dom _

/-- COMPLETE graph, retaining every false/rejected mode as an actual zero
output, as well as both truth values of the genuine ordinal comparison. -/
theorem orderProgram_graph (mode n m out : Nat) :
    out ∈ orderProgram.eval (Nat.pair mode (Nat.pair n m)) ↔
      (out = 1 ∧ Relation mode n m) ∨ (out = 0 ∧ ¬Relation mode n m) := by
  rw [orderProgram_eval, Part.mem_some_iff]
  have hx := answer_exact mode n m
  by_cases hb : answer (Nat.pair mode (Nat.pair n m)) = true
  · have hyes := hx.mp hb
    simp only [answerValue, hb, Bool.cond_true, hyes, and_true, not_true_eq_false,
      and_false, or_false]
  · have hf := Bool.eq_false_of_not_eq_true hb
    have hnot : ¬Relation mode n m := fun h => hb (hx.mpr h)
    simp only [answerValue, hf, Bool.cond_false, hnot, false_and, and_false,
      not_false_eq_true, and_true, false_or]

def orderColumn (mode : Nat) : Program := orderProgram.column mode

theorem orderColumn_primrec : Primrec orderColumn :=
  Program.column_primrec.comp (Primrec.const orderProgram) Primrec.id

theorem orderColumn_graph (mode n m out : Nat) :
    out ∈ (orderColumn mode).eval (Nat.pair n m) ↔
      (out = 1 ∧ Relation mode n m) ∨ (out = 0 ∧ ¬Relation mode n m) := by
  simp only [orderColumn, Program.column, Nat.Partrec.Code.eval_curry, orderProgram_graph]

end Alexander313.HereditaryCanonicalEnumeration.Programs
