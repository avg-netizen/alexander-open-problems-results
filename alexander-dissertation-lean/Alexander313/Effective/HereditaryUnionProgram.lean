import Alexander313.Wilken.HereditaryUniformRecognition

/-!
# An actual Program for the hereditary finite union

The uniform primitive-recursive literal checker supplies a partial-recursive
search. Its mathlib machine code halts exactly on the accepted level-tagged
codes. The existing actual denotation/coverage theorem identifies its image
with the interval below the constructed finite-base supremum.

This is recognition of noncanonical hereditary syntax, not numerical ordinal
comparison or a prescribed υ-domain identification. Denotation remains the
noncomputable actual source interpretation. Uncompiled.
-/

namespace Alexander313.HereditaryUnionProgram

open Wilken.RelativeTerm.Hereditary

/-- A total numerical decision output, in addition to the halting recognizer
    below. The output is one for acceptance and zero for rejection. -/
def decision (query : Nat) : Nat := cond (unionCheck query) 1 0

theorem decision_primrec : Primrec decision :=
  Uniform.unionCheck_primrec.cond (Primrec.const 1) (Primrec.const 0)

theorem decision_eq_one (query : Nat) : decision query = 1 ↔ unionCheck query = true := by
  cases h : unionCheck query <;> simp [decision, h]

/-- An actual total executing Program computes both acceptance and rejection. -/
theorem decisionProgram_exists : ∃ p : Program, ∀ query,
    p.eval query = Part.some (decision query) := by
  have h : Partrec (fun query => Part.some (decision query)) := decision_primrec.to_comp.partrec
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp h)
  exact ⟨p, fun query => congrFun hp query⟩

noncomputable def decisionProgram : Program := Classical.choose decisionProgram_exists

theorem decisionProgram_eval (query : Nat) : decisionProgram.eval query = Part.some (decision query) :=
  Classical.choose_spec decisionProgram_exists query

theorem decisionProgram_total (query : Nat) : decisionProgram.domain query := by
  change (decisionProgram.eval query).Dom
  rw [decisionProgram_eval]
  trivial

theorem decisionProgram_accepts (query : Nat) :
    1 ∈ decisionProgram.eval query ↔ unionCheck query = true := by
  rw [decisionProgram_eval]
  rw [Part.mem_some_iff]
  exact (eq_comm : 1 = decision query ↔ decision query = 1).trans (decision_eq_one query)

private def constantCheck (query : Nat) (_ : Nat) : Bool := unionCheck query

private theorem constantCheck_primrec : Primrec₂ constantCheck :=
  (Uniform.unionCheck_primrec.comp Primrec.fst).to₂

/-- The search returns a finite witness on precisely the accepted inputs. -/
def evaluation (query : Nat) : Part Nat :=
  Nat.rfind (fun witness => Part.some (constantCheck query witness))

theorem evaluation_partrec : Partrec evaluation :=
  Partrec.rfind constantCheck_primrec.to_comp.partrec.to₂

theorem evaluation_domain (query : Nat) : (evaluation query).Dom ↔ unionCheck query = true := by
  simp only [evaluation, constantCheck, Nat.rfind_dom, Part.mem_some_iff,
    Part.some_dom, implies_true, and_true, Bool.true_eq, exists_const]

/-- The code is supplied by the real partial-recursive implementation, with
    exact recognition on all raw natural inputs. -/
theorem recognizer_exists : ∃ p : Program, ∀ query, p.domain query ↔ unionCheck query = true := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp evaluation_partrec)
  refine ⟨p, fun query => ?_⟩
  simpa only [Program.domain, hp] using evaluation_domain query

noncomputable def recognizer : Program := Classical.choose recognizer_exists

theorem recognizer_domain (query : Nat) : recognizer.domain query ↔ unionCheck query = true :=
  Classical.choose_spec recognizer_exists query

theorem recognizer_only_trees (query : Nat) (h : recognizer.domain query) :
    ∃ (r : Nat) (t : Wilken.RelativeTerm Nat),
      query = Nat.pair r t.code ∧ lowCheck r t = true ∧
        unionInterpretation query = denote r t := by
  obtain ⟨r, t, hcode, hcheck⟩ := (unionCheck_iff query).mp ((recognizer_domain query).mp h)
  refine ⟨r, t, hcode, hcheck, ?_⟩
  simp only [hcode, unionInterpretation_pair, interpretation_code]

theorem recognizer_denote_lt (query : Nat) (h : recognizer.domain query) :
    unionInterpretation query < finiteBaseLimit :=
  (lt_finiteBaseLimit_iff_code (unionInterpretation query)).mpr
    ⟨query, (recognizer_domain query).mp h, rfl⟩

/-- Exact image of this actual executing Program, without a supplied
    recognizer, parameter representation or semantic coverage contract. -/
theorem recognizer_covers (ξ : Ordinal.{0}) : ξ < finiteBaseLimit ↔
    ∃ query : Nat, recognizer.domain query ∧ unionInterpretation query = ξ := by
  rw [lt_finiteBaseLimit_iff_code]
  simp only [recognizer_domain]

theorem program_exists : ∃ p : Program,
    (∀ query, p.domain query ↔ unionCheck query = true) ∧
    (∀ ξ : Ordinal.{0}, ξ < finiteBaseLimit ↔
      ∃ query : Nat, p.domain query ∧ unionInterpretation query = ξ) ∧
    (∀ query, p.domain query → ∃ (r : Nat) (t : Wilken.RelativeTerm Nat),
      query = Nat.pair r t.code ∧ lowCheck r t = true ∧
        unionInterpretation query = denote r t) :=
  ⟨recognizer, recognizer_domain, recognizer_covers, recognizer_only_trees⟩

end Alexander313.HereditaryUnionProgram
