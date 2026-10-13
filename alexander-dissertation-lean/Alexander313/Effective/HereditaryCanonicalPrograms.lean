import Alexander313.Wilken.HereditaryCanonicalCodes

/-!
# Actual least-representative Programs

Total columns compute least numerical normal representatives and decisions for
canonical admission/order/equality. Positive columns recognize the exact old
union admission and the graph of its unique normal representative. Program
objects are extracted from the actual primitive-recursive computations; no
semantic canonicalization or effectivity assumption is supplied. These least
codes do not identify printed structural forms or tracking indices. Uncompiled.
-/

namespace Alexander313.HereditaryCanonicalProgram

open Wilken.RelativeTerm.Hereditary

def check (tag payload : Nat) : Bool :=
  cond (tag == 0) (Canonical.check payload)
    (cond (tag == 1) (unionCheck payload)
      (cond (tag == 2) (Canonical.less payload.unpair.1 payload.unpair.2)
        (cond (tag == 3) (Canonical.equal payload.unpair.1 payload.unpair.2)
          (cond (tag == 5) (Canonical.graph payload.unpair.1 payload.unpair.2) false))))

theorem check_primrec : Primrec₂ check := by
  have hp : Primrec (fun p : Nat × Nat => p.2.unpair) := Primrec.unpair.comp Primrec.snd
  have tag (i : Nat) : Primrec (fun p : Nat × Nat => p.1 == i) :=
    Primrec.beq.comp Primrec.fst (Primrec.const i)
  exact ((tag 0).cond (Canonical.Effective.check_primrec.comp Primrec.snd)
    ((tag 1).cond (Canonical.Effective.unionCheck_primrec.comp Primrec.snd)
      ((tag 2).cond (Canonical.Effective.less_primrec.comp (Primrec.fst.comp hp) (Primrec.snd.comp hp))
        ((tag 3).cond (Canonical.Effective.equal_primrec.comp (Primrec.fst.comp hp) (Primrec.snd.comp hp))
          ((tag 5).cond (Canonical.Effective.graph_primrec.comp (Primrec.fst.comp hp)
            (Primrec.snd.comp hp)) (Primrec.const false)))))).to₂

def output (tag payload : Nat) : Nat :=
  cond (tag == 4) (Canonical.canonicalize payload) (cond (check tag payload) 1 0)

theorem output_primrec : Primrec₂ output :=
  ((Primrec.beq.comp Primrec.fst (Primrec.const 4)).cond
    (Canonical.Effective.canonicalize_primrec.comp Primrec.snd)
    (check_primrec.cond (Primrec.const 1) (Primrec.const 0))).to₂

theorem decisionProgram_exists : ∃ p : Program, ∀ query,
    p.eval query = Part.some (output query.unpair.1 query.unpair.2) := by
  have h : Partrec (fun query : Nat => Part.some (output query.unpair.1 query.unpair.2)) :=
    (output_primrec.comp (Primrec.fst.comp Primrec.unpair)
      (Primrec.snd.comp Primrec.unpair)).to_comp.partrec
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp h)
  exact ⟨p, fun query => congrFun hp query⟩

noncomputable def decisionProgram : Program := Classical.choose decisionProgram_exists

theorem decisionProgram_eval (query : Nat) :
    decisionProgram.eval query = Part.some (output query.unpair.1 query.unpair.2) :=
  Classical.choose_spec decisionProgram_exists query

noncomputable def decisionColumn (tag : Nat) : Program := decisionProgram.column tag

theorem decisionColumn_eval (tag payload : Nat) :
    (decisionColumn tag).eval payload = Part.some (output tag payload) := by
  rw [decisionColumn, Program.column, Nat.Partrec.Code.eval_curry, decisionProgram_eval]
  simp only [Nat.unpair_pair]

theorem decisionColumn_total (tag payload : Nat) : (decisionColumn tag).domain payload := by
  change ((decisionColumn tag).eval payload).Dom
  rw [decisionColumn_eval]
  trivial

theorem canonicalize_eval (q : Nat) : (decisionColumn 4).eval q = Part.some (Canonical.canonicalize q) := by
  simpa [output] using decisionColumn_eval 4 q

theorem canonicalize_original (q : Nat) (hq : unionCheck q = true) :
    Canonical.check (Canonical.canonicalize q) = true ∧
      unionCheck (Canonical.canonicalize q) = true ∧
      Theta.Normal (Canonical.canonicalize q).unpair.1
        (ThetaCourse.rawTree (Canonical.canonicalize q).unpair.2) ∧
      unionInterpretation (Canonical.canonicalize q) = unionInterpretation q :=
  ⟨Canonical.canonicalize_check q hq, Canonical.canonicalize_original q hq,
    Canonical.canonicalize_normal q hq, Canonical.canonicalize_value q hq⟩

private def canonicalConstantCheck (query : Nat) (_ : Nat) : Bool :=
  check query.unpair.1 query.unpair.2

private theorem canonicalConstantCheck_primrec : Primrec₂ canonicalConstantCheck :=
  (check_primrec.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst))
    (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst))).to₂

def evaluation (query : Nat) : Part Nat :=
  Nat.rfind (fun witness => Part.some (canonicalConstantCheck query witness))

theorem evaluation_partrec : Partrec evaluation :=
  Partrec.rfind canonicalConstantCheck_primrec.to_comp.partrec.to₂

theorem evaluation_domain (query : Nat) : (evaluation query).Dom ↔
    check query.unpair.1 query.unpair.2 = true := by
  simp only [evaluation, canonicalConstantCheck, Nat.rfind_dom, Part.mem_some_iff,
    Part.some_dom, implies_true, and_true, Bool.true_eq, exists_const]

theorem recognizer_exists : ∃ p : Program, ∀ query,
    p.domain query ↔ check query.unpair.1 query.unpair.2 = true := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp evaluation_partrec)
  refine ⟨p, fun query => ?_⟩
  simpa only [Program.domain, hp] using evaluation_domain query

noncomputable def recognizer : Program := Classical.choose recognizer_exists

theorem recognizer_domain (query : Nat) : recognizer.domain query ↔
    check query.unpair.1 query.unpair.2 = true := Classical.choose_spec recognizer_exists query

noncomputable def recognizerColumn (tag : Nat) : Program := recognizer.column tag

theorem recognizerColumn_domain (tag payload : Nat) :
    (recognizerColumn tag).domain payload ↔ check tag payload = true := by
  simp only [recognizerColumn, Program.column_domain, recognizer_domain, Nat.unpair_pair]

theorem canonical_domain (q : Nat) : (recognizerColumn 0).domain q ↔
    Canonical.acceptedUnion q = true ∧
      ∀ c, Canonical.acceptedUnion c = true → unionInterpretation c = unionInterpretation q → q ≤ c := by
  simpa [check, Canonical.check_exact] using recognizerColumn_domain 0 q

theorem original_domain (q : Nat) : (recognizerColumn 1).domain q ↔ unionCheck q = true := by
  simpa [check] using recognizerColumn_domain 1 q

theorem order_domain (q v : Nat) : (recognizerColumn 2).domain (Nat.pair q v) ↔
    Canonical.check q = true ∧ Canonical.check v = true ∧ unionInterpretation q < unionInterpretation v := by
  simpa [check, Nat.unpair_pair, Canonical.less_exact] using recognizerColumn_domain 2 (Nat.pair q v)

theorem equality_domain (q v : Nat) : (recognizerColumn 3).domain (Nat.pair q v) ↔
    Canonical.check q = true ∧ Canonical.check v = true ∧ unionInterpretation q = unionInterpretation v := by
  simpa [check, Nat.unpair_pair, Canonical.equal_exact] using recognizerColumn_domain 3 (Nat.pair q v)

theorem graph_domain (q c : Nat) : (recognizerColumn 5).domain (Nat.pair q c) ↔
    unionCheck q = true ∧ Canonical.check c = true ∧ unionInterpretation q = unionInterpretation c := by
  simpa [check, Nat.unpair_pair, Canonical.graph_exact] using recognizerColumn_domain 5 (Nat.pair q c)

theorem graph_domain_unique (q : Nat) (hq : unionCheck q = true) :
    ∃! c : Nat, (recognizerColumn 5).domain (Nat.pair q c) := by
  refine ⟨Canonical.canonicalize q, (graph_domain _ _).mpr
    ⟨hq, Canonical.canonicalize_check q hq, (Canonical.canonicalize_value q hq).symm⟩, ?_⟩
  intro c hc
  have hs := (graph_domain q c).mp hc
  exact Canonical.check_value_injective c (Canonical.canonicalize q) hs.2.1
    (Canonical.canonicalize_check q hq)
    (hs.2.2.symm.trans (Canonical.canonicalize_value q hq).symm)

noncomputable def orderProgram : Program := recognizerColumn 2

theorem orderProgram_domain (q v : Nat) : orderProgram.domain (Nat.pair q v) ↔
    Canonical.check q = true ∧ Canonical.check v = true ∧ unionInterpretation q < unionInterpretation v :=
  order_domain q v

end Alexander313.HereditaryCanonicalProgram
