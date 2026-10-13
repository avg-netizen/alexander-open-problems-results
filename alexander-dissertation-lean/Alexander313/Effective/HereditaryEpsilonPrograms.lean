import Alexander313.Wilken.HereditaryEpsilonClassification

/-!
# Executing Programs for the actual hereditary epsilon class

Total columns return the constructed Boolean classifier on all raw inputs.
Separate positive search columns have exactly the original full, low and
finite-level union admission domains whose real values are omega fixed points.
The source guards and actual interpretation are retained. No semantic epsilon
classifier, supplied Program or effectivity contract is assumed. Uncompiled.
-/

namespace Alexander313.HereditaryEpsilonProgram

open Wilken.RelativeTerm.Hereditary

def check (tag payload : Nat) : Bool :=
  cond (tag == 0) (Epsilon.epsilonCheck payload.unpair.1 payload.unpair.2)
    (cond (tag == 1) (Epsilon.epsilonLowCheck payload.unpair.1 payload.unpair.2)
      (cond (tag == 2) (Epsilon.unionEpsilonCheck payload) false))

theorem check_primrec : Primrec₂ check := by
  have hp : Primrec (fun p : Nat × Nat => p.2.unpair) := Primrec.unpair.comp Primrec.snd
  have hr := Primrec.fst.comp hp
  have hc := Primrec.snd.comp hp
  have tag (i : Nat) : Primrec (fun p : Nat × Nat => p.1 == i) :=
    Primrec.beq.comp Primrec.fst (Primrec.const i)
  exact ((tag 0).cond (Epsilon.epsilonCheck_primrec.comp hr hc)
    ((tag 1).cond (Epsilon.epsilonLowCheck_primrec.comp hr hc)
      ((tag 2).cond (Epsilon.unionEpsilonCheck_primrec.comp Primrec.snd)
        (Primrec.const false)))).to₂

def output (tag payload : Nat) : Nat := cond (check tag payload) 1 0

theorem output_primrec : Primrec₂ output :=
  (check_primrec.cond (Primrec.const 1) (Primrec.const 0)).to₂

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

theorem full_eval (r c : Nat) : (decisionColumn 0).eval (Nat.pair r c) =
    Part.some (cond (Epsilon.epsilonCheck r c) 1 0) := by
  simpa [output, check, Nat.unpair_pair] using decisionColumn_eval 0 (Nat.pair r c)

theorem low_eval (r c : Nat) : (decisionColumn 1).eval (Nat.pair r c) =
    Part.some (cond (Epsilon.epsilonLowCheck r c) 1 0) := by
  simpa [output, check, Nat.unpair_pair] using decisionColumn_eval 1 (Nat.pair r c)

theorem union_eval (q : Nat) : (decisionColumn 2).eval q =
    Part.some (cond (Epsilon.unionEpsilonCheck q) 1 0) := by
  simpa [output, check] using decisionColumn_eval 2 q

theorem full_decision (r c : Nat) : 1 ∈ (decisionColumn 0).eval (Nat.pair r c) ↔
    checkCode r c = true ∧ Ordinal.omega0 ^ interpretation r c = interpretation r c := by
  rw [full_eval]
  have h := Epsilon.epsilonCheck_exact r c
  cases hc : Epsilon.epsilonCheck r c <;> simp [hc] at h ⊢ <;> exact h

theorem low_decision (r c : Nat) : 1 ∈ (decisionColumn 1).eval (Nat.pair r c) ↔
    lowCheckCode r c = true ∧ Ordinal.omega0 ^ interpretation r c = interpretation r c := by
  rw [low_eval]
  have h := Epsilon.epsilonLowCheck_exact r c
  cases hc : Epsilon.epsilonLowCheck r c <;> simp [hc] at h ⊢ <;> exact h

theorem union_decision (q : Nat) : 1 ∈ (decisionColumn 2).eval q ↔
    unionCheck q = true ∧ Ordinal.omega0 ^ unionInterpretation q = unionInterpretation q := by
  rw [union_eval]
  have h := Epsilon.unionEpsilonCheck_exact q
  cases hc : Epsilon.unionEpsilonCheck q <;> simp [hc] at h ⊢ <;> exact h

private def constant (query : Nat) (_ : Nat) : Bool := check query.unpair.1 query.unpair.2

private theorem constant_primrec : Primrec₂ constant :=
  ((check_primrec.comp (Primrec.fst.comp Primrec.unpair)
    (Primrec.snd.comp Primrec.unpair)).comp Primrec.fst).to₂

def evaluation (query : Nat) : Part Nat :=
  Nat.rfind (fun witness => Part.some (constant query witness))

theorem evaluation_partrec : Partrec evaluation := Partrec.rfind constant_primrec.to_comp.partrec.to₂

theorem evaluation_domain (query : Nat) : (evaluation query).Dom ↔
    check query.unpair.1 query.unpair.2 = true := by
  simp only [evaluation, constant, Nat.rfind_dom, Part.mem_some_iff,
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

theorem full_domain (r c : Nat) : (recognizerColumn 0).domain (Nat.pair r c) ↔
    checkCode r c = true ∧ Ordinal.omega0 ^ interpretation r c = interpretation r c := by
  simpa [check, Nat.unpair_pair, Epsilon.epsilonCheck_exact] using
    recognizerColumn_domain 0 (Nat.pair r c)

theorem low_domain (r c : Nat) : (recognizerColumn 1).domain (Nat.pair r c) ↔
    lowCheckCode r c = true ∧ Ordinal.omega0 ^ interpretation r c = interpretation r c := by
  simpa [check, Nat.unpair_pair, Epsilon.epsilonLowCheck_exact] using
    recognizerColumn_domain 1 (Nat.pair r c)

theorem union_domain (q : Nat) : (recognizerColumn 2).domain q ↔
    unionCheck q = true ∧ Ordinal.omega0 ^ unionInterpretation q = unionInterpretation q := by
  simpa [check, Epsilon.unionEpsilonCheck_exact] using recognizerColumn_domain 2 q

end Alexander313.HereditaryEpsilonProgram
