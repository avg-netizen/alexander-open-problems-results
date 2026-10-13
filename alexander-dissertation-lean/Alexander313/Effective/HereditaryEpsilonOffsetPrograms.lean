import Alexander313.Wilken.HereditaryEpsilonOffsets

/-!
# Actual epsilon-offset decomposition Programs

Total columns execute the constructed parser, canonical epsilon head and raw
natural offset, with explicit auxiliary fallbacks. Positive columns recognize
the exact original epsilon-offset domain, its unique canonical numerical graph,
and strict epsilon-above-bound/base branches. Every source admission and literal
omega fixed-point equation is retained. No parser Program is supplied. Uncompiled.
-/

namespace Alexander313.HereditaryEpsilonOffsetProgram

open Wilken.RelativeTerm.Hereditary

def check (tag payload : Nat) : Bool :=
  cond (tag == 0) (EpsilonOffsets.check payload)
    (cond (tag == 1) (EpsilonOffsets.graph payload.unpair.1
      payload.unpair.2.unpair.1 payload.unpair.2.unpair.2)
      (cond (tag == 2) (EpsilonOffsets.aboveCheck payload.unpair.1 payload.unpair.2)
        (cond (tag == 3) (EpsilonOffsets.aboveBaseCheck payload.unpair.1 payload.unpair.2) false)))

theorem check_primrec : Primrec₂ check := by
  have hp : Primrec (fun p : Nat × Nat => p.2.unpair) := Primrec.unpair.comp Primrec.snd
  have hleft := Primrec.fst.comp hp
  have hright := Primrec.snd.comp hp
  have hcn := Primrec.unpair.comp hright
  have tag (i : Nat) : Primrec (fun p : Nat × Nat => p.1 == i) :=
    Primrec.beq.comp Primrec.fst (Primrec.const i)
  exact ((tag 0).cond (EpsilonOffsets.check_primrec.comp Primrec.snd)
    ((tag 1).cond (EpsilonOffsets.graph_primrec.comp (hleft.pair hcn))
      ((tag 2).cond (EpsilonOffsets.aboveCheck_primrec.comp hleft hright)
        ((tag 3).cond (EpsilonOffsets.aboveBaseCheck_primrec.comp hleft hright)
          (Primrec.const false))))).to₂

def output (tag payload : Nat) : Nat :=
  cond (tag == 0) (cond (EpsilonOffsets.check payload) 1 0)
    (cond (tag == 1) (EpsilonOffsets.decompose payload)
      (cond (tag == 2) (EpsilonOffsets.head payload)
        (cond (tag == 3) (EpsilonOffsets.offset payload)
          (cond (tag == 4)
            (cond (EpsilonOffsets.aboveCheck payload.unpair.1 payload.unpair.2) 1 0)
            (cond (tag == 5)
              (cond (EpsilonOffsets.aboveBaseCheck payload.unpair.1 payload.unpair.2) 1 0)
              (cond (tag == 6) (cond (EpsilonOffsets.graph payload.unpair.1
                payload.unpair.2.unpair.1 payload.unpair.2.unpair.2) 1 0) 0))))))

theorem output_primrec : Primrec₂ output := by
  have hp : Primrec (fun p : Nat × Nat => p.2.unpair) := Primrec.unpair.comp Primrec.snd
  have hleft := Primrec.fst.comp hp
  have hright := Primrec.snd.comp hp
  have hcn := Primrec.unpair.comp hright
  have tag (i : Nat) : Primrec (fun p : Nat × Nat => p.1 == i) :=
    Primrec.beq.comp Primrec.fst (Primrec.const i)
  exact ((tag 0).cond ((EpsilonOffsets.check_primrec.comp Primrec.snd).cond
      (Primrec.const 1) (Primrec.const 0))
    ((tag 1).cond (EpsilonOffsets.decompose_primrec.comp Primrec.snd)
      ((tag 2).cond (EpsilonOffsets.head_primrec.comp Primrec.snd)
        ((tag 3).cond (EpsilonOffsets.offset_primrec.comp Primrec.snd)
          ((tag 4).cond ((EpsilonOffsets.aboveCheck_primrec.comp hleft hright).cond
              (Primrec.const 1) (Primrec.const 0))
            ((tag 5).cond ((EpsilonOffsets.aboveBaseCheck_primrec.comp hleft hright).cond
                (Primrec.const 1) (Primrec.const 0))
              ((tag 6).cond ((EpsilonOffsets.graph_primrec.comp (hleft.pair hcn)).cond
                (Primrec.const 1) (Primrec.const 0)) (Primrec.const 0)))))))).to₂

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

theorem decisionColumn_primrec : Primrec decisionColumn :=
  Program.column_primrec.comp (Primrec.const decisionProgram) Primrec.id

theorem decisionColumn_eval (tag payload : Nat) :
    (decisionColumn tag).eval payload = Part.some (output tag payload) := by
  rw [decisionColumn, Program.column, Nat.Partrec.Code.eval_curry, decisionProgram_eval]
  simp only [Nat.unpair_pair]

theorem decisionColumn_total (tag payload : Nat) : (decisionColumn tag).domain payload := by
  change ((decisionColumn tag).eval payload).Dom
  rw [decisionColumn_eval]
  trivial

theorem decomposition_eval (q : Nat) :
    (decisionColumn 1).eval q = Part.some (EpsilonOffsets.decompose q) := by
  simpa [output] using decisionColumn_eval 1 q

theorem head_eval (q : Nat) : (decisionColumn 2).eval q = Part.some (EpsilonOffsets.head q) := by
  simpa [output] using decisionColumn_eval 2 q

theorem offset_eval (q : Nat) : (decisionColumn 3).eval q = Part.some (EpsilonOffsets.offset q) := by
  simpa [output] using decisionColumn_eval 3 q

theorem decomposition_original (q : Nat) (hq : EpsilonOffsets.check q = true) :
    unionCheck q = true ∧ Canonical.check (EpsilonOffsets.head q) = true ∧
      Ordinal.omega0 ^ unionInterpretation (EpsilonOffsets.head q) = unionInterpretation (EpsilonOffsets.head q) ∧
      unionInterpretation q = unionInterpretation (EpsilonOffsets.head q) +
        (EpsilonOffsets.offset q : Ordinal.{0}) := EpsilonOffsets.decomposition_spec q hq

theorem decomposition_decision (q : Nat) : 1 ∈ (decisionColumn 0).eval q ↔ unionCheck q = true ∧
    ∃ ε : Ordinal.{0}, ∃ n : Nat, Ordinal.omega0 ^ ε = ε ∧
      unionInterpretation q = ε + (n : Ordinal.{0}) := by
  rw [decisionColumn_eval]
  have h := EpsilonOffsets.check_exact q
  cases hc : EpsilonOffsets.check q <;> simp [output, hc] at h ⊢ <;> exact h

theorem above_decision (q b : Nat) : 1 ∈ (decisionColumn 4).eval (Nat.pair q b) ↔
    unionCheck q = true ∧ unionCheck b = true ∧
      ∃ ε : Ordinal.{0}, ∃ n : Nat, Ordinal.omega0 ^ ε = ε ∧
        unionInterpretation b < ε ∧ unionInterpretation q = ε + (n : Ordinal.{0}) := by
  rw [decisionColumn_eval]
  have h := EpsilonOffsets.aboveCheck_exact q b
  cases hc : EpsilonOffsets.aboveCheck q b <;> simp [output, Nat.unpair_pair, hc] at h ⊢ <;> exact h

theorem above_base_decision (r q : Nat) : 1 ∈ (decisionColumn 5).eval (Nat.pair r q) ↔
    unionCheck q = true ∧ ∃ ε : Ordinal.{0}, ∃ n : Nat, Ordinal.omega0 ^ ε = ε ∧
      finiteBase r < ε ∧ unionInterpretation q = ε + (n : Ordinal.{0}) := by
  rw [decisionColumn_eval]
  have h := EpsilonOffsets.aboveBaseCheck_exact r q
  cases hc : EpsilonOffsets.aboveBaseCheck r q <;>
    simp [output, Nat.unpair_pair, hc] at h ⊢ <;> exact h

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

theorem recognizerColumn_primrec : Primrec recognizerColumn :=
  Program.column_primrec.comp (Primrec.const recognizer) Primrec.id

theorem recognizerColumn_domain (tag payload : Nat) :
    (recognizerColumn tag).domain payload ↔ check tag payload = true := by
  simp only [recognizerColumn, Program.column_domain, recognizer_domain, Nat.unpair_pair]

theorem decomposition_domain (q : Nat) : (recognizerColumn 0).domain q ↔ unionCheck q = true ∧
    ∃ ε : Ordinal.{0}, ∃ n : Nat, Ordinal.omega0 ^ ε = ε ∧
      unionInterpretation q = ε + (n : Ordinal.{0}) := by
  simpa [check, EpsilonOffsets.check_exact] using recognizerColumn_domain 0 q

theorem decomposition_graph_domain (q c n : Nat) :
    (recognizerColumn 1).domain (Nat.pair q (Nat.pair c n)) ↔
      unionCheck q = true ∧ Canonical.check c = true ∧
        Ordinal.omega0 ^ unionInterpretation c = unionInterpretation c ∧
        unionInterpretation q = unionInterpretation c + (n : Ordinal.{0}) := by
  simpa [check, Nat.unpair_pair, EpsilonOffsets.graph_exact] using
    recognizerColumn_domain 1 (Nat.pair q (Nat.pair c n))

theorem decomposition_graph_unique (q : Nat) (hq : EpsilonOffsets.check q = true) :
    ∃! p : Nat × Nat, (recognizerColumn 1).domain (Nat.pair q (Nat.pair p.1 p.2)) := by
  have hs := EpsilonOffsets.decomposition_spec q hq
  refine ⟨(EpsilonOffsets.head q, EpsilonOffsets.offset q), ?_, ?_⟩
  · dsimp only
    rw [decomposition_graph_domain]
    exact hs
  · intro p hp
    have ht := (decomposition_graph_domain q p.1 p.2).mp hp
    obtain ⟨hhead, hoffset⟩ := EpsilonOffsets.decomposition_unique q hq
      (unionInterpretation p.1) p.2 ht.2.2.1 ht.2.2.2
    have heq := Canonical.check_value_injective (EpsilonOffsets.head q) p.1 hs.2.1 ht.2.1 hhead
    have heq' : p.1 = EpsilonOffsets.head q := heq.symm
    have hoffset' : p.2 = EpsilonOffsets.offset q := hoffset.symm
    apply Prod.ext
    · dsimp only
      exact heq'
    · dsimp only
      exact hoffset'

theorem above_domain (q b : Nat) : (recognizerColumn 2).domain (Nat.pair q b) ↔
    unionCheck q = true ∧ unionCheck b = true ∧
      ∃ ε : Ordinal.{0}, ∃ n : Nat, Ordinal.omega0 ^ ε = ε ∧
        unionInterpretation b < ε ∧ unionInterpretation q = ε + (n : Ordinal.{0}) := by
  simpa [check, Nat.unpair_pair, EpsilonOffsets.aboveCheck_exact] using
    recognizerColumn_domain 2 (Nat.pair q b)

theorem above_base_domain (r q : Nat) : (recognizerColumn 3).domain (Nat.pair r q) ↔
    unionCheck q = true ∧ ∃ ε : Ordinal.{0}, ∃ n : Nat, Ordinal.omega0 ^ ε = ε ∧
      finiteBase r < ε ∧ unionInterpretation q = ε + (n : Ordinal.{0}) := by
  simpa [check, Nat.unpair_pair, EpsilonOffsets.aboveBaseCheck_exact] using
    recognizerColumn_domain 3 (Nat.pair r q)

end Alexander313.HereditaryEpsilonOffsetProgram
