import Alexander313.Wilken.HereditaryCanonicalCoefficients

/-!
# Actual canonical coefficient Programs and unique graph columns

A genuine total Program computes the canonical head word, its compressed
positive coefficients, its literal expansion and the actual canonical source
reconstruction. Comparing the complete encoded coefficient lists decides
actual ordinal equality on the unchanged original union domain.

Actual positive columns recognize original source admission, the unique
encoded coefficient output and the unique canonical reconstruction. Their
primitive recursive compilers specialize the actual constructed kernel.
Malformed source codes remain outside all semantic graph contracts.
No equality, canonicalization, reconstruction or compiler oracle is supplied.
All proof terms remain uncompiled candidates.
-/

namespace Alexander313.HereditaryCanonicalCoefficientProgram

open Wilken.RelativeTerm.Hereditary

def output (tag payload : Nat) : Nat :=
  cond (tag == 0) (CanonicalCoefficients.encodeForm payload)
    (cond (tag == 1) (Encodable.encode (CanonicalCoefficients.word payload))
      (cond (tag == 2) (Encodable.encode (Coefficients.expand (CanonicalCoefficients.form payload)))
        (cond (tag == 3) (CanonicalCoefficients.reconstructCode payload)
          (cond (tag == 4)
            (cond (CanonicalCoefficients.formEqual payload.unpair.1 payload.unpair.2) 1 0) 0))))

theorem output_primrec : Primrec₂ output := by
  have hform : Primrec (fun p : Nat × Nat => CanonicalCoefficients.encodeForm p.2) :=
    CanonicalCoefficients.encodeForm_primrec.comp Primrec.snd
  have hword : Primrec (fun p : Nat × Nat => Encodable.encode (CanonicalCoefficients.word p.2)) :=
    Primrec.encode.comp (CanonicalCoefficients.word_primrec.comp Primrec.snd)
  have hexpand : Primrec (fun p : Nat × Nat =>
      Encodable.encode (Coefficients.expand (CanonicalCoefficients.form p.2))) := Primrec.encode.comp
    (Coefficients.expand_primrec.comp (CanonicalCoefficients.form_primrec.comp Primrec.snd))
  have htree : Primrec (fun p : Nat × Nat => CanonicalCoefficients.reconstructCode p.2) :=
    CanonicalCoefficients.reconstructCode_primrec.comp Primrec.snd
  have hp : Primrec (fun p : Nat × Nat => p.2.unpair) := Primrec.unpair.comp Primrec.snd
  have hequal := (CanonicalCoefficients.formEqual_primrec.comp (Primrec.fst.comp hp)
    (Primrec.snd.comp hp)).cond (Primrec.const 1) (Primrec.const 0)
  have tag (i : Nat) : Primrec (fun p : Nat × Nat => p.1 == i) :=
    Primrec.beq.comp Primrec.fst (Primrec.const i)
  exact ((tag 0).cond hform ((tag 1).cond hword ((tag 2).cond hexpand
    ((tag 3).cond htree ((tag 4).cond hequal (Primrec.const 0)))))).to₂

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

theorem form_eval (q : Nat) :
    (decisionColumn 0).eval q = Part.some (CanonicalCoefficients.encodeForm q) := by
  simpa [output] using decisionColumn_eval 0 q

theorem word_eval (q : Nat) :
    (decisionColumn 1).eval q = Part.some (Encodable.encode (CanonicalCoefficients.word q)) := by
  simpa [output] using decisionColumn_eval 1 q

theorem expansion_eval (q : Nat) :
    (decisionColumn 2).eval q =
      Part.some (Encodable.encode (Coefficients.expand (CanonicalCoefficients.form q))) := by
  simpa [output] using decisionColumn_eval 2 q

theorem reconstruction_eval (q : Nat) :
    (decisionColumn 3).eval q = Part.some (CanonicalCoefficients.reconstructCode q) := by
  simpa [output] using decisionColumn_eval 3 q

theorem equality_decision (q v : Nat) : 1 ∈ (decisionColumn 4).eval (Nat.pair q v) ↔
    unionCheck q = true ∧ unionCheck v = true ∧ unionInterpretation q = unionInterpretation v := by
  rw [decisionColumn_eval]
  have h := CanonicalCoefficients.formEqual_exact q v
  cases hc : CanonicalCoefficients.formEqual q v <;>
    simp [output, Nat.unpair_pair, hc] at h ⊢ <;> exact h

theorem form_original (q : Nat) (hq : unionCheck q = true) :
    (∀ p ∈ CanonicalCoefficients.form q, 0 < p.2 ∧ Canonical.check p.1 = true ∧
      0 < unionInterpretation p.1 ∧ Ordinal.IsPrincipal (· + ·) (unionInterpretation p.1)) ∧
    (CanonicalCoefficients.form q).Pairwise (fun p s => unionInterpretation s.1 < unionInterpretation p.1) ∧
    Coefficients.weightedSum unionInterpretation (CanonicalCoefficients.form q) = unionInterpretation q :=
  ⟨fun p hp => ⟨CanonicalCoefficients.form_positive q p hp,
      CanonicalCoefficients.form_head_spec q hq p hp⟩,
    CanonicalCoefficients.form_descending q hq, CanonicalCoefficients.form_weighted_value q hq⟩

theorem reconstruction_original (q : Nat) (hq : unionCheck q = true) :
    Canonical.check (CanonicalCoefficients.reconstructCode q) = true ∧
      unionCheck (CanonicalCoefficients.reconstructCode q) = true ∧
      Theta.Normal (CanonicalCoefficients.reconstructCode q).unpair.1
        (ThetaCourse.rawTree (CanonicalCoefficients.reconstructCode q).unpair.2) ∧
      unionInterpretation (CanonicalCoefficients.reconstructCode q) = unionInterpretation q :=
  ⟨CanonicalCoefficients.reconstructCode_checked q hq,
    Canonical.check_original (CanonicalCoefficients.reconstructCode_checked q hq),
    Canonical.check_normal (CanonicalCoefficients.reconstructCode_checked q hq),
    CanonicalCoefficients.reconstructCode_value q hq⟩

def check (tag payload : Nat) : Bool :=
  cond (tag == 0) (unionCheck payload)
    (cond (tag == 1) (CanonicalCoefficients.graph payload.unpair.1 payload.unpair.2)
      (cond (tag == 2) (Canonical.graph payload.unpair.1 payload.unpair.2)
        (cond (tag == 3) (CanonicalCoefficients.formEqual payload.unpair.1 payload.unpair.2) false)))

theorem check_primrec : Primrec₂ check := by
  have hp : Primrec (fun p : Nat × Nat => p.2.unpair) := Primrec.unpair.comp Primrec.snd
  have hq := Primrec.fst.comp hp
  have hc := Primrec.snd.comp hp
  have tag (i : Nat) : Primrec (fun p : Nat × Nat => p.1 == i) :=
    Primrec.beq.comp Primrec.fst (Primrec.const i)
  exact ((tag 0).cond (Uniform.unionCheck_primrec.comp Primrec.snd)
    ((tag 1).cond (CanonicalCoefficients.graph_primrec.comp hq hc)
      ((tag 2).cond (Canonical.Effective.graph_primrec.comp hq hc)
        ((tag 3).cond (CanonicalCoefficients.formEqual_primrec.comp hq hc) (Primrec.const false))))).to₂

private def constantCheck (query : Nat) (_ : Nat) : Bool := check query.unpair.1 query.unpair.2

private theorem canonical_coefficient_constantCheck_primrec : Primrec₂ constantCheck :=
  (check_primrec.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst))
    (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst))).to₂

def evaluation (query : Nat) : Part Nat := Nat.rfind (fun witness => Part.some (constantCheck query witness))

theorem evaluation_partrec : Partrec evaluation :=
  Partrec.rfind canonical_coefficient_constantCheck_primrec.to_comp.partrec.to₂

theorem evaluation_domain (query : Nat) : (evaluation query).Dom ↔ check query.unpair.1 query.unpair.2 = true := by
  simp only [evaluation, constantCheck, Nat.rfind_dom, Part.mem_some_iff,
    Part.some_dom, implies_true, and_true, Bool.true_eq, exists_const]

theorem recognizer_exists : ∃ p : Program, ∀ query,
    p.domain query ↔ check query.unpair.1 query.unpair.2 = true := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp evaluation_partrec)
  refine ⟨p, fun query => ?_⟩
  simpa only [Program.domain, hp] using evaluation_domain query

noncomputable def recognizer : Program := Classical.choose recognizer_exists

theorem recognizer_domain (query : Nat) : recognizer.domain query ↔ check query.unpair.1 query.unpair.2 = true :=
  Classical.choose_spec recognizer_exists query

noncomputable def recognizerColumn (tag : Nat) : Program := recognizer.column tag

theorem recognizerColumn_primrec : Primrec recognizerColumn :=
  Program.column_primrec.comp (Primrec.const recognizer) Primrec.id

theorem recognizerColumn_domain (tag payload : Nat) :
    (recognizerColumn tag).domain payload ↔ check tag payload = true := by
  simp only [recognizerColumn, Program.column_domain, recognizer_domain, Nat.unpair_pair]

theorem original_domain (q : Nat) : (recognizerColumn 0).domain q ↔ unionCheck q = true := by
  simpa [check] using recognizerColumn_domain 0 q

noncomputable def formGraphColumn (q : Nat) : Program := (recognizerColumn 1).column q

theorem formGraphColumn_primrec : Primrec formGraphColumn :=
  Program.column_primrec.comp (Primrec.const (recognizerColumn 1)) Primrec.id

theorem formGraphColumn_domain (q c : Nat) : (formGraphColumn q).domain c ↔
    unionCheck q = true ∧ c = CanonicalCoefficients.encodeForm q := by
  rw [formGraphColumn, Program.column_domain, recognizerColumn_domain]
  simpa [check, Nat.unpair_pair] using CanonicalCoefficients.graph_exact q c

theorem formGraphColumn_forms (q : Nat) (rs : CanonicalCoefficients.Form) :
    (formGraphColumn q).domain (Encodable.encode rs) ↔ unionCheck q = true ∧ rs = CanonicalCoefficients.form q := by
  simp only [formGraphColumn_domain, CanonicalCoefficients.encodeForm, Encodable.encode_injective.eq_iff]

theorem formGraphColumn_unique (q : Nat) (hq : unionCheck q = true) : ∃! c, (formGraphColumn q).domain c := by
  refine ⟨CanonicalCoefficients.encodeForm q, (formGraphColumn_domain _ _).mpr ⟨hq, rfl⟩, ?_⟩
  intro c hc
  exact ((formGraphColumn_domain q c).mp hc).2

noncomputable def reconstructionGraphColumn (q : Nat) : Program := (recognizerColumn 2).column q

theorem reconstructionGraphColumn_primrec : Primrec reconstructionGraphColumn :=
  Program.column_primrec.comp (Primrec.const (recognizerColumn 2)) Primrec.id

theorem reconstructionGraphColumn_domain (q c : Nat) : (reconstructionGraphColumn q).domain c ↔
    unionCheck q = true ∧ Canonical.check c = true ∧ unionInterpretation c = unionInterpretation q := by
  rw [reconstructionGraphColumn, Program.column_domain, recognizerColumn_domain]
  simpa only [check, Nat.unpair_pair, beq_self_eq_true, Bool.false_eq_true,
    Bool.cond_false, Bool.cond_true, show (2 == 0) = false from rfl,
    show (2 == 1) = false from rfl, eq_comm] using Canonical.graph_exact q c

theorem reconstructionGraphColumn_unique (q : Nat) (hq : unionCheck q = true) :
    ∃! c, (reconstructionGraphColumn q).domain c := by
  refine ⟨CanonicalCoefficients.reconstructCode q, (reconstructionGraphColumn_domain _ _).mpr
    ⟨hq, CanonicalCoefficients.reconstructCode_checked q hq, CanonicalCoefficients.reconstructCode_value q hq⟩, ?_⟩
  intro c hc
  have hs := (reconstructionGraphColumn_domain q c).mp hc
  exact Canonical.check_value_injective c _ hs.2.1 (CanonicalCoefficients.reconstructCode_checked q hq)
    (hs.2.2.trans (CanonicalCoefficients.reconstructCode_value q hq).symm)

theorem equality_domain (q v : Nat) : (recognizerColumn 3).domain (Nat.pair q v) ↔
    unionCheck q = true ∧ unionCheck v = true ∧ unionInterpretation q = unionInterpretation v := by
  rw [recognizerColumn_domain]
  simpa [check, Nat.unpair_pair] using CanonicalCoefficients.formEqual_exact q v

end Alexander313.HereditaryCanonicalCoefficientProgram
