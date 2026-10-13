import Alexander313.Effective.TermReplacement
import Alexander313.Alexander.SourceLabelFormation
import Alexander313.Thesis311

/-!
# Executable tables for the syntactic background branches

This table enumerates all PA instances, including induction for unrestricted
modal formulas, reasoning, introspection and every owner's reflection. The
validity-dependent branches are deliberately not identified with this table.
Every numerical witness produces a genuine closed formula; the search uses
literal equality with its code, rather than a semantic validity test.
-/

namespace Alexander313

namespace Term

theorem var_primrec : Primrec Term.var := by
  apply Primrec.encode_iff.1
  simpa only [encode_eq_code, code, EncodedSyntax.variable, EncodedSyntax.node] using
    (show Primrec (fun n => EncodedSyntax.variable n) from EncodedSyntax.variable_primrec)

theorem succ_primrec : Primrec Term.succ := by
  apply Primrec.encode_iff.1
  simpa only [encode_eq_code, code, EncodedSyntax.node] using
    EncodedSyntax.node_primrec.comp (Primrec.const 2) code_primrec

end Term

namespace Formula

theorem imp_primrec : Primrec₂ (Formula.imp : Formula Nat → Formula Nat → Formula Nat) := by
  apply Primrec.encode_iff.1
  simpa only [encode_eq_code, code, EncodedSyntax.binary, EncodedSyntax.node] using
    (EncodedSyntax.binary_primrec 2).comp (code_primrec.comp Primrec.fst)
      (code_primrec.comp Primrec.snd)

theorem know_primrec : Primrec₂ (Formula.know : Nat → Formula Nat → Formula Nat) := by
  apply Primrec.encode_iff.1
  simpa only [encode_eq_code, code, id_eq, EncodedSyntax.binary, EncodedSyntax.node] using
    (EncodedSyntax.binary_primrec 8).comp Primrec.fst (code_primrec.comp Primrec.snd)

end Formula

namespace SyntacticBackground

def inductionSentence (x : Nat) (φ : Formula Nat) : Formula Nat :=
  Formula.universalClosure (.imp (φ.subst (singleNumeralSubstitution x 0))
    (.imp (.all x (.imp φ (φ.substTerm x (.succ (.var x))))) (.all x φ)))

def reasoningSentence (i : Nat) (φ ψ : Formula Nat) : Formula Nat :=
  Formula.universalClosure (.imp (.know i (.imp φ ψ))
    (.imp (.know i φ) (.know i ψ)))

def introspectionSentence (i : Nat) (φ : Formula Nat) : Formula Nat :=
  Formula.universalClosure (.imp (.know i φ) (.know i (.know i φ)))

theorem inductionSentence_primrec : Primrec₂ inductionSentence := by
  have hx : Primrec (fun p : Nat × Formula Nat => p.1) := Primrec.fst
  have hφ : Primrec (fun p : Nat × Formula Nat => p.2) := Primrec.snd
  have hzero := Formula.singleNumeralSubst_primrec.comp ((hx.pair (Primrec.const 0)).pair hφ)
  have hnext := Term.succ_primrec.comp (Term.var_primrec.comp hx)
  have hsub := Formula.substTerm_primrec.comp ((hx.pair hnext).pair hφ)
  have hstep := Formula.all_primrec.comp hx (Formula.imp_primrec.comp hφ hsub)
  have hall := Formula.all_primrec.comp hx hφ
  exact (Formula.universalClosure_primrec.comp
    (Formula.imp_primrec.comp hzero (Formula.imp_primrec.comp hstep hall))).to₂

theorem reasoningSentence_primrec : Primrec (fun p : (Nat × Formula Nat) × Formula Nat =>
    reasoningSentence p.1.1 p.1.2 p.2) := by
  have hi : Primrec (fun p : (Nat × Formula Nat) × Formula Nat => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hφ : Primrec (fun p : (Nat × Formula Nat) × Formula Nat => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hψ : Primrec (fun p : (Nat × Formula Nat) × Formula Nat => p.2) := Primrec.snd
  have hleft := Formula.know_primrec.comp hi (Formula.imp_primrec.comp hφ hψ)
  have hright := Formula.imp_primrec.comp (Formula.know_primrec.comp hi hφ)
    (Formula.know_primrec.comp hi hψ)
  exact Formula.universalClosure_primrec.comp (Formula.imp_primrec.comp hleft hright)

theorem introspectionSentence_primrec : Primrec₂ introspectionSentence := by
  have hi : Primrec (fun p : Nat × Formula Nat => p.1) := Primrec.fst
  have hk := Formula.know_primrec.comp hi Primrec.snd
  exact (Formula.universalClosure_primrec.comp
    (Formula.imp_primrec.comp hk (Formula.know_primrec.comp hi hk))).to₂

theorem reflection_primrec : Primrec₂ (reflection (Owner := Nat)) := by
  exact (Formula.universalClosure_primrec.comp
    (Formula.imp_primrec.comp (Formula.know_primrec.comp Primrec.fst Primrec.snd)
      Primrec.snd)).to₂

def successorNeZero : Formula Nat := .all 0 (.neg (.equal (.succ (.var 0)) .zero))
def successorInjective : Formula Nat :=
  .all 0 (.all 1 (.imp (.equal (.succ (.var 0)) (.succ (.var 1))) (.equal (.var 0) (.var 1))))
def addZero : Formula Nat := .all 0 (.equal (.add (.var 0) .zero) (.var 0))
def addSucc : Formula Nat :=
  .all 0 (.all 1 (.equal (.add (.var 0) (.succ (.var 1))) (.succ (.add (.var 0) (.var 1)))))
def mulZero : Formula Nat := .all 0 (.equal (.mul (.var 0) .zero) .zero)
def mulSucc : Formula Nat :=
  .all 0 (.all 1 (.equal (.mul (.var 0) (.succ (.var 1)))
    (.add (.mul (.var 0) (.var 1)) (.var 0))))

def admits (i : Nat) (σ : Formula Nat) : Prop :=
  PAInstance Nat σ ∨
    (∃ φ ψ, σ = reasoningSentence i φ ψ) ∨
    (∃ φ, σ = introspectionSentence i φ) ∨
    ∃ j φ, σ = reflection j φ

theorem admits_background {i : Nat} {σ : Formula Nat} (h : admits i σ) :
    BackgroundGenerator i σ := by
  rcases h with h | ⟨φ, ψ, rfl⟩ | ⟨φ, rfl⟩ | ⟨j, φ, rfl⟩
  · exact .arithmetic h
  · exact .structural (.reasoning φ ψ)
  · exact .structural (.introspection φ)
  · exact .reflection j φ

theorem admits_closed {i : Nat} {σ : Formula Nat} (h : admits i σ) : σ.Closed :=
  (admits_background h).closed

abbrev Witness := (Nat × Nat) × (Formula Nat × Formula Nat)

/-- Tags 0--5 are the six fixed PA formulas; 6 is unrestricted induction,
7 reasoning, 8 introspection, and all remaining tags are reflection. -/
def formula (i : Nat) (w : Witness) : Formula Nat :=
  if w.1.1 = 0 then successorNeZero else
  if w.1.1 = 1 then successorInjective else
  if w.1.1 = 2 then addZero else
  if w.1.1 = 3 then addSucc else
  if w.1.1 = 4 then mulZero else
  if w.1.1 = 5 then mulSucc else
  if w.1.1 = 6 then inductionSentence w.1.2 w.2.1 else
  if w.1.1 = 7 then reasoningSentence i w.2.1 w.2.2 else
  if w.1.1 = 8 then introspectionSentence i w.2.1 else
  reflection w.1.2 w.2.1

theorem formula_primrec : Primrec₂ formula := by
  have hi : Primrec (fun p : Nat × Witness => p.1) := Primrec.fst
  have hw : Primrec (fun p : Nat × Witness => p.2) := Primrec.snd
  have htag := Primrec.fst.comp (Primrec.fst.comp hw)
  have hx := Primrec.snd.comp (Primrec.fst.comp hw)
  have hφ := Primrec.fst.comp (Primrec.snd.comp hw)
  have hψ := Primrec.snd.comp (Primrec.snd.comp hw)
  have test (n : Nat) := Primrec.eq.comp htag (Primrec.const n)
  exact (Primrec.ite (test 0) (Primrec.const successorNeZero)
    (Primrec.ite (test 1) (Primrec.const successorInjective)
      (Primrec.ite (test 2) (Primrec.const addZero)
        (Primrec.ite (test 3) (Primrec.const addSucc)
          (Primrec.ite (test 4) (Primrec.const mulZero)
            (Primrec.ite (test 5) (Primrec.const mulSucc)
              (Primrec.ite (test 6) (inductionSentence_primrec.comp hx hφ)
                (Primrec.ite (test 7) (reasoningSentence_primrec.comp ((hi.pair hφ).pair hψ))
                  (Primrec.ite (test 8) (introspectionSentence_primrec.comp hi hφ)
                    (reflection_primrec.comp hx hφ)))))))))).to₂

theorem formula_admitted (i : Nat) (w : Witness) : admits i (formula i w) := by
  unfold formula
  split_ifs
  · exact Or.inl PAInstance.successor_ne_zero
  · exact Or.inl PAInstance.successor_injective
  · exact Or.inl PAInstance.add_zero
  · exact Or.inl PAInstance.add_succ
  · exact Or.inl PAInstance.mul_zero
  · exact Or.inl PAInstance.mul_succ
  · exact Or.inl (PAInstance.induction w.2.1 w.1.2)
  · exact Or.inr (Or.inl ⟨w.2.1, w.2.2, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨w.2.1, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨w.1.2, w.2.1, rfl⟩))

theorem admits_iff_formula (i : Nat) (σ : Formula Nat) :
    admits i σ ↔ ∃ w : Witness, σ = formula i w := by
  constructor
  · rintro (h | ⟨φ, ψ, rfl⟩ | ⟨φ, rfl⟩ | ⟨j, φ, rfl⟩)
    · cases h with
      | successor_ne_zero => exact ⟨((0, 0), (.falsum, .falsum)), rfl⟩
      | successor_injective => exact ⟨((1, 0), (.falsum, .falsum)), rfl⟩
      | add_zero => exact ⟨((2, 0), (.falsum, .falsum)), rfl⟩
      | add_succ => exact ⟨((3, 0), (.falsum, .falsum)), rfl⟩
      | mul_zero => exact ⟨((4, 0), (.falsum, .falsum)), rfl⟩
      | mul_succ => exact ⟨((5, 0), (.falsum, .falsum)), rfl⟩
      | induction φ x => exact ⟨((6, x), (φ, .falsum)), rfl⟩
    · exact ⟨((7, 0), (φ, ψ)), rfl⟩
    · exact ⟨((8, 0), (φ, .falsum)), rfl⟩
    · exact ⟨((9, j), (φ, .falsum)), rfl⟩
  · rintro ⟨w, rfl⟩
    exact formula_admitted i w

noncomputable def decodeWitness (n : Nat) : Witness :=
  (Encodable.decode (α := Witness) n).getD ((0, 0), (.falsum, .falsum))

theorem decodeWitness_primrec : Primrec decodeWitness :=
  Primrec.option_getD.comp Primrec.decode
    (Primrec.const (((0, 0), (.falsum, .falsum)) : Witness))

@[simp] theorem decodeWitness_encode (w : Witness) : decodeWitness (Encodable.encode w) = w := by
  simp [decodeWitness]

noncomputable def check (query witness : Nat) : Bool :=
  query.unpair.2 == (formula query.unpair.1 (decodeWitness witness)).code id

theorem check_primrec : Primrec₂ check := by
  have hq : Primrec (fun p : Nat × Nat => p.1.unpair) := Primrec.unpair.comp Primrec.fst
  have hf := formula_primrec.comp (Primrec.fst.comp hq)
    (decodeWitness_primrec.comp Primrec.snd)
  exact (Primrec.beq.comp (Primrec.snd.comp hq) (Formula.code_primrec.comp hf)).to₂

noncomputable def evaluation (query : Nat) : Part Nat :=
  Nat.rfind (fun witness => Part.some (check query witness))

theorem evaluation_partrec : Partrec evaluation :=
  Partrec.rfind check_primrec.to_comp.partrec.to₂

theorem evaluation_domain (query : Nat) :
    (evaluation query).Dom ↔ ∃ witness, check query witness = true := by
  simp only [evaluation, Nat.rfind_dom, Part.mem_some_iff,
    Part.some_dom, implies_true, and_true, Bool.true_eq]

theorem evaluation_correct (i : Nat) (σ : Formula Nat) :
    (evaluation (Nat.pair i (σ.code id))).Dom ↔ admits i σ := by
  rw [evaluation_domain, admits_iff_formula]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨decodeWitness n, Formula.code_injective id Function.injective_id ?_⟩
    simpa only [check, Nat.unpair_pair, beq_iff_eq] using hn
  · rintro ⟨w, rfl⟩
    exact ⟨Encodable.encode w, by simp [check, Nat.unpair_pair]⟩

theorem evaluation_only_sentences (query : Nat) (h : (evaluation query).Dom) :
    ∃ i, ∃ σ : Formula Nat, query = Nat.pair i (σ.code id) ∧ σ.Closed := by
  obtain ⟨w, hw⟩ := (evaluation_domain query).mp h
  let σ := formula query.unpair.1 (decodeWitness w)
  have hc : query.unpair.2 = σ.code id := beq_iff_eq.mp hw
  refine ⟨query.unpair.1, σ, ?_, admits_closed (formula_admitted _ _)⟩
  rw [← hc]
  exact (Nat.pair_unpair query).symm

theorem program_exists : ∃ c : Program,
    (∀ i σ, c.domain (Nat.pair i (σ.code id)) ↔ admits i σ) ∧
    (∀ query, c.domain query →
      ∃ i, ∃ σ : Formula Nat, query = Nat.pair i (σ.code id) ∧ σ.Closed) := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp evaluation_partrec)
  refine ⟨c, ?_, ?_⟩
  · intro i σ
    change (c.eval _).Dom ↔ _
    rw [hc]
    exact evaluation_correct i σ
  · intro query h
    change (c.eval query).Dom at h
    rw [hc] at h
    exact evaluation_only_sentences query h

end SyntacticBackground
end Alexander313
