import Alexander313.Alexander.HilbertHenkinSyntax

/-!
# Quantified truth for the native Hilbert term quotient

The witness hypothesis is literal syntactic derivability of the ordinary
existential witness implications for every unary matrix. It contains no
semantic truth, model, soundness or completeness field. Maximal consistency
and these actual witnesses prove the universal clause. Strong induction on
formula-node size then proves every sentence and every closed-term bounded
instance. A displayed closed term supplies actual quotient nonemptiness.

Existence of a theory with all witnesses is a separate construction.
-/

noncomputable section

namespace Alexander313.FirstOrderCalculus.HilbertHenkinTruth

universe u v

variable {L : FirstOrder.Language.{u, v}}

open HilbertHenkinSyntax

def HasWitnesses (T : L.Theory) : Prop :=
  ∀ (x : Nat) (φ : L.Formula Nat), φ.freeVarFinset ⊆ {x} →
    ∃ t : L.Term Empty,
      Derivation T ((existsVariable x φ).imp
        (substituteVariable x (ClosedTerm.embed t) φ))

theorem HasWitnesses.mono {T U : L.Theory} (h : HasWitnesses T) (hTU : T ⊆ U) :
    HasWitnesses U := by
  intro x φ hφ
  obtain ⟨t, ht⟩ := h x φ hφ
  exact ⟨t, ht.mono hTU⟩

theorem witnessInstance {T : L.Theory} (witnesses : HasWitnesses T)
    (x : Nat) (φ : L.Formula Nat) (hφ : φ.freeVarFinset ⊆ {x})
    (h : Derivation T (existsVariable x φ)) :
    ∃ t : L.Term Empty, Derivation T (substituteVariable x (ClosedTerm.embed t) φ) := by
  obtain ⟨t, ht⟩ := witnesses x φ hφ
  exact ⟨t, .mp ht h⟩

theorem all_derivable_iff {T : L.Theory} (maximal : Maximal Consistent T)
    (witnesses : HasWitnesses T) (x : Nat) (φ : L.Formula Nat)
    (hφ : φ.freeVarFinset ⊆ {x}) :
    Derivation T (allVariable x φ) ↔
      ∀ t : L.Term Empty, Derivation T (substituteVariable x (ClosedTerm.embed t) φ) := by
  classical
  constructor
  · intro h t
    exact h.specialize x (ClosedTerm.embed t)
  · intro h
    by_contra hall
    let σ := ClosedFormula.sentence (allVariable x φ) (ClosedFormula.allVariable_closed x φ hφ)
    have hσ : σ ∉ T := by
      intro hmem
      apply hall
      simpa only [σ, ClosedFormula.sentenceFormula_sentence] using
        (Derivation.theory σ hmem : Derivation T (sentenceFormula σ))
    have hn : Derivation T (allVariable x φ).not := by
      simpa only [sentenceFormula_not, σ, ClosedFormula.sentenceFormula_sentence] using
        (Derivation.theory σ.not ((MaximalConsistency.not_mem_iff maximal σ).mpr hσ))
    have hex : Derivation T (existsVariable x φ.not) :=
      .mp (Derivation.allMonotone x (Derivation.doubleNegElim φ)).contrapositive hn
    have hnot : φ.not.freeVarFinset ⊆ {x} := by
      simpa only [FirstOrder.Language.BoundedFormula.not,
        FirstOrder.Language.BoundedFormula.freeVarFinset, Finset.union_empty] using hφ
    obtain ⟨t, ht⟩ := witnessInstance witnesses x φ.not hnot hex
    have htn : Derivation T (substituteVariable x (ClosedTerm.embed t) φ).not := by
      simpa only [substituteVariable_not] using ht
    exact maximal.prop (.mp htn (h t))

def instanceSentence (x : Nat) (φ : L.Formula Nat) (hφ : φ.freeVarFinset ⊆ {x})
    (t : L.Term Empty) : L.Sentence :=
  ClosedFormula.sentence (substituteVariable x (ClosedTerm.embed t) φ)
    (ClosedFormula.substituteVariable_closed x (ClosedTerm.embed t)
      (ClosedTerm.embed_varFinset t) φ hφ)

@[simp] theorem instanceSentence_formula (x : Nat) (φ : L.Formula Nat)
    (hφ : φ.freeVarFinset ⊆ {x}) (t : L.Term Empty) :
    sentenceFormula (instanceSentence x φ hφ t) =
      substituteVariable x (ClosedTerm.embed t) φ :=
  ClosedFormula.sentenceFormula_sentence _ _

@[simp] theorem instanceSentence_size (x : Nat) (φ : L.Formula Nat)
    (hφ : φ.freeVarFinset ⊆ {x}) (t : L.Term Empty) :
    formulaSize (instanceSentence x φ hφ t) = formulaSize φ := by
  simp only [instanceSentence, formulaSize_sentence, substituteVariable, formulaSize_subst]

theorem instanceSentence_realize (T : L.Theory) (x : Nat) (φ : L.Formula Nat)
    (hφ : φ.freeVarFinset ⊆ {x}) (t : L.Term Empty)
    (s : Nat → HilbertTermQuotient.Domain T) :
    (instanceSentence x φ hφ t).Realize (HilbertTermQuotient.Domain T) ↔
      φ.Realize (Function.update s x (HilbertTermQuotient.classOf T t)) := by
  have h := sentenceFormula_realize (instanceSentence x φ hφ t) s
  rw [instanceSentence_formula, substituteVariable_realize] at h
  have ht : (ClosedTerm.embed t).realize s = HilbertTermQuotient.classOf T t :=
    HilbertTermQuotient.closedTerm_relabel_realize T t Empty.elim s
  rw [ht] at h
  exact h.symm

private def stripTerm (t : L.Term (Empty ⊕ Fin 0)) : L.Term Empty :=
  t.relabel (Sum.elim id Fin.elim0)

private theorem stripTerm_lift (t : L.Term (Empty ⊕ Fin 0)) :
    (stripTerm t).relabel Sum.inl = t := by
  induction t with
  | var a =>
    cases a with
    | inl e => exact Empty.elim e
    | inr i => exact Fin.elim0 i
  | func f ts ih =>
    change FirstOrder.Language.Term.func f (fun i => (stripTerm (ts i)).relabel Sum.inl) =
      FirstOrder.Language.Term.func f ts
    congr 1
    exact funext ih

theorem sentence_truth {T : L.Theory} (maximal : Maximal Consistent T)
    (witnesses : HasWitnesses T) (t₀ : L.Term Empty) (σ : L.Sentence) :
    σ.Realize (HilbertTermQuotient.Domain T) ↔ σ ∈ T := by
  classical
  have hmain : ∀ k : Nat, ∀ τ : L.Sentence, formulaSize τ = k →
      (τ.Realize (HilbertTermQuotient.Domain T) ↔ τ ∈ T) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro τ hk
      cases τ with
      | falsum => exact HilbertTermQuotient.falsum_realize_iff_mem maximal
      | equal t s =>
        have he : (stripTerm t).equal (stripTerm s) =
            (FirstOrder.Language.BoundedFormula.equal t s : L.Sentence) := by
          change FirstOrder.Language.BoundedFormula.equal
            ((stripTerm t).relabel Sum.inl) ((stripTerm s).relabel Sum.inl) = _
          rw [stripTerm_lift, stripTerm_lift]
        rw [← he]
        exact HilbertTermQuotient.equal_realize_iff_mem maximal _ _
      | rel r ts =>
        have he : HilbertTermQuotient.relationSentence r (fun i => stripTerm (ts i)) =
            (FirstOrder.Language.BoundedFormula.rel r ts : L.Sentence) := by
          change FirstOrder.Language.BoundedFormula.rel r
            (fun i => (stripTerm (ts i)).relabel Sum.inl) = _
          simp only [stripTerm_lift]
        rw [← he]
        exact HilbertTermQuotient.relation_realize_iff_mem maximal _ _
      | imp φ ψ =>
        have hφ : formulaSize φ < k := by simp only [formulaSize] at hk; omega
        have hψ : formulaSize ψ < k := by simp only [formulaSize] at hk; omega
        exact HilbertTermQuotient.imp_realize_iff_mem maximal φ ψ
          (ih _ hφ φ rfl) (ih _ hψ ψ rfl)
      | all φ =>
        let ψ := openUnary 0 φ
        have hψ : ψ.freeVarFinset ⊆ {0} := openUnary_freeVar 0 φ
        let s : Nat → HilbertTermQuotient.Domain T := fun _ => HilbertTermQuotient.classOf T t₀
        have hsmall (t : L.Term Empty) : formulaSize (instanceSentence 0 ψ hψ t) < k := by
          rw [instanceSentence_size]
          change formulaSize (openUnary 0 φ) < k
          rw [formulaSize_openUnary]
          simp only [formulaSize] at hk
          omega
        have hinstances (t : L.Term Empty) :
            (instanceSentence 0 ψ hψ t).Realize (HilbertTermQuotient.Domain T) ↔
              instanceSentence 0 ψ hψ t ∈ T :=
          ih _ (hsmall t) _ rfl
        have hbody (d : HilbertTermQuotient.Domain T) :
            ψ.Realize (Function.update s 0 d) ↔
              φ.Realize (default : Empty → HilbertTermQuotient.Domain T)
                (Fin.snoc (default : Fin 0 → HilbertTermQuotient.Domain T) d) := by
          simpa only [Fin.snoc_zero] using openUnary_realize 0 φ s d
        change (∀ d : HilbertTermQuotient.Domain T,
          φ.Realize (default : Empty → HilbertTermQuotient.Domain T)
            (Fin.snoc (default : Fin 0 → HilbertTermQuotient.Domain T) d)) ↔ φ.all ∈ T
        constructor
        · intro h
          apply (MaximalConsistency.derivation_iff_mem maximal φ.all).mp
          rw [← allVariable_openUnary 0 φ]
          apply (all_derivable_iff maximal witnesses 0 ψ hψ).mpr
          intro t
          have ht : (instanceSentence 0 ψ hψ t).Realize (HilbertTermQuotient.Domain T) :=
            (instanceSentence_realize T 0 ψ hψ t s).mpr
              ((hbody (HilbertTermQuotient.classOf T t)).mpr (h _))
          have hmem := (hinstances t).mp ht
          simpa only [instanceSentence_formula] using
            (Derivation.theory (instanceSentence 0 ψ hψ t) hmem)
        · intro h d
          let t := HilbertTermQuotient.representative d
          have hall : Derivation T (allVariable 0 ψ) := by
            rw [allVariable_openUnary]
            exact .theory φ.all h
          have ht : Derivation T (sentenceFormula (instanceSentence 0 ψ hψ t)) := by
            rw [instanceSentence_formula]
            exact hall.specialize 0 (ClosedTerm.embed t)
          have hmem := (MaximalConsistency.derivation_iff_mem maximal _).mp ht
          have hreal := (instanceSentence_realize T 0 ψ hψ t s).mp
            ((hinstances t).mpr hmem)
          dsimp only [t] at hreal
          rw [HilbertTermQuotient.classOf_representative] at hreal
          exact (hbody d).mp hreal
  exact hmain (formulaSize σ) σ rfl

theorem bounded_truth {T : L.Theory} (maximal : Maximal Consistent T)
    (witnesses : HasWitnesses T) (t₀ : L.Term Empty) {α : Type} {n : Nat}
    (φ : L.BoundedFormula α n) (s : α → L.Term Empty) (ts : Fin n → L.Term Empty) :
    φ.Realize (fun a => HilbertTermQuotient.classOf T (s a))
        (fun i => HilbertTermQuotient.classOf T (ts i)) ↔ instanceFormula φ s ts ∈ T :=
  (instanceFormula_realize T φ s ts).symm.trans
    (sentence_truth maximal witnesses t₀ (instanceFormula φ s ts))

theorem bounded_truth_quotient {T : L.Theory} (maximal : Maximal Consistent T)
    (witnesses : HasWitnesses T) (t₀ : L.Term Empty) {α : Type} {n : Nat}
    (φ : L.BoundedFormula α n) (s : α → HilbertTermQuotient.Domain T)
    (ts : Fin n → HilbertTermQuotient.Domain T) :
    φ.Realize s ts ↔ instanceFormula φ
      (fun a => HilbertTermQuotient.representative (s a))
      (fun i => HilbertTermQuotient.representative (ts i)) ∈ T := by
  simpa only [HilbertTermQuotient.classOf_representative] using
    bounded_truth maximal witnesses t₀ φ
      (fun a => HilbertTermQuotient.representative (s a))
      (fun i => HilbertTermQuotient.representative (ts i))

theorem theory_model {T : L.Theory} (maximal : Maximal Consistent T)
    (witnesses : HasWitnesses T) (t₀ : L.Term Empty) :
    letI : Nonempty (HilbertTermQuotient.Domain T) := HilbertTermQuotient.domain_nonempty T t₀
    FirstOrder.Language.Theory.Model (HilbertTermQuotient.Domain T) T := by
  letI : Nonempty (HilbertTermQuotient.Domain T) := HilbertTermQuotient.domain_nonempty T t₀
  exact ⟨fun σ hσ => (sentence_truth maximal witnesses t₀ σ).mpr hσ⟩

theorem sentence_counterexample {T : L.Theory} (maximal : Maximal Consistent T)
    (witnesses : HasWitnesses T) (t₀ : L.Term Empty) (σ : L.Sentence) (hσ : σ ∉ T) :
    ¬σ.Realize (HilbertTermQuotient.Domain T) :=
  fun h => hσ ((sentence_truth maximal witnesses t₀ σ).mp h)

end Alexander313.FirstOrderCalculus.HilbertHenkinTruth
