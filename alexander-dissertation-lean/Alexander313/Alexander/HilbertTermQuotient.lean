import Alexander313.Alexander.HilbertEquality
import Alexander313.Alexander.HilbertClosedSyntax

/-!
# The actual Hilbert quotient of closed native terms

Closed terms are native terms over `Empty`. The equivalence relation is the
existing Hilbert derivability of their embedded equality. Reflexivity,
symmetry, transitivity and function/relation congruence are derived in
`HilbertEquality`, rather than supplied as fields of a semantic contract.

The quotient carries an actual language structure. Choosing representatives
defines its operations, and the proved congruence laws show independence from
that choice. Atomic equality and relations are proved exact. Nonemptiness
requires an actual closed term; no such term is invented for arbitrary
languages. Henkin witness extension and quantified truth remain separate.
-/

noncomputable section

namespace Alexander313.FirstOrderCalculus.HilbertTermQuotient

universe u v

variable {L : FirstOrder.Language.{u, v}}

abbrev ClosedTerm (L : FirstOrder.Language.{u, v}) := L.Term Empty

def embed (t : ClosedTerm L) : L.Term Nat := t.relabel Empty.elim

@[simp] theorem embed_func {n : Nat} (f : L.Functions n) (ts : Fin n → ClosedTerm L) :
    embed (.func f ts) = .func f (fun i => embed (ts i)) := rfl

def termSetoid (T : L.Theory) : Setoid (ClosedTerm L) where
  r := fun t s => Derivation T ((embed t).equal (embed s))
  iseqv := ⟨fun t => Derivation.equalRefl (embed t),
    fun h => h.equalSymm, fun h k => h.equalTrans k⟩

abbrev Domain (T : L.Theory) := Quotient (termSetoid T)

def classOf (T : L.Theory) (t : ClosedTerm L) : Domain T := Quotient.mk (termSetoid T) t

@[simp] theorem classOf_eq_iff (T : L.Theory) (t s : ClosedTerm L) :
    classOf T t = classOf T s ↔ Derivation T ((embed t).equal (embed s)) :=
  ⟨Quotient.exact, fun h => Quotient.sound h⟩

def representative {T : L.Theory} (q : Domain T) : ClosedTerm L := Quotient.out q

@[simp] theorem classOf_representative {T : L.Theory} (q : Domain T) :
    classOf T (representative q) = q := Quotient.out_eq q

theorem representative_classOf {T : L.Theory} (t : ClosedTerm L) :
    Derivation T ((embed (representative (classOf T t))).equal (embed t)) :=
  (classOf_eq_iff T _ _).mp (classOf_representative (classOf T t))

theorem domain_nonempty (T : L.Theory) (t : ClosedTerm L) : Nonempty (Domain T) :=
  ⟨classOf T t⟩

def functionMap (T : L.Theory) {n : Nat} (f : L.Functions n)
    (xs : Fin n → Domain T) : Domain T :=
  classOf T (.func f (fun i => representative (xs i)))

theorem functionMap_wellDefined (T : L.Theory) {n : Nat} (f : L.Functions n)
    (ts ss : Fin n → ClosedTerm L)
    (h : ∀ i, Derivation T ((embed (ts i)).equal (embed (ss i)))) :
    classOf T (.func f ts) = classOf T (.func f ss) := by
  apply (classOf_eq_iff T _ _).mpr
  simpa only [embed_func] using
    Derivation.functionCongruence f (fun i => embed (ts i)) (fun i => embed (ss i)) h

@[simp] theorem functionMap_classOf (T : L.Theory) {n : Nat} (f : L.Functions n)
    (ts : Fin n → ClosedTerm L) :
    functionMap T f (fun i => classOf T (ts i)) = classOf T (.func f ts) := by
  exact functionMap_wellDefined T f
    (fun i => representative (classOf T (ts i))) ts (fun i => representative_classOf (ts i))

def relationMap (T : L.Theory) {n : Nat} (r : L.Relations n)
    (xs : Fin n → Domain T) : Prop :=
  Derivation T (HilbertEquality.relationAtom r (fun i => embed (representative (xs i))))

theorem relationMap_wellDefined (T : L.Theory) {n : Nat} (r : L.Relations n)
    (ts ss : Fin n → ClosedTerm L)
    (h : ∀ i, Derivation T ((embed (ts i)).equal (embed (ss i)))) :
    Derivation T (HilbertEquality.relationAtom r (fun i => embed (ts i))) ↔
      Derivation T (HilbertEquality.relationAtom r (fun i => embed (ss i))) :=
  Derivation.relationDerivable_iff r _ _ h

@[simp] theorem relationMap_classOf (T : L.Theory) {n : Nat} (r : L.Relations n)
    (ts : Fin n → ClosedTerm L) :
    relationMap T r (fun i => classOf T (ts i)) ↔
      Derivation T (HilbertEquality.relationAtom r (fun i => embed (ts i))) :=
  relationMap_wellDefined T r (fun i => representative (classOf T (ts i))) ts
    (fun i => representative_classOf (ts i))

instance termStructure (T : L.Theory) : L.Structure (Domain T) where
  funMap := functionMap T
  RelMap := relationMap T

@[simp] theorem closedTerm_realize (T : L.Theory) (t : ClosedTerm L) :
    t.realize (default : Empty → Domain T) = classOf T t := by
  induction t with
  | var e => exact Empty.elim e
  | func f ts ih =>
    change functionMap T f (fun i => (ts i).realize (default : Empty → Domain T)) = _
    have htuple : (fun i => (ts i).realize (default : Empty → Domain T)) =
        fun i => classOf T (ts i) := funext ih
    rw [htuple, functionMap_classOf]

@[simp] theorem closedTerm_relabel_realize (T : L.Theory) (t : ClosedTerm L)
    {α : Type} (ρ : Empty → α) (s : α → Domain T) :
    (t.relabel ρ).realize s = classOf T t := by
  induction t with
  | var e => exact Empty.elim e
  | func f ts ih =>
    change functionMap T f (fun i => ((ts i).relabel ρ).realize s) = _
    have htuple : (fun i => ((ts i).relabel ρ).realize s) =
        fun i => classOf T (ts i) := funext ih
    rw [htuple, functionMap_classOf]

def relationSentence {n : Nat} (r : L.Relations n) (ts : Fin n → ClosedTerm L) : L.Sentence :=
  .rel r (fun i => (ts i).relabel Sum.inl)

theorem equal_realize (T : L.Theory) (t s : ClosedTerm L) :
    FirstOrder.Language.Sentence.Realize (Domain T) (t.equal s) ↔
      Derivation T ((embed t).equal (embed s)) := by
  change FirstOrder.Language.Formula.Realize (t.equal s) (default : Empty → Domain T) ↔ _
  rw [FirstOrder.Language.Formula.realize_equal, closedTerm_realize, closedTerm_realize]
  exact classOf_eq_iff T t s

theorem relation_realize (T : L.Theory) {n : Nat} (r : L.Relations n)
    (ts : Fin n → ClosedTerm L) :
    (relationSentence r ts).Realize (Domain T) ↔
      Derivation T (HilbertEquality.relationAtom r (fun i => embed (ts i))) := by
  change relationMap T r (fun i => ((ts i).relabel Sum.inl).realize
    (Sum.elim (default : Empty → Domain T) (default : Fin 0 → Domain T))) ↔ _
  have htuple : (fun i => ((ts i).relabel Sum.inl).realize
      (Sum.elim (default : Empty → Domain T) (default : Fin 0 → Domain T))) =
      fun i => classOf T (ts i) := by
    funext i
    exact closedTerm_relabel_realize T (ts i) Sum.inl _
  rw [htuple]
  exact relationMap_classOf T r ts

theorem equal_realize_iff_mem {T : L.Theory} (maximal : Maximal Consistent T)
    (t s : ClosedTerm L) :
    FirstOrder.Language.Sentence.Realize (Domain T) (t.equal s) ↔ t.equal s ∈ T := by
  rw [equal_realize]
  have h := MaximalConsistency.derivation_iff_mem maximal (t.equal s)
  rw [ClosedFormula.sentenceFormula_equal] at h
  exact h

theorem relation_realize_iff_mem {T : L.Theory} (maximal : Maximal Consistent T)
    {n : Nat} (r : L.Relations n) (ts : Fin n → ClosedTerm L) :
    (relationSentence r ts).Realize (Domain T) ↔ relationSentence r ts ∈ T := by
  rw [relation_realize]
  have h := MaximalConsistency.derivation_iff_mem maximal (ClosedFormula.relation r ts)
  rw [ClosedFormula.sentenceFormula_relation] at h
  exact h

theorem falsum_realize_iff_mem {T : L.Theory} (maximal : Maximal Consistent T) :
    (⊥ : L.Sentence).Realize (Domain T) ↔ (⊥ : L.Sentence) ∈ T := by
  change False ↔ (⊥ : L.Sentence) ∈ T
  exact ⟨False.elim, fun h => MaximalConsistency.falsum_not_mem maximal h⟩

theorem imp_realize_iff_mem {T : L.Theory} (maximal : Maximal Consistent T)
    (σ τ : L.Sentence)
    (hσ : σ.Realize (Domain T) ↔ σ ∈ T)
    (hτ : τ.Realize (Domain T) ↔ τ ∈ T) :
    FirstOrder.Language.Sentence.Realize (Domain T) (σ.imp τ) ↔ σ.imp τ ∈ T := by
  classical
  change (σ.Realize (Domain T) → τ.Realize (Domain T)) ↔ σ.imp τ ∈ T
  rw [hσ, hτ, MaximalConsistency.imp_mem_iff maximal]
  constructor
  · intro h
    by_cases hs : σ ∈ T
    · exact Or.inr (h hs)
    · exact Or.inl hs
  · rintro (hs | ht) hσ
    · exact False.elim (hs hσ)
    · exact ht

end Alexander313.FirstOrderCalculus.HilbertTermQuotient
