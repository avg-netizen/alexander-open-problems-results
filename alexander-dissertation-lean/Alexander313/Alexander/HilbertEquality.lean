import Alexander313.Alexander.HilbertLindenbaum

/-!
# Native Hilbert equality laws and symbol congruence

All equality rules below are consequences of the unchanged reflexivity and
formula-substitution axioms. A bound on the finitely many variable names in
the actual terms supplies a fresh name. Symbol congruence replaces each tuple
coordinate in turn; no semantic equality laws or completeness input is used.
-/

namespace Alexander313.FirstOrderCalculus

universe u v

variable {L : FirstOrder.Language.{u, v}}

namespace HilbertEquality

def termBound : L.Term Nat → Nat
  | .var x => x + 1
  | .func _ ts => Finset.univ.sup (fun i => termBound (ts i))

def termSubstitute (x : Nat) (replacement t : L.Term Nat) : L.Term Nat :=
  t.subst (fun y => if y = x then replacement else .var y)

@[simp] theorem termSubstitute_var (x : Nat) (replacement : L.Term Nat) :
    termSubstitute x replacement (.var x) = replacement := by
  simp [termSubstitute, FirstOrder.Language.Term.subst]

@[simp] theorem termSubstitute_func (x : Nat) (replacement : L.Term Nat)
    {n : Nat} (f : L.Functions n) (ts : Fin n → L.Term Nat) :
    termSubstitute x replacement (.func f ts) =
      .func f (fun i => termSubstitute x replacement (ts i)) := rfl

theorem termSubstitute_fix (x : Nat) (replacement t : L.Term Nat)
    (fresh : termBound t ≤ x) : termSubstitute x replacement t = t := by
  revert fresh
  induction t with
  | var y =>
    intro h
    have hy : y ≠ x := by simp only [termBound] at h; omega
    simp [termSubstitute, FirstOrder.Language.Term.subst, hy]
  | func f ts ih =>
    intro h
    rw [termSubstitute_func]
    congr 1
    funext i
    apply ih i
    exact le_trans (Finset.le_sup (f := fun j => termBound (ts j)) (Finset.mem_univ i)) h

private theorem termSubst_lift (g : Nat → L.Term Nat) (t : L.Term Nat) :
    (t.relabel (Sum.inl : Nat → Nat ⊕ Fin 0)).subst
        (Sum.elim (fun x => (g x).relabel Sum.inl) (fun i => .var (.inr i))) =
      (t.subst g).relabel Sum.inl := by
  induction t <;>
    simp_all [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst]

@[simp] theorem substituteVariable_equal (x : Nat) (replacement t s : L.Term Nat) :
    substituteVariable x replacement (t.equal s) =
      (termSubstitute x replacement t).equal (termSubstitute x replacement s) := by
  change FirstOrder.Language.BoundedFormula.equal
      ((t.relabel Sum.inl).subst
        (Sum.elim (fun y => ((if y = x then replacement else .var y) : L.Term Nat).relabel Sum.inl)
          (fun i => .var (.inr i))))
      ((s.relabel Sum.inl).subst
        (Sum.elim (fun y => ((if y = x then replacement else .var y) : L.Term Nat).relabel Sum.inl)
          (fun i => .var (.inr i)))) = _
  rw [termSubst_lift, termSubst_lift]
  rfl

def relationAtom {n : Nat} (r : L.Relations n) (ts : Fin n → L.Term Nat) : L.Formula Nat :=
  .rel r (fun i => (ts i).relabel Sum.inl)

@[simp] theorem substituteVariable_relationAtom (x : Nat) (replacement : L.Term Nat)
    {n : Nat} (r : L.Relations n) (ts : Fin n → L.Term Nat) :
    substituteVariable x replacement (relationAtom r ts) =
      relationAtom r (fun i => termSubstitute x replacement (ts i)) := by
  change FirstOrder.Language.BoundedFormula.rel r (fun i => ((ts i).relabel Sum.inl).subst
      (Sum.elim (fun y => ((if y = x then replacement else .var y) : L.Term Nat).relabel Sum.inl)
        (fun i => .var (.inr i)))) = _
  simp only [termSubst_lift]
  rfl

def patch {n : Nat} (ts ss : Fin n → L.Term Nat) (S : Finset (Fin n)) : Fin n → L.Term Nat :=
  fun i => if i ∈ S then ss i else ts i

@[simp] theorem patch_empty {n : Nat} (ts ss : Fin n → L.Term Nat) :
    patch ts ss ∅ = ts := by
  funext i
  simp [patch]

@[simp] theorem patch_univ {n : Nat} (ts ss : Fin n → L.Term Nat) :
    patch ts ss Finset.univ = ss := by
  funext i
  simp [patch]

end HilbertEquality

namespace Derivation

open HilbertEquality

variable {T : L.Theory}

theorem equalRefl (t : L.Term Nat) : Derivation T (t.equal t) := .logical (.eqRefl t)

theorem substituteFormulaCongruence {t s : L.Term Nat} (h : Derivation T (t.equal s))
    (x : Nat) (φ : L.Formula Nat) :
    Derivation T ((substituteVariable x t φ).imp (substituteVariable x s φ)) :=
  .mp (.logical (.eqSubst x t s φ)) h

theorem equalSymm {t s : L.Term Nat} (h : Derivation T (t.equal s)) :
    Derivation T (s.equal t) := by
  let x := termBound t
  have ht (replacement : L.Term Nat) : termSubstitute x replacement t = t :=
    termSubstitute_fix x replacement t le_rfl
  have hs : Derivation T ((t.equal t).imp (s.equal t)) := by
    simpa only [substituteVariable_equal, termSubstitute_var, ht] using
      h.substituteFormulaCongruence x ((FirstOrder.Language.Term.var x).equal t)
  exact .mp hs (equalRefl t)

theorem equalTrans {t s r : L.Term Nat} (hts : Derivation T (t.equal s))
    (hsr : Derivation T (s.equal r)) : Derivation T (t.equal r) := by
  let x := termBound t
  have ht (replacement : L.Term Nat) : termSubstitute x replacement t = t :=
    termSubstitute_fix x replacement t le_rfl
  have hs : Derivation T ((t.equal s).imp (t.equal r)) := by
    simpa only [substituteVariable_equal, termSubstitute_var, ht] using
      hsr.substituteFormulaCongruence x (t.equal (.var x))
  exact .mp hs hts

/-- One function coordinate is replaced by the equality axiom with a fresh
    variable in that coordinate and every other actual argument held fixed. -/
theorem functionCoordinate {n : Nat} (f : L.Functions n) (ts : Fin n → L.Term Nat)
    (i : Fin n) (s : L.Term Nat) (h : Derivation T ((ts i).equal s)) :
    Derivation T ((FirstOrder.Language.Term.func f ts).equal
      (.func f (fun j => if j = i then s else ts j))) := by
  classical
  let x := Finset.univ.sup (fun j => termBound (ts j))
  let template : L.Term Nat := .func f (fun j => if j = i then .var x else ts j)
  have hfix (replacement : L.Term Nat) (j : Fin n) : termSubstitute x replacement (ts j) = ts j :=
    termSubstitute_fix x replacement (ts j)
      (Finset.le_sup (f := fun k => termBound (ts k)) (Finset.mem_univ j))
  have hbase (replacement : L.Term Nat) :
      termSubstitute x replacement (.func f ts) = .func f ts := by
    rw [termSubstitute_func]
    congr 1
    funext j
    exact hfix replacement j
  have htemplate (replacement : L.Term Nat) :
      termSubstitute x replacement template = .func f (fun j => if j = i then replacement else ts j) := by
    rw [show template = .func f (fun j => if j = i then .var x else ts j) from rfl,
      termSubstitute_func]
    congr 1
    funext j
    by_cases hj : j = i <;> simp [hj, termSubstitute_var, hfix]
  have hsource : termSubstitute x (ts i) template = .func f ts := by
    rw [htemplate]
    congr 1
    funext j
    by_cases hj : j = i
    · subst j; simp
    · simp [hj]
  have hs : Derivation T
      (((FirstOrder.Language.Term.func f ts).equal (.func f ts)).imp
        ((FirstOrder.Language.Term.func f ts).equal (.func f (fun j => if j = i then s else ts j)))) := by
    simpa only [substituteVariable_equal, hbase, hsource, htemplate] using
      h.substituteFormulaCongruence x ((FirstOrder.Language.Term.func f ts).equal template)
  exact .mp hs (equalRefl (.func f ts))

theorem functionCongruence {n : Nat} (f : L.Functions n) (ts ss : Fin n → L.Term Nat)
    (h : ∀ i, Derivation T ((ts i).equal (ss i))) :
    Derivation T ((FirstOrder.Language.Term.func f ts).equal (.func f ss)) := by
  classical
  have hpatch (S : Finset (Fin n)) :
      Derivation T ((FirstOrder.Language.Term.func f ts).equal (.func f (patch ts ss S))) := by
    induction S using Finset.induction_on with
    | empty => simpa only [patch_empty] using equalRefl (.func f ts)
    | @insert i S hi ih =>
      have hcoordinate : Derivation T (((patch ts ss S) i).equal (ss i)) := by
        simpa only [patch, hi, if_false] using h i
      have hs := functionCoordinate f (patch ts ss S) i (ss i) hcoordinate
      have htuple : (fun j => if j = i then ss i else patch ts ss S j) = patch ts ss (insert i S) := by
        funext j
        by_cases hj : j = i
        · subst j; simp [patch]
        · simp [patch, hj]
      exact ih.equalTrans (by simpa only [htuple] using hs)
  simpa only [patch_univ] using hpatch Finset.univ

theorem relationCoordinate {n : Nat} (r : L.Relations n) (ts : Fin n → L.Term Nat)
    (i : Fin n) (s : L.Term Nat) (h : Derivation T ((ts i).equal s)) :
    Derivation T ((relationAtom r ts).imp
      (relationAtom r (fun j => if j = i then s else ts j))) := by
  classical
  let x := Finset.univ.sup (fun j => termBound (ts j))
  let template : Fin n → L.Term Nat := fun j => if j = i then .var x else ts j
  have hfix (replacement : L.Term Nat) (j : Fin n) : termSubstitute x replacement (ts j) = ts j :=
    termSubstitute_fix x replacement (ts j)
      (Finset.le_sup (f := fun k => termBound (ts k)) (Finset.mem_univ j))
  have htemplate (replacement : L.Term Nat) :
      (fun j => termSubstitute x replacement (template j)) =
        fun j => if j = i then replacement else ts j := by
    funext j
    by_cases hj : j = i <;> simp [template, hj, termSubstitute_var, hfix]
  have hsource : (fun j => termSubstitute x (ts i) (template j)) = ts := by
    rw [htemplate]
    funext j
    by_cases hj : j = i
    · subst j; simp
    · simp [hj]
  simpa only [substituteVariable_relationAtom, hsource, htemplate] using
    h.substituteFormulaCongruence x (relationAtom r template)

theorem relationCongruence {n : Nat} (r : L.Relations n) (ts ss : Fin n → L.Term Nat)
    (h : ∀ i, Derivation T ((ts i).equal (ss i))) :
    Derivation T ((relationAtom r ts).imp (relationAtom r ss)) := by
  classical
  have hpatch (S : Finset (Fin n)) :
      Derivation T ((relationAtom r ts).imp (relationAtom r (patch ts ss S))) := by
    induction S using Finset.induction_on with
    | empty => simpa only [patch_empty] using impRefl (relationAtom r ts)
    | @insert i S hi ih =>
      have hcoordinate : Derivation T (((patch ts ss S) i).equal (ss i)) := by
        simpa only [patch, hi, if_false] using h i
      have hs := relationCoordinate r (patch ts ss S) i (ss i) hcoordinate
      have htuple : (fun j => if j = i then ss i else patch ts ss S j) = patch ts ss (insert i S) := by
        funext j
        by_cases hj : j = i
        · subst j; simp [patch]
        · simp [patch, hj]
      exact ih.impTrans (by simpa only [htuple] using hs)
  simpa only [patch_univ] using hpatch Finset.univ

theorem relationDerivable_iff {n : Nat} (r : L.Relations n) (ts ss : Fin n → L.Term Nat)
    (h : ∀ i, Derivation T ((ts i).equal (ss i))) :
    Derivation T (relationAtom r ts) ↔ Derivation T (relationAtom r ss) :=
  ⟨fun ht => .mp (relationCongruence r ts ss h) ht,
    fun hs => .mp (relationCongruence r ss ts (fun i => (h i).equalSymm)) hs⟩

end Derivation

end Alexander313.FirstOrderCalculus
