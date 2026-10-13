import Alexander313.Alexander.NativeFormulaOperations

/-!
# Effective native free-variable occurrences and freshness

These lists contain occurrences, with repetitions permitted. Their membership
is exactly native free-variable membership. Relation-symbol source labels are
opaque: only their argument terms contribute free variables.
-/

namespace Alexander313.Delta

namespace NativeTerm

def variablesCode : Nat → List Nat
  | 0 => []
  | k + 1 =>
    let tag := k.unpair.1
    let p := k.unpair.2
    cond (tag == 0) (cond (p.unpair.1 == 0) [p.unpair.2] [])
      (cond (tag == 2) (variablesCode p)
        (cond ((tag == 3) || (tag == 4))
          (variablesCode p.unpair.1 ++ variablesCode p.unpair.2) []))
termination_by c => c
decreasing_by
  all_goals
    have hp := Nat.unpair_right_le k
    have hl := Nat.unpair_left_le k.unpair.2
    have hr := Nat.unpair_right_le k.unpair.2
    omega

private def variablesStep (h : List (List Nat)) : List Nat :=
  let k := h.length - 1
  let tag := k.unpair.1
  let p := k.unpair.2
  cond (h.length == 0) []
    (cond (tag == 0) (cond (p.unpair.1 == 0) [p.unpair.2] [])
      (cond (tag == 2) (h[p]?.getD [])
        (cond ((tag == 3) || (tag == 4))
          (h[p.unpair.1]?.getD [] ++ h[p.unpair.2]?.getD []) [])))

private theorem variablesStep_primrec : Primrec variablesStep := by
  have hn := (Primrec.list_length : Primrec (List.length (α := List Nat)))
  have hk := Primrec.nat_sub.comp hn (Primrec.const 1)
  have ht := Primrec.fst.comp (Primrec.unpair.comp hk)
  have hp := Primrec.snd.comp (Primrec.unpair.comp hk)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hp)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hp)
  have test (t : Nat) := Primrec.beq.comp ht (Primrec.const t)
  have get (f : List (List Nat) → Nat) (hf : Primrec f) :
      Primrec (fun h : List (List Nat) => h[f h]?.getD []) :=
    Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.id hf) (Primrec.const [])
  exact (Primrec.beq.comp hn (Primrec.const 0)).cond (Primrec.const [])
    ((test 0).cond ((Primrec.beq.comp hl (Primrec.const 0)).cond
      (Primrec.list_cons.comp hr (Primrec.const [])) (Primrec.const []))
      ((test 2).cond (get _ hp)
        ((Primrec.or.comp (test 3) (test 4)).cond
          (Primrec.list_append.comp (get _ hl) (get _ hr)) (Primrec.const []))))

theorem variablesCode_primrec : Primrec variablesCode := by
  have hg : Primrec₂ (fun (_ : Unit) (h : List (List Nat)) => some (variablesStep h)) :=
    ((Primrec.option_some.comp variablesStep_primrec).comp Primrec.snd).to₂
  have htable := Primrec.nat_strong_rec (fun (_ : Unit) c => variablesCode c) hg (by
    intro a c
    cases c with
    | zero => simp [variablesStep, variablesCode]
    | succ k =>
      have hp : k.unpair.2 < k + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le k)
      have hl := lt_of_le_of_lt (Nat.unpair_left_le k.unpair.2) hp
      have hr := lt_of_le_of_lt (Nat.unpair_right_le k.unpair.2) hp
      simp [variablesStep, variablesCode, hp, hl, hr])
  exact htable.comp (Primrec.const ()) Primrec.id

@[simp] theorem mem_variablesCode_code {n : Nat} (t : Syntax n) (x : Nat) :
    x ∈ variablesCode (code t) ↔ x ∈ t.varFinsetLeft := by
  induction t with
  | var v => cases v <;> simp [code, toLiteral, variableCode, Term.code,
      variablesCode, Nat.unpair_pair]
  | func f ts ih =>
    cases f <;> simp_all [code, toLiteral, Term.code, variablesCode, Nat.unpair_pair,
      FirstOrder.Language.Term.varFinsetLeft, Finset.mem_biUnion,
      Fin.exists_fin_zero, Fin.exists_fin_one, Fin.exists_fin_two]

end NativeTerm

namespace NativeTuple

def variablesCode (c : Nat) : List Nat :=
  ((Encodable.decode₂ (List Nat) c).getD []).flatMap NativeTerm.variablesCode

theorem variablesCode_primrec : Primrec variablesCode :=
  Primrec.list_flatMap
    (Primrec.option_getD.comp Primrec.decode₂ (Primrec.const []))
    (NativeTerm.variablesCode_primrec.comp Primrec.snd).to₂

@[simp] theorem mem_variablesCode_code {n m : Nat}
    (ts : Fin m → NativeTerm.Syntax n) (x : Nat) :
    x ∈ variablesCode (code ts) ↔ ∃ i, x ∈ (ts i).varFinsetLeft := by
  simp [variablesCode, code, List.mem_flatMap]

end NativeTuple

namespace NativeFormula

def variablesCode : Nat → List Nat
  | 0 => []
  | k + 1 =>
    let b := k.unpair.2
    let tag := (b - 1).unpair.1
    let p := (b - 1).unpair.2
    cond (tag == 1) (NativeTerm.variablesCode p.unpair.1 ++ NativeTerm.variablesCode p.unpair.2)
      (cond (tag == 2) (NativeTuple.variablesCode p.unpair.2)
        (cond (tag == 3) (variablesCode p.unpair.1 ++ variablesCode p.unpair.2)
          (cond (tag == 4) (variablesCode p) [])))
termination_by c => c
decreasing_by
  all_goals
    have hb := Nat.unpair_right_le k
    have hk := Nat.sub_le k.unpair.2 1
    have hp := Nat.unpair_right_le (k.unpair.2 - 1)
    have hl := Nat.unpair_left_le (k.unpair.2 - 1).unpair.2
    have hr := Nat.unpair_right_le (k.unpair.2 - 1).unpair.2
    omega

private def variablesStep (h : List (List Nat)) : List Nat :=
  let k := h.length - 1
  let b := k.unpair.2
  let tag := (b - 1).unpair.1
  let p := (b - 1).unpair.2
  cond (h.length == 0) []
    (cond (tag == 1) (NativeTerm.variablesCode p.unpair.1 ++ NativeTerm.variablesCode p.unpair.2)
      (cond (tag == 2) (NativeTuple.variablesCode p.unpair.2)
        (cond (tag == 3) (h[p.unpair.1]?.getD [] ++ h[p.unpair.2]?.getD [])
          (cond (tag == 4) (h[p]?.getD []) []))))

private theorem variablesStep_primrec : Primrec variablesStep := by
  have hn := (Primrec.list_length : Primrec (List.length (α := List Nat)))
  have hk := Primrec.nat_sub.comp hn (Primrec.const 1)
  have hb := Primrec.snd.comp (Primrec.unpair.comp hk)
  have hnode := Primrec.unpair.comp (Primrec.nat_sub.comp hb (Primrec.const 1))
  have ht := Primrec.fst.comp hnode
  have hp := Primrec.snd.comp hnode
  have hl := Primrec.fst.comp (Primrec.unpair.comp hp)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hp)
  have test (t : Nat) := Primrec.beq.comp ht (Primrec.const t)
  have get (f : List (List Nat) → Nat) (hf : Primrec f) :
      Primrec (fun h : List (List Nat) => h[f h]?.getD []) :=
    Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.id hf) (Primrec.const [])
  exact (Primrec.beq.comp hn (Primrec.const 0)).cond (Primrec.const [])
    ((test 1).cond (Primrec.list_append.comp
      (NativeTerm.variablesCode_primrec.comp hl) (NativeTerm.variablesCode_primrec.comp hr))
      ((test 2).cond (NativeTuple.variablesCode_primrec.comp hr)
        ((test 3).cond (Primrec.list_append.comp (get _ hl) (get _ hr))
          ((test 4).cond (get _ hp) (Primrec.const [])))))

theorem variablesCode_primrec : Primrec variablesCode := by
  have hg : Primrec₂ (fun (_ : Unit) (h : List (List Nat)) => some (variablesStep h)) :=
    ((Primrec.option_some.comp variablesStep_primrec).comp Primrec.snd).to₂
  have htable := Primrec.nat_strong_rec (fun (_ : Unit) c => variablesCode c) hg (by
    intro a c
    cases c with
    | zero => simp [variablesStep, variablesCode]
    | succ k =>
      have hb := Nat.unpair_right_le k
      have hk := Nat.sub_le k.unpair.2 1
      have hp₀ := Nat.unpair_right_le (k.unpair.2 - 1)
      have hp : (k.unpair.2 - 1).unpair.2 < k + 1 := by omega
      have hl := lt_of_le_of_lt (Nat.unpair_left_le (k.unpair.2 - 1).unpair.2) hp
      have hr := lt_of_le_of_lt (Nat.unpair_right_le (k.unpair.2 - 1).unpair.2) hp
      simp [variablesStep, variablesCode, hp, hl, hr])
  exact htable.comp (Primrec.const ()) Primrec.id

@[simp] theorem mem_variablesCode_code {n : Nat} (φ : Syntax n) (x : Nat) :
    x ∈ variablesCode (code φ) ↔ x ∈ φ.freeVarFinset := by
  induction φ <;> simp_all [variablesCode, code, Nat.unpair_pair, Finset.mem_biUnion]

theorem variablesCode_toFinset {n : Nat} (φ : Syntax n) :
    (variablesCode (code φ)).toFinset = φ.freeVarFinset := by
  ext x
  simp

theorem freeVariableMembership_primrec (n : Nat) :
    PrimrecRel (fun (x : Nat) (φ : Syntax n) => x ∈ φ.freeVarFinset) := by
  have he : PrimrecRel (fun x y : Nat => x = y) := Primrec.eq
  have h := he.exists_mem_list.comp
    (variablesCode_primrec.comp ((code_primrec n).comp Primrec.snd)) Primrec.fst
  exact h.of_eq (fun p => by simp)

def occurrenceList {n : Nat} (φ : Syntax n) : List Nat := variablesCode (code φ)

theorem occurrenceList_primrec (n : Nat) : Primrec (occurrenceList (n := n)) :=
  variablesCode_primrec.comp (code_primrec n)

private theorem foldl_max_ge (a : Nat) (xs : List Nat) : a ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => exact le_rfl
  | cons y ys ih => exact le_trans (le_max_left a y) (ih (max a y))

private theorem mem_le_foldl_max (a : Nat) (xs : List Nat) {x : Nat}
    (hx : x ∈ xs) : x ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with hxy | hx
    · subst x
      exact le_trans (le_max_right a y) (foldl_max_ge (max a y) ys)
    · exact ih (max a y) hx

def freshCode (c : Nat) : Nat := (variablesCode c).foldl max 0 + 1

theorem freshCode_primrec : Primrec freshCode :=
  Primrec.succ.comp (Primrec.list_foldl variablesCode_primrec (Primrec.const 0)
    (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂)

def fresh {n : Nat} (φ : Syntax n) : Nat := freshCode (code φ)

theorem fresh_primrec (n : Nat) : Primrec (fresh (n := n)) :=
  freshCode_primrec.comp (code_primrec n)

theorem fresh_not_mem {n : Nat} (φ : Syntax n) : fresh φ ∉ φ.freeVarFinset := by
  intro hx
  have hm := mem_le_foldl_max 0 (variablesCode (code φ))
    ((mem_variablesCode_code φ (fresh φ)).mpr hx)
  change (variablesCode (code φ)).foldl max 0 + 1 ≤ (variablesCode (code φ)).foldl max 0 at hm
  omega

theorem freeVar_lt_fresh {n : Nat} (φ : Syntax n) {x : Nat} (hx : x ∈ φ.freeVarFinset) :
    x < fresh φ :=
  Nat.lt_succ_of_le (mem_le_foldl_max 0 (variablesCode (code φ))
    ((mem_variablesCode_code φ x).mpr hx))

end NativeFormula

end Alexander313.Delta
