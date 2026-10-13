import Alexander313.Alexander.DeltaNaturality
import Alexander313.Alexander.NativeFreeVariables

/-!
# Actual primitive-recursive Δ formation

The raw algorithms consume the existing literal source term/formula codes and
produce the existing native labels. Quantifier nodes use the proved literal
bottom-up Δ laws; opaque modal arguments are only used as relation labels and
to form their sorted argument tuples.
-/

namespace Alexander313.Delta

private def freeLeaf (_ : Unit) (x : Nat) : Nat :=
  EncodedSyntax.node 0 (Nat.pair 0 x)

private theorem freeLeaf_primrec : Primrec₂ freeLeaf :=
  (EncodedSyntax.node_primrec.comp (Primrec.const 0)
    (Primrec₂.natPair.comp (Primrec.const 0) Primrec.snd)).to₂

def termCode (c : Nat) : Nat := NativeTerm.rewriteCode freeLeaf () c

theorem termCode_primrec : Primrec termCode :=
  (NativeTerm.rewriteCode_primrec freeLeaf_primrec).comp (Primrec.const ()) Primrec.id

@[simp] theorem termCode_code (t : Term) :
    termCode t.code = NativeTerm.code (n := 0) (term (Owner := Nat) Sum.inl t) := by
  induction t <;> simp_all [termCode, term, NativeTerm.rewriteCode, freeLeaf,
    Term.code, NativeTerm.code, NativeTerm.toLiteral, NativeTerm.variableCode,
    FirstOrder.Language.Functions.apply₁, FirstOrder.Language.Functions.apply₂,
    Nat.unpair_pair, EncodedSyntax.node]

theorem term_primrec : Primrec (fun t : Term => term (Owner := Nat) id t) := by
  apply Primrec.encode_iff.1
  have ht (t : Term) : NativeTerm.freeCode (term (Owner := Nat) id t) = termCode t.code := by
    rw [← NativeTerm.freeCode_relabel (n := 0)]
    have h : ((term (Owner := Nat) id t).relabel Sum.inl : NativeTerm.Syntax 0) =
        term Sum.inl t := by
      induction t <;> simp_all [term, FirstOrder.Language.Term.relabel,
        FirstOrder.Language.Functions.apply₁, FirstOrder.Language.Functions.apply₂] <;>
          funext i <;> fin_cases i <;> simp_all
    rw [h, termCode_code]
  exact (termCode_primrec.comp Term.code_primrec).of_eq (fun t => (ht t).symm)

def nativeNode (n tag payload : Nat) : Nat := Nat.pair n (Nat.pair tag payload + 1) + 1

theorem nativeNode_primrec :
    Primrec (fun p : (Nat × Nat) × Nat => nativeNode p.1.1 p.1.2 p.2) :=
  Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.fst)
    (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)))

def impCode (c e : Nat) : Nat := nativeNode 0 3 (Nat.pair c e)
def notCode (c : Nat) : Nat := impCode c (nativeNode 0 0 0)
def allCode (x c : Nat) : Nat := nativeNode 0 4 (NativeFormula.bindCode x c)

theorem impCode_primrec : Primrec₂ impCode :=
  (nativeNode_primrec.comp
    (((Primrec.const 0).pair (Primrec.const 3)).pair Primrec₂.natPair)).to₂

theorem notCode_primrec : Primrec notCode :=
  impCode_primrec.comp Primrec.id (Primrec.const (nativeNode 0 0 0))

theorem allCode_primrec : Primrec₂ allCode :=
  (nativeNode_primrec.comp (((Primrec.const 0).pair (Primrec.const 4)).pair
    NativeFormula.bindCode_primrec)).to₂

@[simp] theorem impCode_code (φ ψ : NativeFormula.Syntax 0) :
    impCode (NativeFormula.code φ) (NativeFormula.code ψ) = NativeFormula.code (φ.imp ψ) := rfl

@[simp] theorem notCode_code (φ : NativeFormula.Syntax 0) : notCode (NativeFormula.code φ) = NativeFormula.code φ.not := rfl

@[simp] theorem allCode_code (x : Nat) (φ : NativeFormula.Syntax 0) :
    allCode x (NativeFormula.code φ) = NativeFormula.code (FirstOrderCalculus.allVariable x φ) := by
  simp only [allCode, nativeNode, NativeFormula.bindCode_code,
    FirstOrderCalculus.allVariable, NativeFormula.code_all]

def modalTupleCode (c : Nat) : Nat :=
  Encodable.encode ((Formula.freeVariablesCode c).map (fun x => EncodedSyntax.node 0 (Nat.pair 0 x)))

theorem modalTupleCode_primrec : Primrec modalTupleCode :=
  Primrec.encode.comp (Primrec.list_map Formula.freeVariablesCode_primrec
    ((EncodedSyntax.node_primrec.comp (Primrec.const 0)
      (Primrec₂.natPair.comp (Primrec.const 0) Primrec.snd)).to₂))

private theorem freeTuple_list (φ : Formula Nat) : List.ofFn (freeTuple φ) = φ.freeVars.sort (· ≤ ·) := by
  simpa only [freeTuple, List.finRange, List.map_ofFn, Function.comp_def, id_eq] using
    Finset.listMap_orderEmbOfFin_finRange φ.freeVars rfl

@[simp] theorem modalTupleCode_code (φ : Formula Nat) :
    modalTupleCode (φ.code id) = NativeTuple.code
      (fun i => (.var (.inl (freeTuple φ i)) : NativeTerm.Syntax 0)) := by
  simp only [modalTupleCode, Formula.freeVariablesCode_code, NativeTuple.code,
    NativeTerm.code_var, NativeTerm.variableCode]
  rw [← freeTuple_list φ, List.map_ofFn]
  rfl

def formulaCode : Nat → Nat
  | 0 => 0
  | k + 1 =>
    let tag := k.unpair.1
    let p := k.unpair.2
    cond (tag == 0) (nativeNode 0 0 0)
      (cond (tag == 1) (nativeNode 0 1 (Nat.pair (termCode p.unpair.1) (termCode p.unpair.2)))
        (cond (tag == 2) (impCode (formulaCode p.unpair.1) (formulaCode p.unpair.2))
          (cond (tag == 3) (notCode (impCode (formulaCode p.unpair.1) (notCode (formulaCode p.unpair.2))))
            (cond (tag == 4) (impCode (notCode (formulaCode p.unpair.1)) (formulaCode p.unpair.2))
              (cond (tag == 5) (notCode (formulaCode p))
                (cond (tag == 6) (allCode p.unpair.1 (formulaCode p.unpair.2))
                  (cond (tag == 7) (notCode (allCode p.unpair.1 (notCode (formulaCode p.unpair.2))))
                    (cond (tag == 8) (nativeNode 0 2 (Nat.pair p (modalTupleCode p.unpair.2))) 0))))))))
termination_by c => c
decreasing_by
  all_goals
    have hp := Nat.unpair_right_le k
    have hl := Nat.unpair_left_le k.unpair.2
    have hr := Nat.unpair_right_le k.unpair.2
    omega

private def formationStep (h : List Nat) : Nat :=
  let k := h.length - 1
  let tag := k.unpair.1
  let p := k.unpair.2
  let left := h[p.unpair.1]?.getD 0
  let right := h[p.unpair.2]?.getD 0
  cond (h.length == 0) 0
    (cond (tag == 0) (nativeNode 0 0 0)
      (cond (tag == 1) (nativeNode 0 1 (Nat.pair (termCode p.unpair.1) (termCode p.unpair.2)))
        (cond (tag == 2) (impCode left right)
          (cond (tag == 3) (notCode (impCode left (notCode right)))
            (cond (tag == 4) (impCode (notCode left) right)
              (cond (tag == 5) (notCode (h[p]?.getD 0))
                (cond (tag == 6) (allCode p.unpair.1 right)
                  (cond (tag == 7) (notCode (allCode p.unpair.1 (notCode right)))
                    (cond (tag == 8) (nativeNode 0 2 (Nat.pair p (modalTupleCode p.unpair.2))) 0)))))))))

set_option maxHeartbeats 800000 in
private theorem formationStep_primrec : Primrec formationStep := by
  have hn := (Primrec.list_length : Primrec (List.length (α := Nat)))
  have hk := Primrec.nat_sub.comp hn (Primrec.const 1)
  have ht := Primrec.fst.comp (Primrec.unpair.comp hk)
  have hp := Primrec.snd.comp (Primrec.unpair.comp hk)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hp)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hp)
  have test (t : Nat) := Primrec.beq.comp ht (Primrec.const t)
  have get (f : List Nat → Nat) (hf : Primrec f) : Primrec (fun h : List Nat => h[f h]?.getD 0) :=
    Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.id hf) (Primrec.const 0)
  have node (tag : Nat) (f : List Nat → Nat) (hf : Primrec f) :=
    nativeNode_primrec.comp (((Primrec.const 0).pair (Primrec.const tag)).pair hf)
  have left := get _ hl
  have right := get _ hr
  exact (Primrec.beq.comp hn (Primrec.const 0)).cond (Primrec.const 0)
    ((test 0).cond (Primrec.const (nativeNode 0 0 0))
      ((test 1).cond (node 1 _ (Primrec₂.natPair.comp
        (termCode_primrec.comp hl) (termCode_primrec.comp hr)))
        ((test 2).cond (impCode_primrec.comp left right)
          ((test 3).cond (notCode_primrec.comp
            (impCode_primrec.comp left (notCode_primrec.comp right)))
            ((test 4).cond (impCode_primrec.comp (notCode_primrec.comp left) right)
              ((test 5).cond (notCode_primrec.comp (get _ hp))
                ((test 6).cond (allCode_primrec.comp hl right)
                  ((test 7).cond (notCode_primrec.comp
                    (allCode_primrec.comp hl (notCode_primrec.comp right)))
                    ((test 8).cond (node 2 _ (Primrec₂.natPair.comp hp
                      (modalTupleCode_primrec.comp hr))) (Primrec.const 0))))))))))

theorem formulaCode_primrec : Primrec formulaCode := by
  have hg : Primrec₂ (fun (_ : Unit) (h : List Nat) => some (formationStep h)) :=
    ((Primrec.option_some.comp formationStep_primrec).comp Primrec.snd).to₂
  have htable := Primrec.nat_strong_rec (fun (_ : Unit) c => formulaCode c) hg (by
    intro a c
    cases c with
    | zero => simp [formationStep, formulaCode]
    | succ k =>
      have hp : k.unpair.2 < k + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le k)
      have hl := lt_of_le_of_lt (Nat.unpair_left_le k.unpair.2) hp
      have hr := lt_of_le_of_lt (Nat.unpair_right_le k.unpair.2) hp
      simp [formationStep, formulaCode, hp, hl, hr])
  exact htable.comp (Primrec.const ()) Primrec.id

@[simp] theorem formulaCode_code (φ : Formula Nat) :
    formulaCode (φ.code id) = NativeFormula.code (formula φ) := by
  induction φ with
  | falsum => simp [Formula.code, formulaCode, formula, formulaAux, nativeNode, NativeFormula.code]
  | equal t u => simp [Formula.code, formulaCode, formula, formulaAux, nativeNode,
      Nat.unpair_pair, termCode_code, NativeFormula.code_equal]
  | imp φ ψ ihφ ihψ =>
    simp [Formula.code, formulaCode, formula, formulaAux, impCode, nativeNode,
      Nat.unpair_pair, ihφ, ihψ, NativeFormula.code_imp]
  | conj φ ψ ihφ ihψ =>
    change formulaCode (Nat.pair 3 (Nat.pair (φ.code id) (ψ.code id)) + 1) =
      NativeFormula.code (((formula φ).imp (formula ψ).not).not)
    simp [formulaCode, Nat.unpair_pair, ihφ, ihψ, notCode, impCode, nativeNode,
      FirstOrder.Language.BoundedFormula.not, NativeFormula.code]
  | disj φ ψ ihφ ihψ =>
    change formulaCode (Nat.pair 4 (Nat.pair (φ.code id) (ψ.code id)) + 1) =
      NativeFormula.code ((formula φ).not.imp (formula ψ))
    simp [formulaCode, Nat.unpair_pair, ihφ, ihψ]
  | neg φ ih =>
    change formulaCode (Nat.pair 5 (φ.code id) + 1) = NativeFormula.code ((formula φ).not)
    simp [formulaCode, Nat.unpair_pair, ih]
  | all x φ ih =>
    rw [formula_all]
    simp [Formula.code, formulaCode, Nat.unpair_pair, ih]
  | ex x φ ih =>
    rw [formula_ex]
    simp [Formula.code, formulaCode, Nat.unpair_pair, ih]
  | know a φ ih =>
    simp [Formula.code, formulaCode, formula, formulaAux, Nat.unpair_pair,
      nativeNode, NativeFormula.code_rel, NativeFormula.relationCode, modalSymbol]

theorem formula_primrec : Primrec (formula (Owner := Nat)) := by
  apply Primrec.encode_iff.1
  exact (formulaCode_primrec.comp Formula.code_primrec).of_eq formulaCode_code

end Alexander313.Delta
