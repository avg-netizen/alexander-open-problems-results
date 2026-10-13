import Alexander313.Alexander.LiteralCoding
import Alexander313.Effective.TermOperations
import Alexander313.Specification

/-!
# Primitive-recursive free variables of actual source labels

The membership algorithms follow the existing literal source codes. A free
variable of a coded term/formula is smaller than its code, so filtering a finite
range gives exactly the finite free-variable set, without a freshness oracle
or an assumed primitive-recursive cardinality operation. This supplies the
actual arities of the modal relation symbols in Δ.
-/

namespace Alexander313

private theorem payload_lt_node (tag payload : Nat) :
    payload < Nat.pair tag payload + 1 :=
  Nat.lt_succ_of_le (Nat.right_le_pair tag payload)

private theorem left_lt_binary_node (tag a b : Nat) :
    a < Nat.pair tag (Nat.pair a b) + 1 :=
  lt_of_le_of_lt (Nat.left_le_pair a b) (payload_lt_node tag _)

private theorem right_lt_binary_node (tag a b : Nat) :
    b < Nat.pair tag (Nat.pair a b) + 1 :=
  lt_of_le_of_lt (Nat.right_le_pair a b) (payload_lt_node tag _)

namespace Term

def freeMemCode (x : Nat) : Nat → Bool
  | 0 => false
  | k + 1 =>
    let tag := k.unpair.1
    let p := k.unpair.2
    cond (tag == 0) (x == p)
      (cond (tag == 2) (freeMemCode x p)
        (cond ((tag == 3) || (tag == 4))
          (freeMemCode x p.unpair.1 || freeMemCode x p.unpair.2) false))
termination_by n => n
decreasing_by
  all_goals
    have hp := Nat.unpair_right_le k
    have hl := Nat.unpair_left_le k.unpair.2
    have hr := Nat.unpair_right_le k.unpair.2
    omega

private def freeMemStep (x : Nat) (h : List Bool) : Bool :=
  let k := h.length - 1
  let tag := k.unpair.1
  let p := k.unpair.2
  cond (h.length == 0) false
    (cond (tag == 0) (x == p)
      (cond (tag == 2) (h[p]?.getD false)
        (cond ((tag == 3) || (tag == 4))
          (h[p.unpair.1]?.getD false || h[p.unpair.2]?.getD false) false)))

private theorem freeMemStep_primrec : Primrec₂ freeMemStep := by
  have hn : Primrec (fun p : Nat × List Bool => p.2.length) :=
    Primrec.list_length.comp Primrec.snd
  have hk := Primrec.nat_sub.comp hn (Primrec.const 1)
  have ht := Primrec.fst.comp (Primrec.unpair.comp hk)
  have hp := Primrec.snd.comp (Primrec.unpair.comp hk)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hp)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hp)
  have test (n : Nat) := Primrec.beq.comp ht (Primrec.const n)
  have get (f : Nat × List Bool → Nat) (hf : Primrec f) :
      Primrec (fun p : Nat × List Bool => p.2[f p]?.getD false) :=
    Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.snd hf)
      (Primrec.const false)
  exact ((Primrec.beq.comp hn (Primrec.const 0)).cond (Primrec.const false)
    ((test 0).cond (Primrec.beq.comp Primrec.fst hp)
      ((test 2).cond (get _ hp)
        ((Primrec.or.comp (test 3) (test 4)).cond
          (Primrec.or.comp (get _ hl) (get _ hr)) (Primrec.const false))))).to₂

theorem freeMemCode_primrec : Primrec₂ freeMemCode := by
  have hg := Primrec.option_some.comp₂ freeMemStep_primrec
  exact Primrec.nat_strong_rec freeMemCode hg (by
    intro x n
    cases n with
    | zero => simp [freeMemStep, freeMemCode]
    | succ k =>
      have hp : k.unpair.2 < k + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le k)
      have hl : k.unpair.2.unpair.1 < k + 1 := lt_of_le_of_lt (Nat.unpair_left_le _) hp
      have hr : k.unpair.2.unpair.2 < k + 1 := lt_of_le_of_lt (Nat.unpair_right_le _) hp
      simp [freeMemStep, freeMemCode, hp, hl, hr])

@[simp] theorem freeMemCode_code (x : Nat) (t : Term) :
    freeMemCode x t.code = decide (x ∈ t.freeVars) := by
  induction t <;> simp_all [freeMemCode, code, freeVars, Nat.unpair_pair, Bool.beq_eq_decide_eq]

theorem freeVars_lt_code (t : Term) {x : Nat} (hx : x ∈ t.freeVars) : x < t.code := by
  induction t with
  | var v =>
    have h : x = v := Finset.mem_singleton.mp hx
    subst x
    exact payload_lt_node 0 v
  | zero => exact False.elim (Finset.notMem_empty x hx)
  | succ t ih => exact lt_trans (ih hx) (payload_lt_node 2 t.code)
  | add t u iht ihu =>
    rcases Finset.mem_union.mp hx with hx | hx
    · exact lt_trans (iht hx) (left_lt_binary_node 3 t.code u.code)
    · exact lt_trans (ihu hx) (right_lt_binary_node 3 t.code u.code)
  | mul t u iht ihu =>
    rcases Finset.mem_union.mp hx with hx | hx
    · exact lt_trans (iht hx) (left_lt_binary_node 4 t.code u.code)
    · exact lt_trans (ihu hx) (right_lt_binary_node 4 t.code u.code)

end Term

namespace Formula

def freeMemCode (x : Nat) : Nat → Bool
  | 0 => false
  | k + 1 =>
    let tag := k.unpair.1
    let p := k.unpair.2
    cond (tag == 1) (Term.freeMemCode x p.unpair.1 || Term.freeMemCode x p.unpair.2)
      (cond ((tag == 2) || (tag == 3) || (tag == 4))
        (freeMemCode x p.unpair.1 || freeMemCode x p.unpair.2)
        (cond (tag == 5) (freeMemCode x p)
          (cond ((tag == 6) || (tag == 7))
            (!(x == p.unpair.1) && freeMemCode x p.unpair.2)
            (cond (tag == 8) (freeMemCode x p.unpair.2) false))))
termination_by n => n
decreasing_by
  all_goals
    have hp := Nat.unpair_right_le k
    have hl := Nat.unpair_left_le k.unpair.2
    have hr := Nat.unpair_right_le k.unpair.2
    omega

private def freeMemStep (x : Nat) (h : List Bool) : Bool :=
  let k := h.length - 1
  let tag := k.unpair.1
  let p := k.unpair.2
  cond (h.length == 0) false
    (cond (tag == 1) (Term.freeMemCode x p.unpair.1 || Term.freeMemCode x p.unpair.2)
      (cond ((tag == 2) || (tag == 3) || (tag == 4))
        (h[p.unpair.1]?.getD false || h[p.unpair.2]?.getD false)
        (cond (tag == 5) (h[p]?.getD false)
          (cond ((tag == 6) || (tag == 7))
            (!(x == p.unpair.1) && h[p.unpair.2]?.getD false)
            (cond (tag == 8) (h[p.unpair.2]?.getD false) false)))))

private theorem freeMemStep_primrec : Primrec₂ freeMemStep := by
  have hn : Primrec (fun p : Nat × List Bool => p.2.length) :=
    Primrec.list_length.comp Primrec.snd
  have hk := Primrec.nat_sub.comp hn (Primrec.const 1)
  have ht := Primrec.fst.comp (Primrec.unpair.comp hk)
  have hp := Primrec.snd.comp (Primrec.unpair.comp hk)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hp)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hp)
  have test (n : Nat) := Primrec.beq.comp ht (Primrec.const n)
  have get (f : Nat × List Bool → Nat) (hf : Primrec f) :
      Primrec (fun p : Nat × List Bool => p.2[f p]?.getD false) :=
    Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.snd hf)
      (Primrec.const false)
  exact ((Primrec.beq.comp hn (Primrec.const 0)).cond (Primrec.const false)
    ((test 1).cond
      (Primrec.or.comp (Term.freeMemCode_primrec.comp Primrec.fst hl)
        (Term.freeMemCode_primrec.comp Primrec.fst hr))
      ((Primrec.or.comp (Primrec.or.comp (test 2) (test 3)) (test 4)).cond
        (Primrec.or.comp (get _ hl) (get _ hr))
        ((test 5).cond (get _ hp)
          ((Primrec.or.comp (test 6) (test 7)).cond
            (Primrec.and.comp (Primrec.not.comp (Primrec.beq.comp Primrec.fst hl))
              (get _ hr))
            ((test 8).cond (get _ hr) (Primrec.const false))))))).to₂

theorem freeMemCode_primrec : Primrec₂ freeMemCode := by
  have hg := Primrec.option_some.comp₂ freeMemStep_primrec
  exact Primrec.nat_strong_rec freeMemCode hg (by
    intro x n
    cases n with
    | zero => simp [freeMemStep, freeMemCode]
    | succ k =>
      have hp : k.unpair.2 < k + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le k)
      have hl : k.unpair.2.unpair.1 < k + 1 := lt_of_le_of_lt (Nat.unpair_left_le _) hp
      have hr : k.unpair.2.unpair.2 < k + 1 := lt_of_le_of_lt (Nat.unpair_right_le _) hp
      simp [freeMemStep, freeMemCode, hp, hl, hr])

@[simp] theorem freeMemCode_code (x : Nat) (φ : Formula Nat) :
    freeMemCode x (φ.code id) = decide (x ∈ φ.freeVars) := by
  induction φ <;> simp_all [freeMemCode, code, freeVars, Nat.unpair_pair, Bool.beq_eq_decide_eq]

theorem freeVars_lt_code (φ : Formula Nat) {x : Nat}
    (hx : x ∈ φ.freeVars) : x < φ.code id := by
  induction φ with
  | falsum => exact False.elim (Finset.notMem_empty x hx)
  | equal t u =>
    rcases Finset.mem_union.mp hx with hx | hx
    · exact lt_trans (t.freeVars_lt_code hx) (left_lt_binary_node 1 t.code u.code)
    · exact lt_trans (u.freeVars_lt_code hx) (right_lt_binary_node 1 t.code u.code)
  | imp φ ψ ihφ ihψ =>
    rcases Finset.mem_union.mp hx with hx | hx
    · exact lt_trans (ihφ hx) (left_lt_binary_node 2 (φ.code id) (ψ.code id))
    · exact lt_trans (ihψ hx) (right_lt_binary_node 2 (φ.code id) (ψ.code id))
  | conj φ ψ ihφ ihψ =>
    rcases Finset.mem_union.mp hx with hx | hx
    · exact lt_trans (ihφ hx) (left_lt_binary_node 3 (φ.code id) (ψ.code id))
    · exact lt_trans (ihψ hx) (right_lt_binary_node 3 (φ.code id) (ψ.code id))
  | disj φ ψ ihφ ihψ =>
    rcases Finset.mem_union.mp hx with hx | hx
    · exact lt_trans (ihφ hx) (left_lt_binary_node 4 (φ.code id) (ψ.code id))
    · exact lt_trans (ihψ hx) (right_lt_binary_node 4 (φ.code id) (ψ.code id))
  | neg φ ih => exact lt_trans (ih hx) (payload_lt_node 5 (φ.code id))
  | all z φ ih =>
    exact lt_trans (ih (Finset.mem_erase.mp hx).2) (right_lt_binary_node 6 z (φ.code id))
  | ex z φ ih =>
    exact lt_trans (ih (Finset.mem_erase.mp hx).2) (right_lt_binary_node 7 z (φ.code id))
  | know a φ ih => exact lt_trans (ih hx) (right_lt_binary_node 8 a (φ.code id))

def freeVariablesCode (n : Nat) : List Nat :=
  (List.range n).filter (fun x => freeMemCode x n)

theorem freeVariablesCode_primrec : Primrec freeVariablesCode := by
  have hm : PrimrecRel (fun x n : Nat => freeMemCode x n = true) :=
    Primrec.eq.comp freeMemCode_primrec (Primrec.const true)
  exact (hm.listFilter.comp Primrec.list_range Primrec.id).of_eq
    (fun n => by simp [freeVariablesCode])

theorem freeVariablesCode_toFinset (φ : Formula Nat) :
    (freeVariablesCode (φ.code id)).toFinset = φ.freeVars := by
  ext x
  simp only [freeVariablesCode, List.mem_toFinset, List.mem_filter, List.mem_range,
    freeMemCode_code, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun hx => ⟨φ.freeVars_lt_code hx, hx⟩⟩

@[simp] theorem freeVariablesCode_code (φ : Formula Nat) :
    freeVariablesCode (φ.code id) = φ.freeVars.sort (· ≤ ·) := by
  have hn : (freeVariablesCode (φ.code id)).Nodup := List.nodup_range.filter _
  have hp : List.Perm (freeVariablesCode (φ.code id)) (φ.freeVars.sort (· ≤ ·)) :=
    List.perm_of_nodup_nodup_toFinset_eq hn (φ.freeVars.sort_nodup (· ≤ ·))
      (by rw [freeVariablesCode_toFinset, Finset.sort_toFinset])
  exact hp.eq_of_pairwise' (List.pairwise_le_range.filter _)
    (φ.freeVars.pairwise_sort (· ≤ ·))

def freeVariableCardCode (n : Nat) : Nat := (freeVariablesCode n).length

theorem freeVariableCardCode_primrec : Primrec freeVariableCardCode :=
  Primrec.list_length.comp freeVariablesCode_primrec

@[simp] theorem freeVariableCardCode_code (φ : Formula Nat) :
    freeVariableCardCode (φ.code id) = φ.freeVars.card := by
  have hn : (freeVariablesCode (φ.code id)).Nodup := List.nodup_range.filter _
  rw [← freeVariablesCode_toFinset φ, List.toFinset_card_of_nodup hn]
  rfl

def isClosedCode (n : Nat) : Bool := isCode n && (freeVariableCardCode n == 0)

theorem isClosedCode_primrec : Primrec isClosedCode :=
  Primrec.and.comp isCode_primrec
    (Primrec.beq.comp freeVariableCardCode_primrec (Primrec.const 0))

@[simp] theorem isClosedCode_code (φ : Formula Nat) :
    isClosedCode (φ.code id) = true ↔ φ.Closed := by
  simp [isClosedCode, Closed, Finset.card_eq_zero]

theorem isClosedCode_iff (n : Nat) :
    isClosedCode n = true ↔ ∃ φ : Formula Nat, φ.code id = n ∧ φ.Closed := by
  constructor
  · intro h
    have hf : isCode n = true := (Bool.and_eq_true_iff.mp h).1
    obtain ⟨φ, hφ⟩ := isCode_sound n hf
    exact ⟨φ, hφ, (isClosedCode_code φ).mp (by simpa only [hφ] using h)⟩
  · rintro ⟨φ, rfl, hφ⟩
    exact (isClosedCode_code φ).mpr hφ

def isUnaryCode (x n : Nat) : Bool :=
  isCode n && (freeMemCode x n && (freeVariableCardCode n == 1))

theorem isUnaryCode_primrec : Primrec₂ isUnaryCode :=
  (Primrec.and.comp (isCode_primrec.comp Primrec.snd)
    (Primrec.and.comp freeMemCode_primrec
      (Primrec.beq.comp (freeVariableCardCode_primrec.comp Primrec.snd)
        (Primrec.const 1)))).to₂

@[simp] theorem isUnaryCode_code (x : Nat) (φ : Formula Nat) :
    isUnaryCode x (φ.code id) = true ↔ φ.freeVars = {x} := by
  simp only [isUnaryCode, isCode_code, freeMemCode_code, freeVariableCardCode_code,
    Bool.true_and, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro ⟨hx, hcard⟩
    obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hcard
    have hxy : x = y := by simpa only [hy, Finset.mem_singleton] using hx
    simpa only [← hxy] using hy
  · intro h
    simp [h]

theorem isUnaryCode_iff (x n : Nat) :
    isUnaryCode x n = true ↔
      ∃ φ : Formula Nat, φ.code id = n ∧ φ.freeVars = {x} := by
  constructor
  · intro h
    have hf : isCode n = true := (Bool.and_eq_true_iff.mp h).1
    obtain ⟨φ, hφ⟩ := isCode_sound n hf
    exact ⟨φ, hφ, (isUnaryCode_code x φ).mp (by simpa only [hφ] using h)⟩
  · rintro ⟨φ, rfl, hφ⟩
    exact (isUnaryCode_code x φ).mpr hφ

theorem freeVariableCard_primrec : Primrec (fun φ : Formula Nat => φ.freeVars.card) :=
  (freeVariableCardCode_primrec.comp code_primrec).of_eq
    (fun φ => freeVariableCardCode_code φ)

theorem closed_primrec : PrimrecPred (fun φ : Formula Nat => φ.Closed) :=
  (Primrec.eq.comp (isClosedCode_primrec.comp code_primrec) (Primrec.const true)).of_eq
    (fun φ => isClosedCode_code φ)

theorem unary_primrec :
    PrimrecRel (fun (φ : Formula Nat) (x : Nat) => φ.freeVars = {x}) :=
  (Primrec.eq.comp
    (isUnaryCode_primrec.comp Primrec.snd (code_primrec.comp Primrec.fst))
    (Primrec.const true)).of_eq (fun p => isUnaryCode_code p.2 p.1)

theorem freeVariables_primrec :
    Primrec (fun φ : Formula Nat => φ.freeVars.sort (· ≤ ·)) :=
  (freeVariablesCode_primrec.comp code_primrec).of_eq (fun φ => freeVariablesCode_code φ)

theorem all_primrec : Primrec₂ (Formula.all : Nat → Formula Nat → Formula Nat) := by
  have hc : Primrec (fun p : Nat × Formula Nat =>
      Nat.pair 6 (Nat.pair p.1 (p.2.code id)) + 1) :=
    Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 6)
      (Primrec₂.natPair.comp Primrec.fst (code_primrec.comp Primrec.snd)))
  apply Primrec.encode_iff.1
  simpa only [encode_eq_code, code] using hc

theorem universalClosure_primrec : Primrec (Formula.universalClosure (Owner := Nat)) := by
  have hs : Primrec₂ (fun (_ : Formula Nat) (p : Nat × Formula Nat) => Formula.all p.1 p.2) :=
    (Primrec.comp all_primrec Primrec.snd).to₂
  exact Primrec.list_foldr freeVariables_primrec Primrec.id hs

end Formula

end Alexander313
