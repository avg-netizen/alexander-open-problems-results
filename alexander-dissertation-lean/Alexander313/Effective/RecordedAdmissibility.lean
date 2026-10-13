import Alexander313.Effective.RecordedCoding

/-!
# Actual finite tests for recorded syntax

An explicit course table evaluates a Boolean fold on the literal formula
tree. Its three instances compute whole indexed-label support, owner policy
and global nesting. Support is traversed beneath live and ghost owners as
well as indexed owners. Natural labels use their ordinary order; this does
not assert effectivity of Wilken's ordinal notation system.
-/

noncomputable section

namespace Alexander313
namespace RecordedFormula

private theorem payload_lt_node (tag payload : Nat) :
    payload < Nat.pair tag payload + 1 :=
  Nat.lt_succ_of_le (Nat.right_le_pair tag payload)

private theorem left_lt_node (tag a b : Nat) :
    a < Nat.pair tag (Nat.pair a b) + 1 :=
  lt_of_le_of_lt (Nat.left_le_pair a b) (payload_lt_node tag _)

private theorem right_lt_node (tag a b : Nat) :
    b < Nat.pair tag (Nat.pair a b) + 1 :=
  lt_of_le_of_lt (Nat.right_le_pair a b) (payload_lt_node tag _)

namespace BooleanFold

variable {α : Type} [Primcodable α]

def code (combine : Bool → Bool → Bool) (base : Bool)
    (head : α → Nat → Nat → Bool → Bool) (a : α) : Nat → Bool
  | 0 => base
  | k + 1 =>
    let tag := k.unpair.1
    let p := k.unpair.2
    cond ((tag == 2) || (tag == 3) || (tag == 4))
      (combine (code combine base head a p.unpair.1)
        (code combine base head a p.unpair.2))
      (cond (tag == 5) (code combine base head a p)
        (cond ((tag == 6) || (tag == 7)) (code combine base head a p.unpair.2)
          (cond (tag == 8)
            (head a p.unpair.1 p.unpair.2 (code combine base head a p.unpair.2)) base)))
termination_by n => n
decreasing_by
  all_goals
    have hp := Nat.unpair_right_le k
    have hl := Nat.unpair_left_le k.unpair.2
    have hr := Nat.unpair_right_le k.unpair.2
    omega

private def step (combine : Bool → Bool → Bool) (base : Bool)
    (head : α → Nat → Nat → Bool → Bool) (a : α) (h : List Bool) : Bool :=
  let k := h.length - 1
  let tag := k.unpair.1
  let p := k.unpair.2
  cond (h.length == 0) base
    (cond ((tag == 2) || (tag == 3) || (tag == 4))
      (combine (h[p.unpair.1]?.getD base) (h[p.unpair.2]?.getD base))
      (cond (tag == 5) (h[p]?.getD base)
        (cond ((tag == 6) || (tag == 7)) (h[p.unpair.2]?.getD base)
          (cond (tag == 8)
            (head a p.unpair.1 p.unpair.2 (h[p.unpair.2]?.getD base)) base))))

private theorem step_primrec (combine : Bool → Bool → Bool) (base : Bool)
    (head : α → Nat → Nat → Bool → Bool) (hc : Primrec₂ combine)
    (hh : Primrec (fun p : α × (Nat × (Nat × Bool)) => head p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec₂ (step combine base head) := by
  have hn : Primrec (fun p : α × List Bool => p.2.length) :=
    Primrec.list_length.comp Primrec.snd
  have hk := Primrec.nat_sub.comp hn (Primrec.const 1)
  have ht := Primrec.fst.comp (Primrec.unpair.comp hk)
  have hp := Primrec.snd.comp (Primrec.unpair.comp hk)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hp)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hp)
  have test (n : Nat) := Primrec.beq.comp ht (Primrec.const n)
  have get (f : α × List Bool → Nat) (hf : Primrec f) :
      Primrec (fun p : α × List Bool => p.2[f p]?.getD base) :=
    Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.snd hf) (Primrec.const base)
  exact ((Primrec.beq.comp hn (Primrec.const 0)).cond (Primrec.const base)
    ((Primrec.or.comp (Primrec.or.comp (test 2) (test 3)) (test 4)).cond
      (hc.comp (get _ hl) (get _ hr))
      ((test 5).cond (get _ hp)
        ((Primrec.or.comp (test 6) (test 7)).cond (get _ hr)
          ((test 8).cond
            (hh.comp (Primrec.pair Primrec.fst (Primrec.pair hl (Primrec.pair hr (get _ hr)))))
            (Primrec.const base)))))).to₂

theorem code_primrec (combine : Bool → Bool → Bool) (base : Bool)
    (head : α → Nat → Nat → Bool → Bool) (hc : Primrec₂ combine)
    (hh : Primrec (fun p : α × (Nat × (Nat × Bool)) => head p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec₂ (code combine base head) := by
  have hg := Primrec.option_some.comp₂ (step_primrec combine base head hc hh)
  exact Primrec.nat_strong_rec (code combine base head) hg (by
    intro a n
    cases n with
    | zero => simp [step, code]
    | succ k =>
      have hp : k.unpair.2 < k + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le k)
      have hl : k.unpair.2.unpair.1 < k + 1 := lt_of_le_of_lt (Nat.unpair_left_le _) hp
      have hr : k.unpair.2.unpair.2 < k + 1 := lt_of_le_of_lt (Nat.unpair_right_le _) hp
      simp [step, code, hp, hl, hr])

def formula (combine : Bool → Bool → Bool) (base : Bool)
    (head : α → Nat → Nat → Bool → Bool) (a : α) : Syntax → Bool
  | .falsum => base
  | .equal _ _ => base
  | .imp φ ψ => combine (formula combine base head a φ) (formula combine base head a ψ)
  | .conj φ ψ => combine (formula combine base head a φ) (formula combine base head a ψ)
  | .disj φ ψ => combine (formula combine base head a φ) (formula combine base head a ψ)
  | .neg φ => formula combine base head a φ
  | .all _ φ => formula combine base head a φ
  | .ex _ φ => formula combine base head a φ
  | .know b φ => head a b.code (φ.code RecordedHead.code) (formula combine base head a φ)

@[simp] theorem code_formula (combine : Bool → Bool → Bool) (base : Bool)
    (head : α → Nat → Nat → Bool → Bool) (a : α) (φ : Syntax) :
    code combine base head a (φ.code RecordedHead.code) = formula combine base head a φ := by
  induction φ <;> simp_all [code, formula, Formula.code, Nat.unpair_pair]

end BooleanFold

def supportHead (μ owner _body : Nat) (value : Bool) : Bool :=
  cond (owner.unpair.1 == 1) ((μ == owner.unpair.2.unpair.2) || value) value

def supportMemCode (μ n : Nat) : Bool :=
  BooleanFold.code (· || ·) false supportHead μ n

theorem supportMemCode_primrec : Primrec₂ supportMemCode := by
  have ho : Primrec (fun p : Nat × (Nat × (Nat × Bool)) => p.2.1) := Primrec.fst.comp Primrec.snd
  have ht := Primrec.fst.comp (Primrec.unpair.comp ho)
  have hν := Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp ho)))
  have hv : Primrec (fun p : Nat × (Nat × (Nat × Bool)) => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact BooleanFold.code_primrec _ _ _ Primrec.or
    ((Primrec.beq.comp ht (Primrec.const 1)).cond
      (Primrec.or.comp (Primrec.beq.comp Primrec.fst hν) hv) hv)

@[simp] theorem supportMemCode_code (μ : Nat) (φ : Syntax) :
    supportMemCode μ (φ.code RecordedHead.code) = decide (μ ∈ φ.labelSupport) := by
  unfold supportMemCode
  rw [BooleanFold.code_formula]
  induction φ with
  | know a φ ih => cases a <;>
      simp_all [BooleanFold.formula, supportHead, RecordedHead.code, Formula.labelSupport,
        Nat.unpair_pair, Bool.beq_eq_decide_eq]
  | _ => simp_all [BooleanFold.formula, Formula.labelSupport]

theorem support_lt_code (φ : Syntax) {μ : Nat} (hμ : μ ∈ φ.labelSupport) :
    μ < φ.code RecordedHead.code := by
  induction φ with
  | falsum => exact False.elim (Finset.notMem_empty _ hμ)
  | equal t u => exact False.elim (Finset.notMem_empty _ hμ)
  | imp φ ψ ihφ ihψ =>
    rcases Finset.mem_union.mp hμ with h | h
    · exact lt_trans (ihφ h) (left_lt_node 2 _ _)
    · exact lt_trans (ihψ h) (right_lt_node 2 _ _)
  | conj φ ψ ihφ ihψ =>
    rcases Finset.mem_union.mp hμ with h | h
    · exact lt_trans (ihφ h) (left_lt_node 3 _ _)
    · exact lt_trans (ihψ h) (right_lt_node 3 _ _)
  | disj φ ψ ihφ ihψ =>
    rcases Finset.mem_union.mp hμ with h | h
    · exact lt_trans (ihφ h) (left_lt_node 4 _ _)
    · exact lt_trans (ihψ h) (right_lt_node 4 _ _)
  | neg φ ih => exact lt_trans (ih hμ) (payload_lt_node 5 _)
  | all x φ ih => exact lt_trans (ih hμ) (right_lt_node 6 _ _)
  | ex x φ ih => exact lt_trans (ih hμ) (right_lt_node 7 _ _)
  | know a φ ih =>
    cases a with
    | live a => exact lt_trans (ih hμ) (right_lt_node 8 _ _)
    | ghost a => exact lt_trans (ih hμ) (right_lt_node 8 _ _)
    | indexed a ν =>
      rcases Finset.mem_insert.mp hμ with heq | h
      · subst μ
        have hl : ν ≤ RecordedHead.code (.indexed a ν) :=
          le_trans (Nat.right_le_pair a ν) (Nat.right_le_pair 1 _)
        exact lt_of_le_of_lt hl (left_lt_node 8 _ _)
      · exact lt_trans (ih h) (right_lt_node 8 _ _)

def supportListCode (n : Nat) : List Nat :=
  (List.range n).filter (fun μ => supportMemCode μ n)

theorem supportListCode_primrec : Primrec supportListCode := by
  have hm : PrimrecRel (fun μ n : Nat => supportMemCode μ n = true) :=
    Primrec.eq.comp supportMemCode_primrec (Primrec.const true)
  exact (hm.listFilter.comp Primrec.list_range Primrec.id).of_eq
    (fun n => by simp [supportListCode])

theorem supportListCode_toFinset (φ : Syntax) :
    (supportListCode (φ.code RecordedHead.code)).toFinset = φ.labelSupport := by
  ext μ
  simp only [supportListCode, List.mem_toFinset, List.mem_filter, List.mem_range,
    supportMemCode_code, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨support_lt_code φ h, h⟩⟩

@[simp] theorem supportListCode_code (φ : Syntax) :
    supportListCode (φ.code RecordedHead.code) = φ.labelSupport.sort (· ≤ ·) := by
  have hn : (supportListCode (φ.code RecordedHead.code)).Nodup := List.nodup_range.filter _
  have hp : List.Perm (supportListCode (φ.code RecordedHead.code)) (φ.labelSupport.sort (· ≤ ·)) :=
    List.perm_of_nodup_nodup_toFinset_eq hn (φ.labelSupport.sort_nodup (· ≤ ·))
      (by rw [supportListCode_toFinset, Finset.sort_toFinset])
  exact hp.eq_of_pairwise' (List.pairwise_le_range.filter _)
    (φ.labelSupport.pairwise_sort (· ≤ ·))

def labelBoundCode (n : Nat) : Nat :=
  (supportListCode n).foldr (fun μ bound => max (μ + 1) bound) 0

theorem labelBoundCode_primrec : Primrec labelBoundCode :=
  Primrec.list_foldr supportListCode_primrec (Primrec.const 0)
    ((Primrec.nat_max.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂)

private theorem fold_bound (L : List Nat) (ν : Nat) :
    L.foldr (fun μ bound => max (μ + 1) bound) 0 ≤ ν ↔ ∀ μ ∈ L, μ < ν := by
  induction L with
  | nil => simp
  | cons μ L ih => simp [max_le_iff, Nat.succ_le_iff, ih]

theorem labelBoundCode_le_iff (φ : Syntax) (ν : Nat) :
    labelBoundCode (φ.code RecordedHead.code) ≤ ν ↔ ∀ μ ∈ φ.labelSupport, μ < ν := by
  rw [labelBoundCode, fold_bound]
  have hm (μ : Nat) : μ ∈ supportListCode (φ.code RecordedHead.code) ↔ μ ∈ φ.labelSupport := by
    rw [← List.mem_toFinset, supportListCode_toFinset]
  simp only [hm]

def stratifiedHead (_ : Unit) (owner body : Nat) (value : Bool) : Bool :=
  value && cond (owner.unpair.1 == 1)
    (decide (labelBoundCode body ≤ owner.unpair.2.unpair.2)) true

def stratifiedCode (n : Nat) : Bool := BooleanFold.code (· && ·) true stratifiedHead () n

theorem stratifiedCode_primrec : Primrec stratifiedCode := by
  have ho : Primrec (fun p : Unit × (Nat × (Nat × Bool)) => p.2.1) := Primrec.fst.comp Primrec.snd
  have ht := Primrec.fst.comp (Primrec.unpair.comp ho)
  have hν := Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp ho)))
  have hb : Primrec (fun p : Unit × (Nat × (Nat × Bool)) => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hv : Primrec (fun p : Unit × (Nat × (Nat × Bool)) => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hh : Primrec (fun p : Unit × (Nat × (Nat × Bool)) =>
      stratifiedHead p.1 p.2.1 p.2.2.1 p.2.2.2) :=
    Primrec.and.comp hv ((Primrec.beq.comp ht (Primrec.const 1)).cond
      (Primrec.nat_le.comp (labelBoundCode_primrec.comp hb) hν).decide (Primrec.const true))
  exact (BooleanFold.code_primrec _ _ _ Primrec.and hh).comp (Primrec.const ()) Primrec.id

@[simp] theorem stratifiedCode_code (φ : Syntax) :
    stratifiedCode (φ.code RecordedHead.code) = true ↔ φ.GloballyStratified := by
  unfold stratifiedCode
  rw [BooleanFold.code_formula]
  induction φ with
  | know a φ ih => cases a <;>
      simp_all [BooleanFold.formula, stratifiedHead, RecordedHead.code, Formula.GloballyStratified,
        Nat.unpair_pair, labelBoundCode_le_iff]
  | _ => simp_all [BooleanFold.formula, Formula.GloballyStratified]

def listMember (L : List Nat) (a : Nat) : Bool := decide (a ∈ L)

theorem listMember_primrec : Primrec₂ listMember := by
  have hm : PrimrecRel (fun L : List Nat => fun a => a ∈ L) :=
    (Primrec.eq.exists_mem_list).of_eq (by intro L a; simp)
  exact hm.decide

def allowedHeadCode (AE : List Nat × List Nat) (owner : Nat) : Bool :=
  let tag := owner.unpair.1
  let p := owner.unpair.2
  cond (tag == 0) (!(listMember AE.1 p))
    (cond (tag == 1) (listMember AE.1 p.unpair.1)
      (cond (tag == 2) (listMember AE.2 p && !(listMember AE.1 p)) false))

theorem allowedHeadCode_primrec : Primrec₂ allowedHeadCode := by
  have ht : Primrec (fun p : (List Nat × List Nat) × Nat => p.2.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have hp : Primrec (fun p : (List Nat × List Nat) × Nat => p.2.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
  have hA : Primrec (fun p : (List Nat × List Nat) × Nat => p.1.1) := Primrec.fst.comp Primrec.fst
  have hE : Primrec (fun p : (List Nat × List Nat) × Nat => p.1.2) := Primrec.snd.comp Primrec.fst
  exact ((Primrec.beq.comp ht (Primrec.const 0)).cond
    (Primrec.not.comp (listMember_primrec.comp hA hp))
    ((Primrec.beq.comp ht (Primrec.const 1)).cond
      (listMember_primrec.comp hA (Primrec.fst.comp (Primrec.unpair.comp hp)))
      ((Primrec.beq.comp ht (Primrec.const 2)).cond
        (Primrec.and.comp (listMember_primrec.comp hE hp)
          (Primrec.not.comp (listMember_primrec.comp hA hp))) (Primrec.const false)))).to₂

@[simp] theorem allowedHeadCode_code (AE : List Nat × List Nat) (a : Head) :
    allowedHeadCode AE a.code = true ↔ a.Allowed AE.1.toFinset AE.2.toFinset := by
  cases a <;> simp [allowedHeadCode, listMember, RecordedHead.code, RecordedHead.Allowed,
    Nat.unpair_pair]

def allowedHead (AE : List Nat × List Nat) (owner _body : Nat) (value : Bool) : Bool :=
  allowedHeadCode AE owner && value

def headsAllowedCode (AE : List Nat × List Nat) (n : Nat) : Bool :=
  BooleanFold.code (· && ·) true allowedHead AE n

theorem headsAllowedCode_primrec : Primrec₂ headsAllowedCode :=
  BooleanFold.code_primrec _ _ _ Primrec.and
    (Primrec.and.comp (allowedHeadCode_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))

@[simp] theorem headsAllowedCode_code (AE : List Nat × List Nat) (φ : Syntax) :
    headsAllowedCode AE (φ.code RecordedHead.code) = true ↔
      φ.HeadsAllowed AE.1.toFinset AE.2.toFinset := by
  unfold headsAllowedCode
  rw [BooleanFold.code_formula]
  induction φ <;> simp_all [BooleanFold.formula, allowedHead, Formula.HeadsAllowed]

def admissibleCode (AE : List Nat × List Nat) (n : Nat) : Bool :=
  headsAllowedCode AE n && stratifiedCode n

theorem admissibleCode_primrec : Primrec₂ admissibleCode :=
  (Primrec.and.comp headsAllowedCode_primrec (stratifiedCode_primrec.comp Primrec.snd)).to₂

@[simp] theorem admissibleCode_code (AE : List Nat × List Nat) (φ : Syntax) :
    admissibleCode AE (φ.code RecordedHead.code) = true ↔
      φ.RecordedAdmissible AE.1.toFinset AE.2.toFinset := by
  simp [admissibleCode, Formula.RecordedAdmissible]

theorem admissible_primrec : PrimrecRel (fun AE : List Nat × List Nat => fun φ : Syntax =>
    φ.RecordedAdmissible AE.1.toFinset AE.2.toFinset) :=
  (Primrec.eq.comp (admissibleCode_primrec.comp Primrec.fst (code_primrec.comp Primrec.snd))
    (Primrec.const true)).of_eq (fun p => admissibleCode_code p.1 p.2)

theorem support_primrec : Primrec (fun φ : Syntax => φ.labelSupport.sort (· ≤ ·)) := by
  simpa only [supportListCode_code] using supportListCode_primrec.comp code_primrec

end RecordedFormula
end Alexander313
