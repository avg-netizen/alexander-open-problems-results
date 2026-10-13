import Alexander313.Wilken.RelativeTermPublicCodes

/-!
# Literal finite-level hereditary syntax

At level zero a parameter payload must be zero. At level `r+1` it is the
literal numerical code of a low accepted tree at level `r`. Thus every
parameter is represented by an earlier tree, and the finite level decreases
when that representation is opened. No arbitrary parameter-coverage function
or ordinal comparison is part of this grammar.

The checker is primitive recursive for each displayed finite level. This
module makes no claim of uniform primitive recursiveness in the level, no
normal-form or least-code claim, and no identification with Wilken's υ
sequence. The next module proves actual source denotation and coverage.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary

private def lowStep (leaf : Nat → Bool) (c : Nat) : Bool :=
  (isCode c &&
    (ValueFold.code (fun (_ : Nat) p => (leaf p, 0))
      SourceOne.sumState SourceOne.thetaState (false, 0) (heightCode c + 1) c).1) &&
    decide (SourceOne.PublicCodes.outerSortCode c ≤ 1)

/-- A payload code opens one earlier level. Level zero has only the real
    zero parameter of the base-one source grammar. -/
def lowCheckCode : Nat → Nat → Bool
  | 0 => lowStep (fun p => p == 0)
  | r + 1 => lowStep (lowCheckCode r)

def parameterCheck : Nat → Nat → Bool
  | 0, p => p == 0
  | r + 1, p => lowCheckCode r p

@[simp] theorem parameterCheck_zero (p : Nat) : parameterCheck 0 p = (p == 0) := rfl

@[simp] theorem parameterCheck_succ (r p : Nat) :
    parameterCheck (r + 1) p = lowCheckCode r p := rfl

private theorem lowStep_primrec (leaf : Nat → Bool) (h : Primrec leaf) :
    Primrec (lowStep leaf) := by
  have hp : Primrec₂ (fun (_ : Nat) p => (leaf p, 0)) :=
    ((h.comp Primrec.snd).pair (Primrec.const 0)).to₂
  have hs := ValueFold.code_primrec (fun (_ : Nat) p => (leaf p, 0))
    SourceOne.sumState SourceOne.thetaState (false, 0)
    hp SourceOne.sumState_primrec SourceOne.thetaState_primrec
  have hf := Primrec.fst.comp
    (hs.comp (Primrec.succ.comp heightCode_primrec) Primrec.id)
  have ho := (Primrec.nat_le.comp SourceOne.PublicCodes.outerSortCode_primrec
    (Primrec.const 1)).decide
  exact Primrec.and.comp (Primrec.and.comp isCode_primrec hf) ho

theorem lowCheckCode_primrec (r : Nat) : Primrec (lowCheckCode r) := by
  induction r with
  | zero => exact lowStep_primrec _ (Primrec.beq.comp Primrec.id (Primrec.const 0))
  | succ r ih => exact lowStep_primrec _ ih

theorem parameterCheck_primrec (r : Nat) : Primrec (parameterCheck r) := by
  cases r with
  | zero => exact Primrec.beq.comp Primrec.id (Primrec.const 0)
  | succ r => exact lowCheckCode_primrec r

def parameterState (r : Nat) (_ : Nat) (p : Nat) : Bool × Nat :=
  (parameterCheck r p, 0)

def stateCode (r n c : Nat) : Bool × Nat :=
  ValueFold.code (parameterState r) SourceOne.sumState SourceOne.thetaState
    (false, 0) n c

def state (r n : Nat) (t : RelativeTerm Nat) : Bool × Nat :=
  ValueFold.term (parameterState r) SourceOne.sumState SourceOne.thetaState n t

theorem parameterState_primrec (r : Nat) : Primrec₂ (parameterState r) :=
  (((parameterCheck_primrec r).comp Primrec.snd).pair (Primrec.const 0)).to₂

theorem stateCode_primrec (r : Nat) : Primrec₂ (stateCode r) :=
  ValueFold.code_primrec (parameterState r) SourceOne.sumState SourceOne.thetaState
    (false, 0) (parameterState_primrec r)
    SourceOne.sumState_primrec SourceOne.thetaState_primrec

theorem state_primrec (r : Nat) : Primrec₂ (state r) :=
  ValueFold.term_primrec (parameterState r) SourceOne.sumState SourceOne.thetaState
    (false, 0) (parameterState_primrec r)
    SourceOne.sumState_primrec SourceOne.thetaState_primrec

@[simp] theorem stateCode_code (r n : Nat) (t : RelativeTerm Nat) :
    stateCode r n t.code = state r n t :=
  ValueFold.code_term (parameterState r) SourceOne.sumState SourceOne.thetaState
    (false, 0) n t

@[simp] theorem state_sort (r n : Nat) (t : RelativeTerm Nat) :
    (state r n t).2 = t.outerSort := by
  induction t <;> simp_all [state, ValueFold.term, parameterState,
    SourceOne.sumState, SourceOne.thetaState, outerSort]

def finiteCheck (r n : Nat) (t : RelativeTerm Nat) : Bool := (state r n t).1

@[simp] theorem finiteCheck_parameter (r n p : Nat) :
    finiteCheck r n (.parameter p) = parameterCheck r p := rfl

@[simp] theorem finiteCheck_sum (r n : Nat) (a b : RelativeTerm Nat) :
    finiteCheck r n (.sum a b) = (finiteCheck r n a && finiteCheck r n b) := rfl

@[simp] theorem finiteCheck_theta (r n k : Nat) (a : RelativeTerm Nat) :
    finiteCheck r n (.theta k a) =
      ((finiteCheck r n a && decide (k < n)) && decide (a.outerSort ≤ k + 2)) := by
  change ((finiteCheck r n a && decide (k < n)) && decide ((state r n a).2 ≤ k + 2)) = _
  rw [state_sort]

theorem finiteCheck_primrec (r : Nat) : Primrec₂ (finiteCheck r) :=
  Primrec.fst.comp₂ (state_primrec r)

def finiteCheckCode (r n c : Nat) : Bool := isCode c && (stateCode r n c).1

theorem finiteCheckCode_primrec (r : Nat) : Primrec₂ (finiteCheckCode r) := by
  have hs : Primrec (fun p : Nat × Nat => stateCode r p.1 p.2) := stateCode_primrec r
  exact (Primrec.and.comp (isCode_primrec.comp Primrec.snd) (Primrec.fst.comp hs)).to₂

@[simp] theorem finiteCheckCode_code (r n : Nat) (t : RelativeTerm Nat) :
    finiteCheckCode r n t.code = finiteCheck r n t := by
  simp only [finiteCheckCode, isCode_code, stateCode_code, Bool.true_and, finiteCheck]

theorem finiteCheckCode_iff (r n c : Nat) :
    finiteCheckCode r n c = true ↔
      ∃ t : RelativeTerm Nat, t.code = c ∧ finiteCheck r n t = true := by
  constructor
  · intro hc
    have hs := Bool.and_eq_true_iff.mp hc
    obtain ⟨t, ht⟩ := isCode_sound c hs.1
    refine ⟨t, ht, ?_⟩
    simpa only [← ht, stateCode_code, finiteCheck] using hs.2
  · rintro ⟨t, rfl, ht⟩
    rw [finiteCheckCode_code]
    exact ht

def check (r : Nat) (t : RelativeTerm Nat) : Bool :=
  finiteCheck r (SourceOne.PublicCodes.fragment t) t

def checkCode (r c : Nat) : Bool := finiteCheckCode r (heightCode c + 1) c

theorem check_primrec (r : Nat) : Primrec (check r) :=
  (finiteCheck_primrec r).comp SourceOne.PublicCodes.fragment_primrec Primrec.id

theorem checkCode_primrec (r : Nat) : Primrec (checkCode r) :=
  (finiteCheckCode_primrec r).comp (Primrec.succ.comp heightCode_primrec) Primrec.id

@[simp] theorem checkCode_code (r : Nat) (t : RelativeTerm Nat) :
    checkCode r t.code = check r t := by
  simp only [checkCode, heightCode_code, finiteCheckCode_code, check,
    SourceOne.PublicCodes.fragment]

theorem checkCode_iff (r c : Nat) :
    checkCode r c = true ↔ ∃ t : RelativeTerm Nat, t.code = c ∧ check r t = true := by
  constructor
  · intro hc
    obtain ⟨t, ht, ha⟩ := (finiteCheckCode_iff r (heightCode c + 1) c).mp hc
    refine ⟨t, ht, ?_⟩
    simpa only [← ht, heightCode_code, check, SourceOne.PublicCodes.fragment] using ha
  · rintro ⟨t, rfl, ht⟩
    rw [checkCode_code]
    exact ht

def lowCheck (r : Nat) (t : RelativeTerm Nat) : Bool :=
  check r t && decide (t.outerSort ≤ 1)

theorem lowCheck_primrec (r : Nat) : Primrec (lowCheck r) :=
  Primrec.and.comp (check_primrec r)
    (Primrec.nat_le.comp outerSort_primrec (Primrec.const 1)).decide

theorem lowCheckCode_eq (r c : Nat) :
    lowCheckCode r c = (checkCode r c && decide (SourceOne.PublicCodes.outerSortCode c ≤ 1)) := by
  cases r <;> rfl

@[simp] theorem lowCheckCode_code (r : Nat) (t : RelativeTerm Nat) :
    lowCheckCode r t.code = lowCheck r t := by
  simp only [lowCheckCode_eq, checkCode_code, SourceOne.PublicCodes.outerSortCode_code, lowCheck]

theorem lowCheckCode_iff (r c : Nat) :
    lowCheckCode r c = true ↔ ∃ t : RelativeTerm Nat, t.code = c ∧ lowCheck r t = true := by
  constructor
  · intro hc
    have hs : checkCode r c = true ∧ SourceOne.PublicCodes.outerSortCode c ≤ 1 := by
      simpa only [lowCheckCode_eq, Bool.and_eq_true, decide_eq_true_eq] using hc
    obtain ⟨t, ht, hcheck⟩ := (checkCode_iff r c).mp hs.1
    refine ⟨t, ht, ?_⟩
    have hsort : t.outerSort ≤ 1 := by
      simpa only [← ht, SourceOne.PublicCodes.outerSortCode_code] using hs.2
    simp only [lowCheck, hcheck, hsort, decide_true, Bool.true_and]
  · rintro ⟨t, rfl, ht⟩
    rw [lowCheckCode_code]
    exact ht

theorem finiteCheck_transfer (r n : Nat) (t : RelativeTerm Nat)
    (h : finiteCheck r n t = true) (n' : Nat) (hheight : t.height ≤ n') :
    finiteCheck r n' t = true := by
  have transfer : ∀ (a : RelativeTerm Nat) (p q : Nat),
      finiteCheck r p a = true → a.height ≤ q → finiteCheck r q a = true := by
    intro a
    induction a with
    | parameter p =>
      intro n n' h hheight
      simpa only [finiteCheck_parameter] using h
    | sum a b iha ihb =>
      intro n n' h hheight
      have hs : finiteCheck r n a = true ∧ finiteCheck r n b = true := by
        simpa only [finiteCheck_sum, Bool.and_eq_true] using h
      have ha := (le_max_left a.height b.height).trans hheight
      have hb := (le_max_right a.height b.height).trans hheight
      simp only [finiteCheck_sum, iha n n' hs.1 ha, ihb n n' hs.2 hb, Bool.true_and]
    | theta k a ih =>
      intro n n' h hheight
      have hs : finiteCheck r n a = true ∧ k < n ∧ a.outerSort ≤ k + 2 := by
        simpa only [finiteCheck_theta, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using h
      have ha := (le_max_right (k + 1) a.height).trans hheight
      have hk : k < n' := by
        have hk' := (le_max_left (k + 1) a.height).trans hheight
        omega
      simp only [finiteCheck_theta, ih n n' hs.1 ha, hk, hs.2.2, decide_true, Bool.true_and]
  exact transfer t n n' h hheight

/-- At the bottom level this is exactly the earlier literal base-one grammar. -/
@[simp] theorem finiteCheck_zero (n : Nat) (t : RelativeTerm Nat) :
    finiteCheck 0 n t = SourceOne.check n t := rfl

@[simp] theorem check_zero (t : RelativeTerm Nat) :
    check 0 t = SourceOne.PublicCodes.check t := rfl

@[simp] theorem lowCheckCode_zero (c : Nat) :
    lowCheckCode 0 c = SourceOne.PublicCodes.lowCheckCode c := rfl

private theorem pair_left_le (a b : Nat) : a ≤ Nat.pair a b := by
  simpa only [Nat.unpair_pair] using Nat.unpair_left_le (Nat.pair a b)

private theorem pair_right_le (a b : Nat) : b ≤ Nat.pair a b := by
  simpa only [Nat.unpair_pair] using Nat.unpair_right_le (Nat.pair a b)

/-- Opening a parameter payload also strictly decreases its literal
    numerical code. This is a syntax fact, not an ordinal order test. -/
theorem parameter_lt_code (t : RelativeTerm Nat) (p : Nat) (hp : p ∈ t.parameters) :
    p < t.code := by
  induction t with
  | parameter q =>
    have heq : p = q := by simpa only [RelativeTerm.parameters, Finset.mem_singleton] using hp
    subst p
    exact Nat.lt_succ_of_le (pair_right_le 0 q)
  | sum a b iha ihb =>
    have hs : p ∈ a.parameters ∨ p ∈ b.parameters := by
      simpa only [RelativeTerm.parameters, Finset.mem_union] using hp
    rcases hs with ha | hb
    · exact (iha ha).trans_le ((pair_left_le a.code b.code).trans
        ((pair_right_le 1 (Nat.pair a.code b.code)).trans (Nat.le_succ _)))
    · exact (ihb hb).trans_le ((pair_right_le a.code b.code).trans
        ((pair_right_le 1 (Nat.pair a.code b.code)).trans (Nat.le_succ _)))
  | theta k a ih =>
    exact (ih hp).trans_le ((pair_right_le k a.code).trans
      ((pair_right_le 2 (Nat.pair k a.code)).trans (Nat.le_succ _)))

end Alexander313.Wilken.RelativeTerm.Hereditary
