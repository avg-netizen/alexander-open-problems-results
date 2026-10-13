import Alexander313.Wilken.RelativeTermCoding
import Alexander313.Wilken.AdmissibleTerms

/-!
# Actual source-sort recognition at the base one

The source hull and proper-collapse laws determine the value sort of an
admissible relative term. A theta node hides its argument's value sort:
`theta 0 (theta 1 (parameter 0))` has whole-tree height 2 but its value is
below Ω₁. The separate `outerSort` measure records the theta indices exposed
by the outer additive expression, without traversing through a theta node.

For τ=1, natural parameter payloads denote their actual finite ordinals, so
the parameter test is exactly `p=0`. The constructed primitive-recursive
checker uses the derived outer-sort law for every theta argument and is exact
for the existing semantic `Admissible` predicate, with its actual source
finite-collapse family. Raw numerical recognition also checks the literal
syntax image. This is not additive normalization, a hereditary public-code
domain, semantic ordinal equality/comparison, tracking or R₁/R₂ recognition.
-/

namespace Alexander313.Wilken.RelativeTerm

variable {Parameter : Type}

/-- The sort of the outer additive expression; a theta argument is hidden
    from its parent's value sort, but must pass its own admission check. -/
def outerSort : RelativeTerm Parameter → Nat
  | .parameter _ => 0
  | .sum a b => max a.outerSort b.outerSort
  | .theta k _ => k + 1

theorem outerSort_le_height (t : RelativeTerm Parameter) : t.outerSort ≤ t.height := by
  induction t with
  | parameter _ => exact le_rfl
  | sum a b iha ihb => exact max_le_max iha ihb
  | theta k a ih => exact le_max_left _ _

/-- Every actual source-admissible tree lies in the zero-argument hull at
    every available level. Lower theta values are absorbed into its parameter
    segment using the already constructed proper-collapse theorem. -/
theorem source_hull_at (τ : Ordinal) (parameters : Parameter → Ordinal)
    (n : Nat) (t : RelativeTerm Parameter)
    (ht : Admissible parameters (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 t) :
    ∀ r, r < n →
      Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n r 0
        (omegaSequence τ (r + 1)) (t.eval parameters (sourceFiniteCollapse τ n)) := by
  induction ht with
  | parameter hp =>
    intro r hr
    exact .below_parameter (hp.trans_le
      ((omegaSequence_strictMono τ).monotone (Nat.zero_le (r + 1))))
  | sum _ _ iha ihb =>
    intro r hr
    exact .add (iha r hr) (ihb r hr)
  | @theta k a h0k hkn hsort ha ih =>
    have hproper := sourceFiniteCollapse_proper τ n k hkn
      (a.eval parameters (sourceFiniteCollapse τ n)) hsort (ih k hkn)
    intro r hr
    by_cases hkr : k ≤ r
    · exact .below_parameter (hproper.trans_le
        ((omegaSequence_strictMono τ).monotone (Nat.add_le_add_right hkr 1)))
    · exact .higher (Nat.lt_of_not_ge hkr) hkn hsort (ih r hr)

/-- The source theta value lies in its genuine half-open cardinal-sort
    interval. Its strict upper bound is proved from the admissible argument,
    rather than taken from the total collapse family's fallback bound. -/
theorem source_theta_range (τ : Ordinal) (parameters : Parameter → Ordinal)
    (n k : Nat) (a : RelativeTerm Parameter) (hkn : k < n)
    (ha : Admissible parameters (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 a)
    (hsort : a.eval parameters (sourceFiniteCollapse τ n) < omegaSequence τ (k + 2)) :
    omegaSequence τ k ≤ sourceFiniteCollapse τ n k
        (a.eval parameters (sourceFiniteCollapse τ n)) ∧
      sourceFiniteCollapse τ n k (a.eval parameters (sourceFiniteCollapse τ n)) <
        omegaSequence τ (k + 1) :=
  ⟨(sourceFiniteCollapse_bounds τ n k hkn _).1,
    sourceFiniteCollapse_proper τ n k hkn _ hsort (source_hull_at τ parameters n a ha k hkn)⟩

/-- Exact semantic sort recognition on the already admissible source syntax.
    The positive target-sort hypothesis supplies additive closure of Ω_q. -/
theorem source_eval_lt_iff_outerSort_le (τ : Ordinal) (parameters : Parameter → Ordinal)
    (n : Nat) (t : RelativeTerm Parameter)
    (ht : Admissible parameters (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 t)
    (q : Nat) (hq : 0 < q) :
    t.eval parameters (sourceFiniteCollapse τ n) < omegaSequence τ q ↔ t.outerSort ≤ q := by
  induction ht generalizing q with
  | parameter hp =>
    constructor
    · intro _; exact Nat.zero_le q
    · intro _
      exact hp.trans_le ((omegaSequence_strictMono τ).monotone (Nat.zero_le q))
  | @sum a b ha hb iha ihb =>
    cases q with
    | zero => omega
    | succ q =>
      change a.eval parameters (sourceFiniteCollapse τ n) +
          b.eval parameters (sourceFiniteCollapse τ n) < omegaSequence τ (q + 1) ↔
        max a.outerSort b.outerSort ≤ q + 1
      constructor
      · intro hsum
        exact max_le
          ((iha (q + 1) (Nat.zero_lt_succ q)).mp (le_self_add.trans_lt hsum))
          ((ihb (q + 1) (Nat.zero_lt_succ q)).mp (le_add_self.trans_lt hsum))
      · intro hmax
        exact omegaSequence_add_closed τ q
          ((iha (q + 1) (Nat.zero_lt_succ q)).mpr ((le_max_left _ _).trans hmax))
          ((ihb (q + 1) (Nat.zero_lt_succ q)).mpr ((le_max_right _ _).trans hmax))
  | @theta k a h0k hkn hsort ha ih =>
    have hrange := source_theta_range τ parameters n k a hkn ha hsort
    change sourceFiniteCollapse τ n k (a.eval parameters (sourceFiniteCollapse τ n)) <
        omegaSequence τ q ↔ k + 1 ≤ q
    constructor
    · intro hvalue
      by_contra hnot
      have hqk : q ≤ k := by omega
      exact hvalue.not_ge
        (((omegaSequence_strictMono τ).monotone hqk).trans hrange.1)
    · intro hkq
      exact hrange.2.trans_le ((omegaSequence_strictMono τ).monotone hkq)

namespace SourceOne

def parameters (p : Nat) : Ordinal.{0} := p

noncomputable def denote (n : Nat) (t : RelativeTerm Nat) : Ordinal.{0} :=
  t.eval parameters (sourceFiniteCollapse 1 n)

def admissible (n : Nat) (t : RelativeTerm Nat) : Prop :=
  Admissible parameters (omegaSequence 1) (sourceFiniteCollapse 1 n) n 0 t

theorem parameter_lt_base_iff (p : Nat) :
    parameters p < omegaSequence 1 0 ↔ p = 0 := by
  change (p : Ordinal.{0}) < (1 : Ordinal.{0}) ↔ p = 0
  norm_cast <;> omega

theorem denote_lt_iff_outerSort_le (n : Nat) (t : RelativeTerm Nat)
    (ht : admissible n t) (q : Nat) (hq : 0 < q) :
    denote n t < omegaSequence 1 q ↔ t.outerSort ≤ q :=
  source_eval_lt_iff_outerSort_le 1 parameters n t ht q hq

def parameterState (_ : Nat) (p : Nat) : Bool × Nat := (p == 0, 0)

def sumState (a b : Bool × Nat) : Bool × Nat := (a.1 && b.1, max a.2 b.2)

def thetaState (n k : Nat) (a : Bool × Nat) : Bool × Nat :=
  ((a.1 && decide (k < n)) && decide (a.2 ≤ k + 2), k + 1)

def stateCode (n c : Nat) : Bool × Nat :=
  ValueFold.code parameterState sumState thetaState (false, 0) n c

def state (n : Nat) (t : RelativeTerm Nat) : Bool × Nat :=
  ValueFold.term parameterState sumState thetaState n t

theorem parameterState_primrec : Primrec₂ parameterState := by
  exact ((Primrec.beq.comp Primrec.snd (Primrec.const 0)).pair (Primrec.const 0)).to₂

theorem sumState_primrec : Primrec₂ sumState := by
  have hv : Primrec (fun p : (Bool × Nat) × (Bool × Nat) => p.1.1 && p.2.1) :=
    Primrec.and.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)
  have hs : Primrec (fun p : (Bool × Nat) × (Bool × Nat) => max p.1.2 p.2.2) :=
    Primrec.nat_max.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)
  exact (hv.pair hs).to₂

theorem thetaState_primrec :
    Primrec (fun p : Nat × (Nat × (Bool × Nat)) => thetaState p.1 p.2.1 p.2.2) := by
  have hk : Primrec (fun p : Nat × (Nat × (Bool × Nat)) => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hv : Primrec (fun p : Nat × (Nat × (Bool × Nat)) => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hs : Primrec (fun p : Nat × (Nat × (Bool × Nat)) => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hi := (Primrec.nat_lt.comp hk Primrec.fst).decide
  have hb := (Primrec.nat_le.comp hs (Primrec.nat_add.comp hk (Primrec.const 2))).decide
  exact (Primrec.and.comp (Primrec.and.comp hv hi) hb).pair (Primrec.succ.comp hk)

theorem stateCode_primrec : Primrec₂ stateCode :=
  ValueFold.code_primrec parameterState sumState thetaState (false, 0)
    parameterState_primrec sumState_primrec thetaState_primrec

theorem state_primrec : Primrec₂ state :=
  ValueFold.term_primrec parameterState sumState thetaState (false, 0)
    parameterState_primrec sumState_primrec thetaState_primrec

@[simp] theorem stateCode_code (n : Nat) (t : RelativeTerm Nat) :
    stateCode n t.code = state n t :=
  ValueFold.code_term parameterState sumState thetaState (false, 0) n t

@[simp] theorem state_sort (n : Nat) (t : RelativeTerm Nat) : (state n t).2 = t.outerSort := by
  induction t <;> simp_all [state, ValueFold.term, parameterState, sumState, thetaState, outerSort]

def check (n : Nat) (t : RelativeTerm Nat) : Bool := (state n t).1

@[simp] theorem check_parameter (n p : Nat) : check n (.parameter p) = (p == 0) := rfl

@[simp] theorem check_sum (n : Nat) (a b : RelativeTerm Nat) :
    check n (.sum a b) = (check n a && check n b) := rfl

@[simp] theorem check_theta (n k : Nat) (a : RelativeTerm Nat) :
    check n (.theta k a) =
      ((check n a && decide (k < n)) && decide (a.outerSort ≤ k + 2)) := by
  change ((check n a && decide (k < n)) && decide ((state n a).2 ≤ k + 2)) = _
  rw [state_sort]

theorem check_primrec : Primrec₂ check := Primrec.fst.comp₂ state_primrec

/-- Every child sort test is discharged by the proved source value-sort law;
    no semantic comparison procedure or admissibility oracle is supplied. -/
theorem check_iff (n : Nat) (t : RelativeTerm Nat) : check n t = true ↔ admissible n t := by
  induction t with
  | parameter p =>
    constructor
    · intro hc
      have hp : p = 0 := by simpa only [check_parameter, beq_iff_eq] using hc
      exact .parameter ((parameter_lt_base_iff p).mpr hp)
    · intro ha
      cases ha with
      | parameter hp =>
        have hzero := (parameter_lt_base_iff p).mp hp
        simp only [check_parameter, hzero, beq_self_eq_true]
  | sum a b iha ihb =>
    constructor
    · intro hc
      have hs : check n a = true ∧ check n b = true := by simpa only [check_sum, Bool.and_eq_true] using hc
      exact .sum (iha.mp hs.1) (ihb.mp hs.2)
    · intro ha
      cases ha with
      | sum ha hb => simp only [check_sum, iha.mpr ha, ihb.mpr hb, Bool.true_and]
  | theta k a ih =>
    constructor
    · intro hc
      have hs : check n a = true ∧ k < n ∧ a.outerSort ≤ k + 2 := by
        simpa only [check_theta, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using hc
      have ha := ih.mp hs.1
      exact .theta (Nat.zero_le k) hs.2.1
        ((denote_lt_iff_outerSort_le n a ha (k + 2) (by omega)).mpr hs.2.2) ha
    · intro ha
      cases ha with
      | theta h0k hkn hsort ha =>
        have hc := ih.mpr ha
        have hs := (denote_lt_iff_outerSort_le n a ha (k + 2) (by omega)).mp hsort
        simp only [check_theta, hc, hkn, hs, decide_true, Bool.true_and]

/-- The syntax-image test prevents default fold values from admitting any
    malformed numerical input. -/
def checkCode (n c : Nat) : Bool := isCode c && (stateCode n c).1

theorem checkCode_primrec : Primrec₂ checkCode := by
  have hs : Primrec (fun p : Nat × Nat => stateCode p.1 p.2) := stateCode_primrec
  exact (Primrec.and.comp (isCode_primrec.comp Primrec.snd) (Primrec.fst.comp hs)).to₂

@[simp] theorem checkCode_code (n : Nat) (t : RelativeTerm Nat) : checkCode n t.code = check n t := by
  simp only [checkCode, isCode_code, stateCode_code, Bool.true_and, check]

theorem checkCode_iff (n c : Nat) :
    checkCode n c = true ↔ ∃ t : RelativeTerm Nat, t.code = c ∧ admissible n t := by
  constructor
  · intro hc
    have hs : isCode c = true ∧ (stateCode n c).1 = true := Bool.and_eq_true_iff.mp hc
    obtain ⟨t, ht⟩ := isCode_sound c hs.1
    refine ⟨t, ht, (check_iff n t).mp ?_⟩
    simpa only [← ht, stateCode_code, check] using hs.2
  · rintro ⟨t, rfl, ht⟩
    rw [checkCode_code]
    exact (check_iff n t).mpr ht

theorem checked_denote (n : Nat) (t : RelativeTerm Nat) (ht : check n t = true) :
    FiniteNotation (omegaSequence 1) (sourceFiniteCollapse 1 n) n 0 (denote n t) :=
  ((check_iff n t).mp ht).denote

theorem checked_sourceNotation (n : Nat) (hn : 0 < n) (t : RelativeTerm Nat)
    (ht : check n t = true) : sourceNotation 1 n 0 (denote n t) := by
  rw [sourceNotation, if_pos hn]
  exact checked_denote n t ht

/-- A checked body's strict argument bound is an actual source ordinal bound. -/
theorem checked_argument_sort (n k : Nat) (a : RelativeTerm Nat)
    (h : check n (.theta k a) = true) : denote n a < omegaSequence 1 (k + 2) := by
  have ha := (check_iff n (.theta k a)).mp h
  cases ha with
  | theta h0k hkn hsort ha => exact hsort

def hiddenHigh : RelativeTerm Nat := .theta 0 (.theta 1 (.parameter 0))

theorem hiddenHigh_admissible : admissible 2 hiddenHigh :=
  (check_iff 2 hiddenHigh).mp rfl

@[simp] theorem hiddenHigh_height : hiddenHigh.height = 2 := rfl

@[simp] theorem hiddenHigh_outerSort : hiddenHigh.outerSort = 1 := rfl

theorem hiddenHigh_denote_lt : denote 2 hiddenHigh < omegaSequence 1 1 :=
  (denote_lt_iff_outerSort_le 2 hiddenHigh hiddenHigh_admissible 1 (by omega)).mpr le_rfl

end SourceOne

theorem outerSort_primrec : Primrec (outerSort (Parameter := Nat)) := by
  have hs := SourceOne.state_primrec.comp (Primrec.const 0) Primrec.id
  exact (Primrec.snd.comp hs).of_eq (fun t => SourceOne.state_sort 0 t)

end Alexander313.Wilken.RelativeTerm
