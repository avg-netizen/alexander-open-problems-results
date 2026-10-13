import Alexander313.Wilken.HighCollapseEpsilon
import Alexander313.Wilken.HereditaryPrincipalClassification

/-!
# Actual epsilon recognition in the original hereditary grammar

Normalize an originally admitted tree, then recurse through its genuine earlier
payloads. A source-normal sum is epsilon exactly when its left value is zero and
its final principal is epsilon. An admitted theta is epsilon exactly for a high
argument, or a zero argument at an epsilon base. The initial base-one zero
collapse is one and is rejected. A literal Boolean course table proves uniform
primitive recursiveness; no semantic epsilon decision or oracle is supplied.
All proof terms remain uncompiled.
-/

namespace Alexander313.Wilken

/-- Uniqueness of the actual principal normal word forbids a nonempty prefix
in a source-normal sum which is itself epsilon. -/
theorem sourceNormalSum_epsilon_iff {ξ α β : Ordinal.{0}}
    (hnormal : SourceNormalSum ξ α β) :
    Ordinal.omega0 ^ ξ = ξ ↔ α = 0 ∧ Ordinal.omega0 ^ β = β := by
  constructor
  · intro hepsilon
    have hpositive : 0 < ξ := by
      rw [← hepsilon]
      exact Ordinal.opow_pos _ Ordinal.omega0_pos
    have hprincipal : Ordinal.IsPrincipal (· + ·) ξ := by
      rw [← hepsilon]
      exact Ordinal.isPrincipal_add_omega0_opow _
    rcases hnormal with ⟨hzero, _, _⟩ | ⟨xs, hxs, hα, hξ⟩
    · exact False.elim ((ne_of_gt hpositive) hzero)
    · have hword := canonicalANF_eq_of_normal hxs hξ
      rw [canonicalANF_principal hpositive hprincipal] at hword
      have hlength := congrArg List.length hword
      simp only [List.length_singleton, List.length_append] at hlength
      have hempty : xs = [] := List.length_eq_zero_iff.mp (by omega)
      subst xs
      have hβ : β = ξ := by
        simpa only [List.nil_append, principalSum, add_zero] using hξ
      exact ⟨by simpa only [principalSum] using hα.symm,
        by simpa only [hβ] using hepsilon⟩
  · rintro ⟨hα, hβ⟩
    rw [sourceNormalSum_eq_add hnormal, hα, zero_add]
    exact hβ

namespace RelativeTerm.Hereditary.Epsilon

open Theta ThetaCourse

/-- Exact epsilon status of the actual base at every hereditary/cardinal sort. -/
theorem omegaSequence_epsilon_iff (r k : Nat) :
    Ordinal.omega0 ^ omegaSequence (finiteBase r) k = omegaSequence (finiteBase r) k ↔
      0 < r ∨ 0 < k := by
  cases k with
  | succ k =>
    exact ⟨fun _ => Or.inr (Nat.zero_lt_succ k),
      fun _ => omegaSequence_succ_omegaPower_eq_self (finiteBase r) k⟩
  | zero =>
    rw [omegaSequence_zero]
    cases r with
    | succ r =>
      exact ⟨fun _ => Or.inl (Nat.zero_lt_succ r),
        fun _ => finiteBase_succ_omegaPower_eq_self r⟩
    | zero =>
      simp only [finiteBase_zero, Ordinal.opow_one, Nat.lt_irrefl, false_or]
      exact ⟨fun h => False.elim (Ordinal.one_lt_omega0.ne' h), False.elim⟩

/-- Both branches are proved on the genuine sorted source argument domain.
Positive low arguments are excluded by the actual low growth theorem. -/
theorem finiteCollapse_epsilon_iff (r n k : Nat) (hk : k < n)
    (α : Ordinal.{0}) (hsort : α < omegaSequence (finiteBase r) (k + 2))
    (hα : sourceNotation (finiteBase r) n (k + 1) α) :
    Ordinal.omega0 ^ sourceFiniteCollapse (finiteBase r) n k α =
        sourceFiniteCollapse (finiteBase r) n k α ↔
      omegaSequence (finiteBase r) (k + 1) ≤ α ∨
        (α = 0 ∧ (0 < r ∨ 0 < k)) := by
  have hzero := sourceFiniteCollapse_zero (finiteBase r) (finiteBase_pos r)
    (epsilon_or_one_add_closed (finiteBase_epsilon_or_one r)) n k hk
  constructor
  · intro hepsilon
    by_cases hhigh : omegaSequence (finiteBase r) (k + 1) ≤ α
    · exact Or.inl hhigh
    · have hlow : α < omegaSequence (finiteBase r) (k + 1) := lt_of_not_ge hhigh
      have hαzero : α = 0 := by
        by_contra hne
        exact sourceFiniteCollapse_low_non_epsilon_of_pos (finiteBase r) n k hk α
          (lt_of_le_of_ne ((zero_le : 0 ≤ α)) (Ne.symm hne)) hlow hepsilon
      subst α
      rw [hzero] at hepsilon
      exact Or.inr ⟨rfl, (omegaSequence_epsilon_iff r k).mp hepsilon⟩
  · rintro (hhigh | ⟨rfl, hbase⟩)
    · exact sourceFiniteCollapse_high_omegaPower_eq_self (finiteBase r) (finiteBase_pos r)
        n k hk α hhigh
        (sourceFiniteCollapse_proper_notation (finiteBase r) n k hk α hsort hα)
    · rw [hzero]
      exact (omegaSequence_epsilon_iff r k).mpr hbase

/-- Literal outer sort is converted using the proved actual ordinal bounds. -/
theorem theta_epsilon_iff (r k : Nat) (a : RelativeTerm Nat)
    (ht : check r (.theta k a) = true) :
    Ordinal.omega0 ^ denote r (.theta k a) = denote r (.theta k a) ↔
      k + 1 < a.outerSort ∨ (denote r a = 0 ∧ (0 < r ∨ 0 < k)) := by
  let n := SourceOne.PublicCodes.fragment (.theta k a)
  have had := checked_admissible r n (.theta k a) ht
    (SourceOne.PublicCodes.height_le_fragment _)
  have ha := admitted_theta_argument had
  have hac := admitted_checked ha
  have hhigh : omegaSequence (finiteBase r) (k + 1) ≤ denote r a ↔
      k + 1 < a.outerSort := by
    simpa only [not_lt, not_le] using
      not_congr (denote_lt_iff_outerSort_le r a hac (k + 1) (Nat.zero_lt_succ k))
  rw [denote_eq_finite r n (.theta k a) had.2]
  cases had.2 with
  | theta h0k hkn hsort haa =>
    have hnotation := (sourceAdmittedOrdinal (finiteBase r) (parameters r) n k hkn a haa).property
    have h := finiteCollapse_epsilon_iff r n k hkn (finiteDenote r n a) hsort hnotation
    rw [← denote_eq_finite r n a haa, hhigh] at h
    simpa only [finiteDenote, eval, denote_eq_finite r n a haa] using h

/-- The empty actual normalized word recognizes zero, including arbitrary
spellings of zero in the unchanged admitted grammar. -/
def zeroCode (r c : Nat) : Bool := decide ((Principal.normalizedAtoms r c).length = 0)

theorem zeroCode_primrec : Primrec₂ zeroCode :=
  ((Primrec.eq.comp (Primrec.list_length.comp Principal.normalizedAtoms_primrec)
    (Primrec.const 0)).decide).to₂

theorem zeroCode_exact (r c : Nat) (hc : checkCode r c = true) :
    zeroCode r c = true ↔ interpretation r c = 0 := by
  simp only [zeroCode, decide_eq_true_eq, List.length_eq_zero_iff,
    Principal.normalizedAtoms_zero_iff r c hc]

theorem zeroCode_tree_exact (r : Nat) (t : RelativeTerm Nat) (ht : check r t = true) :
    zeroCode r t.code = true ↔ denote r t = 0 := by
  simpa only [interpretation_code] using
    zeroCode_exact r t.code (by simpa only [checkCode_code] using ht)

/-- Recursion opens earlier payloads. Current theta arguments are tested by
their real sort and zero value; their epsilon status is not an input. -/
def normalEpsilon : Nat → RelativeTerm Nat → Bool
  | 0, .parameter _ => false
  | r + 1, .parameter p => normalEpsilon r (rawTree p)
  | r, .sum a b => zeroCode r a.code && normalEpsilon r b
  | r, .theta k a => decide (k + 1 < a.outerSort) ||
      (zeroCode r a.code && decide (0 < r ∨ 0 < k))
termination_by r t => expandedSize r t.code
decreasing_by
  · exact parameter_payload_size_lt _ _
  · exact ThetaCourse.sum_right_size_lt _ _ _

@[simp] theorem normalEpsilon_default (r : Nat) : normalEpsilon r (.parameter 0) = false := by
  induction r with
  | zero => simp only [normalEpsilon]
  | succ r ih => simpa [normalEpsilon, rawTree, decode] using ih

theorem normalEpsilon_correct (r : Nat) (t : RelativeTerm Nat)
    (ht : check r t = true) (hn : Normal r t) :
    normalEpsilon r t = true ↔ Ordinal.omega0 ^ denote r t = denote r t := by
  induction r generalizing t with
  | zero =>
    revert ht hn
    induction t with
    | parameter p =>
      intro ht hn
      have hp : p = 0 := by
        simpa only [check, finiteCheck_parameter, parameterCheck_zero, beq_iff_eq] using ht
      subst p
      simp [normalEpsilon, denote, RelativeTerm.eval, parameters_zero, SourceOne.parameters]
    | sum a b iha ihb =>
      intro ht hn
      have hs : check 0 a = true ∧ check 0 b = true := by
        simpa only [Uniform.check_sum, Bool.and_eq_true] using ht
      have hsum := ((normal_sum 0 a b).mp hn).2.2
      simpa only [normalEpsilon, Bool.and_eq_true, zeroCode_tree_exact 0 a hs.1,
        ihb hs.2 hn.sum_right] using (sourceNormalSum_epsilon_iff hsum).symm
    | theta k a ih =>
      intro ht hn
      have ha := admitted_checked (admitted_theta_argument
        (checked_admissible 0 (SourceOne.PublicCodes.fragment (.theta k a)) _ ht
          (SourceOne.PublicCodes.height_le_fragment _)))
      simpa only [normalEpsilon, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
        zeroCode_tree_exact 0 a ha] using (theta_epsilon_iff 0 k a ht).symm
  | succ r ihr =>
    revert ht hn
    induction t with
    | parameter p =>
      intro ht hn
      simpa only [normalEpsilon, denote_parameter_succ] using
        ihr (rawTree p) (checked_parameter_payload r p ht)
          ((normal_parameter_succ r p).mp hn)
    | sum a b iha ihb =>
      intro ht hn
      have hs : check (r + 1) a = true ∧ check (r + 1) b = true := by
        simpa only [Uniform.check_sum, Bool.and_eq_true] using ht
      have hsum := ((normal_sum (r + 1) a b).mp hn).2.2
      simpa only [normalEpsilon, Bool.and_eq_true, zeroCode_tree_exact (r + 1) a hs.1,
        ihb hs.2 hn.sum_right] using (sourceNormalSum_epsilon_iff hsum).symm
    | theta k a ih =>
      intro ht hn
      have ha := admitted_checked (admitted_theta_argument
        (checked_admissible (r + 1) (SourceOne.PublicCodes.fragment (.theta k a)) _ ht
          (SourceOne.PublicCodes.height_le_fragment _)))
      simpa only [normalEpsilon, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
        zeroCode_tree_exact (r + 1) a ha] using (theta_epsilon_iff (r + 1) k a ht).symm

namespace Effective

private def parameterOp (_ : Nat × Nat) (p : Nat) (previous : Bool) : Bool :=
  cond (isCode p) previous false

private def sumOp (q : Nat × Nat) (_ b : Bool) : Bool :=
  let p := (q.2 - 1).unpair.2
  zeroCode q.1 p.unpair.1 && b

private def thetaOp (q : Nat × Nat) (k : Nat) (_ : Bool) : Bool :=
  let c := (q.2 - 1).unpair.2.unpair.2
  decide (k + 1 < SourceOne.PublicCodes.outerSortCode c) ||
    (zeroCode q.1 c && decide (0 < q.1 ∨ 0 < k))

private def course : Nat → Nat → Bool :=
  run (fun _ => false) (fun _ _ => false) parameterOp sumOp thetaOp

private theorem course_primrec : Primrec₂ course := by
  have hp : Primrec (fun p : (Nat × Nat) × (Nat × Bool) => parameterOp p.1 p.2.1 p.2.2) :=
    (isCode_primrec.comp (Primrec.fst.comp Primrec.snd)).cond
      (Primrec.snd.comp Primrec.snd) (Primrec.const false)
  have hs : Primrec (fun p : (Nat × Nat) × (Bool × Bool) => sumOp p.1 p.2.1 p.2.2) := by
    have hr : Primrec (fun p : (Nat × Nat) × (Bool × Bool) => p.1.1) := Primrec.fst.comp Primrec.fst
    have hc : Primrec (fun p : (Nat × Nat) × (Bool × Bool) => p.1.2) := Primrec.snd.comp Primrec.fst
    have hpay := Primrec.snd.comp (Primrec.unpair.comp
      (Primrec.nat_sub.comp hc (Primrec.const 1)))
    have hl := Primrec.fst.comp (Primrec.unpair.comp hpay)
    exact Primrec.and.comp (zeroCode_primrec.comp hr hl) (Primrec.snd.comp Primrec.snd)
  have ht : Primrec (fun p : (Nat × Nat) × (Nat × Bool) => thetaOp p.1 p.2.1 p.2.2) := by
    have hr : Primrec (fun p : (Nat × Nat) × (Nat × Bool) => p.1.1) := Primrec.fst.comp Primrec.fst
    have hc : Primrec (fun p : (Nat × Nat) × (Nat × Bool) => p.1.2) := Primrec.snd.comp Primrec.fst
    have hk : Primrec (fun p : (Nat × Nat) × (Nat × Bool) => p.2.1) := Primrec.fst.comp Primrec.snd
    have hpay := Primrec.snd.comp (Primrec.unpair.comp
      (Primrec.nat_sub.comp hc (Primrec.const 1)))
    have ha := Primrec.snd.comp (Primrec.unpair.comp hpay)
    have hhigh := (Primrec.nat_lt.comp (Primrec.succ.comp hk)
      (SourceOne.PublicCodes.outerSortCode_primrec.comp ha)).decide
    have hbase := Primrec.or.comp
      ((Primrec.nat_lt.comp (Primrec.const 0) hr).decide)
      ((Primrec.nat_lt.comp (Primrec.const 0) hk).decide)
    have hbase_eq : (fun p : (Nat × Nat) × (Nat × Bool) =>
        decide (0 < p.1.1) || decide (0 < p.2.1)) =
        (fun p : (Nat × Nat) × (Nat × Bool) => decide (0 < p.1.1 ∨ 0 < p.2.1)) := by
      funext p
      by_cases h1 : 0 < p.1.1 <;> by_cases h2 : 0 < p.2.1 <;> simp [h1, h2]
    rw [hbase_eq] at hbase
    exact Primrec.or.comp hhigh (Primrec.and.comp (zeroCode_primrec.comp hr ha) hbase)
  exact run_primrec _ _ _ _ _ (Primrec.const false) (Primrec.const false).to₂ hp hs ht

private theorem course_code (r : Nat) (t : RelativeTerm Nat) :
    course r t.code = normalEpsilon r t := by
  induction r generalizing t with
  | zero =>
    induction t <;>
      simp_all [course, run, code, Nat.unpair_pair, normalEpsilon, sumOp, thetaOp,
        SourceOne.PublicCodes.outerSortCode_code]
  | succ r ihr =>
    induction t with
    | parameter p =>
      cases hd : decode p with
      | none =>
        have hs := (decode_eq_none_iff p).mp hd
        simp [course, run, code, Nat.unpair_pair, parameterOp, hs, normalEpsilon, rawTree, hd]
      | some u =>
        have hu := decode_sound p u hd
        have hprevious := ihr u
        simp only [course] at hprevious
        rw [← hu]
        simp [course, run, code, Nat.unpair_pair, parameterOp, normalEpsilon, rawTree, hprevious]
    | sum a b iha ihb =>
      simp only [course] at iha ihb
      simp [course, run, code, Nat.unpair_pair, ihb, normalEpsilon, sumOp]
    | theta k a ih =>
      simp [course, run, code, Nat.unpair_pair, normalEpsilon, thetaOp,
        SourceOne.PublicCodes.outerSortCode_code]

theorem normalEpsilon_primrec : Primrec₂ normalEpsilon := by
  have h := course_primrec.comp Primrec.fst (code_primrec.comp Primrec.snd)
  simpa only [course_code] using h.to₂

end Effective

/-- Normalization makes correctness cover every originally admitted tree. -/
def epsilonCheck (r c : Nat) : Bool :=
  checkCode r c && normalEpsilon r (Principal.normalizedTree r c)

theorem epsilonCheck_primrec : Primrec₂ epsilonCheck :=
  (Primrec.and.comp Uniform.hereditaryCheckCode_primrec
    (Effective.normalEpsilon_primrec.comp Primrec.fst Principal.normalizedTree_primrec)).to₂

theorem epsilonCheck_exact (r c : Nat) : epsilonCheck r c = true ↔
    checkCode r c = true ∧ Ordinal.omega0 ^ interpretation r c = interpretation r c := by
  simp only [epsilonCheck, Bool.and_eq_true]
  apply and_congr_right
  intro hc
  have hs := Principal.normalizedTree_spec r c hc
  simpa only [hs.2.2] using normalEpsilon_correct r (Principal.normalizedTree r c) hs.1 hs.2.1

def epsilonLowCheck (r c : Nat) : Bool := lowCheckCode r c && epsilonCheck r c

theorem epsilonLowCheck_primrec : Primrec₂ epsilonLowCheck :=
  (Primrec.and.comp Uniform.hereditaryLowCheckCode_primrec epsilonCheck_primrec).to₂

theorem epsilonLowCheck_exact (r c : Nat) : epsilonLowCheck r c = true ↔
    lowCheckCode r c = true ∧ Ordinal.omega0 ^ interpretation r c = interpretation r c := by
  rw [epsilonLowCheck, Bool.and_eq_true, epsilonCheck_exact]
  constructor
  · rintro ⟨hc, _, he⟩
    exact ⟨hc, he⟩
  · rintro ⟨hc, he⟩
    exact ⟨hc, (Bool.and_eq_true_iff.mp (by simpa only [lowCheckCode_eq] using hc)).1, he⟩

def unionEpsilonCheck (q : Nat) : Bool := epsilonLowCheck q.unpair.1 q.unpair.2

theorem unionEpsilonCheck_primrec : Primrec unionEpsilonCheck :=
  epsilonLowCheck_primrec.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)

theorem unionEpsilonCheck_exact (q : Nat) : unionEpsilonCheck q = true ↔
    unionCheck q = true ∧ Ordinal.omega0 ^ unionInterpretation q = unionInterpretation q :=
  epsilonLowCheck_exact q.unpair.1 q.unpair.2

theorem unionEpsilonCheck_computable : Computable unionEpsilonCheck := unionEpsilonCheck_primrec.to_comp

theorem epsilonCheck_invariant (r c d : Nat) (hc : checkCode r c = true)
    (hd : checkCode r d = true) (he : interpretation r c = interpretation r d) :
    epsilonCheck r c = epsilonCheck r d := by
  apply Bool.eq_iff_iff.mpr
  simp only [epsilonCheck_exact, hc, hd, true_and, he]

theorem unionEpsilonCheck_invariant (q v : Nat) (hq : unionCheck q = true)
    (hv : unionCheck v = true) (he : unionInterpretation q = unionInterpretation v) :
    unionEpsilonCheck q = unionEpsilonCheck v := by
  apply Bool.eq_iff_iff.mpr
  simp only [unionEpsilonCheck_exact, hq, hv, true_and, he]

end RelativeTerm.Hereditary.Epsilon
end Alexander313.Wilken
