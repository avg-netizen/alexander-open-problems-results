import Alexander313.Wilken.SourceOneNativeIotaSupport

/-!
# Actual finite admission of the original base-one iota shift

Below alpha, original source-one low trees become genuine same-value native
parameters. Other original constructors retain their sums and shift positive
theta indices down by one. Full original P0 restriction makes every original
theta-zero subtree an atomic-stop branch. The original finite source checker
then derives every target theta caller and actual native output admission.
Written height and outer sort decrease by one. No target admission, caller,
comparison result or code-conversion oracle is assumed. Full semantic order,
Normal transport, inverse and source-one mu are not claimed. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota

def transform (a : Nat) : RelativeTerm Nat → RelativeTerm Nat
  | .parameter p => .parameter (parameterCode (.parameter p))
  | .sum t u => cond (small a (.sum t u)) (.parameter (parameterCode (.sum t u)))
      (.sum (transform a t) (transform a u))
  | .theta k t => cond (small a (.theta k t)) (.parameter (parameterCode (.theta k t)))
      (.theta (k - 1) (transform a t))

theorem transform_below (a : Nat) (ha : rootCheck a = true) (t : RelativeTerm Nat)
    (ht : check 0 t = true) (hb : denote 0 t < interpretation 0 a) :
    transform a t = .parameter (parameterCode t) := by
  cases t with
  | parameter p => rfl
  | sum t u => simp only [transform, (small_exact a ha _ ht).mpr hb, Bool.cond_true]
  | theta k t => simp only [transform, (small_exact a ha _ ht).mpr hb, Bool.cond_true]

theorem transform_below_value (a : Nat) (ha : rootCheck a = true) (t : RelativeTerm Nat)
    (ht : check 0 t = true) (hb : denote 0 t < interpretation 0 a) :
    NativeContext.denote (alphaCode a) (transform a t) = denote 0 t := by
  rw [transform_below a ha t ht hb]
  exact (parameterCode_spec a ha t ht hb).2

theorem transform_outerSort (a : Nat) (ha : rootCheck a = true) (t : RelativeTerm Nat)
    (ht : check 0 t = true) (hr : Restricted a t) :
    (transform a t).outerSort ≤ t.outerSort - 1 := by
  revert ht hr
  induction t with
  | parameter p => intro ht hr; exact Nat.zero_le _
  | sum t u iht ihu =>
    intro ht hr
    have had := (check_iff_finite_admissible 0 (.sum t u)).mp ht
    obtain ⟨n, hn⟩ := had
    cases hn.2 with
    | sum ht' hu' =>
      have hc := (restricted_sum a t u).mp hr
      have hct := Theta.admitted_checked (show admissible 0 n t from ⟨hn.1.1, ht'⟩)
      have hcu := Theta.admitted_checked (show admissible 0 n u from ⟨hn.1.2, hu'⟩)
      have hst := iht hct hc.1
      have hsu := ihu hcu hc.2
      cases h : small a (.sum t u) <;>
        simp only [transform, h, Bool.cond_true, Bool.cond_false, outerSort] <;> omega
  | theta k t ih =>
    intro ht hr
    have had := (check_iff_finite_admissible 0 (.theta k t)).mp ht
    obtain ⟨n, hn⟩ := had
    have hct := Theta.admitted_checked (Theta.admitted_theta_argument hn)
    cases k with
    | zero =>
      rw [transform_below a ha _ ht ((restricted_theta_zero a t).mp hr).1]
      exact Nat.zero_le _
    | succ k =>
      have hst := ih hct ((restricted_theta_succ a k t).mp hr)
      cases h : small a (.theta (k + 1) t) <;>
        simp only [transform, h, Bool.cond_true, Bool.cond_false, outerSort] <;> omega

theorem transform_height (a : Nat) (ha : rootCheck a = true) (t : RelativeTerm Nat)
    (ht : check 0 t = true) (hr : Restricted a t) :
    (transform a t).height ≤ t.height - 1 := by
  revert ht hr
  induction t with
  | parameter p => intro ht hr; exact Nat.zero_le _
  | sum t u iht ihu =>
    intro ht hr
    obtain ⟨n, hn⟩ := (check_iff_finite_admissible 0 (.sum t u)).mp ht
    cases hn.2 with
    | sum ht' hu' =>
      have hc := (restricted_sum a t u).mp hr
      have hst := iht (Theta.admitted_checked (show admissible 0 n t from ⟨hn.1.1, ht'⟩)) hc.1
      have hsu := ihu (Theta.admitted_checked (show admissible 0 n u from ⟨hn.1.2, hu'⟩)) hc.2
      cases h : small a (.sum t u) <;>
        simp only [transform, h, Bool.cond_true, Bool.cond_false, height] <;> omega
  | theta k t ih =>
    intro ht hr
    obtain ⟨n, hn⟩ := (check_iff_finite_admissible 0 (.theta k t)).mp ht
    have hct := Theta.admitted_checked (Theta.admitted_theta_argument hn)
    cases k with
    | zero =>
      rw [transform_below a ha _ ht ((restricted_theta_zero a t).mp hr).1]
      exact Nat.zero_le _
    | succ k =>
      have hst := ih hct ((restricted_theta_succ a k t).mp hr)
      cases h : small a (.theta (k + 1) t) <;>
        simp only [transform, h, Bool.cond_true, Bool.cond_false, height] <;> omega

/-- Every target finite theta caller is derived from the actual original
base-one finite checker and the literal full source restriction. -/
theorem transform_finite (a n : Nat) (ha : rootCheck a = true) (t : RelativeTerm Nat)
    (ht : finiteCheck 0 n t = true) (hr : Restricted a t) :
    NativeContext.finiteCheck (alphaCode a) (n - 1) (transform a t) = true := by
  revert ht hr
  induction t with
  | parameter p =>
    intro ht hr
    have hc := Theta.admitted_checked ((finiteCheck_iff 0 n (.parameter p)).mp ht)
    have hp : parameterCheck 0 p = true := ht
    have hb : denote 0 (.parameter p) < interpretation 0 a := by
      have h := parameter_sound 0 p hp
      have h1 := EpsilonOffsets.epsilon_one_lt (root_epsilon a ha)
      exact (by simpa only [denote, RelativeTerm.eval, finiteBase_zero] using h).trans h1
    exact (parameterCode_spec a ha _ hc hb).1
  | sum t u iht ihu =>
    intro ht hr
    have hf := Bool.and_eq_true.mp ht
    have hc := Theta.admitted_checked ((finiteCheck_iff 0 n (.sum t u)).mp ht)
    have hs := (restricted_sum a t u).mp hr
    cases h : small a (.sum t u) with
    | true =>
      simpa only [transform, h, Bool.cond_true, NativeContext.finiteCheck_parameter] using
        (parameterCode_spec a ha _ hc ((small_exact a ha _ hc).mp h)).1
    | false =>
      simp only [transform, h, Bool.cond_false, NativeContext.finiteCheck_sum,
        iht hf.1 hs.1, ihu hf.2 hs.2, Bool.true_and]
  | theta k t ih =>
    intro ht hr
    have hf : finiteCheck 0 n t = true ∧ k < n ∧ t.outerSort ≤ k + 2 := by
      simpa only [finiteCheck_theta, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using ht
    have hc := Theta.admitted_checked ((finiteCheck_iff 0 n (.theta k t)).mp ht)
    cases h : small a (.theta k t) with
    | true =>
      simpa only [transform, h, Bool.cond_true, NativeContext.finiteCheck_parameter] using
        (parameterCode_spec a ha _ hc ((small_exact a ha _ hc).mp h)).1
    | false =>
      have hk : 0 < k := by
        cases k with
        | zero =>
          have hh := (small_exact a ha _ hc).mpr ((restricted_theta_zero a t).mp hr).1
          rw [h] at hh
          cases hh
        | succ k => exact Nat.succ_pos k
      have hrt : Restricted a t := by
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hk)
        exact (restricted_theta_succ a j t).mp hr
      have hct := Theta.admitted_checked ((finiteCheck_iff 0 n t).mp hf.1)
      have hs := transform_outerSort a ha t hct hrt
      have hn : k - 1 < n - 1 := by omega
      have hsort : (transform a t).outerSort ≤ k - 1 + 2 := by omega
      simp only [transform, h, Bool.cond_false, NativeContext.finiteCheck_theta,
        ih hf.1 hrt, hn, hsort, decide_true, Bool.true_and]

/-- Original source-one admission and the full original restriction alone
construct actual target admission; the target parser is never a premise. -/
theorem transform_checked (a : Nat) (ha : rootCheck a = true) (t : RelativeTerm Nat)
    (ht : check 0 t = true) (hr : Restricted a t) :
    NativeContext.check (alphaCode a) (transform a t) = true := by
  apply (NativeContext.check_exact _ _).mpr
  exact ⟨alphaCode_baseCheck a ha, SourceOne.PublicCodes.fragment t - 1,
    (NativeContext.finiteCheck_exact _ _ _).mp
      (transform_finite a _ ha t ht hr)⟩

abbrev State := Nat × (RelativeTerm Nat × RelativeTerm Nat)

def parameterState (a p : Nat) : State :=
  (a, (.parameter p, .parameter (parameterCode (.parameter p))))

def sumState (x y : State) : State :=
  let t := RelativeTerm.sum x.2.1 y.2.1
  (x.1, (t, cond (small x.1 t) (.parameter (parameterCode t)) (.sum x.2.2 y.2.2)))

def thetaState (a k : Nat) (x : State) : State :=
  let t := RelativeTerm.theta k x.2.1
  (a, (t, cond (small a t) (.parameter (parameterCode t)) (.theta (k - 1) x.2.2)))

def stateCode (a c : Nat) : State := ValueFold.code parameterState sumState thetaState
  (0, (.parameter 0, .parameter 0)) a c

theorem parameterState_primrec : Primrec₂ parameterState := by
  have ht : Primrec (fun p : Nat × Nat => RelativeTerm.parameter p.2) :=
    parameter_primrec.comp Primrec.snd
  have ho := parameter_primrec.comp (parameterCode_primrec.comp ht)
  exact (Primrec.fst.pair (ht.pair ho)).to₂

theorem sumState_primrec : Primrec₂ sumState := by
  have hctx : Primrec (fun p : State × State => p.1.1) := Primrec.fst.comp Primrec.fst
  have ht : Primrec (fun p : State × State => RelativeTerm.sum p.1.2.1 p.2.2.1) :=
    sum_primrec.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have hsmall := small_primrec.comp hctx ht
  have hp := parameter_primrec.comp (parameterCode_primrec.comp ht)
  have ho := sum_primrec.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact (hctx.pair (ht.pair (hsmall.cond hp ho))).to₂

theorem thetaState_primrec : Primrec
    (fun p : Nat × (Nat × State) => thetaState p.1 p.2.1 p.2.2) := by
  have hk : Primrec (fun p : Nat × (Nat × State) => p.2.1) := Primrec.fst.comp Primrec.snd
  have ht : Primrec (fun p : Nat × (Nat × State) => RelativeTerm.theta p.2.1 p.2.2.2.1) :=
    theta_primrec.comp hk (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hs := small_primrec.comp Primrec.fst ht
  have hp := parameter_primrec.comp (parameterCode_primrec.comp ht)
  have ho := theta_primrec.comp (Primrec.nat_sub.comp hk (Primrec.const 1))
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  exact Primrec.fst.pair (ht.pair (hs.cond hp ho))

theorem stateCode_primrec : Primrec₂ stateCode :=
  ValueFold.code_primrec parameterState sumState thetaState (0, (.parameter 0, .parameter 0))
    parameterState_primrec sumState_primrec thetaState_primrec

theorem stateCode_code (a : Nat) (t : RelativeTerm Nat) :
    stateCode a t.code = (a, (t, transform a t)) := by
  rw [stateCode, ValueFold.code_term]
  induction t <;> simp_all only [ValueFold.term, parameterState, sumState, thetaState, transform]

theorem transform_primrec : Primrec₂ transform := by
  have h := Primrec.snd.comp (Primrec.snd.comp
    (stateCode_primrec.comp Primrec.fst (code_primrec.comp Primrec.snd)))
  simpa only [stateCode_code] using h.to₂

/-- The genuine finite syntax evaluator with the original source-one guard. -/
def literalCode (a c : Nat) : Nat := cond (inputCheck a c) (stateCode a c).2.2.code 0

theorem literalCode_primrec : Primrec₂ literalCode := by
  have hi : Primrec (fun p : Nat × Nat => inputCheck p.1 p.2) := inputCheck_primrec
  have hs : Primrec (fun p : Nat × Nat => stateCode p.1 p.2) := stateCode_primrec
  exact (hi.cond (code_primrec.comp (Primrec.snd.comp (Primrec.snd.comp hs)))
    (Primrec.const 0)).to₂

theorem literalCode_code (a : Nat) (ha : rootCheck a = true) (t : RelativeTerm Nat)
    (ht : check 0 t = true) (hn : Theta.Normal 0 t) (hr : Restricted a t) :
    literalCode a t.code = (transform a t).code := by
  have hc := (inputCheck_exact a t.code).mpr
    ⟨ha, t, rfl, ht, hn, (restricted_iff_sourceStar a ha t ht hn).mp hr⟩
  simp only [literalCode, hc, Bool.cond_true, stateCode_code]

/-- Every original admitted restricted normal input has actual native output
admission, including original high arguments at arbitrary finite height. -/
theorem literalCode_checked (a c : Nat) (hc : inputCheck a c = true) :
    NativeContext.checkCode (alphaCode a) (literalCode a c) = true := by
  obtain ⟨ha, t, rfl, ht, hn, hs⟩ := (inputCheck_exact a c).mp hc
  have hr := (restricted_iff_sourceStar a ha t ht hn).mpr hs
  rw [literalCode_code a ha t ht hn hr, NativeContext.checkCode_code]
  exact transform_checked a ha t ht hr

theorem literalCode_height (a c : Nat) (hc : inputCheck a c = true) :
    heightCode (literalCode a c) ≤ heightCode c - 1 := by
  obtain ⟨ha, t, rfl, ht, hn, hs⟩ := (inputCheck_exact a c).mp hc
  have hr := (restricted_iff_sourceStar a ha t ht hn).mpr hs
  rw [literalCode_code a ha t ht hn hr, heightCode_code, heightCode_code]
  exact transform_height a ha t ht hr

theorem argument_literalCode_checked (a : Nat) (ha : rootCheck a = true) :
    NativeContext.checkCode (alphaCode a) (literalCode a (Localization.argumentCode a)) = true :=
  literalCode_checked a _ (argument_inputCheck a ha)

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota
