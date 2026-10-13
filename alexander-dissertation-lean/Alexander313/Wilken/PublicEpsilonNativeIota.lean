import Alexander313.Wilken.PublicEpsilonNativeIotaSupport

/-!
# Actual finite iota at EVERY canonical public epsilon reference

The original literal q source and its original admitted Normal high beta
root below the genuinely selected endpoint derive all small LOW return
callers and every lowered finite theta caller. A real finite state fold
executes the original restricted Normal domain, with literal height and
sort descent. Proper source-one reference epsilons use the true uniform
public return, never a native parser at base one. No target Normal or order
oracle is assumed; the full comparison induction follows. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonIota

def small (q b : Nat) (t : RelativeTerm Nat) : Bool :=
  Normalization.lessRawCode (q) t.code b

theorem small_primrec : Primrec₂ (fun ctx : Context => small ctx.1 ctx.2) :=
  (Normalization.Effective.lessRawCode_primrec.comp
    ((Primrec.fst.comp Primrec.fst).pair
      ((code_primrec.comp Primrec.snd).pair (Primrec.snd.comp Primrec.fst)))).to₂

theorem small_exact (q b : Nat) (ha : rootCheck q b = true) (t : RelativeTerm Nat)
    (ht : check (q) t = true) : small q b t = true ↔
      denote (q) t < interpretation (q) b := by
  simp only [small, Normalization.lessRawCode_exact, checkCode_code, ht,
    root_original q b ha, interpretation_code, true_and]

def transform (q b : Nat) : RelativeTerm Nat → RelativeTerm Nat
  | .parameter p => .parameter (parameterCode q (.parameter p))
  | .sum t u => cond (small q b (.sum t u))
      (.parameter (parameterCode q (.sum t u))) (.sum (transform q b t) (transform q b u))
  | .theta k t => cond (small q b (.theta k t))
      (.parameter (parameterCode q (.theta k t))) (.theta (k - 1) (transform q b t))

theorem transform_below (q b : Nat) (ha : rootCheck q b = true) (t : RelativeTerm Nat)
    (ht : check (q) t = true) (hb : denote (q) t < interpretation (q) b) :
    transform q b t = .parameter (parameterCode q t) := by
  have hs := (small_exact q b ha t ht).mpr hb
  cases t <;> simp only [transform, hs, Bool.cond_true]

theorem transform_parameter_value (q b : Nat) (ha : rootCheck q b = true) (t : RelativeTerm Nat)
    (ht : check (q) t = true) (hb : denote (q) t < interpretation (q) b) :
    check (betaCode q b) (transform q b t) = true ∧
      denote (betaCode q b) (transform q b t) = denote (q) t := by
  have hp := parameterCode_spec q b ha t ht hb
  rw [transform_below q b ha t ht hb]
  refine ⟨?_, hp.2⟩
  simp only [check, betaCode_baseCheck q b ha, finiteCheck_parameter, hp.1, Bool.true_and]

theorem transform_outerSort (q b : Nat) (ha : rootCheck q b = true) (t : RelativeTerm Nat)
    (ht : check (q) t = true) (hr : Restricted q b t) :
    (transform q b t).outerSort ≤ t.outerSort - 1 := by
  revert ht hr
  induction t with
  | parameter p => intro ht hr; exact Nat.zero_le _
  | sum t u iht ihu =>
    intro ht hr
    have hc := BaseTransformation.sum_checks _ t u ht
    have hs := (restricted_sum q b t u).mp hr
    cases h : small q b (.sum t u) with
    | true => simp only [transform, h, Bool.cond_true, outerSort]; exact Nat.zero_le _
    | false =>
      have hl := iht hc.1 hs.1
      have hu := ihu hc.2 hs.2
      simp only [transform, h, Bool.cond_false, outerSort]
      omega
  | theta k t ih =>
    intro ht hr
    cases k with
    | zero =>
      rw [transform_below q b ha _ ht ((restricted_theta_zero q b t).mp hr).1]
      exact Nat.zero_le _
    | succ k =>
      cases h : small q b (.theta (k + 1) t) <;>
        simp only [transform, h, Bool.cond_false, Bool.cond_true, outerSort] <;> omega

theorem transform_height (q b : Nat) (ha : rootCheck q b = true) (t : RelativeTerm Nat)
    (ht : check (q) t = true) (hr : Restricted q b t) :
    (transform q b t).height ≤ t.height - 1 := by
  revert ht hr
  induction t with
  | parameter p => intro ht hr; exact Nat.zero_le _
  | sum t u iht ihu =>
    intro ht hr
    have hc := BaseTransformation.sum_checks _ t u ht
    have hs := (restricted_sum q b t u).mp hr
    cases h : small q b (.sum t u) with
    | true => simp only [transform, h, Bool.cond_true, height]; exact Nat.zero_le _
    | false =>
      have hl := iht hc.1 hs.1
      have hu := ihu hc.2 hs.2
      simp only [transform, h, Bool.cond_false, height]
      omega
  | theta k t ih =>
    intro ht hr
    cases k with
    | zero =>
      rw [transform_below q b ha _ ht ((restricted_theta_zero q b t).mp hr).1]
      exact Nat.zero_le _
    | succ k =>
      have hc := BaseTransformation.theta_argument_check _ (k + 1) t ht
      have hr' := (restricted_theta_succ q b k t).mp hr
      have hh := ih hc hr'
      cases h : small q b (.theta (k + 1) t) <;>
        simp only [transform, h, Bool.cond_false, Bool.cond_true, height] <;> omega

theorem transform_finite (q b n : Nat) (ha : rootCheck q b = true) (t : RelativeTerm Nat)
    (ht : finiteCheck (q) n t = true) (hr : Restricted q b t) :
    finiteCheck (betaCode q b) (n - 1) (transform q b t) = true := by
  revert ht hr
  induction t with
  | parameter p =>
    intro ht hr
    have hc := Comparison.admitted_checked _ n (source_checked q b ha) (.parameter p)
      ((finiteCheck_exact _ n _).mp ht)
    have hp := checked_parameters _ (.parameter p) hc p (by simp [RelativeTerm.parameters])
    have hb : denote (q) (.parameter p) < interpretation (q) b :=
      hp.2.trans_le (root_base_le q b ha)
    exact (parameterCode_spec q b ha (.parameter p) hc hb).1
  | sum t u iht ihu =>
    intro ht hr
    have hf := Bool.and_eq_true.mp ht
    have hc := Comparison.admitted_checked _ n (source_checked q b ha) (.sum t u)
      ((finiteCheck_exact _ n _).mp ht)
    have hs := (restricted_sum q b t u).mp hr
    cases h : small q b (.sum t u) with
    | true =>
      simpa only [transform, h, Bool.cond_true, finiteCheck_parameter] using
        (parameterCode_spec q b ha (.sum t u) hc ((small_exact q b ha _ hc).mp h)).1
    | false =>
      simp only [transform, h, Bool.cond_false, finiteCheck_sum,
        iht hf.1 hs.1, ihu hf.2 hs.2, Bool.true_and]
  | theta k t ih =>
    intro ht hr
    have hf : finiteCheck (q) n t = true ∧ k < n ∧ t.outerSort ≤ k + 2 := by
      simpa only [finiteCheck_theta, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using ht
    have hc := Comparison.admitted_checked _ n (source_checked q b ha) (.theta k t)
      ((finiteCheck_exact _ n _).mp ht)
    cases h : small q b (.theta k t) with
    | true =>
      simpa only [transform, h, Bool.cond_true, finiteCheck_parameter] using
        (parameterCode_spec q b ha (.theta k t) hc ((small_exact q b ha _ hc).mp h)).1
    | false =>
      have hk : 0 < k := by
        cases k with
        | zero =>
          have hh := (small_exact q b ha _ hc).mpr ((restricted_theta_zero q b t).mp hr).1
          rw [h] at hh
          cases hh
        | succ k => exact Nat.succ_pos k
      have hr' : Restricted q b t := by
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hk)
        exact (restricted_theta_succ q b j t).mp hr
      have hct := Comparison.admitted_checked _ n (source_checked q b ha) t
        ((finiteCheck_exact _ n _).mp hf.1)
      have hs := transform_outerSort q b ha t hct hr'
      have hn : k - 1 < n - 1 := by omega
      have hsort : (transform q b t).outerSort ≤ k - 1 + 2 := by omega
      simp only [transform, h, Bool.cond_false, finiteCheck_theta, ih hf.1 hr',
        hn, hsort, decide_true, Bool.true_and]

theorem transform_checked (q b : Nat) (ha : rootCheck q b = true) (t : RelativeTerm Nat)
    (ht : check (q) t = true) (hr : Restricted q b t) :
    check (betaCode q b) (transform q b t) = true := by
  apply (check_exact _ _).mpr
  exact ⟨betaCode_baseCheck q b ha, SourceOne.PublicCodes.fragment t - 1,
    (finiteCheck_exact _ _ _).mp (transform_finite q b _ ha t (Bool.and_eq_true.mp ht).2 hr)⟩

abbrev State := Context × (RelativeTerm Nat × RelativeTerm Nat)

def parameterState (ctx : Context) (p : Nat) : State :=
  (ctx, (.parameter p, .parameter (parameterCode ctx.1 (.parameter p))))

def sumState (x y : State) : State :=
  let t := RelativeTerm.sum x.2.1 y.2.1
  (x.1, (t, cond (small x.1.1 x.1.2 t)
    (.parameter (parameterCode x.1.1 t)) (.sum x.2.2 y.2.2)))

def thetaState (ctx : Context) (k : Nat) (x : State) : State :=
  let t := RelativeTerm.theta k x.2.1
  (ctx, (t, cond (small ctx.1 ctx.2 t)
    (.parameter (parameterCode ctx.1 t)) (.theta (k - 1) x.2.2)))

def stateCode (q b c : Nat) : State := ValueFold.code parameterState sumState thetaState
  ((0, 0), (Normalization.zeroTree, Normalization.zeroTree)) (q, b) c

theorem parameterState_primrec : Primrec₂ parameterState := by
  have ht := parameter_primrec.comp Primrec.snd
  have hp := parameter_primrec.comp (parameterCode_primrec.comp (Primrec.fst.comp Primrec.fst) ht)
  exact (Primrec.fst.pair (ht.pair hp)).to₂

theorem sumState_primrec : Primrec₂ sumState := by
  have hctx := Primrec.fst.comp Primrec.fst
  have ht := sum_primrec.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have hsmall := small_primrec.comp hctx ht
  have hp := parameter_primrec.comp (parameterCode_primrec.comp (Primrec.fst.comp hctx) ht)
  have ho := sum_primrec.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact (hctx.pair (ht.pair (hsmall.cond hp ho))).to₂

theorem thetaState_primrec : Primrec (fun p : Context × (Nat × State) => thetaState p.1 p.2.1 p.2.2) := by
  have hk := Primrec.fst.comp Primrec.snd
  have ht := theta_primrec.comp hk (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hs := small_primrec.comp Primrec.fst ht
  have hp := parameter_primrec.comp (parameterCode_primrec.comp (Primrec.fst.comp Primrec.fst) ht)
  have ho := theta_primrec.comp (Primrec.nat_sub.comp hk (Primrec.const 1))
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  exact Primrec.fst.pair (ht.pair (hs.cond hp ho))

theorem stateCode_primrec : Primrec₂ (fun ctx : Context => stateCode ctx.1 ctx.2) :=
  ValueFold.code_primrec parameterState sumState thetaState
    ((0, 0), (Normalization.zeroTree, Normalization.zeroTree))
    parameterState_primrec sumState_primrec thetaState_primrec

theorem stateCode_code (q b : Nat) (t : RelativeTerm Nat) :
    stateCode q b t.code = ((q, b), (t, transform q b t)) := by
  rw [stateCode, ValueFold.code_term]
  induction t <;> simp_all only [ValueFold.term, parameterState, sumState, thetaState, transform]

theorem transform_primrec : Primrec₂ (fun ctx : Context => transform ctx.1 ctx.2) := by
  have h := Primrec.snd.comp (Primrec.snd.comp
    (stateCode_primrec.comp Primrec.fst (code_primrec.comp Primrec.snd)))
  simpa only [stateCode_code] using h.to₂

def restrictionCheck (q b c : Nat) : Bool :=
  Iota.allBelow q b (RelativeTerm.PrincipalSupport.listCode 0 c)

theorem restrictionCheck_primrec : Primrec₂ (fun ctx : Context => restrictionCheck ctx.1 ctx.2) :=
  (Iota.allBelow_primrec.comp
    (Primrec.fst.pair (RelativeTerm.PrincipalSupport.listCode_primrec.comp
      (Primrec.const 0) Primrec.snd))).to₂

theorem restrictionCheck_code (q b : Nat) (ha : rootCheck q b = true) (t : RelativeTerm Nat)
    (ht : check (q) t = true) : restrictionCheck q b t.code = true ↔ Restricted q b t := by
  rw [restrictionCheck, RelativeTerm.PrincipalSupport.listCode_code, Iota.allBelow_exact]
  constructor
  · intro h u hu
    have hs := (Normalization.lessRawCode_exact _ _ _).mp
      (h u.code (List.mem_map.mpr ⟨u, hu, rfl⟩))
    simpa only [interpretation_code] using hs.2.2
  · intro h c hc
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hc
    exact (Normalization.lessRawCode_exact _ _ _).mpr
      ⟨by simpa only [checkCode_code] using Iota.checked_full_node _ t u ht hu,
        root_original q b ha, by simpa only [interpretation_code] using h u hu⟩

def inputCheck (q b c : Nat) : Bool := rootCheck q b &&
  (Comparison.acceptedCode (q) c && restrictionCheck q b c)

theorem inputCheck_primrec : Primrec₂ (fun ctx : Context => inputCheck ctx.1 ctx.2) :=
  (Primrec.and.comp (Primrec.comp rootCheck_primrec Primrec.fst)
    (Primrec.and.comp (Comparison.acceptedCode_primrec.comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd) restrictionCheck_primrec)).to₂

theorem inputCheck_exact (q b c : Nat) : inputCheck q b c = true ↔
    rootCheck q b = true ∧ ∃ t : RelativeTerm Nat, c = t.code ∧
      check (q) t = true ∧ Comparison.Normal (q) t ∧
        Iota.sourceStar (q) t < interpretation (q) b := by
  constructor
  · intro h
    obtain ⟨ha, hc, hr⟩ := (by simpa only [inputCheck, Bool.and_eq_true] using h :
      rootCheck q b = true ∧ Comparison.acceptedCode (q) c = true ∧ restrictionCheck q b c = true)
    have hs := (Comparison.acceptedCode_exact _ c).mp hc
    obtain ⟨t, he, ht⟩ := (checkCode_exact _ c).mp hs.1
    have hn : Comparison.Normal (q) t := by simpa only [← he, ThetaCourse.rawTree_code] using hs.2
    have hrt := (restrictionCheck_code q b ha t ht).mp (by simpa only [← he] using hr)
    exact ⟨ha, t, he.symm, ht, hn, (restricted_iff_sourceStar q b ha t ht hn).mp hrt⟩
  · rintro ⟨ha, t, rfl, ht, hn, hr⟩
    have hrt := (restricted_iff_sourceStar q b ha t ht hn).mpr hr
    simp only [inputCheck, ha, Bool.true_and, Bool.and_eq_true]
    exact ⟨(Comparison.acceptedCode_exact _ _).mpr
      ⟨by simpa only [checkCode_code] using ht, by simpa only [ThetaCourse.rawTree_code] using hn⟩,
      (restrictionCheck_code q b ha t ht).mpr hrt⟩

def literalCode (q b c : Nat) : Nat := cond (inputCheck q b c) (stateCode q b c).2.2.code 0

theorem literalCode_primrec : Primrec₂ (fun ctx : Context => literalCode ctx.1 ctx.2) :=
  (inputCheck_primrec.cond (code_primrec.comp (Primrec.snd.comp (Primrec.snd.comp stateCode_primrec)))
    (Primrec.const 0)).to₂

theorem literalCode_code (q b : Nat) (ha : rootCheck q b = true) (t : RelativeTerm Nat)
    (ht : check (q) t = true) (hn : Comparison.Normal (q) t)
    (hr : Restricted q b t) : literalCode q b t.code = (transform q b t).code := by
  have hc := (inputCheck_exact q b t.code).mpr
    ⟨ha, t, rfl, ht, hn, (restricted_iff_sourceStar q b ha t ht hn).mp hr⟩
  simp only [literalCode, hc, Bool.cond_true, stateCode_code]

theorem literalCode_checked (q b c : Nat) (hc : inputCheck q b c = true) :
    checkCode (betaCode q b) (literalCode q b c) = true := by
  obtain ⟨ha, t, rfl, ht, hn, hs⟩ := (inputCheck_exact q b c).mp hc
  have hr := (restricted_iff_sourceStar q b ha t ht hn).mpr hs
  rw [literalCode_code q b ha t ht hn hr, checkCode_code]
  exact transform_checked q b ha t ht hr

theorem literalCode_height (q b c : Nat) (hc : inputCheck q b c = true) :
    heightCode (literalCode q b c) ≤ heightCode c - 1 := by
  obtain ⟨ha, t, rfl, ht, hn, hs⟩ := (inputCheck_exact q b c).mp hc
  have hr := (restricted_iff_sourceStar q b ha t ht hn).mpr hs
  rw [literalCode_code q b ha t ht hn hr, heightCode_code, heightCode_code]
  exact transform_height q b ha t ht hr

theorem argument_inputCheck (q b : Nat) (ha : rootCheck q b = true) :
    inputCheck q b (Localization.argumentCode b) = true := by
  obtain ⟨_, ⟨t, he, ht, hn, hh⟩, _⟩ := (rootCheck_exact q b).mp ha
  have hc := BaseTransformation.theta_argument_check _ 0 t ht
  have hr := argument_restricted q b ha
  apply (inputCheck_exact q b _).mpr
  refine ⟨ha, t, by simp only [he, Localization.argumentCode_theta], hc, hn, ?_⟩
  apply (restricted_iff_sourceStar q b ha t hc hn).mp
  simpa only [he, Localization.argumentCode_theta, ThetaCourse.rawTree_code] using hr

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonIota
