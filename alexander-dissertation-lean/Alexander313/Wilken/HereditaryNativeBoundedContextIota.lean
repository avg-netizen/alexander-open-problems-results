import Alexander313.Wilken.HereditaryNativeBoundedContextIotaSupport

/-!
# Actual finite iota in the genuine bounded intermediate context

The new beta public code and every parameter are computed by the actual
full bounded SAME-value return. Original source admission and restriction
derive every lowered theta caller and the literal height/sort drop. A real
finite fold executes on the original normal source-star guard. No target
Normal, order-isomorphism, inverse or mu-translation is assumed or claimed;
the full comparison induction is a separate ensuing proof. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.BoundedContextIota

def small (s a b : Nat) (t : RelativeTerm Nat) : Bool :=
  Normalization.lessRawCode (sourceCode s a) t.code b

theorem small_primrec : Primrec₂ (fun ctx : Context => small ctx.1.1 ctx.1.2 ctx.2) :=
  (Normalization.Effective.lessRawCode_primrec.comp
    ((sourceCode_primrec.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
        ((code_primrec.comp Primrec.snd).pair (Primrec.snd.comp Primrec.fst)))).to₂

theorem small_exact (s a b : Nat) (ha : rootCheck s a b = true) (t : RelativeTerm Nat)
    (ht : check (sourceCode s a) t = true) : small s a b t = true ↔
      denote (sourceCode s a) t < interpretation (sourceCode s a) b := by
  simp only [small, Normalization.lessRawCode_exact, checkCode_code, ht,
    root_original s a b ha, interpretation_code, true_and]

def transform (s a b : Nat) : RelativeTerm Nat → RelativeTerm Nat
  | .parameter p => .parameter (parameterCode s a (.parameter p))
  | .sum t u => cond (small s a b (.sum t u))
      (.parameter (parameterCode s a (.sum t u))) (.sum (transform s a b t) (transform s a b u))
  | .theta k t => cond (small s a b (.theta k t))
      (.parameter (parameterCode s a (.theta k t))) (.theta (k - 1) (transform s a b t))

theorem transform_below (s a b : Nat) (ha : rootCheck s a b = true) (t : RelativeTerm Nat)
    (ht : check (sourceCode s a) t = true) (hb : denote (sourceCode s a) t < interpretation (sourceCode s a) b) :
    transform s a b t = .parameter (parameterCode s a t) := by
  have hs := (small_exact s a b ha t ht).mpr hb
  cases t <;> simp only [transform, hs, Bool.cond_true]

theorem transform_parameter_value (s a b : Nat) (ha : rootCheck s a b = true) (t : RelativeTerm Nat)
    (ht : check (sourceCode s a) t = true) (hb : denote (sourceCode s a) t < interpretation (sourceCode s a) b) :
    check (betaCode s a b) (transform s a b t) = true ∧
      denote (betaCode s a b) (transform s a b t) = denote (sourceCode s a) t := by
  have hp := parameterCode_spec s a b ha t ht hb
  rw [transform_below s a b ha t ht hb]
  refine ⟨?_, hp.2⟩
  simp only [check, betaCode_baseCheck s a b ha, finiteCheck_parameter, hp.1, Bool.true_and]

theorem transform_outerSort (s a b : Nat) (ha : rootCheck s a b = true) (t : RelativeTerm Nat)
    (ht : check (sourceCode s a) t = true) (hr : Restricted s a b t) :
    (transform s a b t).outerSort ≤ t.outerSort - 1 := by
  revert ht hr
  induction t with
  | parameter p => intro ht hr; exact Nat.zero_le _
  | sum t u iht ihu =>
    intro ht hr
    have hc := BaseTransformation.sum_checks _ t u ht
    have hs := (restricted_sum s a b t u).mp hr
    cases h : small s a b (.sum t u) with
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
      rw [transform_below s a b ha _ ht ((restricted_theta_zero s a b t).mp hr).1]
      exact Nat.zero_le _
    | succ k =>
      cases h : small s a b (.theta (k + 1) t) <;>
        simp only [transform, h, Bool.cond_false, Bool.cond_true, outerSort] <;> omega

theorem transform_height (s a b : Nat) (ha : rootCheck s a b = true) (t : RelativeTerm Nat)
    (ht : check (sourceCode s a) t = true) (hr : Restricted s a b t) :
    (transform s a b t).height ≤ t.height - 1 := by
  revert ht hr
  induction t with
  | parameter p => intro ht hr; exact Nat.zero_le _
  | sum t u iht ihu =>
    intro ht hr
    have hc := BaseTransformation.sum_checks _ t u ht
    have hs := (restricted_sum s a b t u).mp hr
    cases h : small s a b (.sum t u) with
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
      rw [transform_below s a b ha _ ht ((restricted_theta_zero s a b t).mp hr).1]
      exact Nat.zero_le _
    | succ k =>
      have hc := BaseTransformation.theta_argument_check _ (k + 1) t ht
      have hr' := (restricted_theta_succ s a b k t).mp hr
      have hh := ih hc hr'
      cases h : small s a b (.theta (k + 1) t) <;>
        simp only [transform, h, Bool.cond_false, Bool.cond_true, height] <;> omega

theorem transform_finite (s a b n : Nat) (ha : rootCheck s a b = true) (t : RelativeTerm Nat)
    (ht : finiteCheck (sourceCode s a) n t = true) (hr : Restricted s a b t) :
    finiteCheck (betaCode s a b) (n - 1) (transform s a b t) = true := by
  revert ht hr
  induction t with
  | parameter p =>
    intro ht hr
    have hc := Comparison.admitted_checked _ n (sourceCode_checked s a b ha) (.parameter p)
      ((finiteCheck_exact _ n _).mp ht)
    have hp := checked_parameters _ (.parameter p) hc p (by simp [RelativeTerm.parameters])
    have hb : denote (sourceCode s a) (.parameter p) < interpretation (sourceCode s a) b :=
      hp.2.trans_le (root_base_le s a b ha)
    exact (parameterCode_spec s a b ha (.parameter p) hc hb).1
  | sum t u iht ihu =>
    intro ht hr
    have hf := Bool.and_eq_true.mp ht
    have hc := Comparison.admitted_checked _ n (sourceCode_checked s a b ha) (.sum t u)
      ((finiteCheck_exact _ n _).mp ht)
    have hs := (restricted_sum s a b t u).mp hr
    cases h : small s a b (.sum t u) with
    | true =>
      simpa only [transform, h, Bool.cond_true, finiteCheck_parameter] using
        (parameterCode_spec s a b ha (.sum t u) hc ((small_exact s a b ha _ hc).mp h)).1
    | false =>
      simp only [transform, h, Bool.cond_false, finiteCheck_sum,
        iht hf.1 hs.1, ihu hf.2 hs.2, Bool.true_and]
  | theta k t ih =>
    intro ht hr
    have hf : finiteCheck (sourceCode s a) n t = true ∧ k < n ∧ t.outerSort ≤ k + 2 := by
      simpa only [finiteCheck_theta, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using ht
    have hc := Comparison.admitted_checked _ n (sourceCode_checked s a b ha) (.theta k t)
      ((finiteCheck_exact _ n _).mp ht)
    cases h : small s a b (.theta k t) with
    | true =>
      simpa only [transform, h, Bool.cond_true, finiteCheck_parameter] using
        (parameterCode_spec s a b ha (.theta k t) hc ((small_exact s a b ha _ hc).mp h)).1
    | false =>
      have hk : 0 < k := by
        cases k with
        | zero =>
          have hh := (small_exact s a b ha _ hc).mpr ((restricted_theta_zero s a b t).mp hr).1
          rw [h] at hh
          cases hh
        | succ k => exact Nat.succ_pos k
      have hr' : Restricted s a b t := by
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hk)
        exact (restricted_theta_succ s a b j t).mp hr
      have hct := Comparison.admitted_checked _ n (sourceCode_checked s a b ha) t
        ((finiteCheck_exact _ n _).mp hf.1)
      have hs := transform_outerSort s a b ha t hct hr'
      have hn : k - 1 < n - 1 := by omega
      have hsort : (transform s a b t).outerSort ≤ k - 1 + 2 := by omega
      simp only [transform, h, Bool.cond_false, finiteCheck_theta, ih hf.1 hr',
        hn, hsort, decide_true, Bool.true_and]

theorem transform_checked (s a b : Nat) (ha : rootCheck s a b = true) (t : RelativeTerm Nat)
    (ht : check (sourceCode s a) t = true) (hr : Restricted s a b t) :
    check (betaCode s a b) (transform s a b t) = true := by
  apply (check_exact _ _).mpr
  exact ⟨betaCode_baseCheck s a b ha, SourceOne.PublicCodes.fragment t - 1,
    (finiteCheck_exact _ _ _).mp (transform_finite s a b _ ha t (Bool.and_eq_true.mp ht).2 hr)⟩

abbrev State := Context × (RelativeTerm Nat × RelativeTerm Nat)

def parameterState (ctx : Context) (p : Nat) : State :=
  (ctx, (.parameter p, .parameter (parameterCode ctx.1.1 ctx.1.2 (.parameter p))))

def sumState (x y : State) : State :=
  let t := RelativeTerm.sum x.2.1 y.2.1
  (x.1, (t, cond (small x.1.1.1 x.1.1.2 x.1.2 t)
    (.parameter (parameterCode x.1.1.1 x.1.1.2 t)) (.sum x.2.2 y.2.2)))

def thetaState (ctx : Context) (k : Nat) (x : State) : State :=
  let t := RelativeTerm.theta k x.2.1
  (ctx, (t, cond (small ctx.1.1 ctx.1.2 ctx.2 t)
    (.parameter (parameterCode ctx.1.1 ctx.1.2 t)) (.theta (k - 1) x.2.2)))

def stateCode (s a b c : Nat) : State := ValueFold.code parameterState sumState thetaState
  (((0, 0), 0), (Normalization.zeroTree, Normalization.zeroTree)) ((s, a), b) c

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

theorem stateCode_primrec : Primrec₂ (fun ctx : Context => stateCode ctx.1.1 ctx.1.2 ctx.2) :=
  ValueFold.code_primrec parameterState sumState thetaState
    (((0, 0), 0), (Normalization.zeroTree, Normalization.zeroTree))
    parameterState_primrec sumState_primrec thetaState_primrec

theorem stateCode_code (s a b : Nat) (t : RelativeTerm Nat) :
    stateCode s a b t.code = (((s, a), b), (t, transform s a b t)) := by
  rw [stateCode, ValueFold.code_term]
  induction t <;> simp_all only [ValueFold.term, parameterState, sumState, thetaState, transform]

theorem transform_primrec : Primrec₂ (fun ctx : Context => transform ctx.1.1 ctx.1.2 ctx.2) := by
  have h := Primrec.snd.comp (Primrec.snd.comp
    (stateCode_primrec.comp Primrec.fst (code_primrec.comp Primrec.snd)))
  simpa only [stateCode_code] using h.to₂

def restrictionCheck (s a b c : Nat) : Bool :=
  Iota.allBelow (sourceCode s a) b (RelativeTerm.PrincipalSupport.listCode 0 c)

theorem restrictionCheck_primrec : Primrec₂ (fun ctx : Context => restrictionCheck ctx.1.1 ctx.1.2 ctx.2) :=
  (Iota.allBelow_primrec.comp
    (((sourceCode_primrec.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair (Primrec.snd.comp Primrec.fst)).pair
        (RelativeTerm.PrincipalSupport.listCode_primrec.comp (Primrec.const 0) Primrec.snd))).to₂

theorem restrictionCheck_code (s a b : Nat) (ha : rootCheck s a b = true) (t : RelativeTerm Nat)
    (ht : check (sourceCode s a) t = true) : restrictionCheck s a b t.code = true ↔ Restricted s a b t := by
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
        root_original s a b ha, by simpa only [interpretation_code] using h u hu⟩

def inputCheck (s a b c : Nat) : Bool := rootCheck s a b &&
  (Comparison.acceptedCode (sourceCode s a) c && restrictionCheck s a b c)

theorem inputCheck_primrec : Primrec₂ (fun ctx : Context => inputCheck ctx.1.1 ctx.1.2 ctx.2) :=
  (Primrec.and.comp (rootCheck_primrec.comp Primrec.fst)
    (Primrec.and.comp (Comparison.acceptedCode_primrec.comp
      (sourceCode_primrec.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))) Primrec.snd) restrictionCheck_primrec)).to₂

theorem inputCheck_exact (s a b c : Nat) : inputCheck s a b c = true ↔
    rootCheck s a b = true ∧ ∃ t : RelativeTerm Nat, c = t.code ∧
      check (sourceCode s a) t = true ∧ Comparison.Normal (sourceCode s a) t ∧
        Iota.sourceStar (sourceCode s a) t < interpretation (sourceCode s a) b := by
  constructor
  · intro h
    obtain ⟨ha, hc, hr⟩ := (by simpa only [inputCheck, Bool.and_eq_true] using h :
      rootCheck s a b = true ∧ Comparison.acceptedCode (sourceCode s a) c = true ∧ restrictionCheck s a b c = true)
    have hs := (Comparison.acceptedCode_exact _ c).mp hc
    obtain ⟨t, he, ht⟩ := (checkCode_exact _ c).mp hs.1
    have hn : Comparison.Normal (sourceCode s a) t := by simpa only [← he, ThetaCourse.rawTree_code] using hs.2
    have hrt := (restrictionCheck_code s a b ha t ht).mp (by simpa only [← he] using hr)
    exact ⟨ha, t, he.symm, ht, hn, (restricted_iff_sourceStar s a b ha t ht hn).mp hrt⟩
  · rintro ⟨ha, t, rfl, ht, hn, hr⟩
    have hrt := (restricted_iff_sourceStar s a b ha t ht hn).mpr hr
    simp only [inputCheck, ha, Bool.true_and, Bool.and_eq_true]
    exact ⟨(Comparison.acceptedCode_exact _ _).mpr
      ⟨by simpa only [checkCode_code] using ht, by simpa only [ThetaCourse.rawTree_code] using hn⟩,
      (restrictionCheck_code s a b ha t ht).mpr hrt⟩

def literalCode (s a b c : Nat) : Nat := cond (inputCheck s a b c) (stateCode s a b c).2.2.code 0

theorem literalCode_primrec : Primrec₂ (fun ctx : Context => literalCode ctx.1.1 ctx.1.2 ctx.2) :=
  (inputCheck_primrec.cond (code_primrec.comp (Primrec.snd.comp (Primrec.snd.comp stateCode_primrec)))
    (Primrec.const 0)).to₂

theorem literalCode_code (s a b : Nat) (ha : rootCheck s a b = true) (t : RelativeTerm Nat)
    (ht : check (sourceCode s a) t = true) (hn : Comparison.Normal (sourceCode s a) t)
    (hr : Restricted s a b t) : literalCode s a b t.code = (transform s a b t).code := by
  have hc := (inputCheck_exact s a b t.code).mpr
    ⟨ha, t, rfl, ht, hn, (restricted_iff_sourceStar s a b ha t ht hn).mp hr⟩
  simp only [literalCode, hc, Bool.cond_true, stateCode_code]

theorem literalCode_checked (s a b c : Nat) (hc : inputCheck s a b c = true) :
    checkCode (betaCode s a b) (literalCode s a b c) = true := by
  obtain ⟨ha, t, rfl, ht, hn, hs⟩ := (inputCheck_exact s a b c).mp hc
  have hr := (restricted_iff_sourceStar s a b ha t ht hn).mpr hs
  rw [literalCode_code s a b ha t ht hn hr, checkCode_code]
  exact transform_checked s a b ha t ht hr

theorem literalCode_height (s a b c : Nat) (hc : inputCheck s a b c = true) :
    heightCode (literalCode s a b c) ≤ heightCode c - 1 := by
  obtain ⟨ha, t, rfl, ht, hn, hs⟩ := (inputCheck_exact s a b c).mp hc
  have hr := (restricted_iff_sourceStar s a b ha t ht hn).mpr hs
  rw [literalCode_code s a b ha t ht hn hr, heightCode_code, heightCode_code]
  exact transform_height s a b ha t ht hr

theorem argument_inputCheck (s a b : Nat) (ha : rootCheck s a b = true) :
    inputCheck s a b (Localization.argumentCode b) = true := by
  obtain ⟨_, ⟨t, he, ht, hn, hh⟩, _⟩ := (rootCheck_exact s a b).mp ha
  have hc := BaseTransformation.theta_argument_check _ 0 t ht
  have hr := argument_restricted s a b ha
  apply (inputCheck_exact s a b _).mpr
  refine ⟨ha, t, by simp only [he, Localization.argumentCode_theta], hc, hn, ?_⟩
  apply (restricted_iff_sourceStar s a b ha t hc hn).mp
  simpa only [he, Localization.argumentCode_theta, ThetaCourse.rawTree_code] using hr

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.BoundedContextIota
