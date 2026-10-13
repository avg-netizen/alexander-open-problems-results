import Alexander313.Wilken.HereditaryNativeIotaSupport

/-!
# Executing the finite syntax of Definition 2.45 iota

At the same positive public epsilon source context, the root supplies a real
new public-coded epsilon alpha. Every written subtree below alpha becomes
its actual original public parameter. Other sums are retained and every
theta(k+1) is replaced by theta(k). The original source-star restriction
excludes every retained theta0. All target payloads and argument sorts are
proved from the original source admission, without a supplied translator.

The literal shifted output is admitted in the actual native alpha context.
Its optional real target normalizer produces weak normality and preserves
THAT target value. A finite ValueFold proves uniform PR execution. This does
not prove shifted-collapse naturality, the (<,+)-isomorphism/coverage of2.46,
source canonical-height bounds, or an arbitrary temporary inverse.
All proofs are uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Iota

open NativePublicBridge (contextCode contextCode_checked)

def small (s a : Nat) (t : RelativeTerm Nat) : Bool :=
  Normalization.lessRawCode (contextCode s) t.code a

theorem small_primrec : Primrec₂ (fun p : Nat × Nat => small p.1 p.2) :=
  (Normalization.Effective.lessRawCode_primrec.comp
    ((NativePublicBridge.contextCode_primrec.comp (Primrec.fst.comp Primrec.fst)).pair
      ((code_primrec.comp Primrec.snd).pair (Primrec.snd.comp Primrec.fst)))).to₂

theorem small_exact (s a : Nat) (ha : rootCheck s a = true) (t : RelativeTerm Nat)
    (ht : check (contextCode s) t = true) : small s a t = true ↔
      denote (contextCode s) t < interpretation (contextCode s) a := by
  simp only [small, Normalization.lessRawCode_exact, checkCode_code, ht,
    root_original s a ha, interpretation_code, true_and]

def transform (s a : Nat) : RelativeTerm Nat → RelativeTerm Nat
  | .parameter p => .parameter (parameterCode s (.parameter p))
  | .sum t u => cond (small s a (.sum t u))
      (.parameter (parameterCode s (.sum t u))) (.sum (transform s a t) (transform s a u))
  | .theta k t => cond (small s a (.theta k t))
      (.parameter (parameterCode s (.theta k t))) (.theta (k - 1) (transform s a t))

theorem transform_below (s a : Nat) (ha : rootCheck s a = true) (t : RelativeTerm Nat)
    (ht : check (contextCode s) t = true)
    (hs : denote (contextCode s) t < interpretation (contextCode s) a) :
    transform s a t = .parameter (parameterCode s t) := by
  have h := (small_exact s a ha t ht).mpr hs
  cases t <;> simp only [transform, h, Bool.cond_true]

theorem transform_parameter_value (s a : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (contextCode s) t = true)
    (hs : denote (contextCode s) t < interpretation (contextCode s) a) :
    check (alphaCode s a) (transform s a t) = true ∧
      denote (alphaCode s a) (transform s a t) = denote (contextCode s) t := by
  have hp := parameterCode_spec s a ha t ht hs
  rw [transform_below s a ha t ht hs]
  refine ⟨?_, hp.2⟩
  simp only [check, alphaCode_baseCheck s a ha, finiteCheck_parameter, hp.1, Bool.true_and]

/-- Every retained constructor reduces the outer cardinal sort by one;
collapsed subtrees have sort zero. The source-star guard handles theta0. -/
theorem transform_outerSort (s a : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (contextCode s) t = true) (hr : Restricted s a t) :
    (transform s a t).outerSort ≤ t.outerSort - 1 := by
  revert ht hr
  induction t with
  | parameter p => intro ht hr; exact Nat.zero_le _
  | sum t u iht ihu =>
    intro ht hr
    have hc := BaseTransformation.sum_checks _ t u ht
    have hs := (restricted_sum s a t u).mp hr
    cases h : small s a (.sum t u) with
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
      rw [transform_below s a ha _ ht ((restricted_theta_zero s a t).mp hr).1]
      exact Nat.zero_le _
    | succ k =>
      cases h : small s a (.theta (k + 1) t) <;>
        simp only [transform, h, Bool.cond_false, Bool.cond_true, outerSort] <;> omega

theorem transform_height (s a : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (contextCode s) t = true) (hr : Restricted s a t) :
    (transform s a t).height ≤ t.height - 1 := by
  revert ht hr
  induction t with
  | parameter p => intro ht hr; exact Nat.zero_le _
  | sum t u iht ihu =>
    intro ht hr
    have hc := BaseTransformation.sum_checks _ t u ht
    have hs := (restricted_sum s a t u).mp hr
    cases h : small s a (.sum t u) with
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
      rw [transform_below s a ha _ ht ((restricted_theta_zero s a t).mp hr).1]
      exact Nat.zero_le _
    | succ k =>
      have haa := BaseTransformation.theta_argument_check _ (k + 1) t ht
      have hrt := (restricted_theta_succ s a k t).mp hr
      have hh := ih haa hrt
      cases h : small s a (.theta (k + 1) t) <;>
        simp only [transform, h, Bool.cond_false, Bool.cond_true, height] <;> omega

/-- The original finite fragment loses one level. This proves every actual
target theta caller and does not assume any cross-base collapse equation. -/
theorem transform_finite (s a n : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : finiteCheck (contextCode s) n t = true)
    (hr : Restricted s a t) : finiteCheck (alphaCode s a) (n - 1) (transform s a t) = true := by
  revert ht hr
  induction t with
  | parameter p =>
    intro ht hr
    have hc := Comparison.admitted_checked _ n (contextCode_checked s) (.parameter p)
      ((finiteCheck_exact _ n _).mp ht)
    have hp := checked_parameters _ (.parameter p) hc p (by simp [RelativeTerm.parameters])
    have hs : denote (contextCode s) (.parameter p) < interpretation (contextCode s) a :=
      hp.2.trans_le (root_base_le s a ha)
    exact (parameterCode_spec s a ha (.parameter p) hc hs).1
  | sum t u iht ihu =>
    intro ht hr
    have hf := Bool.and_eq_true.mp ht
    have hc := Comparison.admitted_checked _ n (contextCode_checked s) (.sum t u)
      ((finiteCheck_exact _ n _).mp ht)
    have hs := (restricted_sum s a t u).mp hr
    cases h : small s a (.sum t u) with
    | true =>
      simpa only [transform, h, Bool.cond_true, finiteCheck_parameter] using
        (parameterCode_spec s a ha (.sum t u) hc ((small_exact s a ha _ hc).mp h)).1
    | false =>
      simp only [transform, h, Bool.cond_false, finiteCheck_sum,
        iht hf.1 hs.1, ihu hf.2 hs.2, Bool.true_and]
  | theta k t ih =>
    intro ht hr
    have hf : finiteCheck (contextCode s) n t = true ∧ k < n ∧ t.outerSort ≤ k + 2 := by
      simpa only [finiteCheck_theta, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using ht
    have hc := Comparison.admitted_checked _ n (contextCode_checked s) (.theta k t)
      ((finiteCheck_exact _ n _).mp ht)
    cases h : small s a (.theta k t) with
    | true =>
      simpa only [transform, h, Bool.cond_true, finiteCheck_parameter] using
        (parameterCode_spec s a ha (.theta k t) hc ((small_exact s a ha _ hc).mp h)).1
    | false =>
      have hk : 0 < k := by
        cases k with
        | zero =>
          have hh := (small_exact s a ha _ hc).mpr ((restricted_theta_zero s a t).mp hr).1
          rw [h] at hh; cases hh
        | succ k => exact Nat.succ_pos k
      have hrt : Restricted s a t := by
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hk)
        exact (restricted_theta_succ s a j t).mp hr
      have hct := Comparison.admitted_checked _ n (contextCode_checked s) t
        ((finiteCheck_exact _ n _).mp hf.1)
      have hs := transform_outerSort s a ha t hct hrt
      have hn : k - 1 < n - 1 := by omega
      have hsort : (transform s a t).outerSort ≤ k - 1 + 2 := by omega
      simp only [transform, h, Bool.cond_false, finiteCheck_theta, ih hf.1 hrt,
        hn, hsort, decide_true, Bool.true_and]

theorem transform_checked (s a : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (contextCode s) t = true) (hr : Restricted s a t) :
    check (alphaCode s a) (transform s a t) = true := by
  apply (check_exact _ _).mpr
  exact ⟨alphaCode_baseCheck s a ha, SourceOne.PublicCodes.fragment t - 1,
    (finiteCheck_exact _ _ _).mp
      (transform_finite s a _ ha t (Bool.and_eq_true.mp ht).2 hr)⟩

abbrev State := (Nat × Nat) × (RelativeTerm Nat × RelativeTerm Nat)

def parameterState (context : Nat × Nat) (p : Nat) : State :=
  (context, (.parameter p, .parameter (parameterCode context.1 (.parameter p))))

def sumState (x y : State) : State :=
  let t := RelativeTerm.sum x.2.1 y.2.1
  (x.1, (t, cond (small x.1.1 x.1.2 t) (.parameter (parameterCode x.1.1 t))
    (.sum x.2.2 y.2.2)))

def thetaState (context : Nat × Nat) (k : Nat) (x : State) : State :=
  let t := RelativeTerm.theta k x.2.1
  (context, (t, cond (small context.1 context.2 t) (.parameter (parameterCode context.1 t))
    (.theta (k - 1) x.2.2)))

def stateCode (s a c : Nat) : State := ValueFold.code parameterState sumState thetaState
  ((0, 0), (Normalization.zeroTree, Normalization.zeroTree)) (s, a) c

theorem parameterState_primrec : Primrec₂ parameterState := by
  have ht : Primrec (fun p : (Nat × Nat) × Nat => RelativeTerm.parameter p.2) :=
    parameter_primrec.comp Primrec.snd
  have ho := parameter_primrec.comp (parameterCode_primrec.comp
    (Primrec.fst.comp Primrec.fst) ht)
  exact (Primrec.fst.pair (ht.pair ho)).to₂

theorem sumState_primrec : Primrec₂ sumState := by
  have hctx : Primrec (fun p : State × State => p.1.1) := Primrec.fst.comp Primrec.fst
  have hs : Primrec (fun p : State × State => p.1.1.1) := Primrec.fst.comp hctx
  have ht : Primrec (fun p : State × State => RelativeTerm.sum p.1.2.1 p.2.2.1) :=
    sum_primrec.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have hsmall := small_primrec.comp hctx ht
  have hp := parameter_primrec.comp (parameterCode_primrec.comp hs ht)
  have ho := sum_primrec.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact (hctx.pair (ht.pair (hsmall.cond hp ho))).to₂

theorem thetaState_primrec : Primrec
    (fun p : (Nat × Nat) × (Nat × State) => thetaState p.1 p.2.1 p.2.2) := by
  have hk : Primrec (fun p : (Nat × Nat) × (Nat × State) => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have ht : Primrec (fun p : (Nat × Nat) × (Nat × State) =>
      RelativeTerm.theta p.2.1 p.2.2.2.1) := theta_primrec.comp hk
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hsmall := small_primrec.comp Primrec.fst ht
  have hp := parameter_primrec.comp (parameterCode_primrec.comp (Primrec.fst.comp Primrec.fst) ht)
  have ho := theta_primrec.comp (Primrec.nat_sub.comp hk (Primrec.const 1))
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  exact Primrec.fst.pair (ht.pair (hsmall.cond hp ho))

theorem stateCode_primrec : Primrec
    (fun p : (Nat × Nat) × Nat => stateCode p.1.1 p.1.2 p.2) :=
  ValueFold.code_primrec parameterState sumState thetaState
    ((0, 0), (Normalization.zeroTree, Normalization.zeroTree))
    parameterState_primrec sumState_primrec thetaState_primrec

theorem stateCode_code (s a : Nat) (t : RelativeTerm Nat) :
    stateCode s a t.code = ((s, a), (t, transform s a t)) := by
  rw [stateCode, ValueFold.code_term]
  induction t <;> simp_all only [ValueFold.term, parameterState, sumState, thetaState, transform]

def inputCheck (s a c : Nat) : Bool :=
  (rootCheck s a && Comparison.acceptedCode (contextCode s) c) && restrictionCheck s a c

theorem inputCheck_primrec : Primrec
    (fun p : (Nat × Nat) × Nat => inputCheck p.1.1 p.1.2 p.2) := by
  have ha := rootCheck_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)
  have hc := Comparison.acceptedCode_primrec.comp
    (NativePublicBridge.contextCode_primrec.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd
  exact Primrec.and.comp (Primrec.and.comp ha hc) restrictionCheck_primrec

theorem inputCheck_exact (s a c : Nat) : inputCheck s a c = true ↔
    rootCheck s a = true ∧ ∃ t : RelativeTerm Nat, c = t.code ∧ check (contextCode s) t = true ∧
      Comparison.Normal (contextCode s) t ∧ sourceStar (contextCode s) t < interpretation (contextCode s) a := by
  constructor
  · intro h
    obtain ⟨hpair, hr⟩ := Bool.and_eq_true.mp h
    obtain ⟨ha, hc⟩ := Bool.and_eq_true.mp hpair
    have hn := (Comparison.acceptedCode_exact _ c).mp hc
    obtain ⟨t, he, ht⟩ := (checkCode_exact _ c).mp hn.1
    have hnt : Comparison.Normal (contextCode s) t := by simpa only [← he, ThetaCourse.rawTree_code] using hn.2
    exact ⟨ha, t, he.symm, ht, hnt, (restricted_iff_sourceStar s a ha t ht hnt).mp
      ((restrictionCheck_code s a ha t ht).mp (by simpa only [he] using hr))⟩
  · rintro ⟨ha, t, rfl, ht, hn, hs⟩
    exact Bool.and_eq_true.mpr ⟨Bool.and_eq_true.mpr ⟨ha,
      (Comparison.acceptedCode_exact _ _).mpr ⟨by simpa only [checkCode_code] using ht,
        by simpa only [ThetaCourse.rawTree_code] using hn⟩⟩,
      (restrictionCheck_code s a ha t ht).mpr ((restricted_iff_sourceStar s a ha t ht hn).mpr hs)⟩

def literalCode (s a c : Nat) : Nat := cond (inputCheck s a c) (stateCode s a c).2.2.code 0

def normalizeCode (s a c : Nat) : Nat := cond (inputCheck s a c)
  (Normalization.normalizeCode (alphaCode s a) (literalCode s a c)) 0

theorem literalCode_primrec : Primrec
    (fun p : (Nat × Nat) × Nat => literalCode p.1.1 p.1.2 p.2) :=
  inputCheck_primrec.cond (code_primrec.comp (Primrec.snd.comp (Primrec.snd.comp stateCode_primrec)))
    (Primrec.const 0)

theorem normalizeCode_primrec : Primrec
    (fun p : (Nat × Nat) × Nat => normalizeCode p.1.1 p.1.2 p.2) :=
  inputCheck_primrec.cond (Normalization.Effective.normalizeCode_primrec.comp
    (alphaCode_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst))
      literalCode_primrec) (Primrec.const 0)

theorem literalCode_spec (s a c : Nat) (hc : inputCheck s a c = true) :
    ∃ t : RelativeTerm Nat, c = t.code ∧ literalCode s a c = (transform s a t).code ∧
      check (alphaCode s a) (transform s a t) = true ∧
      (transform s a t).height ≤ t.height - 1 := by
  obtain ⟨ha, t, he, ht, hn, hs⟩ := (inputCheck_exact s a c).mp hc
  have hr := (restricted_iff_sourceStar s a ha t ht hn).mpr hs
  exact ⟨t, he, by simp only [literalCode, hc, Bool.cond_true, he, stateCode_code],
    transform_checked s a ha t ht hr, transform_height s a ha t ht hr⟩

theorem normalizeCode_spec (s a c : Nat) (hc : inputCheck s a c = true) :
    Comparison.acceptedCode (alphaCode s a) (normalizeCode s a c) = true ∧
      interpretation (alphaCode s a) (normalizeCode s a c) =
        interpretation (alphaCode s a) (literalCode s a c) := by
  obtain ⟨t, ht, he, hcheck, hh⟩ := literalCode_spec s a c hc
  have hl : checkCode (alphaCode s a) (literalCode s a c) = true := by
    simpa only [he, checkCode_code] using hcheck
  simpa only [normalizeCode, hc, Bool.cond_true] using
    Normalization.normalizeCode_accepted (alphaCode s a) (literalCode s a c) hl

def rawInputCheck (s a c : Nat) : Bool := checkCode (contextCode s) c &&
  inputCheck s a (Normalization.normalizeCode (contextCode s) c)

def rawLiteralCode (s a c : Nat) : Nat := cond (rawInputCheck s a c)
  (literalCode s a (Normalization.normalizeCode (contextCode s) c)) 0

def rawNormalizeCode (s a c : Nat) : Nat := cond (rawInputCheck s a c)
  (normalizeCode s a (Normalization.normalizeCode (contextCode s) c)) 0

theorem rawInputCheck_primrec : Primrec
    (fun p : (Nat × Nat) × Nat => rawInputCheck p.1.1 p.1.2 p.2) := by
  have hq := NativePublicBridge.contextCode_primrec.comp (Primrec.fst.comp Primrec.fst)
  have hn := Normalization.Effective.normalizeCode_primrec.comp hq Primrec.snd
  exact Primrec.and.comp (checkCode_primrec.comp hq Primrec.snd)
    (inputCheck_primrec.comp (Primrec.fst.pair hn))

theorem rawLiteralCode_primrec : Primrec
    (fun p : (Nat × Nat) × Nat => rawLiteralCode p.1.1 p.1.2 p.2) :=
  rawInputCheck_primrec.cond (literalCode_primrec.comp (Primrec.fst.pair
    (Normalization.Effective.normalizeCode_primrec.comp
      (NativePublicBridge.contextCode_primrec.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)))
      (Primrec.const 0)

theorem rawNormalizeCode_primrec : Primrec
    (fun p : (Nat × Nat) × Nat => rawNormalizeCode p.1.1 p.1.2 p.2) :=
  rawInputCheck_primrec.cond (normalizeCode_primrec.comp (Primrec.fst.pair
    (Normalization.Effective.normalizeCode_primrec.comp
      (NativePublicBridge.contextCode_primrec.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)))
      (Primrec.const 0)

theorem rawNormalizeCode_spec (s a c : Nat) (hc : rawInputCheck s a c = true) :
    checkCode (contextCode s) c = true ∧
      Comparison.acceptedCode (alphaCode s a) (rawNormalizeCode s a c) = true ∧
      interpretation (alphaCode s a) (rawNormalizeCode s a c) =
        interpretation (alphaCode s a) (rawLiteralCode s a c) := by
  have hs := Bool.and_eq_true.mp hc
  have hn := normalizeCode_spec s a _ hs.2
  exact ⟨hs.1, by simpa only [rawNormalizeCode, hc, Bool.cond_true] using hn.1,
    by simpa only [rawNormalizeCode, rawLiteralCode, hc, Bool.cond_true] using hn.2⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Iota
