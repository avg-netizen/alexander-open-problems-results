import Alexander313.Wilken.PublicEpsilonNativeRootCompleteScalarCollapse
import Alexander313.Wilken.PublicEpsilonNativeIotaOrderInduction

/-!
# Direct original-source provenance for returned iota

Original parameters and whole theta-zero nodes retain their ORIGINAL
syntax. Sums execute genuine native normalization. Positive source indices
are lowered through the complete relative scalar producer. All recursive
source Normality and sort callers are derived, without arbitrary target
payload inversion or a selected return endpoint. The mapped-iota equation
will use the original restricted domain separately. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.ReturnedIota

open ThetaCourse

abbrev Context := PublicEpsilonIota.Context

def returnedTreeCode (q b : Nat) : RelativeTerm Nat → Nat
  | .parameter p => (.parameter p : RelativeTerm Nat).code
  | .sum t u => Arithmetic.addCode q (returnedTreeCode q b t) (returnedTreeCode q b u)
  | .theta 0 t => (.theta 0 t : RelativeTerm Nat).code
  | .theta (k + 1) t => RootCompleteScalarCollapse.collapseCode q b k (returnedTreeCode q b t)

abbrev State := Context × (RelativeTerm Nat × Nat)

def parameterState (ctx : Context) (p : Nat) : State :=
  (ctx, (.parameter p, (.parameter p : RelativeTerm Nat).code))

def sumState (x y : State) : State :=
  (x.1, (.sum x.2.1 y.2.1, Arithmetic.addCode x.1.1 x.2.2 y.2.2))

def thetaState (ctx : Context) (k : Nat) (x : State) : State :=
  let t := RelativeTerm.theta k x.2.1
  (ctx, (t, cond (decide (k = 0)) t.code
    (RootCompleteScalarCollapse.collapseCode ctx.1 ctx.2 (k - 1) x.2.2)))

theorem parameterState_primrec : Primrec₂ parameterState := by
  have ht := parameter_primrec.comp Primrec.snd
  exact (Primrec.fst.pair (ht.pair (code_primrec.comp ht))).to₂

theorem sumState_primrec : Primrec₂ sumState := by
  have hctx := Primrec.fst.comp Primrec.fst
  have ht := sum_primrec.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have hq := Primrec.fst.comp hctx
  have hc := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hd := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact (hctx.pair (ht.pair (Arithmetic.addCode_primrec.comp (hq.pair (hc.pair hd))))).to₂

theorem thetaState_primrec : Primrec
    (fun p : Context × (Nat × State) => thetaState p.1 p.2.1 p.2.2) := by
  have hk := Primrec.fst.comp Primrec.snd
  have ht := theta_primrec.comp hk (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hz := (Primrec.eq.comp hk (Primrec.const 0)).decide
  have hc := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hs := RootCompleteScalarCollapse.collapseCode_primrec.comp
    ((Primrec.fst.comp Primrec.fst).pair ((Primrec.snd.comp Primrec.fst).pair
      ((Primrec.nat_sub.comp hk (Primrec.const 1)).pair hc)))
  exact Primrec.fst.pair (ht.pair (hz.cond (code_primrec.comp ht) hs))

def stateCode (q b c : Nat) : State := ValueFold.code parameterState sumState thetaState
  ((0, 0), (Normalization.zeroTree, 0)) (q, b) c

theorem stateCode_primrec : Primrec₂ (fun ctx : Context => stateCode ctx.1 ctx.2) :=
  ValueFold.code_primrec parameterState sumState thetaState
    ((0, 0), (Normalization.zeroTree, 0))
    parameterState_primrec sumState_primrec thetaState_primrec

theorem stateCode_code (q b : Nat) (t : RelativeTerm Nat) :
    stateCode q b t.code = ((q, b), (t, returnedTreeCode q b t)) := by
  rw [stateCode, ValueFold.code_term]
  induction t with
  | parameter p => rfl
  | sum t u iht ihu => simp only [ValueFold.term, sumState, iht, ihu, returnedTreeCode]
  | theta k t ih =>
    cases k with
    | zero => simp only [ValueFold.term, thetaState, ih, returnedTreeCode,
        decide_eq_true (rfl : (0 : Nat) = 0), Bool.cond_true]
    | succ k => simp only [ValueFold.term, thetaState, ih, returnedTreeCode,
        decide_eq_false (Nat.succ_ne_zero k), Bool.cond_false, Nat.add_sub_cancel]

theorem returnedTreeCode_primrec : Primrec₂ (fun ctx : Context => returnedTreeCode ctx.1 ctx.2) := by
  have h := Primrec.snd.comp (Primrec.snd.comp
    (stateCode_primrec.comp Primrec.fst (code_primrec.comp Primrec.snd)))
  simpa only [stateCode_code] using h.to₂

theorem original_accepted (q : Nat) (t : RelativeTerm Nat)
    (ht : check q t = true) (hn : Comparison.Normal q t) : Comparison.acceptedCode q t.code = true :=
  (Comparison.acceptedCode_exact q _).mpr
    ⟨by simpa only [checkCode_code] using ht, by simpa only [rawTree_code] using hn⟩

/-- True native addition preserves a positive cardinal sort bound. -/
theorem addCode_sort (q c d j : Nat) (hc : Comparison.acceptedCode q c = true)
    (hd : Comparison.acceptedCode q d = true) (hj : 0 < j)
    (hcs : (rawTree c).outerSort ≤ j) (hds : (rawTree d).outerSort ≤ j) :
    (rawTree (Arithmetic.addCode q c d)).outerSort ≤ j := by
  have hc' := ((Comparison.acceptedCode_exact q c).mp hc).1
  have hd' := ((Comparison.acceptedCode_exact q d).mp hd).1
  have hs := Arithmetic.addCode_spec q c d hc' hd'
  have ho := ((Comparison.acceptedCode_exact q _).mp hs.1).1
  apply (denote_lt_iff_outerSort_le q _ (Arithmetic.raw_checked q _ ho) j hj).mp
  rw [Arithmetic.raw_value q _ ho, hs.2.1]
  have hcv : interpretation q c < omegaSequence (base q) j := by
    rw [← Arithmetic.raw_value q c hc']
    exact (denote_lt_iff_outerSort_le q _ (Arithmetic.raw_checked q c hc') j hj).mpr hcs
  have hdv : interpretation q d < omegaSequence (base q) j := by
    rw [← Arithmetic.raw_value q d hd']
    exact (denote_lt_iff_outerSort_le q _ (Arithmetic.raw_checked q d hd') j hj).mpr hds
  have he : j - 1 + 1 = j := by omega
  have hclosed := (omegaSequence_add_closed (base q) (j - 1))
    (by simpa only [he] using hcv) (by simpa only [he] using hdv)
  simpa only [he] using hclosed

/-- The genuine complete scalar output has its literal lowered sort;
zero uses its actual LOW codec witness, positive indices its real node. -/
theorem scalar_output_sort (q b k c : Nat)
    (hi : RootCompleteScalarCollapse.inputCheck q b k c = true) :
    (rawTree (RootCompleteScalarCollapse.collapseCode q b k c)).outerSort ≤ k + 1 := by
  by_cases hk : 0 < k
  · have hb : RootCompleteScalarCollapse.knownBranch q b k c = true := by
      simp only [RootCompleteScalarCollapse.knownBranch, decide_eq_true hk, Bool.true_or]
    have hs := RootCompleteScalarCollapse.scalar_caller q b k c hi hb
    have hp := RootCompleteScalarCollapse.positive_caller q b k c hi hk
    simp only [RootCompleteScalarCollapse.collapseCode, hi, hb, Bool.cond_true,
      RootScalarCollapse.collapseCode, hs, decide_eq_true hk,
      RootPositiveCollapse.collapseCode, hp, RootPositiveCollapse.nodeCode,
      rawTree_code, outerSort, le_refl]
  · have he : k = 0 := by omega
    subst k
    obtain ⟨t, ht, hchecked⟩ := (lowCheckCode_exact q _).mp
      (RootCompleteScalarCollapse.collapseCode_zero_low q b c hi)
    have hsort := of_decide_eq_true (Bool.and_eq_true.mp hchecked).2
    simpa only [← ht, rawTree_code, Nat.zero_add] using hsort

theorem scalar_caller (q b k : Nat) (ha : RootLowCollapse.rootCheck q b = true)
    (t : RelativeTerm Nat) (ht : check q (.theta (k + 1) t) = true)
    (out : Nat) (ho : Comparison.acceptedCode q out = true)
    (hs : (rawTree out).outerSort ≤ max 1 (t.outerSort - 1)) :
    RootCompleteScalarCollapse.inputCheck q b k out = true := by
  have hc := FixedPoint.checked_theta_argument q (k + 1) t ht
  have hsort := (denote_lt_iff_outerSort_le q t hc (k + 1 + 2) (by omega)).mp
    (FixedPoint.checked_theta_sort q (k + 1) t ht)
  exact (RootCompleteScalarCollapse.inputCheck_exact q b k out).mpr ⟨ha, ho, by omega⟩

/-- Admission and sort need ONLY the original high root and original
checked Normal syntax. Original endpoint or restriction is not assumed. -/
theorem returnedTreeCode_admitted (q b : Nat) (ha : RootLowCollapse.rootCheck q b = true)
    (t : RelativeTerm Nat) (ht : check q t = true) (hn : Comparison.Normal q t) :
    Comparison.acceptedCode q (returnedTreeCode q b t) = true ∧
      (rawTree (returnedTreeCode q b t)).outerSort ≤ max 1 (t.outerSort - 1) := by
  revert ht hn
  induction t with
  | parameter p =>
    intro ht hn
    exact ⟨original_accepted q _ ht hn, by
      simpa only [returnedTreeCode, rawTree_code, outerSort] using
        (Nat.zero_le (max 1 ((0 : Nat) - 1)))⟩
  | sum t u iht ihu =>
    intro ht hn
    have hc := BaseTransformation.sum_checks q t u ht
    have hl := iht hc.1 hn.1
    have hr := ihu hc.2 hn.2.1
    have hs := Arithmetic.addCode_spec q _ _
      ((Comparison.acceptedCode_exact q _).mp hl.1).1
      ((Comparison.acceptedCode_exact q _).mp hr.1).1
    refine ⟨hs.1, addCode_sort q _ _ _ hl.1 hr.1 (by omega) ?_ ?_⟩
    · simp only [outerSort]; omega
    · simp only [outerSort]; omega
  | theta k t ih =>
    intro ht hn
    cases k with
    | zero =>
      exact ⟨original_accepted q _ ht hn,
        by simpa only [returnedTreeCode, rawTree_code, outerSort] using
          (le_max_left (1 : Nat) (1 - 1))⟩
    | succ k =>
      have hs := ih (FixedPoint.checked_theta_argument q (k + 1) t ht) hn
      have hc := scalar_caller q b k ha t ht _ hs.1 hs.2
      refine ⟨(RootCompleteScalarCollapse.collapseCode_spec q b k _ hc).1, ?_⟩
      have hsort := scalar_output_sort q b k _ hc
      simp only [returnedTreeCode, outerSort]
      omega

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.ReturnedIota
