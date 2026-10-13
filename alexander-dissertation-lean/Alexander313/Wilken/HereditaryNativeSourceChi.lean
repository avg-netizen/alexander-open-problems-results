import Alexander313.Wilken.HereditaryNativeSourceChiSupport
import Alexander313.Wilken.HereditaryNativeLogEndZero

/-!
# The executing source indicator in original native epsilon contexts

The actual syntax fold carries each genuine native ANF atom together with
its already computed indicator. Native parameters are atomic source leaves;
their comparison representatives are rewrapped parameters with indicator
zero. The theta branch takes the final retained high label for chi(Delta),
and proves it equals chi of the actual rebuilt Delta term. This avoids an
unjustified descent claim about an enlarged reconstructed code.

Original native admission includes the actual coded epsilon-base check.
The real fixed-point and full-native zero-last-exponent tests select the
printed source branch, and base/parameter/sum/theta clauses are derived.
Original raw execution constructs the genuine normalized spelling first.
No arbitrary-spelling chi invariance, source translation or Lemma 3.4 is
asserted. All proof candidates remain uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceChi

abbrev Entry := RelativeTerm Nat × Bool
abbrev State := RelativeTerm Nat × (Bool × List Entry)

def lastIndicator (as : List Entry) : Bool := (as.reverse.head?.getD (.parameter 0, false)).2

theorem lastIndicator_primrec : Primrec lastIndicator :=
  Primrec.snd.comp (Primrec.option_getD.comp
    (Primrec.list_head?.comp Primrec.list_reverse) (Primrec.const (.parameter 0, false)))

def highLabels (m : Nat) : List Entry → List Entry
  | [] => []
  | e :: es => cond (Decomposition.above m e.1) (e :: highLabels m es) (highLabels m es)

theorem highLabels_primrec : Primrec₂ highLabels := by
  have hc := Decomposition.above_primrec.comp (Primrec.fst.comp Primrec.fst)
    (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
  have hs := (hc.cond (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
    (Primrec.snd.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)).to₂
  have h := Primrec.list_foldr Primrec.snd (Primrec.const ([] : List Entry)) hs
  have he : (fun p : Nat × List Entry => p.2.foldr (fun e es =>
      cond (Decomposition.above p.1 e.1) (e :: es) es) []) =
      (fun p => highLabels p.1 p.2) := by
    funext p
    rcases p with ⟨m, es⟩
    induction es with
    | nil => rfl
    | cons e es ih => simp only [List.foldr_cons, highLabels, ih]
  rw [he] at h
  exact h.to₂

def chooseHigh (q m c : Nat) : Bool := FixedPoint.fixedCode q m c ||
  LogEndZero.zeroCheck q (Decomposition.lowCode m c)

theorem chooseHigh_primrec : Primrec (fun p : Nat × (Nat × Nat) => chooseHigh p.1 p.2.1 p.2.2) :=
  Primrec.or.comp FixedPoint.fixedCode_primrec
    (LogEndZero.zeroCheck_primrec.comp Primrec.fst
      (Decomposition.lowCode_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)))

def parameterState (q p : Nat) : State :=
  (.parameter p, (false, (Comparison.atoms (.parameter p)).map (fun a => (a, false))))

def sumState (a b : State) : State := (.sum a.1 b.1, (b.2.1, a.2.2 ++ b.2.2))

def baseCase (q m c : Nat) : Bool := (m == 0) && FixedPoint.zeroCheck c

def thetaState (q m : Nat) (a : State) : State :=
  let v := cond (baseCase q m a.1.code) true
    (cond (chooseHigh q m a.1.code) (lastIndicator (highLabels m a.2.2)) a.2.1)
  (.theta m a.1, (v, [(.theta m a.1, v)]))

theorem parameterState_primrec : Primrec₂ parameterState := by
  have ht := parameter_primrec.comp Primrec.snd
  have ha := Comparison.atoms_primrec.comp ht
  have hm := Primrec.list_map ha (Primrec.snd.pair (Primrec.const false)).to₂
  exact (ht.pair ((Primrec.const false).pair hm)).to₂

theorem sumState_primrec : Primrec₂ sumState := by
  have ht := sum_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)
  have hv := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have ha := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hb := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact (ht.pair (hv.pair (Primrec.list_append.comp ha hb))).to₂

theorem baseCase_primrec : Primrec (fun p : Nat × (Nat × Nat) => baseCase p.1 p.2.1 p.2.2) :=
  Primrec.and.comp (Primrec.beq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 0))
    (FixedPoint.zeroCheck_primrec.comp (Primrec.snd.comp Primrec.snd))

theorem thetaState_primrec : Primrec (fun p : Nat × (Nat × State) => thetaState p.1 p.2.1 p.2.2) := by
  have hm := Primrec.fst.comp Primrec.snd
  have ha := Primrec.snd.comp Primrec.snd
  have ht := Primrec.fst.comp ha
  have hc := code_primrec.comp ht
  have hp := Primrec.fst.pair (hm.pair hc)
  have hlabels := Primrec.snd.comp (Primrec.snd.comp ha)
  have hhigh := lastIndicator_primrec.comp (highLabels_primrec.comp hm hlabels)
  have hvalue := (baseCase_primrec.comp hp).cond (Primrec.const true)
    ((chooseHigh_primrec.comp hp).cond hhigh (Primrec.fst.comp (Primrec.snd.comp ha)))
  have hnode := theta_primrec.comp hm ht
  have hentry := hnode.pair hvalue
  exact hnode.pair (hvalue.pair (Primrec.list_cons.comp hentry (Primrec.const [])))

def state (q : Nat) (t : RelativeTerm Nat) : State :=
  ValueFold.term parameterState sumState thetaState q t

def stateCode (q c : Nat) : State :=
  ValueFold.code parameterState sumState thetaState (.parameter 0, (false, [])) q c

theorem state_primrec : Primrec₂ state :=
  ValueFold.term_primrec parameterState sumState thetaState (.parameter 0, (false, []))
    parameterState_primrec sumState_primrec thetaState_primrec

theorem stateCode_primrec : Primrec₂ stateCode :=
  ValueFold.code_primrec parameterState sumState thetaState (.parameter 0, (false, []))
    parameterState_primrec sumState_primrec thetaState_primrec

@[simp] theorem stateCode_code (q : Nat) (t : RelativeTerm Nat) : stateCode q t.code = state q t :=
  ValueFold.code_term parameterState sumState thetaState (.parameter 0, (false, [])) q t

theorem state_tree (q : Nat) (t : RelativeTerm Nat) : (state q t).1 = t := by
  induction t with
  | parameter p => rfl
  | sum a b iha ihb =>
    change RelativeTerm.sum (state q a).1 (state q b).1 = _
    rw [iha, ihb]
  | theta m a ih =>
    change RelativeTerm.theta m (state q a).1 = _
    rw [ih]

def indicator (q : Nat) (t : RelativeTerm Nat) : Bool := (state q t).2.1

theorem indicator_primrec : Primrec₂ indicator :=
  (Primrec.fst.comp Primrec.snd).comp₂ state_primrec

@[simp] theorem indicator_parameter (q p : Nat) : indicator q (.parameter p) = false := rfl

@[simp] theorem indicator_sum (q : Nat) (a b : RelativeTerm Nat) :
    indicator q (.sum a b) = indicator q b := rfl

private theorem parameter_atoms_shape (p : Nat) (a : RelativeTerm Nat)
    (ha : a ∈ Comparison.atoms (.parameter p)) : ∃ v, a = .parameter v := by
  obtain ⟨v, hv, he⟩ := List.mem_map.mp ha
  exact ⟨v, he.symm⟩

/-- Every stored label is the same genuinely computed indicator of its
literal principal representative. -/
theorem state_labels (q : Nat) (t : RelativeTerm Nat) :
    (state q t).2.2 = (Comparison.atoms t).map (fun a => (a, indicator q a)) := by
  induction t with
  | parameter p =>
    change (Comparison.atoms (.parameter p)).map (fun a => (a, false)) = _
    apply List.map_congr_left
    intro a ha
    obtain ⟨v, rfl⟩ := parameter_atoms_shape p a ha
    rfl
  | sum a b iha ihb =>
    change (state q a).2.2 ++ (state q b).2.2 = _
    rw [iha, ihb, Comparison.atoms, List.map_append]
  | theta m a ih =>
    change [(.theta m (state q a).1, indicator q (.theta m a))] = _
    rw [state_tree, Comparison.atoms]
    rfl

theorem highLabels_map (m : Nat) (as : List (RelativeTerm Nat)) (f : RelativeTerm Nat → Bool) :
    highLabels m (as.map (fun a => (a, f a))) =
      (Decomposition.select true m as).map (fun a => (a, f a)) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    cases h : Decomposition.above m a <;>
      simp only [List.map_cons, highLabels, Decomposition.select, Bool.cond_true,
        h, Bool.cond_false, ih]

theorem state_highLabels (q m : Nat) (a : RelativeTerm Nat) :
    highLabels m (state q a).2.2 =
      (Decomposition.highWord m a.code).map (fun b => (b, indicator q b)) := by
  rw [state_labels, highLabels_map]
  simp only [Decomposition.highWord, Decomposition.word, ThetaCourse.rawTree_code]

@[simp] theorem indicator_zeroTree (q : Nat) : indicator q (Normalization.zeroTree) = false := rfl

theorem indicator_buildAtoms (q : Nat) (as : List (RelativeTerm Nat)) :
    indicator q (Normalization.buildAtoms as) =
      lastIndicator (as.map (fun a => (a, indicator q a))) := by
  unfold lastIndicator
  rw [← List.map_reverse]
  cases hr : as.reverse with
  | nil => simp [Normalization.buildAtoms, hr, Normalization.buildRev, indicator_zeroTree]
  | cons a bs => simp [Normalization.buildAtoms, hr, Normalization.buildRev, indicator_sum]

/-- Both printed recursive targets are already computed by strict descent
through the original finite syntax, including the reconstructed Delta target. -/
theorem indicator_theta (q m : Nat) (a : RelativeTerm Nat) :
    indicator q (.theta m a) = cond (baseCase q m a.code) true
      (cond (chooseHigh q m a.code)
        (indicator q (Decomposition.highPartTerm m a.code)) (indicator q a)) := by
  change cond (baseCase q m (state q a).1.code) true
    (cond (chooseHigh q m (state q a).1.code)
      (lastIndicator (highLabels m (state q a).2.2)) (indicator q a)) = _
  rw [state_tree, state_highLabels, Decomposition.highPartTerm, indicator_buildAtoms]

theorem indicator_below_base (q : Nat) (t : RelativeTerm Nat)
    (ht : check q t = true) (hn : Comparison.Normal q t) (hv : denote q t < base q) :
    indicator q t = false := by
  revert ht hn hv
  induction t with
  | parameter p => intros; rfl
  | sum a b iha ihb =>
    intro ht hn hv
    have hs := sum_children q a b ht hn
    rw [indicator_sum]
    apply ihb hs.2.2.1 hs.2.2.2.1
    exact (show denote q b ≤ denote q (.sum a b) by
      change denote q b ≤ denote q a + denote q b
      exact le_add_self).trans_lt hv
  | theta m a ih =>
    intro ht hn hv
    have hs := (FixedPoint.checked_theta_range q m a ht).1
    exact False.elim (hv.not_ge
      (((omegaSequence_strictMono (base q)).monotone (Nat.zero_le m)).trans hs))

theorem indicator_base (q : Nat) (t : RelativeTerm Nat)
    (ht : check q t = true) (hn : Comparison.Normal q t) (hv : denote q t = base q) :
    indicator q t = true := by
  revert ht hn hv
  induction t with
  | parameter p =>
    intro ht hn hv
    exact False.elim ((ne_of_lt (FixedPoint.checked_parameter_lt_base q p ht)) hv)
  | sum a b iha ihb =>
    intro ht hn hv
    have hs := sum_children q a b ht hn
    have hz : denote q a = 0 := by
      by_contra h
      exact RelativeTerm.PrincipalSupport.sourceNormalSum_not_principal hs.2.2.2.2
        (pos_iff_ne_zero.mpr h) (hv.symm ▸ base_add_closed q (Bool.and_eq_true.mp ht).1)
    have hb : denote q b = base q := by
      change denote q a + denote q b = base q at hv
      simpa only [hz, zero_add] using hv
    rw [indicator_sum]
    exact ihb hs.2.2.1 hs.2.2.2.1 hb
  | theta m a ih =>
    intro ht hn hv
    obtain ⟨rfl, hz⟩ := theta_base_argument_zero q m a ht hv
    have ha := (theta_argument_parts q 0 a ht hn).1
    have hc : FixedPoint.zeroCheck a.code = true :=
      (FixedPoint.zeroCheck_exact q a.code ha).mpr (by simpa only [interpretation_code] using hz)
    simp only [indicator_theta, baseCase, beq_self_eq_true, hc, Bool.true_and, Bool.cond_true]

theorem chooseHigh_correct (q m : Nat) (a : RelativeTerm Nat)
    (ht : check q (.theta m a) = true) (hn : Comparison.Normal q (.theta m a)) :
    chooseHigh q m a.code = true ↔ FixedPoint.SourceFixed q m a.code ∨
      Hereditary.LogEndZero.SourceZero (interpretation q (Decomposition.lowCode m a.code)) := by
  have hi := theta_argument_input q m a ht hn
  have hp := theta_argument_parts q m a ht hn
  rw [chooseHigh, Bool.or_eq_true, FixedPoint.fixedCode_correct q m a.code hi]
  simpa only [Hereditary.LogEndZero.SourceZero] using
    or_congr Iff.rfl (LogEndZero.zeroCheck_correct q _ hp.2.2)

/-- The branch is exactly fixed residual supremum OR literal zero last
exponent, whenever that genuine last exponent is presented by SourceLogSpec. -/
theorem chooseHigh_logend (q m : Nat) (a : RelativeTerm Nat)
    (ht : check q (.theta m a) = true) (hn : Comparison.Normal q (.theta m a))
    (ell : Ordinal.{0})
    (he : LogEnd.SourceLogSpec true (interpretation q (Decomposition.lowCode m a.code)) ell) :
    chooseHigh q m a.code = true ↔ FixedPoint.SourceFixed q m a.code ∨ ell = 0 := by
  rw [chooseHigh_correct q m a ht hn]
  exact or_congr Iff.rfl (Hereditary.LogEndZero.sourceLogSpec_zero_iff _ _ he).symm

/-- The branch condition is the literal source supremum at the actual
divisible prefix and residual, together with literal logend-zero. -/
theorem chooseHigh_literal (q m : Nat) (a : RelativeTerm Nat)
    (ht : check q (.theta m a) = true) (hn : Comparison.Normal q (.theta m a))
    (ell : Ordinal.{0})
    (he : LogEnd.SourceLogSpec true (interpretation q (Decomposition.lowCode m a.code)) ell) :
    chooseHigh q m a.code = true ↔
      SourceFixedPointLimits.globalResidualImageSup (base q) m
        (interpretation q (Decomposition.highCode m a.code))
        (interpretation q (Decomposition.lowCode m a.code)) =
          interpretation q (Decomposition.lowCode m a.code) ∨ ell = 0 := by
  have hp := Decomposition.parts_code_value q m a.code (theta_argument_parts q m a ht hn).1
  simpa only [FixedPoint.SourceFixed, FixedPoint.delta, FixedPoint.residual,
    hp.1, hp.2] using chooseHigh_logend q m a ht hn ell he

theorem baseCase_false (q m : Nat) (a : RelativeTerm Nat)
    (ht : check q (.theta m a) = true) (hn : Comparison.Normal q (.theta m a))
    (harg : m = 0 → 0 < denote q a) : baseCase q m a.code = false := by
  cases h : baseCase q m a.code with
  | false => rfl
  | true =>
    obtain ⟨hm, hz⟩ := Bool.and_eq_true.mp h
    have hm0 : m = 0 := by simpa only [beq_iff_eq] using hm
    have ha := (theta_argument_parts q m a ht hn).1
    have hv : denote q a = 0 := by
      simpa only [interpretation_code] using (FixedPoint.zeroCheck_exact q a.code ha).mp hz
    exact False.elim ((ne_of_gt (harg hm0)) hv)

theorem indicator_theta_high (q m : Nat) (a : RelativeTerm Nat)
    (ht : check q (.theta m a) = true) (hn : Comparison.Normal q (.theta m a))
    (harg : m = 0 → 0 < denote q a) (hc : chooseHigh q m a.code = true) :
    indicator q (.theta m a) = indicator q (Decomposition.highPartTerm m a.code) := by
  rw [indicator_theta, baseCase_false q m a ht hn harg, hc]
  rfl

theorem indicator_theta_argument (q m : Nat) (a : RelativeTerm Nat)
    (ht : check q (.theta m a) = true) (hn : Comparison.Normal q (.theta m a))
    (harg : m = 0 → 0 < denote q a) (hc : chooseHigh q m a.code = false) :
    indicator q (.theta m a) = indicator q a := by
  rw [indicator_theta, baseCase_false q m a ht hn harg, hc]
  rfl

def inputCheck (q c : Nat) : Bool := Decomposition.inputCheck q c

theorem inputCheck_primrec : Primrec₂ inputCheck := Decomposition.inputCheck_primrec

theorem inputCheck_exact (q c : Nat) : inputCheck q c = true ↔
    checkCode q c = true ∧ Comparison.Normal q (ThetaCourse.rawTree c) :=
  Decomposition.inputCheck_exact q c

def chiCode (q c : Nat) : Bool := inputCheck q c && (stateCode q c).2.1

theorem chiCode_primrec : Primrec₂ chiCode :=
  (Primrec.and.comp inputCheck_primrec ((Primrec.fst.comp Primrec.snd).comp stateCode_primrec)).to₂

theorem chiCode_correct (q : Nat) (t : RelativeTerm Nat)
    (ht : check q t = true) (hn : Comparison.Normal q t) : chiCode q t.code = indicator q t := by
  have hi := (inputCheck_exact q t.code).mpr ⟨by simpa only [checkCode_code] using ht,
    by simpa only [ThetaCourse.rawTree_code] using hn⟩
  simp only [chiCode, hi, stateCode_code, indicator, Bool.true_and]

theorem chiCode_below_base (q : Nat) (t : RelativeTerm Nat)
    (ht : check q t = true) (hn : Comparison.Normal q t) (hv : denote q t < base q) :
    chiCode q t.code = false :=
  (chiCode_correct q t ht hn).trans (indicator_below_base q t ht hn hv)

theorem chiCode_base (q : Nat) (t : RelativeTerm Nat)
    (ht : check q t = true) (hn : Comparison.Normal q t) (hv : denote q t = base q) :
    chiCode q t.code = true :=
  (chiCode_correct q t ht hn).trans (indicator_base q t ht hn hv)

def dualCode (q c : Nat) : Bool := inputCheck q c && !(stateCode q c).2.1

theorem dualCode_primrec : Primrec₂ dualCode :=
  (Primrec.and.comp inputCheck_primrec (Primrec.not.comp
    ((Primrec.fst.comp Primrec.snd).comp stateCode_primrec))).to₂

theorem dualCode_correct (q : Nat) (t : RelativeTerm Nat)
    (ht : check q t = true) (hn : Comparison.Normal q t) : dualCode q t.code = !(indicator q t) := by
  have hi := (inputCheck_exact q t.code).mpr ⟨by simpa only [checkCode_code] using ht,
    by simpa only [ThetaCourse.rawTree_code] using hn⟩
  simp only [dualCode, hi, stateCode_code, indicator, Bool.true_and]

def rawInputCheck (q c : Nat) : Bool := checkCode q c

theorem rawInputCheck_primrec : Primrec₂ rawInputCheck := NativeContext.checkCode_primrec

theorem rawInputCheck_exact (q c : Nat) : rawInputCheck q c = true ↔ checkCode q c = true := Iff.rfl

theorem normalized_input (q c : Nat) (hc : rawInputCheck q c = true) :
    inputCheck q (Normalization.normalizeCode q c) = true :=
  (Normalization.normalizeCode_accepted q c hc).1

def rawChiCode (q c : Nat) : Bool := rawInputCheck q c &&
  chiCode q (Normalization.normalizeCode q c)

theorem rawChiCode_primrec : Primrec₂ rawChiCode :=
  (Primrec.and.comp rawInputCheck_primrec (chiCode_primrec.comp Primrec.fst
    Normalization.Effective.normalizeCode_primrec)).to₂

theorem rawChiCode_correct (q c : Nat) (hc : rawInputCheck q c = true) :
    rawChiCode q c = indicator q (Normalization.normalize q (ThetaCourse.rawTree c)) := by
  have hn := normalized_input q c hc
  obtain ⟨t, ht, hcheck⟩ := (checkCode_exact q c).mp hc
  subst c
  simp only [rawChiCode, hc, chiCode, hn, Bool.true_and, Normalization.normalizeCode, checkCode_code, hcheck,
    stateCode_code, indicator, ThetaCourse.rawTree_code]

def rawDualCode (q c : Nat) : Bool := rawInputCheck q c &&
  dualCode q (Normalization.normalizeCode q c)

theorem rawDualCode_primrec : Primrec₂ rawDualCode :=
  (Primrec.and.comp rawInputCheck_primrec (dualCode_primrec.comp Primrec.fst
    Normalization.Effective.normalizeCode_primrec)).to₂

theorem rawDualCode_correct (q c : Nat) (hc : rawInputCheck q c = true) :
    rawDualCode q c = !(indicator q (Normalization.normalize q (ThetaCourse.rawTree c))) := by
  have hn := normalized_input q c hc
  obtain ⟨t, ht, hcheck⟩ := (checkCode_exact q c).mp hc
  subst c
  simp only [rawDualCode, hc, dualCode, hn, Bool.true_and, Normalization.normalizeCode, checkCode_code, hcheck,
    stateCode_code, indicator, ThetaCourse.rawTree_code]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceChi
