import Alexander313.Wilken.PublicEpsilonNativeUnboundedIotaLogEndZeroTransport
import Alexander313.Wilken.HereditaryNativeSourceChiBaseChangeSupport
import Alexander313.Wilken.HereditaryNativeSourceChiArithmetic

/-!
# A genuine finite indicator fold on original source syntax

The fold keeps the ORIGINAL tree and its principal labels. Level-zero
source nodes have bit zero, and a genuine level-one node with zero argument
has bit one. The remaining positive branch uses the actual original
chooseHigh test and the already computed final high label. Thus the intended
bit is chi at the NEW beta base after iota, not the original q indicator.
No target parameter word, indicator invariance or recursive oracle is used.
All source candidates are uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.ShiftedIndicator

open ThetaCourse

abbrev State := SourceChi.State

def baseCase (q k c : Nat) : Bool := (k == 1) && FixedPoint.zeroCheck c

def thetaState (q k : Nat) (a : State) : State :=
  let v := cond (k == 0) false
    (cond (baseCase q k a.1.code) true
      (cond (SourceChi.chooseHigh q k a.1.code)
        (SourceChi.lastIndicator (SourceChi.highLabels k a.2.2)) a.2.1))
  (.theta k a.1, (v, [(.theta k a.1, v)]))

theorem baseCase_primrec : Primrec
    (fun p : Nat × (Nat × Nat) => baseCase p.1 p.2.1 p.2.2) :=
  Primrec.and.comp (Primrec.beq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1))
    (FixedPoint.zeroCheck_primrec.comp (Primrec.snd.comp Primrec.snd))

theorem thetaState_primrec : Primrec
    (fun p : Nat × (Nat × State) => thetaState p.1 p.2.1 p.2.2) := by
  have hk := Primrec.fst.comp Primrec.snd
  have ha := Primrec.snd.comp Primrec.snd
  have ht := Primrec.fst.comp ha
  have hc := code_primrec.comp ht
  have hp := Primrec.fst.pair (hk.pair hc)
  have hlabels := Primrec.snd.comp (Primrec.snd.comp ha)
  have hhigh := SourceChi.lastIndicator_primrec.comp (SourceChi.highLabels_primrec.comp hk hlabels)
  have hbody := (baseCase_primrec.comp hp).cond (Primrec.const true)
    ((SourceChi.chooseHigh_primrec.comp hp).cond hhigh (Primrec.fst.comp (Primrec.snd.comp ha)))
  have hvalue := (Primrec.beq.comp hk (Primrec.const 0)).cond (Primrec.const false) hbody
  have hnode := theta_primrec.comp hk ht
  exact hnode.pair (hvalue.pair
    (Primrec.list_cons.comp (hnode.pair hvalue) (Primrec.const [])))

def state (q : Nat) (t : RelativeTerm Nat) : State :=
  ValueFold.term SourceChi.parameterState SourceChi.sumState thetaState q t

def stateCode (q c : Nat) : State :=
  ValueFold.code SourceChi.parameterState SourceChi.sumState thetaState
    (.parameter 0, (false, [])) q c

theorem state_primrec : Primrec₂ state :=
  ValueFold.term_primrec SourceChi.parameterState SourceChi.sumState thetaState
    (.parameter 0, (false, [])) SourceChi.parameterState_primrec
    SourceChi.sumState_primrec thetaState_primrec

theorem stateCode_primrec : Primrec₂ stateCode :=
  ValueFold.code_primrec SourceChi.parameterState SourceChi.sumState thetaState
    (.parameter 0, (false, [])) SourceChi.parameterState_primrec
    SourceChi.sumState_primrec thetaState_primrec

@[simp] theorem stateCode_code (q : Nat) (t : RelativeTerm Nat) : stateCode q t.code = state q t :=
  ValueFold.code_term SourceChi.parameterState SourceChi.sumState thetaState
    (.parameter 0, (false, [])) q t

theorem state_tree (q : Nat) (t : RelativeTerm Nat) : (state q t).1 = t := by
  induction t with
  | parameter p => rfl
  | sum a b iha ihb =>
    change RelativeTerm.sum (state q a).1 (state q b).1 = _
    rw [iha, ihb]
  | theta k a ih =>
    change RelativeTerm.theta k (state q a).1 = _
    rw [ih]

def indicator (q : Nat) (t : RelativeTerm Nat) : Bool := (state q t).2.1

theorem indicator_primrec : Primrec₂ indicator :=
  (Primrec.fst.comp Primrec.snd).comp₂ state_primrec

@[simp] theorem indicator_parameter (q p : Nat) : indicator q (.parameter p) = false := rfl

@[simp] theorem indicator_sum (q : Nat) (a b : RelativeTerm Nat) :
    indicator q (.sum a b) = indicator q b := rfl

@[simp] theorem indicator_theta_zero (q : Nat) (a : RelativeTerm Nat) :
    indicator q (.theta 0 a) = false := rfl

def highBits (q m : Nat) (t : RelativeTerm Nat) : List Bool :=
  (SourceChi.highLabels m (state q t).2.2).map Prod.snd

private theorem highLabels_append (m : Nat) (as bs : List SourceChi.Entry) :
    SourceChi.highLabels m (as ++ bs) =
      SourceChi.highLabels m as ++ SourceChi.highLabels m bs := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    cases hc : Decomposition.above m a.1 <;>
      simp only [List.cons_append, SourceChi.highLabels, hc,
        Bool.cond_false, Bool.cond_true, ih]

theorem highBits_parameter (q m p : Nat) : highBits q m (.parameter p) = [] := by
  unfold highBits
  change (SourceChi.highLabels m (((CanonicalCoefficients.word p).map RelativeTerm.parameter).map
    (fun a => (a, false)))).map Prod.snd = []
  induction CanonicalCoefficients.word p with
  | nil => rfl
  | cons a as ih =>
    simpa only [List.map_cons, SourceChi.highLabels, Decomposition.above,
      RelativeTerm.outerSort, Nat.not_lt_zero, decide_false, Bool.cond_false] using ih

theorem highBits_sum (q m : Nat) (a b : RelativeTerm Nat) :
    highBits q m (.sum a b) = highBits q m a ++ highBits q m b := by
  change (SourceChi.highLabels m ((state q a).2.2 ++ (state q b).2.2)).map Prod.snd = _
  rw [highLabels_append, List.map_append]
  rfl

theorem highBits_theta (q m k : Nat) (a : RelativeTerm Nat) :
    highBits q m (.theta k a) =
      cond (Decomposition.above m (.theta k a)) [indicator q (.theta k a)] [] := by
  change (SourceChi.highLabels m [(.theta k (state q a).1, indicator q (.theta k a))]).map
    Prod.snd = _
  rw [state_tree]
  cases hc : Decomposition.above m (.theta k a) <;>
    simp only [SourceChi.highLabels, hc, Bool.cond_false, Bool.cond_true,
      List.map_cons, List.map_nil]

theorem indicator_low (q : Nat) (t : RelativeTerm Nat) (hs : t.outerSort ≤ 1) :
    indicator q t = false := by
  revert hs
  induction t with
  | parameter p => intros; rfl
  | sum a b iha ihb =>
    intro hs
    exact ihb ((le_max_right _ _).trans hs)
  | theta k a ih =>
    intro hs
    have hk : k = 0 := by simp only [RelativeTerm.outerSort] at hs; omega
    subst k
    rfl

theorem highBits_low (q m : Nat) (t : RelativeTerm Nat) (hs : t.outerSort ≤ m + 1) :
    highBits q m t = [] := by
  revert hs
  induction t with
  | parameter p => intro hs; exact highBits_parameter q m p
  | sum a b iha ihb =>
    intro hs
    rw [highBits_sum, iha ((le_max_left _ _).trans hs),
      ihb ((le_max_right _ _).trans hs), List.nil_append]
  | theta k a ih =>
    intro hs
    have hh : ¬m + 1 < (.theta k a : RelativeTerm Nat).outerSort := not_lt_of_ge hs
    simp only [highBits_theta, Decomposition.above, decide_eq_false hh, Bool.cond_false]

private theorem lastIndicator_bools (as : List SourceChi.Entry) :
    SourceChi.lastIndicator as = (as.map Prod.snd).reverse.head?.getD false := by
  unfold SourceChi.lastIndicator
  rw [← List.map_reverse]
  cases as.reverse <;> rfl

theorem indicator_theta_bits (q k : Nat) (a : RelativeTerm Nat) :
    indicator q (.theta k a) = cond (k == 0) false
      (cond (baseCase q k a.code) true
        (cond (SourceChi.chooseHigh q k a.code)
          ((highBits q k a).reverse.head?.getD false) (indicator q a))) := by
  change cond (k == 0) false
    (cond (baseCase q k (state q a).1.code) true
      (cond (SourceChi.chooseHigh q k (state q a).1.code)
        (SourceChi.lastIndicator (SourceChi.highLabels k (state q a).2.2)) (indicator q a))) = _
  rw [state_tree, lastIndicator_bools]
  rfl

theorem target_indicator_theta_bits (q k : Nat) (a : RelativeTerm Nat) :
    SourceChi.indicator q (.theta k a) = cond (SourceChi.baseCase q k a.code) true
      (cond (SourceChi.chooseHigh q k a.code)
        ((SourceChi.Arithmetic.highBits q k a).reverse.head?.getD false) (SourceChi.indicator q a)) := by
  change cond (SourceChi.baseCase q k (SourceChi.state q a).1.code) true
    (cond (SourceChi.chooseHigh q k (SourceChi.state q a).1.code)
      (SourceChi.lastIndicator (SourceChi.highLabels k (SourceChi.state q a).2.2))
      (SourceChi.indicator q a)) = _
  rw [SourceChi.state_tree, lastIndicator_bools]
  rfl

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.ShiftedIndicator
