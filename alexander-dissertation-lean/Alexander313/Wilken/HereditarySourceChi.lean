import Alexander313.Wilken.HereditarySourceChiSupport
import Alexander313.Wilken.HereditaryLogEndZero

/-!
# The executing source indicator on public epsilon bases

The real syntax fold carries each actual principal atom together with its
already computed indicator. The theta branch uses the final retained high
atom for chi(Delta), so it does not recursively evaluate an enlarged rebuilt
code. Genuine fixed-point and last-exponent-zero tests select the printed
branch. The reconstructed high part has exactly that computed indicator.

The stated source scope is original checked weak-normal public terms at
positive hereditary levels, whose bases are literal epsilons. The base and
parameter clauses, normal-sum clause and both theta branches are derived.
Raw execution first constructs the actual normalized spelling. This does
not assert arbitrary-spelling invariance, temporary-context translation or
Lemma 3.4. All source proof candidates remain uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceChi

abbrev Entry := RelativeTerm Nat × Bool
abbrev State := RelativeTerm Nat × (Bool × List Entry)

def lastIndicator (as : List Entry) : Bool := (as.reverse.head?.getD (.parameter 0, false)).2

theorem lastIndicator_primrec : Primrec lastIndicator :=
  Primrec.snd.comp (Primrec.option_getD.comp
    (Primrec.list_head?.comp Primrec.list_reverse) (Primrec.const (.parameter 0, false)))

def highLabels (m : Nat) : List Entry → List Entry
  | [] => []
  | e :: es => cond (SourceDecomposition.above m e.1) (e :: highLabels m es) (highLabels m es)

theorem highLabels_primrec : Primrec₂ highLabels := by
  have hc := SourceDecomposition.above_primrec.comp (Primrec.fst.comp Primrec.fst)
    (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
  have hs := (hc.cond (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
    (Primrec.snd.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)).to₂
  have h := Primrec.list_foldr Primrec.snd (Primrec.const ([] : List Entry)) hs
  have he : (fun p : Nat × List Entry => p.2.foldr (fun e es =>
      cond (SourceDecomposition.above p.1 e.1) (e :: es) es) []) =
      (fun p => highLabels p.1 p.2) := by
    funext p
    rcases p with ⟨m, es⟩
    induction es with
    | nil => rfl
    | cons e es ih => simp only [List.foldr_cons, highLabels, ih]
  rw [he] at h
  exact h.to₂

def chooseHigh (r m c : Nat) : Bool := SourceFixedPoint.fixedCode r m c ||
  LogEndZero.publicZeroCheck r (SourceDecomposition.lowCode r m c)

theorem chooseHigh_primrec : Primrec (fun p : Nat × (Nat × Nat) => chooseHigh p.1 p.2.1 p.2.2) :=
  Primrec.or.comp SourceFixedPoint.fixedCode_primrec
    (LogEndZero.publicZeroCheck_primrec.comp Primrec.fst SourceDecomposition.lowCode_primrec)

def parameterState (r p : Nat) : State :=
  (.parameter p, (false, (Theta.atoms r (.parameter p)).map (fun a => (a, false))))

def sumState (a b : State) : State := (.sum a.1 b.1, (b.2.1, a.2.2 ++ b.2.2))

def baseCase (r m c : Nat) : Bool := (m == 0) && SourceFixedPoint.zeroCheck r c

def thetaState (r m : Nat) (a : State) : State :=
  let v := cond (baseCase r m a.1.code) true
    (cond (chooseHigh r m a.1.code) (lastIndicator (highLabels m a.2.2)) a.2.1)
  (.theta m a.1, (v, [(.theta m a.1, v)]))

theorem parameterState_primrec : Primrec₂ parameterState := by
  have ht := parameter_primrec.comp Primrec.snd
  have ha := Theta.Effective.atoms_primrec.comp Primrec.fst ht
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
    (SourceFixedPoint.zeroCheck_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd))

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

def state (r : Nat) (t : RelativeTerm Nat) : State :=
  ValueFold.term parameterState sumState thetaState r t

def stateCode (r c : Nat) : State :=
  ValueFold.code parameterState sumState thetaState (.parameter 0, (false, [])) r c

theorem state_primrec : Primrec₂ state :=
  ValueFold.term_primrec parameterState sumState thetaState (.parameter 0, (false, []))
    parameterState_primrec sumState_primrec thetaState_primrec

theorem stateCode_primrec : Primrec₂ stateCode :=
  ValueFold.code_primrec parameterState sumState thetaState (.parameter 0, (false, []))
    parameterState_primrec sumState_primrec thetaState_primrec

@[simp] theorem stateCode_code (r : Nat) (t : RelativeTerm Nat) : stateCode r t.code = state r t :=
  ValueFold.code_term parameterState sumState thetaState (.parameter 0, (false, [])) r t

theorem state_tree (r : Nat) (t : RelativeTerm Nat) : (state r t).1 = t := by
  induction t with
  | parameter p => rfl
  | sum a b iha ihb =>
    change RelativeTerm.sum (state r a).1 (state r b).1 = _
    rw [iha, ihb]
  | theta m a ih =>
    change RelativeTerm.theta m (state r a).1 = _
    rw [ih]

def indicator (r : Nat) (t : RelativeTerm Nat) : Bool := (state r t).2.1

theorem indicator_primrec : Primrec₂ indicator :=
  (Primrec.fst.comp Primrec.snd).comp₂ state_primrec

@[simp] theorem indicator_parameter (r p : Nat) : indicator r (.parameter p) = false := rfl

@[simp] theorem indicator_sum (r : Nat) (a b : RelativeTerm Nat) :
    indicator r (.sum a b) = indicator r b := rfl

private theorem parameter_atoms_shape (r p : Nat) (a : RelativeTerm Nat)
    (ha : a ∈ Theta.atoms r (.parameter p)) : ∃ q, a = .parameter q := by
  cases r with
  | zero => simp only [Theta.atoms_parameter_zero, List.not_mem_nil] at ha
  | succ r =>
    change a ∈ ((decode p).map (fun u =>
      (Theta.atoms r u).map (fun b => RelativeTerm.parameter b.code))).getD [] at ha
    cases hd : decode p with
    | none => simp only [hd, Option.map_none, Option.getD_none, List.not_mem_nil] at ha
    | some u =>
      simp only [hd, Option.map_some, Option.getD_some] at ha
      obtain ⟨b, hb, he⟩ := List.mem_map.mp ha
      exact ⟨b.code, he.symm⟩

/-- Every stored label is the same genuinely computed indicator of its
literal principal representative. -/
theorem state_labels (r : Nat) (t : RelativeTerm Nat) :
    (state r t).2.2 = (Theta.atoms r t).map (fun a => (a, indicator r a)) := by
  induction t with
  | parameter p =>
    change (Theta.atoms r (.parameter p)).map (fun a => (a, false)) = _
    apply List.map_congr_left
    intro a ha
    obtain ⟨q, rfl⟩ := parameter_atoms_shape r p a ha
    rfl
  | sum a b iha ihb =>
    change (state r a).2.2 ++ (state r b).2.2 = _
    rw [iha, ihb, Theta.atoms_sum, List.map_append]
  | theta m a ih =>
    change [(.theta m (state r a).1, indicator r (.theta m a))] = _
    rw [state_tree, Theta.atoms_theta]
    rfl

theorem highLabels_map (m : Nat) (as : List (RelativeTerm Nat)) (f : RelativeTerm Nat → Bool) :
    highLabels m (as.map (fun a => (a, f a))) =
      (SourceDecomposition.select true m as).map (fun a => (a, f a)) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    cases h : SourceDecomposition.above m a <;>
      simp only [List.map_cons, highLabels, SourceDecomposition.select, Bool.cond_true,
        h, Bool.cond_false, ih]

theorem state_highLabels (r m : Nat) (a : RelativeTerm Nat) :
    highLabels m (state r a).2.2 =
      (SourceDecomposition.highWord r m a.code).map (fun b => (b, indicator r b)) := by
  rw [state_labels, highLabels_map]
  simp only [SourceDecomposition.highWord, SourceDecomposition.word, ThetaCourse.rawTree_code]

@[simp] theorem indicator_zeroTree (r : Nat) : indicator r (zeroTree r) = false := by
  cases r <;> rfl

theorem indicator_buildAtoms (r : Nat) (as : List (RelativeTerm Nat)) :
    indicator r (Theta.Normalization.buildAtoms r as) =
      lastIndicator (as.map (fun a => (a, indicator r a))) := by
  unfold lastIndicator
  rw [← List.map_reverse]
  cases hr : as.reverse with
  | nil => simp [Theta.Normalization.buildAtoms, hr, Theta.Normalization.buildRev, indicator_zeroTree]
  | cons a bs => simp [Theta.Normalization.buildAtoms, hr, Theta.Normalization.buildRev, indicator_sum]

/-- Both printed recursive targets are already computed by strict descent
through the original finite syntax, including the reconstructed Delta target. -/
theorem indicator_theta (r m : Nat) (a : RelativeTerm Nat) :
    indicator r (.theta m a) = cond (baseCase r m a.code) true
      (cond (chooseHigh r m a.code)
        (indicator r (SourceDecomposition.highPartTerm r m a.code)) (indicator r a)) := by
  change cond (baseCase r m (state r a).1.code) true
    (cond (chooseHigh r m (state r a).1.code)
      (lastIndicator (highLabels m (state r a).2.2)) (indicator r a)) = _
  rw [state_tree, state_highLabels, SourceDecomposition.highPartTerm, indicator_buildAtoms]

theorem indicator_below_base (r : Nat) (t : RelativeTerm Nat)
    (ht : check r t = true) (hn : Theta.Normal r t) (hv : denote r t < finiteBase r) :
    indicator r t = false := by
  revert ht hn hv
  induction t with
  | parameter p => intros; rfl
  | sum a b iha ihb =>
    intro ht hn hv
    have hs := sum_children r a b ht hn
    rw [indicator_sum]
    apply ihb hs.2.2.1 hs.2.2.2.1
    exact (show denote r b ≤ denote r (.sum a b) by
      change denote r b ≤ denote r a + denote r b
      exact le_add_self).trans_lt hv
  | theta m a ih =>
    intro ht hn hv
    have hs := (SourceFixedPoint.checked_theta_range r m a ht).1
    exact False.elim (hv.not_ge
      (((omegaSequence_strictMono (finiteBase r)).monotone (Nat.zero_le m)).trans hs))

theorem indicator_base (r : Nat) (t : RelativeTerm Nat)
    (ht : check r t = true) (hn : Theta.Normal r t) (hv : denote r t = finiteBase r) :
    indicator r t = true := by
  revert ht hn hv
  induction t with
  | parameter p =>
    intro ht hn hv
    exact False.elim ((ne_of_lt (SourceFixedPoint.checked_parameter_lt_base r p ht)) hv)
  | sum a b iha ihb =>
    intro ht hn hv
    have hs := sum_children r a b ht hn
    have hz : denote r a = 0 := by
      by_contra h
      exact RelativeTerm.PrincipalSupport.sourceNormalSum_not_principal hs.2.2.2.2
        (pos_iff_ne_zero.mpr h) (hv.symm ▸ finiteBase_add_closed r)
    have hb : denote r b = finiteBase r := by
      change denote r a + denote r b = finiteBase r at hv
      simpa only [hz, zero_add] using hv
    rw [indicator_sum]
    exact ihb hs.2.2.1 hs.2.2.2.1 hb
  | theta m a ih =>
    intro ht hn hv
    obtain ⟨rfl, hz⟩ := theta_base_argument_zero r m a ht hv
    have ha := (theta_argument_parts r 0 a ht hn).1
    have hc : SourceFixedPoint.zeroCheck r a.code = true :=
      (SourceFixedPoint.zeroCheck_exact r a.code ha).mpr (by simpa only [interpretation_code] using hz)
    simp only [indicator_theta, baseCase, beq_self_eq_true, hc, Bool.true_and, Bool.cond_true]

theorem chooseHigh_correct (r m : Nat) (a : RelativeTerm Nat)
    (ht : check r (.theta m a) = true) (hn : Theta.Normal r (.theta m a)) :
    chooseHigh r m a.code = true ↔ SourceFixedPoint.SourceFixed r m a.code ∨
      LogEndZero.SourceZero (interpretation r (SourceDecomposition.lowCode r m a.code)) := by
  have hi := theta_argument_input r m a ht hn
  have hp := theta_argument_parts r m a ht hn
  rw [chooseHigh, Bool.or_eq_true, SourceFixedPoint.fixedCode_correct r m a.code hi]
  simpa only [LogEndZero.SourceZero] using
    or_congr Iff.rfl (LogEndZero.publicZeroCheck_correct r _ hp.2.2)

/-- The branch is exactly fixed residual supremum OR literal zero last
exponent, whenever that genuine last exponent is presented by SourceLogSpec. -/
theorem chooseHigh_logend (r m : Nat) (a : RelativeTerm Nat)
    (ht : check r (.theta m a) = true) (hn : Theta.Normal r (.theta m a))
    (ell : Ordinal.{0})
    (he : LogEnd.SourceLogSpec true (interpretation r (SourceDecomposition.lowCode r m a.code)) ell) :
    chooseHigh r m a.code = true ↔ SourceFixedPoint.SourceFixed r m a.code ∨ ell = 0 := by
  rw [chooseHigh_correct r m a ht hn]
  exact or_congr Iff.rfl (LogEndZero.sourceLogSpec_zero_iff _ _ he).symm

/-- The branch condition is the literal source supremum at the actual
divisible prefix and residual, together with literal logend-zero. -/
theorem chooseHigh_literal (r m : Nat) (a : RelativeTerm Nat)
    (ht : check r (.theta m a) = true) (hn : Theta.Normal r (.theta m a))
    (ell : Ordinal.{0})
    (he : LogEnd.SourceLogSpec true (interpretation r (SourceDecomposition.lowCode r m a.code)) ell) :
    chooseHigh r m a.code = true ↔
      SourceFixedPointLimits.globalResidualImageSup (finiteBase r) m
        (interpretation r (SourceDecomposition.highCode r m a.code))
        (interpretation r (SourceDecomposition.lowCode r m a.code)) =
          interpretation r (SourceDecomposition.lowCode r m a.code) ∨ ell = 0 := by
  have hp := SourceDecomposition.parts_code_value r m a.code (theta_argument_parts r m a ht hn).1
  simpa only [SourceFixedPoint.SourceFixed, SourceFixedPoint.delta, SourceFixedPoint.residual,
    hp.1, hp.2] using chooseHigh_logend r m a ht hn ell he

theorem baseCase_false (r m : Nat) (a : RelativeTerm Nat)
    (ht : check r (.theta m a) = true) (hn : Theta.Normal r (.theta m a))
    (harg : m = 0 → 0 < denote r a) : baseCase r m a.code = false := by
  cases h : baseCase r m a.code with
  | false => rfl
  | true =>
    obtain ⟨hm, hz⟩ := Bool.and_eq_true.mp h
    have hm0 : m = 0 := by simpa only [beq_iff_eq] using hm
    have ha := (theta_argument_parts r m a ht hn).1
    have hv : denote r a = 0 := by
      simpa only [interpretation_code] using (SourceFixedPoint.zeroCheck_exact r a.code ha).mp hz
    exact False.elim ((ne_of_gt (harg hm0)) hv)

theorem indicator_theta_high (r m : Nat) (a : RelativeTerm Nat)
    (ht : check r (.theta m a) = true) (hn : Theta.Normal r (.theta m a))
    (harg : m = 0 → 0 < denote r a) (hc : chooseHigh r m a.code = true) :
    indicator r (.theta m a) = indicator r (SourceDecomposition.highPartTerm r m a.code) := by
  rw [indicator_theta, baseCase_false r m a ht hn harg, hc]
  rfl

theorem indicator_theta_argument (r m : Nat) (a : RelativeTerm Nat)
    (ht : check r (.theta m a) = true) (hn : Theta.Normal r (.theta m a))
    (harg : m = 0 → 0 < denote r a) (hc : chooseHigh r m a.code = false) :
    indicator r (.theta m a) = indicator r a := by
  rw [indicator_theta, baseCase_false r m a ht hn harg, hc]
  rfl

def inputCheck (r c : Nat) : Bool := decide (0 < r) && SourceDecomposition.inputCheck r c

theorem inputCheck_primrec : Primrec₂ inputCheck :=
  (Primrec.and.comp ((Primrec.nat_lt.comp (Primrec.const 0) Primrec.fst).decide)
    SourceDecomposition.inputCheck_primrec).to₂

theorem inputCheck_exact (r c : Nat) : inputCheck r c = true ↔
    0 < r ∧ checkCode r c = true ∧ Theta.Normal r (ThetaCourse.rawTree c) := by
  simp only [inputCheck, Bool.and_eq_true, decide_eq_true_eq, SourceDecomposition.inputCheck_exact]

def chiCode (r c : Nat) : Bool := inputCheck r c && (stateCode r c).2.1

theorem chiCode_primrec : Primrec₂ chiCode :=
  (Primrec.and.comp inputCheck_primrec ((Primrec.fst.comp Primrec.snd).comp stateCode_primrec)).to₂

theorem chiCode_correct (r : Nat) (t : RelativeTerm Nat) (hr : 0 < r)
    (ht : check r t = true) (hn : Theta.Normal r t) : chiCode r t.code = indicator r t := by
  have hi := (inputCheck_exact r t.code).mpr ⟨hr, by simpa only [checkCode_code] using ht,
    by simpa only [ThetaCourse.rawTree_code] using hn⟩
  simp only [chiCode, hi, stateCode_code, indicator, Bool.true_and]

theorem chiCode_below_base (r : Nat) (t : RelativeTerm Nat) (hr : 0 < r)
    (ht : check r t = true) (hn : Theta.Normal r t) (hv : denote r t < finiteBase r) :
    chiCode r t.code = false :=
  (chiCode_correct r t hr ht hn).trans (indicator_below_base r t ht hn hv)

theorem chiCode_base (r : Nat) (t : RelativeTerm Nat) (hr : 0 < r)
    (ht : check r t = true) (hn : Theta.Normal r t) (hv : denote r t = finiteBase r) :
    chiCode r t.code = true :=
  (chiCode_correct r t hr ht hn).trans (indicator_base r t ht hn hv)

def dualCode (r c : Nat) : Bool := inputCheck r c && !(stateCode r c).2.1

theorem dualCode_primrec : Primrec₂ dualCode :=
  (Primrec.and.comp inputCheck_primrec (Primrec.not.comp
    ((Primrec.fst.comp Primrec.snd).comp stateCode_primrec))).to₂

theorem dualCode_correct (r : Nat) (t : RelativeTerm Nat) (hr : 0 < r)
    (ht : check r t = true) (hn : Theta.Normal r t) : dualCode r t.code = !(indicator r t) := by
  have hi := (inputCheck_exact r t.code).mpr ⟨hr, by simpa only [checkCode_code] using ht,
    by simpa only [ThetaCourse.rawTree_code] using hn⟩
  simp only [dualCode, hi, stateCode_code, indicator, Bool.true_and]

def rawInputCheck (r c : Nat) : Bool := decide (0 < r) && checkCode r c

theorem rawInputCheck_primrec : Primrec₂ rawInputCheck :=
  (Primrec.and.comp ((Primrec.nat_lt.comp (Primrec.const 0) Primrec.fst).decide)
    Uniform.hereditaryCheckCode_primrec).to₂

theorem rawInputCheck_exact (r c : Nat) : rawInputCheck r c = true ↔ 0 < r ∧ checkCode r c = true := by
  simp only [rawInputCheck, Bool.and_eq_true, decide_eq_true_eq]

theorem normalized_input (r c : Nat) (hc : rawInputCheck r c = true) :
    inputCheck r (Theta.Normalization.normalizeCode r c) = true := by
  obtain ⟨hr, ht⟩ := (rawInputCheck_exact r c).mp hc
  have hn := Theta.Normalization.normalizeCode_checked r c ht
  exact (inputCheck_exact r _).mpr ⟨hr, hn.1, hn.2.1⟩

def rawChiCode (r c : Nat) : Bool := rawInputCheck r c &&
  chiCode r (Theta.Normalization.normalizeCode r c)

theorem rawChiCode_primrec : Primrec₂ rawChiCode :=
  (Primrec.and.comp rawInputCheck_primrec (chiCode_primrec.comp Primrec.fst
    Theta.Normalization.Effective.normalizeCode_primrec)).to₂

theorem rawChiCode_correct (r c : Nat) (hc : rawInputCheck r c = true) :
    rawChiCode r c = indicator r (Theta.Normalization.normalize r (ThetaCourse.rawTree c)) := by
  have hn := normalized_input r c hc
  obtain ⟨t, ht, hcheck⟩ := (checkCode_iff r c).mp ((rawInputCheck_exact r c).mp hc).2
  subst c
  simp only [rawChiCode, hc, chiCode, hn, Bool.true_and, Theta.Normalization.normalizeCode_code,
    stateCode_code, indicator, ThetaCourse.rawTree_code]

def rawDualCode (r c : Nat) : Bool := rawInputCheck r c &&
  dualCode r (Theta.Normalization.normalizeCode r c)

theorem rawDualCode_primrec : Primrec₂ rawDualCode :=
  (Primrec.and.comp rawInputCheck_primrec (dualCode_primrec.comp Primrec.fst
    Theta.Normalization.Effective.normalizeCode_primrec)).to₂

theorem rawDualCode_correct (r c : Nat) (hc : rawInputCheck r c = true) :
    rawDualCode r c = !(indicator r (Theta.Normalization.normalize r (ThetaCourse.rawTree c))) := by
  have hn := normalized_input r c hc
  obtain ⟨t, ht, hcheck⟩ := (checkCode_iff r c).mp ((rawInputCheck_exact r c).mp hc).2
  subst c
  simp only [rawDualCode, hc, dualCode, hn, Bool.true_and, Theta.Normalization.normalizeCode_code,
    stateCode_code, indicator, ThetaCourse.rawTree_code]

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceChi
