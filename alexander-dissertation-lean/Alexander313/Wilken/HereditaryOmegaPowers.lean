import Alexander313.Wilken.LowOmegaArithmetic
import Alexander313.Wilken.HereditaryEpsilonOffsets
import Alexander313.Wilken.HereditaryLowering

/-!
# Executing ordinary omega powers on the original hereditary union

An actual bounded iteration opens earlier payloads while the exponent is
below its current finite base. Genuine epsilon inputs remain fixed. At the
remaining source level, the real epsilon-plus-finite decomposition supplies
the finite-tail predecessor, and actual subtraction supplies the ordinary
base-removal branch. A literal theta term then has value omega^exponent by
the proved exact low source arithmetic. Canonicalization gives unique normal
outputs. The public guard rejects malformed inputs. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.OmegaPowers

open ThetaCourse
open Alexander313.HereditaryOrdinalLabels (zeroCode zeroCode_checked zeroCode_value)

private theorem omegaNat_beq_false {a b : Nat} (h : a ≠ b) : (a == b) = false := by
  cases he : a == b with
  | false => rfl
  | true => exact False.elim (h (beq_iff_eq.mp he))

def finiteCode : Nat → Nat
  | 0 => BaseArithmetic.zeroCode 0
  | n + 1 => Addition.sumCode (finiteCode n) (BaseArithmetic.freshCode 0)

theorem finiteCode_primrec : Primrec finiteCode := by
  have h : Primrec₂ (fun (_ : Unit) n => Nat.rec (motive := fun _ => Nat)
      (BaseArithmetic.zeroCode 0) (fun _ c => Addition.sumCode c (BaseArithmetic.freshCode 0)) n) :=
    Primrec.nat_rec (Primrec.const (BaseArithmetic.zeroCode 0))
      ((Addition.sumCode_primrec.comp (Primrec.snd.comp Primrec.snd)
        (Primrec.const (BaseArithmetic.freshCode 0))).to₂)
  exact (h.comp (Primrec.const ()) Primrec.id).of_eq (by
    intro n
    induction n <;> simp_all [finiteCode])

theorem finiteCode_checked (n : Nat) : lowCheckCode 0 (finiteCode n) = true := by
  induction n with
  | zero => simpa only [finiteCode, BaseArithmetic.zeroCode_eq, lowCheckCode_code] using zeroTree_lowCheck 0
  | succ n ih => exact (Addition.sumCode_lowChecked 0 _ _ ih
      (BaseArithmetic.checkCode_old 0 _ (BaseArithmetic.fresh_checked 0))).1

theorem finiteCode_value (n : Nat) : interpretation 0 (finiteCode n) = (n : Ordinal.{0}) := by
  induction n with
  | zero => simp only [finiteCode, BaseArithmetic.zeroCode_eq, interpretation_code, zeroTree_denote, Nat.cast_zero]
  | succ n ih =>
    rw [finiteCode, (Addition.sumCode_lowChecked 0 _ _ (finiteCode_checked n)
      (BaseArithmetic.checkCode_old 0 _ (BaseArithmetic.fresh_checked 0))).2, ih,
      BaseArithmetic.fresh_value, finiteBase_zero]
    simp only [Nat.cast_succ]

def numeralAt (r n : Nat) : Nat := BaseArithmetic.embedCode r (finiteCode n)

theorem numeralAt_primrec : Primrec₂ numeralAt :=
  (BaseArithmetic.embedCode_primrec.comp Primrec.fst (finiteCode_primrec.comp Primrec.snd)).to₂

theorem numeralAt_checked (r n : Nat) : lowCheckCode r (numeralAt r n) = true := by
  simpa only [numeralAt, Nat.zero_add] using Theta.embed_old_checked 0 r _ (finiteCode_checked n)

theorem numeralAt_value (r n : Nat) : interpretation r (numeralAt r n) = (n : Ordinal.{0}) := by
  simpa only [numeralAt, Nat.zero_add, finiteCode_value] using Theta.embed_original_value 0 r (finiteCode n)

def thetaCode (c : Nat) : Nat := (.theta 0 (rawTree c) : RelativeTerm Nat).code

theorem thetaCode_primrec : Primrec thetaCode :=
  code_primrec.comp (theta_primrec.comp (Primrec.const 0) rawTree_primrec)

theorem thetaCode_checked (r c : Nat) (hc : lowCheckCode r c = true) :
    lowCheckCode r (thetaCode c) = true := by
  obtain ⟨t, rfl, ht⟩ := (lowCheckCode_iff r c).mp hc
  have hs : check r t = true ∧ t.outerSort ≤ 1 := by
    simpa only [lowCheck, Bool.and_eq_true, decide_eq_true_eq] using ht
  have hsort : t.outerSort ≤ 0 + 2 := hs.2.trans (by omega)
  simp only [thetaCode, rawTree_code, lowCheckCode_code, lowCheck,
    Uniform.check_theta, hs.1, hsort, decide_true, outerSort, Nat.zero_add,
    le_refl, Bool.true_and]

theorem thetaCode_value (r c : Nat) (hc : lowCheckCode r c = true) :
    interpretation r (thetaCode c) = globalCollapse (finiteBase r) 0 (interpretation r c) := by
  obtain ⟨t, rfl, _⟩ := (lowCheckCode_iff r c).mp hc
  simp only [thetaCode, rawTree_code, interpretation_code]
  rfl

private theorem raw_offset_spec (q : Nat) (hq : EpsilonOffsets.check q = true) :
    unionCheck (EpsilonOffsets.rawHead q) = true ∧
      Ordinal.omega0 ^ unionInterpretation (EpsilonOffsets.rawHead q) =
        unionInterpretation (EpsilonOffsets.rawHead q) ∧
      unionInterpretation q = unionInterpretation (EpsilonOffsets.rawHead q) +
        (EpsilonOffsets.offset q : Ordinal.{0}) := by
  have hs := EpsilonOffsets.decomposition_spec q hq
  have hnonempty : 0 < (EpsilonOffsets.word q).length :=
    of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hq).1).2
  have hh := EpsilonOffsets.rawHead_checked q hs.1 hnonempty
  have hv : unionInterpretation (EpsilonOffsets.head q) =
      unionInterpretation (EpsilonOffsets.rawHead q) := Canonical.canonicalize_value _ hh
  exact ⟨hh, by simpa only [hv] using hs.2.2.1, by simpa only [hv] using hs.2.2.2⟩

private theorem offset_positive (q : Nat) (hq : EpsilonOffsets.check q = true)
    (hne : Epsilon.unionEpsilonCheck q = false) : 0 < EpsilonOffsets.offset q := by
  apply Nat.pos_of_ne_zero
  intro hz
  have hs := raw_offset_spec q hq
  have he : Ordinal.omega0 ^ unionInterpretation q = unionInterpretation q := by
    rw [hs.2.2, hz, Nat.cast_zero, add_zero]
    exact hs.2.1
  have ht := (Epsilon.unionEpsilonCheck_exact q).mpr ⟨(EpsilonOffsets.decomposition_spec q hq).1, he⟩
  rw [hne] at ht
  cases ht

private theorem offset_head_base_le_core (r : Nat) (ξ ε : Ordinal.{0}) (n : Nat)
    (hε : Ordinal.omega0 ^ ε = ε) (hv : ξ = ε + (n : Ordinal.{0}))
    (hb : finiteBase r ≤ ξ) : finiteBase r ≤ ε := by
  by_contra! hsmall
  cases r with
  | zero =>
    exact (EpsilonOffsets.epsilon_one_lt hε).not_ge
      (by simpa only [finiteBase_zero] using hsmall.le)
  | succ r =>
    have hn : (n : Ordinal.{0}) < finiteBase (r + 1) :=
      (Ordinal.natCast_lt_omega0 n).trans (epsilon_omega_lt (finiteBase_succ_omegaPower_eq_self r))
    have hvalue : ξ < finiteBase (r + 1) := by
      have h := (finiteBase_add_closed (r + 1)) hsmall hn
      simpa only [← hv] using h
    exact (not_lt_of_ge hb) hvalue

private theorem offset_head_base_le (r c : Nat) (hq : EpsilonOffsets.check (Nat.pair r c) = true)
    (hb : finiteBase r ≤ interpretation r c) :
    finiteBase r ≤ unionInterpretation (EpsilonOffsets.rawHead (Nat.pair r c)) := by
  have hs := raw_offset_spec _ hq
  exact offset_head_base_le_core r (interpretation r c)
    (unionInterpretation (EpsilonOffsets.rawHead (Nat.pair r c)))
    (EpsilonOffsets.offset (Nat.pair r c)) hs.2.1
    (by simpa only [unionInterpretation_pair] using hs.2.2) hb

private theorem offset_head_above (r q : Nat) (hq : EpsilonOffsets.check q = true) :
    EpsilonOffsets.aboveBaseCheck r q = true ↔
      finiteBase r < unionInterpretation (EpsilonOffsets.rawHead q) := by
  have hs := raw_offset_spec q hq
  have hv : unionInterpretation (EpsilonOffsets.head q) = unionInterpretation (EpsilonOffsets.rawHead q) :=
    Canonical.canonicalize_value _ hs.1
  constructor
  · intro h
    obtain ⟨_, ε, n, hε, hb, he⟩ := (EpsilonOffsets.aboveBaseCheck_exact r q).mp h
    have hu := EpsilonOffsets.decomposition_unique q hq ε n hε he
    simpa only [← hv, hu.1] using hb
  · intro h
    exact (EpsilonOffsets.aboveBaseCheck_exact r q).mpr
      ⟨(EpsilonOffsets.decomposition_spec q hq).1, _, _, hs.2.1, h, hs.2.2⟩

/-- All finite-tail arithmetic is on the extracted Nat, rather than the
left-removing ordinal subtraction. The nonoffset branch removes the base. -/
def argumentCode (r c : Nat) : Nat :=
  let q := Nat.pair r c
  cond (EpsilonOffsets.check q)
    (cond (EpsilonOffsets.aboveBaseCheck r q)
      (Addition.normalizedSumCode r (EpsilonOffsets.headTree q).code
        (numeralAt r (EpsilonOffsets.offset q - 1)))
      (numeralAt r (EpsilonOffsets.offset q)))
    (cond (r == 0) c (Difference.fullSubtraction r (BaseArithmetic.freshCode r) c))

theorem argumentCode_primrec : Primrec₂ argumentCode := by
  have hq := Primrec₂.natPair
  have hn := EpsilonOffsets.offset_primrec.comp hq
  have hhead := code_primrec.comp (EpsilonOffsets.headTree_primrec.comp hq)
  have hpred := Primrec.nat_sub.comp hn (Primrec.const 1)
  have habove := EpsilonOffsets.aboveBaseCheck_primrec.comp Primrec.fst hq
  have hsum := Addition.normalizedSumCode_primrec.comp
    (Primrec.fst.pair (hhead.pair (numeralAt_primrec.comp Primrec.fst hpred)))
  have hsub := Difference.fullSubtraction_primrec.comp
    (Primrec.fst.pair ((BaseArithmetic.freshCode_primrec.comp Primrec.fst).pair Primrec.snd))
  exact ((EpsilonOffsets.check_primrec.comp hq).cond
    (habove.cond hsum (numeralAt_primrec.comp Primrec.fst hn))
    ((Primrec.beq.comp Primrec.fst (Primrec.const 0)).cond Primrec.snd hsub)).to₂

theorem argumentCode_checked (r c : Nat) (hc : lowCheckCode r c = true) :
    lowCheckCode r (argumentCode r c) = true := by
  have hq : unionCheck (Nat.pair r c) = true := by simpa only [unionCheck_pair] using hc
  cases hoff : EpsilonOffsets.check (Nat.pair r c) with
  | true =>
    have hh := (raw_offset_spec _ hoff).1
    have hhead : lowCheckCode r (EpsilonOffsets.headTree (Nat.pair r c)).code = true := by
      simpa only [EpsilonOffsets.rawHead, unionCheck, Nat.unpair_pair] using hh
    cases habove : EpsilonOffsets.aboveBaseCheck r (Nat.pair r c) with
    | true =>
      have hs := Addition.normalizedSumCode_lowChecked r _ _ hhead
        (numeralAt_checked r (EpsilonOffsets.offset (Nat.pair r c) - 1))
      simpa only [argumentCode, hoff, habove, Bool.cond_true] using ((Theta.acceptedLowCode_iff _ _).mp hs.1).1
    | false => simpa only [argumentCode, hoff, habove, Bool.cond_true, Bool.cond_false] using numeralAt_checked r _
  | false =>
    by_cases hr : r = 0
    · subst r
      simpa only [argumentCode, hoff, Bool.cond_false, beq_self_eq_true, Bool.cond_true] using hc
    · have hs := Difference.fullSubtraction_lowChecked r _ _
        (BaseArithmetic.checkCode_old r _ (BaseArithmetic.fresh_checked r)) hc
      simpa only [argumentCode, hoff, Bool.cond_false, omegaNat_beq_false hr] using
        ((Theta.acceptedLowCode_iff _ _).mp hs.1).1

theorem argumentCode_exponent (r c : Nat) (hc : lowCheckCode r c = true)
    (hb : finiteBase r ≤ interpretation r c)
    (hne : Epsilon.unionEpsilonCheck (Nat.pair r c) = false) :
    lowOmegaExponent (finiteBase r) (interpretation r (argumentCode r c)) = interpretation r c := by
  let q := Nat.pair r c
  have hq : unionCheck q = true := by simpa only [q, unionCheck_pair] using hc
  cases hoff : EpsilonOffsets.check q with
  | true =>
    have hs := raw_offset_spec q hoff
    have hpositive := offset_positive q hoff hne
    have hh : lowCheckCode r (EpsilonOffsets.headTree q).code = true := by
      simpa only [q, EpsilonOffsets.rawHead, unionCheck, Nat.unpair_pair] using hs.1
    cases habove : EpsilonOffsets.aboveBaseCheck r q with
    | true =>
      have hbound := (offset_head_above r q hoff).mp habove
      have hsum := (Addition.normalizedSumCode_lowChecked r _ _ hh
        (numeralAt_checked r (EpsilonOffsets.offset q - 1))).2
      have hv : interpretation r (argumentCode r c) =
          unionInterpretation (EpsilonOffsets.rawHead q) +
            ((EpsilonOffsets.offset q - 1 : Nat) : Ordinal.{0}) := by
        simpa only [argumentCode, q, hoff, habove, Bool.cond_true, numeralAt_value,
          EpsilonOffsets.rawHead_value, Nat.unpair_pair, interpretation_code] using hsum
      rw [hv, lowOmegaExponent_offset_predecessor _ _ _ hbound hs.2.1 hpositive]
      simpa only [q, unionInterpretation_pair] using hs.2.2.symm
    | false =>
      have hheadLe : unionInterpretation (EpsilonOffsets.rawHead q) ≤ finiteBase r := by
        by_contra! hgt
        have ht := (offset_head_above r q hoff).mpr hgt
        rw [habove] at ht
        cases ht
      have hheadEq : unionInterpretation (EpsilonOffsets.rawHead q) = finiteBase r :=
        le_antisymm hheadLe (by simpa only [q] using offset_head_base_le r c hoff hb)
      have hepsilon : Ordinal.omega0 ^ finiteBase r = finiteBase r := by
        simpa only [hheadEq] using hs.2.1
      have hv : interpretation r (argumentCode r c) = (EpsilonOffsets.offset q : Ordinal.{0}) := by
        simp only [argumentCode, q, hoff, habove, Bool.cond_true, Bool.cond_false, numeralAt_value]
      rw [hv, lowOmegaExponent_nat, lowOmegaBase_of_epsilon _ hepsilon]
      simpa only [q, unionInterpretation_pair, hheadEq] using hs.2.2.symm
  | false =>
    have hnot : ¬ EpsilonFiniteAbove (finiteBase r) (interpretation r c) := by
      rintro ⟨ε, n, _, hε, he⟩
      have ht := (EpsilonOffsets.check_exact q).mpr ⟨hq, ε, n, hε, by simpa only [q, unionInterpretation_pair] using he⟩
      rw [hoff] at ht
      cases ht
    by_cases hr : r = 0
    · subst r
      simp only [argumentCode, q, hoff, Bool.cond_false, beq_self_eq_true, Bool.cond_true]
      rw [lowOmegaExponent_of_not_offset _ _ hnot, finiteBase_zero, lowOmegaBase_one, zero_add]
    · have hepsilon : Ordinal.omega0 ^ finiteBase r = finiteBase r := by
        cases r with
        | zero => exact False.elim (hr rfl)
        | succ r => exact finiteBase_succ_omegaPower_eq_self r
      have hsub := (Difference.fullSubtraction_lowChecked r _ _
        (BaseArithmetic.checkCode_old r _ (BaseArithmetic.fresh_checked r)) hc).2
      have hv : interpretation r (argumentCode r c) = interpretation r c - lowOmegaBase (finiteBase r) := by
        simpa only [argumentCode, q, hoff, Bool.cond_false, omegaNat_beq_false hr,
          BaseArithmetic.fresh_value, lowOmegaBase_of_epsilon _ hepsilon] using hsub
      rw [hv]
      exact lowOmegaExponent_sub_base _ _ (by simpa only [lowOmegaBase_of_epsilon _ hepsilon] using hb) hnot

def lowerStep (q : Nat) : Nat :=
  cond (q.unpair.1 == 0) q
    (cond (Lowering.checkInput (q.unpair.1 - 1) q.unpair.2)
      (Nat.pair (q.unpair.1 - 1) (Lowering.lowerCode (q.unpair.1 - 1) q.unpair.2)) q)

theorem lowerStep_primrec : Primrec lowerStep := by
  have hr := Primrec.fst.comp Primrec.unpair
  have hc := Primrec.snd.comp Primrec.unpair
  have hp := Primrec.nat_sub.comp hr (Primrec.const 1)
  exact (Primrec.beq.comp hr (Primrec.const 0)).cond Primrec.id
    ((Lowering.checkInput_primrec.comp hp hc).cond
      (Primrec₂.natPair.comp hp (Lowering.lowerCode_primrec.comp hp hc)) Primrec.id)

theorem lowerStep_spec (q : Nat) (hq : unionCheck q = true) :
    unionCheck (lowerStep q) = true ∧ unionInterpretation (lowerStep q) = unionInterpretation q := by
  obtain ⟨r, c, rfl⟩ : ∃ r c, q = Nat.pair r c :=
    ⟨q.unpair.1, q.unpair.2, (Nat.pair_unpair q).symm⟩
  cases r with
  | zero => simpa only [lowerStep, Nat.unpair_pair, beq_self_eq_true, Bool.cond_true] using
      And.intro hq (Eq.refl (unionInterpretation (Nat.pair 0 c)))
  | succ r =>
    cases hg : Lowering.checkInput r c with
    | true =>
      have hs := Lowering.lowerCode_spec r c hg
      simpa only [lowerStep, Nat.unpair_pair, Nat.add_sub_cancel,
        omegaNat_beq_false (Nat.succ_ne_zero r), Bool.cond_false, hg,
        Bool.cond_true, unionCheck_pair, unionInterpretation_pair] using hs
    | false =>
      simpa only [lowerStep, Nat.unpair_pair, Nat.add_sub_cancel,
        omegaNat_beq_false (Nat.succ_ne_zero r), hg, Bool.cond_false] using
          And.intro hq (Eq.refl (unionInterpretation (Nat.pair (r + 1) c)))

def lowerLoop (q : Nat) : Nat → Nat
  | 0 => q
  | k + 1 => lowerStep (lowerLoop q k)

theorem lowerLoop_primrec : Primrec₂ lowerLoop := by
  have h := Primrec.nat_rec Primrec.id ((lowerStep_primrec.comp (Primrec.snd.comp Primrec.snd)).to₂)
  exact h.of_eq (by intro q n; induction n <;> simp_all [lowerLoop])

theorem lowerLoop_spec (q k : Nat) (hq : unionCheck q = true) :
    unionCheck (lowerLoop q k) = true ∧ unionInterpretation (lowerLoop q k) = unionInterpretation q := by
  induction k with
  | zero => exact ⟨hq, rfl⟩
  | succ k ih =>
    have hs := lowerStep_spec _ ih.1
    exact ⟨hs.1, hs.2.trans ih.2⟩

theorem lowerLoop_fixed (q k : Nat) (hq : lowerStep q = q) : lowerLoop q k = q := by
  induction k <;> simp_all only [lowerLoop, hq]

theorem lowerLoop_shift (q k : Nat) : lowerLoop q (k + 1) = lowerLoop (lowerStep q) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change lowerStep (lowerLoop q (k + 1)) = lowerStep (lowerLoop (lowerStep q) k)
    exact congrArg lowerStep ih

theorem lowerLoop_ready (r c : Nat) (hc : lowCheckCode r c = true) :
    (lowerLoop (Nat.pair r c) r).unpair.1 = 0 ∨
      finiteBase (lowerLoop (Nat.pair r c) r).unpair.1 ≤
        unionInterpretation (lowerLoop (Nat.pair r c) r) := by
  induction r generalizing c with
  | zero => exact Or.inl (by simp only [lowerLoop, Nat.unpair_pair])
  | succ r ih =>
    by_cases hb : interpretation (r + 1) c < finiteBase (r + 1)
    · have hcheck : checkCode (r + 1) c = true :=
        (Bool.and_eq_true_iff.mp (by simpa only [lowCheckCode_eq] using hc)).1
      have hg := (Lowering.checkInput_exact r c).mpr ⟨hcheck, hb⟩
      have he : lowerStep (Nat.pair (r + 1) c) = Nat.pair r (Lowering.lowerCode r c) := by
        simp only [lowerStep, Nat.unpair_pair, Nat.add_sub_cancel,
          omegaNat_beq_false (Nat.succ_ne_zero r), Bool.cond_false, hg, Bool.cond_true]
      rw [lowerLoop_shift, he]
      exact ih _ (Lowering.lowerCode_spec r c hg).1
    · have hg : Lowering.checkInput r c = false := by
        cases h : Lowering.checkInput r c with
        | false => rfl
        | true => exact False.elim (hb ((Lowering.checkInput_exact r c).mp h).2)
      have he : lowerStep (Nat.pair (r + 1) c) = Nat.pair (r + 1) c := by
        simp only [lowerStep, Nat.unpair_pair, Nat.add_sub_cancel,
          omegaNat_beq_false (Nat.succ_ne_zero r), Bool.cond_false, hg]
      rw [lowerLoop_fixed _ _ he]
      exact Or.inr (by simpa only [Nat.unpair_pair, unionInterpretation_pair] using le_of_not_gt hb)

def prepare (q : Nat) : Nat := lowerLoop q q.unpair.1

theorem prepare_primrec : Primrec prepare := lowerLoop_primrec.comp Primrec.id (Primrec.fst.comp Primrec.unpair)

theorem prepare_spec (q : Nat) (hq : unionCheck q = true) :
    unionCheck (prepare q) = true ∧ unionInterpretation (prepare q) = unionInterpretation q :=
  lowerLoop_spec q q.unpair.1 hq

theorem prepare_base_le (q : Nat) (hq : unionCheck q = true) (hnonzero : unionInterpretation q ≠ 0) :
    finiteBase (prepare q).unpair.1 ≤ unionInterpretation (prepare q) := by
  have hr := lowerLoop_ready q.unpair.1 q.unpair.2 hq
  simp only [Nat.pair_unpair] at hr
  change (prepare q).unpair.1 = 0 ∨ finiteBase (prepare q).unpair.1 ≤ unionInterpretation (prepare q) at hr
  rcases hr with hr | hr
  · rw [hr, finiteBase_zero]
    have hp : 0 < unionInterpretation (prepare q) := lt_of_le_of_ne (zero_le)
      (fun he => hnonzero ((prepare_spec q hq).2.symm.trans he.symm))
    simpa only [zero_add] using Order.add_one_le_of_lt hp
  · exact hr

def zeroCheck (q : Nat) : Bool := Canonical.graph q (Canonical.canonicalize zeroCode)

theorem zeroCheck_primrec : Primrec zeroCheck :=
  Canonical.Effective.graph_primrec.comp Primrec.id (Primrec.const (Canonical.canonicalize zeroCode))

theorem zeroCheck_exact (q : Nat) : zeroCheck q = true ↔ unionCheck q = true ∧ unionInterpretation q = 0 := by
  simp only [zeroCheck, Canonical.graph_exact, Canonical.canonicalize_check zeroCode zeroCode_checked,
    Canonical.canonicalize_value zeroCode zeroCode_checked, zeroCode_value, true_and]

def powerAt (q : Nat) : Nat :=
  cond (Epsilon.unionEpsilonCheck q) (Canonical.canonicalize q)
    (cond (zeroCheck q) (Canonical.canonicalize CanonicalArithmetic.oneCode)
      (Canonical.canonicalize (Nat.pair q.unpair.1 (thetaCode (argumentCode q.unpair.1 q.unpair.2)))))

theorem powerAt_primrec : Primrec powerAt := by
  have hr := Primrec.fst.comp Primrec.unpair
  have hc := Primrec.snd.comp Primrec.unpair
  have htheta := Primrec₂.natPair.comp hr (thetaCode_primrec.comp (argumentCode_primrec.comp hr hc))
  exact Epsilon.unionEpsilonCheck_primrec.cond Canonical.Effective.canonicalize_primrec
    (zeroCheck_primrec.cond (Primrec.const (Canonical.canonicalize CanonicalArithmetic.oneCode))
      (Canonical.Effective.canonicalize_primrec.comp htheta))

theorem powerAt_spec (q : Nat) (hq : unionCheck q = true)
    (hb : unionInterpretation q ≠ 0 → finiteBase q.unpair.1 ≤ unionInterpretation q) :
    Canonical.check (powerAt q) = true ∧ unionInterpretation (powerAt q) = Ordinal.omega0 ^ unionInterpretation q := by
  cases he : Epsilon.unionEpsilonCheck q with
  | true =>
    have hs := (Epsilon.unionEpsilonCheck_exact q).mp he
    simpa only [powerAt, he, Bool.cond_true, Canonical.canonicalize_value q hq, hs.2] using
      And.intro (Canonical.canonicalize_check q hq) (Canonical.canonicalize_value q hq)
  | false =>
    cases hz : zeroCheck q with
    | true =>
      have hv := (zeroCheck_exact q).mp hz
      simpa only [powerAt, he, hz, Bool.cond_false, Bool.cond_true, hv.2, Ordinal.opow_zero,
        Canonical.canonicalize_value _ CanonicalArithmetic.oneCode_checked, CanonicalArithmetic.oneCode_value] using
        And.intro (Canonical.canonicalize_check _ CanonicalArithmetic.oneCode_checked)
          ((Canonical.canonicalize_value _ CanonicalArithmetic.oneCode_checked).trans CanonicalArithmetic.oneCode_value)
    | false =>
      have hnonzero : unionInterpretation q ≠ 0 := by
        intro hv
        have ht := (zeroCheck_exact q).mpr ⟨hq, hv⟩
        rw [hz] at ht
        cases ht
      have ha := argumentCode_checked q.unpair.1 q.unpair.2 hq
      have ht : unionCheck (Nat.pair q.unpair.1 (thetaCode (argumentCode q.unpair.1 q.unpair.2))) = true := by
        simpa only [unionCheck_pair] using thetaCode_checked _ _ ha
      have hsmall := ((lt_nextBase_iff_code q.unpair.1 _).mpr
        ⟨argumentCode q.unpair.1 q.unpair.2, ha, rfl⟩).trans (finiteBase_lt_cardinal q.unpair.1)
      have hvalue : unionInterpretation (Nat.pair q.unpair.1 (thetaCode (argumentCode q.unpair.1 q.unpair.2))) =
          Ordinal.omega0 ^ unionInterpretation q := by
        rw [unionInterpretation_pair, thetaCode_value _ _ ha,
          globalCollapse_low_eq_omegaPower _ (finiteBase_epsilon_or_one _) _ hsmall,
          argumentCode_exponent _ _ hq (hb hnonzero) (by simpa only [Nat.pair_unpair] using he)]
        rfl
      simp only [powerAt, he, hz, Bool.cond_false]
      exact ⟨Canonical.canonicalize_check _ ht, (Canonical.canonicalize_value _ ht).trans hvalue⟩

def powerCode (q : Nat) : Nat := cond (unionCheck q) (powerAt (prepare q)) 0

theorem powerCode_primrec : Primrec powerCode :=
  Uniform.unionCheck_primrec.cond (powerAt_primrec.comp prepare_primrec) (Primrec.const 0)

theorem powerCode_checked (q : Nat) (hq : unionCheck q = true) : Canonical.check (powerCode q) = true := by
  have hs := prepare_spec q hq
  have hp := powerAt_spec (prepare q) hs.1 (fun hn => prepare_base_le q hq (fun hz => hn (hs.2.trans hz)))
  simpa only [powerCode, hq, Bool.cond_true] using hp.1

theorem powerCode_value (q : Nat) (hq : unionCheck q = true) :
    unionInterpretation (powerCode q) = Ordinal.omega0 ^ unionInterpretation q := by
  have hs := prepare_spec q hq
  have hp := powerAt_spec (prepare q) hs.1 (fun hn => prepare_base_le q hq (fun hz => hn (hs.2.trans hz)))
  simpa only [powerCode, hq, Bool.cond_true, hs.2] using hp.2

theorem powerCode_original (q : Nat) (hq : unionCheck q = true) : unionCheck (powerCode q) = true :=
  Canonical.check_original (powerCode_checked q hq)

theorem powerCode_normal (q : Nat) (hq : unionCheck q = true) :
    Theta.Normal (powerCode q).unpair.1 (rawTree (powerCode q).unpair.2) :=
  Canonical.check_normal (powerCode_checked q hq)

theorem powerCode_rejected (q : Nat) (hq : unionCheck q = false) : powerCode q = 0 := by
  simp only [powerCode, hq, Bool.cond_false]

theorem powerCode_unique (q c : Nat) (hq : unionCheck q = true) (hc : Canonical.check c = true)
    (hv : unionInterpretation c = Ordinal.omega0 ^ unionInterpretation q) : c = powerCode q :=
  Canonical.check_value_injective c _ hc (powerCode_checked q hq) (hv.trans (powerCode_value q hq).symm)

theorem powerCode_invariant (q v : Nat) (hq : unionCheck q = true) (hv : unionCheck v = true)
    (he : unionInterpretation q = unionInterpretation v) : powerCode q = powerCode v := by
  apply powerCode_unique v _ hv (powerCode_checked q hq)
  rw [powerCode_value q hq, he]

theorem powerCode_below_limit (q : Nat) (hq : unionCheck q = true) :
    Ordinal.omega0 ^ unionInterpretation q < finiteBaseLimit :=
  (Hereditary.lt_finiteBaseLimit_iff_code _).mpr ⟨powerCode q, powerCode_original q hq, powerCode_value q hq⟩

theorem powerCode_computable : Computable powerCode := powerCode_primrec.to_comp

def labelPower (μ : Alexander313.HereditaryOrdinalLabels.Label) : Alexander313.HereditaryOrdinalLabels.Label :=
  ⟨powerCode μ.1, powerCode_checked μ.1 (Canonical.check_original μ.2)⟩

theorem labelPower_value (μ : Alexander313.HereditaryOrdinalLabels.Label) :
    Alexander313.HereditaryOrdinalLabels.value (labelPower μ) =
      Ordinal.omega0 ^ Alexander313.HereditaryOrdinalLabels.value μ :=
  powerCode_value μ.1 (Canonical.check_original μ.2)

end Alexander313.Wilken.RelativeTerm.Hereditary.OmegaPowers
