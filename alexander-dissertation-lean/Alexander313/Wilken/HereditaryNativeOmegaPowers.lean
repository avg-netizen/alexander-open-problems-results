import Alexander313.Wilken.HereditaryNativeOmegaPowerOffsets

/-!
# Genuine LOW omega powers at EVERY original coded epsilon base

All branches are finite primitive-recursive native/public operations. Below
the base, actual parameter aggregation and public omega power give a genuine
admitted payload. At an epsilon value the actual native normalizer returns
the input value. Epsilon-plus-positive-finite inputs use the genuine head
and extracted Nat predecessor, including the base boundary separately.
All other high inputs use actual native left removal of the original base.
The real low collapse equation then proves exact omega-power denotation.

Every original raw LOW input at every original coded epsilon is covered.
LOW output and Normality are constructed, and actual height endpoints give
written output height at most canonical input height, including zero. No
recoder, representation, epsilon/offset or height oracle is supplied. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.OmegaPowers

open ThetaCourse
open OmegaPowerHeight (numeralCode finiteTailCode)

def headAbove (q c : Nat) : Bool := Normalization.lessRawCode q Offsets.baseCode (Offsets.headCode q c)

theorem headAbove_primrec : Primrec₂ headAbove :=
  (Normalization.Effective.lessRawCode_primrec.comp
    (Primrec.fst.pair ((Primrec.const Offsets.baseCode).pair Offsets.headCode_primrec))).to₂

def argumentCode (q c : Nat) : Nat := cond (Offsets.check q c)
  (cond (headAbove q c) (finiteTailCode q (Offsets.headCode q c) (Offsets.offset q c - 1))
    (numeralCode (Offsets.offset q c)))
  (Arithmetic.subtractCode q Offsets.baseCode c)

theorem argumentCode_primrec : Primrec₂ argumentCode := by
  have hn := Primrec.nat_sub.comp Offsets.offset_primrec (Primrec.const 1)
  have hs := OmegaPowerHeight.finiteTailCode_primrec.comp
    ((Primrec.fst.pair Offsets.headCode_primrec).pair hn)
  have hsub := Arithmetic.subtractCode_primrec.comp
    (Primrec.fst.pair ((Primrec.const Offsets.baseCode).pair Primrec.snd))
  exact (Offsets.check_primrec.cond (headAbove_primrec.cond hs
    (OmegaPowerHeight.numeralCode_primrec.comp Offsets.offset_primrec)) hsub).to₂

/-- The original native argument producer supplies its genuine LOW Normal
caller and exact inverse low-collapse exponent. The only branch restriction
is that an epsilon with zero finite offset has already been returned. -/
theorem argumentCode_spec (q c : Nat) (hc : lowCheckCode q c = true)
    (hb : base q ≤ interpretation q c)
    (hnz : ¬ (Offsets.check q c = true ∧ Offsets.offset q c = 0)) :
    lowCheckCode q (argumentCode q c) = true ∧ Comparison.acceptedCode q (argumentCode q c) = true ∧
      lowOmegaExponent (base q) (interpretation q (argumentCode q c)) = interpretation q c := by
  have hi := HeightBoundary.input_spec q c hc
  have hq := hi.2.1
  have hbase := Offsets.baseCode_spec q hq
  cases hoff : Offsets.check q c with
  | true =>
    have hs := Offsets.decomposition_spec q c hoff
    have hn : 0 < Offsets.offset q c := Nat.pos_of_ne_zero (fun hz => hnz ⟨hoff, hz⟩)
    have hhead : base q ≤ interpretation q (Offsets.headCode q c) := by
      by_contra! hsmall
      have hnat : (Offsets.offset q c : Ordinal.{0}) < base q :=
        (Ordinal.natCast_lt_omega0 _).trans (epsilon_omega_lt (SourceChi.epsilon_base q hq))
      have hlt := OmegaPowerHeight.endpoint_add_closed_all q 0 hq
        (by simpa only [HeightBoundary.endpoint_zero q hq] using hsmall)
        (by simpa only [HeightBoundary.endpoint_zero q hq] using hnat)
      exact (not_lt_of_ge hb) (by
        simpa only [HeightBoundary.endpoint_zero q hq, ← hs.2.2.2.2] using hlt)
    have he : headAbove q c = true ↔ base q < interpretation q (Offsets.headCode q c) := by
      simpa only [headAbove, hbase.2, ((Comparison.acceptedCode_exact q _).mp hbase.1).1,
        ((Comparison.acceptedCode_exact q _).mp hs.2.2.1).1, true_and] using
        Normalization.lessRawCode_exact q Offsets.baseCode (Offsets.headCode q c)
    cases ha : headAbove q c with
    | true =>
      have ht := OmegaPowerHeight.finiteTailCode_spec q (Offsets.headCode q c) (Offsets.offset q c - 1) hs.2.1
      refine ⟨by simpa only [argumentCode, hoff, ha, Bool.cond_true] using ht.1,
        by simpa only [argumentCode, hoff, ha, Bool.cond_true] using ht.2.1, ?_⟩
      simp only [argumentCode, hoff, ha, Bool.cond_true]
      rw [ht.2.2.1, lowOmegaExponent_offset_predecessor _ _ _ (he.mp ha) hs.2.2.2.1 hn]
      exact hs.2.2.2.2.symm
    | false =>
      have hle : interpretation q (Offsets.headCode q c) ≤ base q := le_of_not_gt (by
        intro h
        have ht := he.mpr h
        simp only [ha, Bool.false_eq_true] at ht)
      have heq := le_antisymm hle hhead
      have ht := OmegaPowerHeight.numeralCode_spec q (Offsets.offset q c) hq
      refine ⟨by simpa only [argumentCode, hoff, ha, Bool.cond_true, Bool.cond_false] using ht.1,
        by simpa only [argumentCode, hoff, ha, Bool.cond_true, Bool.cond_false] using ht.2.1, ?_⟩
      simp only [argumentCode, hoff, ha, Bool.cond_true, Bool.cond_false]
      rw [ht.2.2.1, lowOmegaExponent_nat, lowOmegaBase_of_epsilon _ (SourceChi.epsilon_base q hq)]
      exact (by simpa only [heq] using hs.2.2.2.2.symm)
  | false =>
    have hn : ¬ EpsilonFiniteAbove (base q) (interpretation q c) := by
      rintro ⟨ε, n, hεb, hε, hv⟩
      have ht := (Offsets.check_exact q c).mpr ⟨hc, ε, n, hε, hv⟩
      simp only [hoff, Bool.false_eq_true] at ht
    have ht := Arithmetic.subtractCode_spec q Offsets.baseCode c
      ((Comparison.acceptedCode_exact q _).mp hbase.1).1 hi.1
    have hlo := low_of_bound q _ ((Comparison.acceptedCode_exact q _).mp ht.1).1 (by
      rw [ht.2.1]
      exact (Ordinal.sub_le_self _ _).trans_lt hi.2.2)
    refine ⟨by simpa only [argumentCode, hoff, Bool.cond_false] using hlo,
      by simpa only [argumentCode, hoff, Bool.cond_false] using ht.1, ?_⟩
    simp only [argumentCode, hoff, Bool.cond_false]
    have hv : interpretation q (Arithmetic.subtractCode q Offsets.baseCode c) =
        interpretation q c - lowOmegaBase (base q) := by
      rw [ht.2.1, hbase.2, lowOmegaBase_of_epsilon _ (SourceChi.epsilon_base q hq)]
    rw [hv]
    exact lowOmegaExponent_sub_base _ _
      (by simpa only [lowOmegaBase_of_epsilon _ (SourceChi.epsilon_base q hq)] using hb) hn

def powerCode (q c : Nat) : Nat := cond (lowCheckCode q c)
  (cond (Normalization.lessRawCode q c Offsets.baseCode) (belowPowerCode q c)
    (cond (Offsets.check q c && (Offsets.offset q c == 0)) (Normalization.normalizeCode q c)
      (thetaCode (argumentCode q c)))) 0

theorem powerCode_primrec : Primrec₂ powerCode := by
  have hb := Normalization.Effective.lessRawCode_primrec.comp
    (Primrec.fst.pair (Primrec.snd.pair (Primrec.const Offsets.baseCode)))
  have hz := Primrec.and.comp Offsets.check_primrec (Primrec.beq.comp Offsets.offset_primrec (Primrec.const 0))
  exact (lowCheckCode_primrec.cond (hb.cond belowPowerCode_primrec
    (hz.cond Normalization.Effective.normalizeCode_primrec
      (thetaCode_primrec.comp argumentCode_primrec))) (Primrec.const 0)).to₂

/-- Every original raw LOW input at EVERY original coded epsilon has an
actual primitive-recursive LOW Normal omega-power output in that SAME context. -/
theorem powerCode_spec (q c : Nat) (hc : lowCheckCode q c = true) :
    lowCheckCode q (powerCode q c) = true ∧ Comparison.acceptedCode q (powerCode q c) = true ∧
      interpretation q (powerCode q c) = Ordinal.omega0 ^ interpretation q c := by
  have hi := HeightBoundary.input_spec q c hc
  have hbase := Offsets.baseCode_spec q hi.2.1
  have he : Normalization.lessRawCode q c Offsets.baseCode = true ↔ interpretation q c < base q := by
    simpa only [hi.1, ((Comparison.acceptedCode_exact q _).mp hbase.1).1, hbase.2,
      true_and] using Normalization.lessRawCode_exact q c Offsets.baseCode
  cases hb : Normalization.lessRawCode q c Offsets.baseCode with
  | true =>
    simpa only [powerCode, hc, hb, Bool.cond_true] using belowPowerCode_spec q c hi.1 (he.mp hb)
  | false =>
    have hge : base q ≤ interpretation q c := le_of_not_gt (by
      intro h
      have ht := he.mpr h
      simp only [hb, Bool.false_eq_true] at ht)
    cases hz : Offsets.check q c && (Offsets.offset q c == 0) with
    | true =>
      have hparts := Bool.and_eq_true.mp hz
      have hoff := Offsets.decomposition_spec q c hparts.1
      have hn : Offsets.offset q c = 0 := beq_iff_eq.mp hparts.2
      have hε : Ordinal.omega0 ^ interpretation q c = interpretation q c := by
        rw [hoff.2.2.2.2, hn, Nat.cast_zero, add_zero]
        exact hoff.2.2.2.1
      have ht := Normalization.normalizeCode_accepted q c hi.1
      have hlo := low_of_bound q _ ((Comparison.acceptedCode_exact q _).mp ht.1).1 (by rw [ht.2]; exact hi.2.2)
      simpa only [powerCode, hc, hb, hz, Bool.cond_true, Bool.cond_false] using
        (show lowCheckCode q (Normalization.normalizeCode q c) = true ∧
          Comparison.acceptedCode q (Normalization.normalizeCode q c) = true ∧
          interpretation q (Normalization.normalizeCode q c) = Ordinal.omega0 ^ interpretation q c from
          ⟨hlo, ht.1, ht.2.trans hε.symm⟩)
    | false =>
      have hnz : ¬ (Offsets.check q c = true ∧ Offsets.offset q c = 0) := by
        rintro ⟨h, hn⟩
        simp only [h, hn, beq_self_eq_true, Bool.true_and, Bool.true_eq_false] at hz
      have ha := argumentCode_spec q c hc hge hnz
      have ht := thetaCode_spec q _ ha.1 ha.2.1
      refine ⟨by simpa only [powerCode, hc, hb, hz, Bool.cond_true, Bool.cond_false] using ht.1,
        by simpa only [powerCode, hc, hb, hz, Bool.cond_true, Bool.cond_false] using ht.2.1, ?_⟩
      simp only [powerCode, hc, hb, hz, Bool.cond_true, Bool.cond_false]
      rw [ht.2.2, globalCollapse_low_eq_omegaPower (base q) (Or.inr (SourceChi.epsilon_base q hi.2.1)) _
        (HeightBoundary.input_spec q _ ha.1).2.2, ha.2.2]

/-- The actual all-index epsilon endpoints prove the exact written output
height on EVERY original raw LOW input, including canonical height zero. -/
theorem powerCode_height (q c : Nat) (hc : lowCheckCode q c = true) :
    heightCode (powerCode q c) ≤ CanonicalHeight.canonicalHeightCode q c := by
  have hs := powerCode_spec q c hc
  rw [← CanonicalHeight.canonicalHeightCode_normal q _ hs.2.1]
  apply (HeightBoundary.canonicalHeightCode_le_iff_endpoint q _ _ hs.1).mpr
  rw [hs.2.2]
  exact (omegaPower_strictMono ((HeightBoundary.canonicalHeightCode_le_iff_endpoint q _ c hc).mp le_rfl)).trans_eq
    (OmegaPowerHeight.endpoint_epsilon_all q _ (HeightBoundary.input_spec q c hc).2.1)

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.OmegaPowers
