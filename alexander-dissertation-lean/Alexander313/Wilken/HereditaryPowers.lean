import Alexander313.Wilken.HereditaryExponentDecomposition
import Alexander313.Wilken.HereditaryFinitePowers

/-!
# Actual ordinary exponentiation with arbitrary original coded bases

Every exponent is genuinely decomposed as omega*delta+n. A nonzero/nonunit
finite base uses omega^delta for its limit factor; an infinite base uses the
actual leading logarithm gamma and omega^(gamma*(omega*delta)). A zero limit
prefix returns one. The actual finite power and multiplier form the final
product. Base zero and one have explicit branches, including 0^0=1.

All input, intermediate canonical and ordinal-bound claims are derived from
the real executing arithmetic. Termination is exactly both original input
admissions. The routine is partial recursive, not claimed PR. No base-power,
decomposition, arithmetic, semantic graph or effectivity oracle is supplied.
All proof terms remain uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.Powers

open ExponentDecomposition (delta offset «prefix» DataSpec)

def infiniteLimitFactor (q data : Nat) : Part Nat :=
  (LogEnd.leadingLog q).bind (fun g =>
    (Multiplication.multiply g («prefix» data)).map OmegaPowers.powerCode)

theorem infiniteLimitFactor_partrec : Partrec₂ infiniteLimitFactor := by
  have hm : Partrec (fun p : (Nat × Nat) × Nat => Multiplication.multiply p.2 («prefix» p.1.2)) :=
    Multiplication.multiply_partrec.comp Computable.snd
      (ExponentDecomposition.prefix_primrec.comp (Primrec.snd.comp Primrec.fst)).to_comp
  have hs := (hm.map (OmegaPowers.powerCode_primrec.comp Primrec.snd).to_comp.to₂).to₂
  exact ((LogEnd.leadingLog_partrec.comp Computable.fst).bind hs).to₂

def limitFactor (q data : Nat) : Part Nat :=
  cond (OmegaPowers.zeroCheck (delta data)) (Part.some FinitePowers.oneCode)
    (cond (NaturalCodes.check q) (Part.some (OmegaPowers.powerCode (delta data)))
      (infiniteLimitFactor q data))

theorem limitFactor_partrec : Partrec₂ limitFactor :=
  (Partrec.cond
    (OmegaPowers.zeroCheck_primrec.comp (ExponentDecomposition.delta_primrec.comp Primrec.snd)).to_comp
    (Computable.const FinitePowers.oneCode).partrec
    (Partrec.cond (NaturalCodes.check_primrec.comp Primrec.fst).to_comp
      (OmegaPowers.powerCode_primrec.comp (ExponentDecomposition.delta_primrec.comp Primrec.snd)).to_comp.partrec
      infiniteLimitFactor_partrec)).to₂

theorem limitFactor_returns (q v data : Nat) (hq : unionCheck q = true) (hd : DataSpec v data) :
    ∃ c : Nat, c ∈ limitFactor q data ∧ Canonical.check c = true := by
  cases hz : OmegaPowers.zeroCheck (delta data) with
  | true => exact ⟨FinitePowers.oneCode, by simp [limitFactor, hz], FinitePowers.oneCode_checked⟩
  | false =>
    cases hf : NaturalCodes.check q with
    | true => exact ⟨OmegaPowers.powerCode (delta data), by simp [limitFactor, hz, hf],
        OmegaPowers.powerCode_checked _ (Canonical.check_original hd.2.1)⟩
    | false =>
      obtain ⟨g, hg, hgc, _⟩ := LogEnd.componentLog_returns false q hq
      obtain ⟨d, hmul, hdc, _⟩ := Multiplication.multiply_returns g («prefix» data)
        (Canonical.check_original hgc) (Canonical.check_original hd.2.2.1)
      have hm := Part.mem_bind hg (Part.mem_map OmegaPowers.powerCode hmul)
      exact ⟨OmegaPowers.powerCode d, by simpa only [limitFactor, hz, hf,
        Bool.cond_false, infiniteLimitFactor, LogEnd.leadingLog] using hm,
        OmegaPowers.powerCode_checked d (Canonical.check_original hdc)⟩

theorem leading_bounds (q g : Nat) (hq : unionCheck q = true)
    (hp : 0 < unionInterpretation q) (hg : g ∈ LogEnd.leadingLog q) :
    Ordinal.omega0 ^ unionInterpretation g ≤ unionInterpretation q ∧
      unionInterpretation q < Ordinal.omega0 ^ (unionInterpretation g + 1) := by
  obtain ⟨xs, hxs⟩ := LogEnd.mcCode_anf_cons q hq hp
  have hn := canonicalANF_normal (unionInterpretation q)
  rw [hxs] at hn
  have hs := MultiplicativePrincipalArithmetic.principalSum_leading_bounds hn
    (LogEnd.leadingLog_power q g hg hp).symm
  have he : principalSum (unionInterpretation (LogEnd.mcCode q) :: xs) = unionInterpretation q := by
    rw [← hxs, principalSum_canonicalANF]
  simpa only [he] using hs

theorem limitFactor_value (q v data c : Nat) (hq : unionCheck q = true)
    (hp : 1 < unionInterpretation q) (hd : DataSpec v data) (hc : c ∈ limitFactor q data) :
    Canonical.check c = true ∧ unionInterpretation c = unionInterpretation q ^ unionInterpretation («prefix» data) := by
  cases hz : OmegaPowers.zeroCheck (delta data) with
  | true =>
    have he : c = FinitePowers.oneCode := by simpa [limitFactor, hz] using hc
    have hzero := ((OmegaPowers.zeroCheck_exact _).mp hz).2
    subst c
    refine ⟨FinitePowers.oneCode_checked, ?_⟩
    rw [hd.2.2.2.1, hzero, mul_zero, Ordinal.opow_zero, FinitePowers.oneCode_value]
  | false =>
    cases hf : NaturalCodes.check q with
    | true =>
      have he : c = OmegaPowers.powerCode (delta data) := by simpa [limitFactor, hz, hf] using hc
      have hqv := NaturalCodes.extract_value q hf
      have hmOrd : (1 : Ordinal.{0}) < (NaturalCodes.extract q : Ordinal.{0}) := by rw [← hqv]; exact hp
      have hm : 1 < NaturalCodes.extract q := by exact_mod_cast hmOrd
      subst c
      refine ⟨OmegaPowers.powerCode_checked _ (Canonical.check_original hd.2.1), ?_⟩
      rw [OmegaPowers.powerCode_value _ (Canonical.check_original hd.2.1), hd.2.2.2.1, hqv,
        OrdinalPowerArithmetic.finite_opow_omega_mul hm]
    | false =>
      have hin : c ∈ infiniteLimitFactor q data := by simpa only [limitFactor, hz, hf, Bool.cond_false] using hc
      obtain ⟨g, hg, hmap⟩ := Part.mem_bind_iff.mp hin
      obtain ⟨d, hmul, he⟩ := (Part.mem_map_iff OmegaPowers.powerCode).mp hmap
      have hprod := Multiplication.multiply_value g («prefix» data) d hmul
      have hb := leading_bounds q g hq (zero_lt_one.trans hp) hg
      have hinfinite : Ordinal.omega0 ≤ unionInterpretation q := by
        apply le_of_not_gt
        intro hsmall
        have ht := (NaturalCodes.check_below_omega q).mpr ⟨hq, hsmall⟩
        rw [hf] at ht
        contradiction
      have hgp := OrdinalPowerArithmetic.leading_positive_of_infinite hinfinite hb.2
      have hdp : 0 < unionInterpretation (delta data) := by
        apply pos_iff_ne_zero.mpr
        intro hzero
        have ht := (OmegaPowers.zeroCheck_exact _).mpr ⟨Canonical.check_original hd.2.1, hzero⟩
        rw [hz] at ht
        contradiction
      have hlimit : Order.IsSuccLimit (unionInterpretation («prefix» data)) := by
        rw [hd.2.2.2.1]
        exact OrdinalPowerArithmetic.omega_mul_isSuccLimit hdp
      rw [← he]
      refine ⟨OmegaPowers.powerCode_checked d (Canonical.check_original hprod.2.2.1), ?_⟩
      rw [OmegaPowers.powerCode_value d (Canonical.check_original hprod.2.2.1), hprod.2.2.2,
        OrdinalPowerArithmetic.leading_bounds_opow_limit hgp hb.1 hb.2 hlimit]

def tailProduct (q data : Nat) : Part Nat :=
  (limitFactor q data).bind (fun p =>
    (FinitePowers.power q (offset data)).bind (fun f => Multiplication.multiply p f))

theorem tailProduct_partrec : Partrec₂ tailProduct := by
  have ht : Partrec (fun p : (Nat × Nat) × Nat => FinitePowers.power p.1.1 (offset p.1.2)) :=
    FinitePowers.power_partrec.comp (Computable.fst.comp Computable.fst)
      (ExponentDecomposition.offset_primrec.comp (Primrec.snd.comp Primrec.fst)).to_comp
  have hm : Partrec₂ (fun (p : (Nat × Nat) × Nat) (f : Nat) => Multiplication.multiply p.2 f) :=
    (Multiplication.multiply_partrec.comp (Computable.snd.comp Computable.fst) Computable.snd).to₂
  exact (limitFactor_partrec.bind (ht.bind hm).to₂).to₂

theorem tailProduct_returns (q v data : Nat) (hq : unionCheck q = true) (hd : DataSpec v data) :
    ∃ c : Nat, c ∈ tailProduct q data ∧ Canonical.check c = true := by
  obtain ⟨p, hp, hpc⟩ := limitFactor_returns q v data hq hd
  obtain ⟨f, hf, hfc, _⟩ := FinitePowers.power_returns q (offset data) hq
  obtain ⟨c, hc, hcc, _⟩ := Multiplication.multiply_returns p f
    (Canonical.check_original hpc) (Canonical.check_original hfc)
  exact ⟨c, Part.mem_bind hp (Part.mem_bind hf hc), hcc⟩

theorem tailProduct_value (q v data c : Nat) (hq : unionCheck q = true)
    (hp : 1 < unionInterpretation q) (hd : DataSpec v data) (hc : c ∈ tailProduct q data) :
    Canonical.check c = true ∧ unionInterpretation c = unionInterpretation q ^ unionInterpretation v := by
  obtain ⟨p, hprefix, hrest⟩ := Part.mem_bind_iff.mp hc
  obtain ⟨f, hfinite, hmul⟩ := Part.mem_bind_iff.mp hrest
  have hpc := limitFactor_value q v data p hq hp hd hprefix
  have hfc := FinitePowers.power_value q (offset data) f hfinite
  have hs := Multiplication.multiply_value p f c hmul
  refine ⟨hs.2.2.1, ?_⟩
  rw [hs.2.2.2, hpc.2, hfc.2.2, ← Ordinal.opow_add, ← hd.2.2.2.2]

def oneCheck (q : Nat) : Bool := Canonical.graph q FinitePowers.oneCode

theorem oneCheck_primrec : Primrec oneCheck :=
  Canonical.Effective.graph_primrec.comp Primrec.id (Primrec.const FinitePowers.oneCode)

theorem oneCheck_exact (q : Nat) : oneCheck q = true ↔ unionCheck q = true ∧ unionInterpretation q = 1 := by
  simp only [oneCheck, Canonical.graph_exact, FinitePowers.oneCode_checked, FinitePowers.oneCode_value, true_and]

def evaluation (input : Nat) : Part Nat :=
  let q := input.unpair.1
  let v := input.unpair.2
  cond (unionCheck q && unionCheck v)
    (cond (OmegaPowers.zeroCheck q)
      (cond (OmegaPowers.zeroCheck v) (Part.some FinitePowers.oneCode) (Part.some Multiplication.zeroCode))
      (cond (oneCheck q) (Part.some FinitePowers.oneCode)
        ((ExponentDecomposition.decompose v).bind (tailProduct q)))) Part.none

theorem evaluation_partrec : Partrec evaluation := by
  have hq := Primrec.fst.comp Primrec.unpair
  have hv := Primrec.snd.comp Primrec.unpair
  have hdata := ExponentDecomposition.decompose_partrec.comp hv.to_comp
  have hstep : Partrec₂ (fun (input : Nat) (data : Nat) => tailProduct input.unpair.1 data) :=
    (tailProduct_partrec.comp (hq.comp Primrec.fst).to_comp Computable.snd).to₂
  exact Partrec.cond
    (Primrec.and.comp (Uniform.unionCheck_primrec.comp hq) (Uniform.unionCheck_primrec.comp hv)).to_comp
    (Partrec.cond (OmegaPowers.zeroCheck_primrec.comp hq).to_comp
      (Partrec.cond (OmegaPowers.zeroCheck_primrec.comp hv).to_comp
        (Computable.const FinitePowers.oneCode).partrec (Computable.const Multiplication.zeroCode).partrec)
      (Partrec.cond (oneCheck_primrec.comp hq).to_comp (Computable.const FinitePowers.oneCode).partrec
        (hdata.bind hstep))) Partrec.none

def power (q v : Nat) : Part Nat := evaluation (Nat.pair q v)

theorem power_partrec : Partrec₂ power := (evaluation_partrec.comp Primrec₂.natPair.to_comp).to₂

theorem power_original_inputs (q v c : Nat) (hc : c ∈ power q v) : unionCheck q = true ∧ unionCheck v = true := by
  cases h : unionCheck q && unionCheck v with
  | true => exact Bool.and_eq_true.mp h
  | false => have hf : False := by simpa [power, evaluation, Nat.unpair_pair, h] using hc; exact hf.elim

theorem power_returns (q v : Nat) (hq : unionCheck q = true) (hv : unionCheck v = true) :
    ∃ c : Nat, c ∈ power q v ∧ Canonical.check c = true := by
  cases hz : OmegaPowers.zeroCheck q with
  | true =>
    cases he : OmegaPowers.zeroCheck v with
    | true => exact ⟨FinitePowers.oneCode, by simp [power, evaluation, Nat.unpair_pair, hq, hv, hz, he], FinitePowers.oneCode_checked⟩
    | false => exact ⟨Multiplication.zeroCode, by simp [power, evaluation, Nat.unpair_pair, hq, hv, hz, he], Multiplication.zeroCode_checked⟩
  | false =>
    cases ho : oneCheck q with
    | true => exact ⟨FinitePowers.oneCode, by simp [power, evaluation, Nat.unpair_pair, hq, hv, hz, ho], FinitePowers.oneCode_checked⟩
    | false =>
      obtain ⟨data, hd, hs⟩ := ExponentDecomposition.decompose_returns v hv
      obtain ⟨c, hc, hcc⟩ := tailProduct_returns q v data hq hs
      exact ⟨c, by simpa only [power, evaluation, Nat.unpair_pair, hq, hv,
        Bool.true_and, hz, ho, Bool.cond_true, Bool.cond_false] using Part.mem_bind hd hc, hcc⟩

theorem power_domain (q v : Nat) : (power q v).Dom ↔ unionCheck q = true ∧ unionCheck v = true := by
  constructor
  · intro h; obtain ⟨c, hc⟩ := Part.dom_iff_mem.mp h; exact power_original_inputs q v c hc
  · rintro ⟨hq, hv⟩; obtain ⟨c, hc, _⟩ := power_returns q v hq hv; exact Part.dom_iff_mem.mpr ⟨c, hc⟩

theorem power_value (q v c : Nat) (hc : c ∈ power q v) :
    unionCheck q = true ∧ unionCheck v = true ∧ Canonical.check c = true ∧
      unionInterpretation c = unionInterpretation q ^ unionInterpretation v := by
  have hs := power_original_inputs q v c hc
  refine ⟨hs.1, hs.2, ?_⟩
  cases hz : OmegaPowers.zeroCheck q with
  | true =>
    have hq0 := ((OmegaPowers.zeroCheck_exact q).mp hz).2
    cases he : OmegaPowers.zeroCheck v with
    | true =>
      have hv0 := ((OmegaPowers.zeroCheck_exact v).mp he).2
      have hcc : c = FinitePowers.oneCode := by simpa [power, evaluation, Nat.unpair_pair, hs.1, hs.2, hz, he] using hc
      subst c
      exact ⟨FinitePowers.oneCode_checked, by rw [hv0, Ordinal.opow_zero, FinitePowers.oneCode_value]⟩
    | false =>
      have hvn : unionInterpretation v ≠ 0 := by
        intro h0; have ht := (OmegaPowers.zeroCheck_exact v).mpr ⟨hs.2, h0⟩; rw [he] at ht; contradiction
      have hcc : c = Multiplication.zeroCode := by simpa [power, evaluation, Nat.unpair_pair, hs.1, hs.2, hz, he] using hc
      subst c
      exact ⟨Multiplication.zeroCode_checked, by rw [hq0, Ordinal.zero_opow hvn, Multiplication.zeroCode_value]⟩
  | false =>
    cases ho : oneCheck q with
    | true =>
      have hq1 := ((oneCheck_exact q).mp ho).2
      have hcc : c = FinitePowers.oneCode := by simpa [power, evaluation, Nat.unpair_pair, hs.1, hs.2, hz, ho] using hc
      subst c
      exact ⟨FinitePowers.oneCode_checked, by rw [hq1, Ordinal.one_opow, FinitePowers.oneCode_value]⟩
    | false =>
      have hqn : unionInterpretation q ≠ 0 := by
        intro h0; have ht := (OmegaPowers.zeroCheck_exact q).mpr ⟨hs.1, h0⟩; rw [hz] at ht; contradiction
      have hq1 : unionInterpretation q ≠ 1 := by
        intro h1; have ht := (oneCheck_exact q).mpr ⟨hs.1, h1⟩; rw [ho] at ht; contradiction
      have hp : 1 < unionInterpretation q :=
        (lt_or_eq_of_le (Order.one_le_iff_pos.mpr (pos_iff_ne_zero.mpr hqn))).resolve_right (Ne.symm hq1)
      have hm : c ∈ (ExponentDecomposition.decompose v).bind (tailProduct q) := by
        simpa only [power, evaluation, Nat.unpair_pair, hs.1, hs.2, Bool.true_and,
          hz, ho, Bool.cond_true, Bool.cond_false] using hc
      obtain ⟨data, hd, hout⟩ := Part.mem_bind_iff.mp hm
      exact tailProduct_value q v data c hs.1 hp (ExponentDecomposition.decompose_value v data hd) hout

theorem power_graph_iff (q v c : Nat) : c ∈ power q v ↔
    unionCheck q = true ∧ unionCheck v = true ∧ Canonical.check c = true ∧
      unionInterpretation c = unionInterpretation q ^ unionInterpretation v := by
  constructor
  · exact power_value q v c
  · rintro ⟨hq, hv, hc, he⟩
    obtain ⟨d, hd, hdc⟩ := power_returns q v hq hv
    have hcd := Canonical.check_value_injective c d hc hdc (he.trans (power_value q v d hd).2.2.2.symm)
    rw [hcd]
    exact hd

theorem power_output_unique (q v c d : Nat) (hc : c ∈ power q v) (hd : d ∈ power q v) : c = d := by
  have hs := power_value q v c hc
  have ht := power_value q v d hd
  exact Canonical.check_value_injective c d hs.2.2.1 ht.2.2.1 (hs.2.2.2.trans ht.2.2.2.symm)

theorem power_invariant (q v q' v' c d : Nat) (hc : c ∈ power q v) (hd : d ∈ power q' v')
    (hq : unionInterpretation q = unionInterpretation q') (hv : unionInterpretation v = unionInterpretation v') : c = d := by
  have hs := power_value q v c hc
  have ht := power_value q' v' d hd
  exact Canonical.check_value_injective c d hs.2.2.1 ht.2.2.1
    (hs.2.2.2.trans (by rw [hq, hv]; exact ht.2.2.2.symm))

theorem power_below_limit (q v : Nat) (hq : unionCheck q = true) (hv : unionCheck v = true) :
    unionInterpretation q ^ unionInterpretation v < finiteBaseLimit := by
  obtain ⟨c, hc, hcc⟩ := power_returns q v hq hv
  exact (Hereditary.lt_finiteBaseLimit_iff_code _).mpr
    ⟨c, Canonical.check_original hcc, (power_value q v c hc).2.2.2⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.Powers
