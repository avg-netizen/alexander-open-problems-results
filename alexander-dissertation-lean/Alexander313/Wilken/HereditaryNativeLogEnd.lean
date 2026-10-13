import Alexander313.Wilken.HereditaryNativeLogEndSupport

/-!
# Actual last-exponent execution at every coded epsilon base

The original raw LOW input is normalized by the genuine native normalizer.
Its last positive principal atom uses the actual public logarithm when it
is a parameter. The public logarithm stays below that original payload,
so its native parameter caller is derived. A theta-zero atom with high
argument is genuinely epsilon and returns itself; a LOW argument uses the
constructed corrected low-collapse exponent. The real empty-word branch
returns the actual native zero numeral. Every original raw LOW input is
covered, with genuine LOW Normal output and the literal last-log relation.
No public-return, logarithm, atom-shape or caller oracle is assumed.
Source-only, uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.LogEnd

open ThetaCourse

def atom (q c : Nat) : Part Nat :=
  let tag := c.pred.unpair.1
  let p := c.pred.unpair.2
  cond (tag == 0) ((Hereditary.LogEnd.logend p).map OmegaPowers.parameterCode)
    (cond ((tag == 2) && (p.unpair.1 == 0))
      (cond (Decomposition.above 0 (rawTree p.unpair.2)) (Part.some c)
        (Part.some (Support.correctedCode q p.unpair.2))) Part.none)

theorem atom_partrec : Partrec₂ atom := by
  have hp := Primrec.snd.comp (Primrec.unpair.comp (Primrec.pred.comp Primrec.snd))
  have ht := Primrec.fst.comp (Primrec.unpair.comp (Primrec.pred.comp Primrec.snd))
  have ha := Primrec.snd.comp (Primrec.unpair.comp hp)
  have hl := (Hereditary.LogEnd.logend_partrec.comp hp.to_comp).map
    (OmegaPowers.parameterCode_primrec.comp Primrec.snd).to_comp.to₂
  have hh := Decomposition.above_primrec.comp (Primrec.const 0) (rawTree_primrec.comp ha)
  have hc := Support.correctedCode_primrec.comp Primrec.fst ha
  exact (Partrec.cond (Primrec.beq.comp ht (Primrec.const 0)).to_comp hl
    (Partrec.cond (Primrec.and.comp (Primrec.beq.comp ht (Primrec.const 2))
      (Primrec.beq.comp (Primrec.fst.comp (Primrec.unpair.comp hp)) (Primrec.const 0))).to_comp
      (Partrec.cond hh.to_comp Primrec.snd.to_comp hc.to_comp) Partrec.none)).to₂

@[simp] theorem atom_parameter (q p : Nat) :
    atom q (.parameter p : RelativeTerm Nat).code =
      (Hereditary.LogEnd.logend p).map OmegaPowers.parameterCode := by
  simp only [atom, code_parameter, Nat.pred_succ, Nat.unpair_pair,
    beq_self_eq_true, Bool.cond_true]

@[simp] theorem atom_theta_zero (q : Nat) (a : RelativeTerm Nat) :
    atom q (.theta 0 a).code = cond (Decomposition.above 0 a)
      (Part.some (.theta 0 a).code) (Part.some (Support.correctedCode q a.code)) := by
  simp only [atom, code_theta, Nat.pred_succ, Nat.unpair_pair, rawTree_code,
    beq_self_eq_true, Bool.cond_true, Bool.cond_false, Bool.true_and]

theorem atom_parameter_domain (q p : Nat) (ht : check q (.parameter p) = true) :
    (atom q (.parameter p : RelativeTerm Nat).code).Dom := by
  rw [atom_parameter]
  exact (Hereditary.LogEnd.logend_domain p).mpr
    ((parameterCheck_exact q p).mp (checked_admissible q _ ht).1).1

theorem atom_parameter_spec (q p out : Nat) (ht : check q (.parameter p) = true)
    (hp : 0 < denote q (.parameter p))
    (hprincipal : Ordinal.IsPrincipal (· + ·) (denote q (.parameter p)))
    (ho : out ∈ atom q (.parameter p : RelativeTerm Nat).code) :
    lowCheckCode q out = true ∧ Comparison.acceptedCode q out = true ∧
      Ordinal.omega0 ^ interpretation q out = denote q (.parameter p) := by
  rw [atom_parameter] at ho
  obtain ⟨v, hv, rfl⟩ := (Part.mem_map_iff _).mp ho
  have hs := Hereditary.LogEnd.logend_value p v hv
  have hq := (Bool.and_eq_true.mp ht).1
  have hparam := (parameterCheck_exact q p).mp (checked_admissible q _ ht).1
  have hb : parameters v < base q :=
    (Hereditary.LogEnd.componentLog_bound true p v hv).trans_lt hparam.2.2
  have hpc := (parameterCheck_exact q v).mpr
    ⟨Canonical.check_original hs.2.1, ((baseCheck_exact q).mp hq).1, hb⟩
  have hn := OmegaPowers.parameterCode_spec q v hpc hq
  refine ⟨hn.1, hn.2.1, ?_⟩
  rw [hn.2.2]
  have he : Hereditary.LogEnd.endValue (unionInterpretation p) = unionInterpretation p :=
    SourceChi.Powers.endValue_principal _ hp hprincipal
  have hvp : Ordinal.omega0 ^ unionInterpretation v =
      Hereditary.LogEnd.endValue (unionInterpretation p) := by
    simpa only [Hereditary.LogEnd.SourceLogSpec, if_neg (ne_of_gt hp),
      Hereditary.LogEnd.endValue] using hs.2.2
  exact hvp.trans he

theorem atom_theta_zero_domain (q : Nat) (a : RelativeTerm Nat) :
    (atom q (.theta 0 a).code).Dom := by
  rw [atom_theta_zero]
  cases Decomposition.above 0 a <;> simp only [Bool.cond_true, Bool.cond_false, Part.some_dom]

theorem atom_theta_zero_spec (q : Nat) (a : RelativeTerm Nat)
    (hc : lowCheckCode q (.theta 0 a).code = true)
    (hn : Comparison.acceptedCode q (.theta 0 a).code = true)
    (out : Nat) (ho : out ∈ atom q (.theta 0 a).code) :
    lowCheckCode q out = true ∧ Comparison.acceptedCode q out = true ∧
      Ordinal.omega0 ^ interpretation q out = denote q (.theta 0 a) := by
  have ht : check q (.theta 0 a) = true := by
    simpa only [checkCode_code] using (HeightBoundary.input_spec q _ hc).1
  rw [atom_theta_zero] at ho
  cases hh : Decomposition.above 0 a with
  | true =>
    have he : out = (.theta 0 a : RelativeTerm Nat).code := by
      simpa only [hh, Bool.cond_true, Part.mem_some_iff] using ho
    subst out
    refine ⟨hc, hn, ?_⟩
    rw [interpretation_code]
    exact SourceChi.Powers.theta_epsilon_of_high q a ht
      (by simpa only [Nat.zero_add] using
        (Decomposition.above_exact q 0 a (FixedPoint.checked_theta_argument q 0 a ht)).mp hh)
  | false =>
    have he : out = Support.correctedCode q a.code := by
      simpa only [hh, Bool.cond_false, Part.mem_some_iff] using ho
    subst out
    have hal := Support.theta_argument_low q a ht hh
    have hs := Support.correctedCode_spec q a.code hal
    refine ⟨hs.1, hs.2.1, ?_⟩
    rw [hs.2.2, interpretation_code]
    change Ordinal.omega0 ^ lowOmegaExponent (base q) (denote q a) =
      globalCollapse (base q) 0 (denote q a)
    exact (globalCollapse_low_eq_omegaPower (base q)
      (Or.inr (SourceChi.epsilon_base q (Bool.and_eq_true.mp ht).1)) _
      (by simpa only [interpretation_code] using (HeightBoundary.input_spec q _ hal).2.2)).symm

/-- Only shapes derived from a genuine original ANF atom enter this
internal routine; the public entry point below derives that shape itself. -/
theorem atom_domain (q c : Nat) (hc : lowCheckCode q c = true)
    (shape : (∃ p, rawTree c = .parameter p) ∨ ∃ k a, rawTree c = .theta k a) :
    (atom q c).Dom := by
  have hi := HeightBoundary.input_spec q c hc
  have he : (rawTree c).code = c := by
    obtain ⟨t, ht, hct⟩ := (checkCode_exact q c).mp hi.1
    simp only [← ht, rawTree_code]
  rcases shape with ⟨p, hp⟩ | ⟨k, a, ha⟩
  · have ht : check q (.parameter p) = true := by
      simpa only [hp] using Arithmetic.raw_checked q c hi.1
    rw [← he, hp]
    exact atom_parameter_domain q p ht
  · have hkc : (.theta k a : RelativeTerm Nat).code = c := by rw [← ha]; exact he
    have hk := Support.theta_low_index q k a (by simpa only [hkc] using hc)
    subst k
    rw [← hkc]
    exact atom_theta_zero_domain q a

theorem atom_spec (q c out : Nat) (hc : lowCheckCode q c = true)
    (hn : Comparison.acceptedCode q c = true) (hp : 0 < interpretation q c)
    (hprincipal : Ordinal.IsPrincipal (· + ·) (interpretation q c))
    (shape : (∃ p, rawTree c = .parameter p) ∨ ∃ k a, rawTree c = .theta k a)
    (ho : out ∈ atom q c) :
    lowCheckCode q out = true ∧ Comparison.acceptedCode q out = true ∧
      Ordinal.omega0 ^ interpretation q out = interpretation q c := by
  have hi := HeightBoundary.input_spec q c hc
  have he : (rawTree c).code = c := by
    obtain ⟨t, ht, hct⟩ := (checkCode_exact q c).mp hi.1
    simp only [← ht, rawTree_code]
  rcases shape with ⟨p, h⟩ | ⟨k, a, h⟩
  · have hpc : (.parameter p : RelativeTerm Nat).code = c := by rw [← h]; exact he
    have ht : check q (.parameter p) = true := by
      simpa only [h] using Arithmetic.raw_checked q c hi.1
    have hv : interpretation q c = denote q (.parameter p) := by rw [← hpc, interpretation_code]
    simpa only [hv] using atom_parameter_spec q p out ht (by simpa only [hv] using hp)
      (by simpa only [hv] using hprincipal) (by simpa only [hpc] using ho)
  · have hkc : (.theta k a : RelativeTerm Nat).code = c := by rw [← h]; exact he
    have hk := Support.theta_low_index q k a (by simpa only [hkc] using hc)
    subst k
    simpa only [← hkc, interpretation_code] using atom_theta_zero_spec q a
      (by simpa only [hkc] using hc) (by simpa only [hkc] using hn) out
      (by simpa only [hkc] using ho)

def execute (q c : Nat) : Part Nat := cond (lowCheckCode q c)
  (cond (FixedPoint.zeroCheck (Normalization.normalizeCode q c))
    (Part.some (OmegaPowerHeight.numeralCode 0))
    (atom q (LogEndZero.endCode (Normalization.normalizeCode q c)))) Part.none

theorem execute_partrec : Partrec₂ execute := by
  have hn := Normalization.Effective.normalizeCode_primrec
  have he := LogEndZero.endCode_primrec.comp hn
  exact (Partrec.cond lowCheckCode_primrec.to_comp
    (Partrec.cond (FixedPoint.zeroCheck_primrec.comp hn).to_comp
      (Computable.const (OmegaPowerHeight.numeralCode 0))
      (atom_partrec.comp Computable.fst he.to_comp)) Partrec.none).to₂

theorem normalized_low (q c : Nat) (hc : lowCheckCode q c = true) :
    lowCheckCode q (Normalization.normalizeCode q c) = true := by
  have hi := HeightBoundary.input_spec q c hc
  have hn := Normalization.normalizeCode_accepted q c hi.1
  exact OmegaPowers.low_of_bound q _ ((Comparison.acceptedCode_exact q _).mp hn.1).1
    (by rw [hn.2]; exact hi.2.2)

/-- The executing routine covers EXACTLY every original raw LOW input
at its actual coded epsilon, without an extra Normal or shape guard. -/
theorem execute_domain (q c : Nat) : (execute q c).Dom ↔ lowCheckCode q c = true := by
  cases hc : lowCheckCode q c with
  | false => simp only [execute, hc, Bool.cond_false, Part.not_none_dom, Bool.false_eq_true]
  | true =>
    have hn := Normalization.normalizeCode_accepted q c (HeightBoundary.input_spec q c hc).1
    cases hz : FixedPoint.zeroCheck (Normalization.normalizeCode q c) with
    | true => simp only [execute, hc, hz, Bool.cond_true, Part.some_dom]
    | false =>
      have hne : interpretation q (Normalization.normalizeCode q c) ≠ 0 := by
        intro h
        have ht := (FixedPoint.zeroCheck_exact q _ hn.1).mpr h
        simp only [hz, Bool.false_eq_true] at ht
      have hs := Support.endCode_spec q _ (normalized_low q c hc) hn.1 hne
      simp only [execute, hc, hz, Bool.cond_true, Bool.cond_false]
      exact iff_true_intro (atom_domain q _ hs.1 hs.2.2.2.2.2)

/-- Every real output is LOW Normal and satisfies the original literal
last-log relation, including the original logend-zero convention. -/
theorem execute_spec (q c out : Nat) (ho : out ∈ execute q c) :
    lowCheckCode q c = true ∧ lowCheckCode q out = true ∧
      Comparison.acceptedCode q out = true ∧
      Hereditary.LogEnd.SourceLogSpec true (interpretation q c) (interpretation q out) := by
  have hc := (execute_domain q c).mp (Part.dom_iff_mem.mpr ⟨out, ho⟩)
  have hi := HeightBoundary.input_spec q c hc
  have hn := Normalization.normalizeCode_accepted q c hi.1
  cases hz : FixedPoint.zeroCheck (Normalization.normalizeCode q c) with
  | true =>
    have he : out = OmegaPowerHeight.numeralCode 0 := by
      simpa only [execute, hc, hz, Bool.cond_true, Part.mem_some_iff] using ho
    subst out
    have hs := OmegaPowerHeight.numeralCode_spec q 0 hi.2.1
    have hv : interpretation q c = 0 :=
      hn.2.symm.trans ((FixedPoint.zeroCheck_exact q _ hn.1).mp hz)
    exact ⟨hc, hs.1, hs.2.1, by
      simp only [Hereditary.LogEnd.SourceLogSpec, hv, if_pos rfl, hs.2.2.1, Nat.cast_zero]⟩
  | false =>
    have hne : interpretation q (Normalization.normalizeCode q c) ≠ 0 := by
      intro h
      have ht := (FixedPoint.zeroCheck_exact q _ hn.1).mpr h
      simp only [hz, Bool.false_eq_true] at ht
    have hs := Support.endCode_spec q _ (normalized_low q c hc) hn.1 hne
    have hm : out ∈ atom q (LogEndZero.endCode (Normalization.normalizeCode q c)) := by
      simpa only [execute, hc, hz, Bool.cond_true, Bool.cond_false] using ho
    have hv := atom_spec q _ out hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.2 hm
    have hcn : interpretation q c ≠ 0 := by simpa only [hn.2] using hne
    refine ⟨hc, hv.1, hv.2.1, ?_⟩
    simp only [Hereditary.LogEnd.SourceLogSpec, if_neg hcn]
    exact hv.2.2.trans (by rw [LogEndZero.endCode_value q _ hn.1, hn.2]; rfl)

theorem execute_bound (q c out : Nat) (ho : out ∈ execute q c) :
    interpretation q out ≤ interpretation q c := by
  have hs := execute_spec q c out ho
  by_cases hz : interpretation q c = 0
  · have he : interpretation q out = 0 := by
      simpa only [Hereditary.LogEnd.SourceLogSpec, hz, if_pos rfl] using hs.2.2.2
    rw [he, hz]
  · have hn := Normalization.normalizeCode_accepted q c (HeightBoundary.input_spec q c hs.1).1
    have he := Support.endCode_spec q _ (normalized_low q c hs.1) hn.1
      (by simpa only [hn.2] using hz)
    have hp : Ordinal.omega0 ^ interpretation q out =
        interpretation q (LogEndZero.endCode (Normalization.normalizeCode q c)) := by
      rw [LogEndZero.endCode_value q _ hn.1, hn.2]
      simpa only [Hereditary.LogEnd.SourceLogSpec, if_neg hz] using hs.2.2.2
    exact ((omegaPower_self_le _).trans_eq hp).trans (by simpa only [hn.2] using he.2.2.2.2.1)

theorem execute_height (q c out : Nat) (ho : out ∈ execute q c) :
    heightCode out ≤ CanonicalHeight.canonicalHeightCode q c := by
  have hs := execute_spec q c out ho
  rw [← CanonicalHeight.canonicalHeightCode_normal q out hs.2.2.1]
  apply (HeightBoundary.canonicalHeightCode_le_iff_endpoint q _ out hs.2.1).mpr
  exact (execute_bound q c out ho).trans_lt
    ((HeightBoundary.canonicalHeightCode_le_iff_endpoint q _ c hs.1).mp le_rfl)

theorem execute_value_invariant (q c v d out other : Nat)
    (ho : out ∈ execute q c) (hp : other ∈ execute v d)
    (he : interpretation q c = interpretation v d) :
    interpretation q out = interpretation v other := by
  have hs := (execute_spec q c out ho).2.2.2
  have ht := (execute_spec v d other hp).2.2.2
  rw [← he] at ht
  by_cases hz : interpretation q c = 0
  · have h0 : interpretation q out = 0 := by
      simpa only [Hereditary.LogEnd.SourceLogSpec, if_pos hz] using hs
    have h1 : interpretation v other = 0 := by
      simpa only [Hereditary.LogEnd.SourceLogSpec, if_pos hz] using ht
    exact h0.trans h1.symm
  · apply omegaPower_strictMono.injective
    exact (show Ordinal.omega0 ^ interpretation q out = Hereditary.LogEnd.componentValue true
      (interpretation q c) by simpa only [Hereditary.LogEnd.SourceLogSpec, if_neg hz] using hs).trans
      (show Ordinal.omega0 ^ interpretation v other = Hereditary.LogEnd.componentValue true
        (interpretation q c) by simpa only [Hereditary.LogEnd.SourceLogSpec, if_neg hz] using ht).symm

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.LogEnd
