import Alexander313.Wilken.HereditaryEpsilonClassification
import Alexander313.Effective.HereditaryOrdinalFormation

/-!
# Native contexts at actual coded epsilon bases

The base is an original hereditary union code whose actual ordinal is epsilon.
Native relative terms have original union codes as atomic parameter payloads.
The real public comparison admits exactly parameters below the base; it does
not expand their public representations into the native syntax. The uniform
primitive-recursive checker derives every theta argument sort from the proved
source outer-sort law. Its denotation uses the actual relative omega sequence,
finite collapse and global collapse at the base ordinal.

Parameter coverage is derived from the existing public interval. Actual finite
notation induction and finite/global fidelity then prove complete global and
low interval coverage. Native output ordinals are not thereby recoded into the
public union. Native ordinal comparison, translation, iota and mu are not
constructed here. Syntax height is not identified with a source normal-form
height. All proof candidates are uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext

noncomputable def base (q : Nat) : Ordinal.{0} := unionInterpretation q

def baseCheck (q : Nat) : Bool := Epsilon.unionEpsilonCheck q

theorem baseCheck_primrec : Primrec baseCheck := Epsilon.unionEpsilonCheck_primrec

theorem baseCheck_exact (q : Nat) : baseCheck q = true ↔
    unionCheck q = true ∧ Ordinal.omega0 ^ base q = base q :=
  Epsilon.unionEpsilonCheck_exact q

theorem base_pos (q : Nat) (hq : baseCheck q = true) : 0 < base q := by
  have he := (baseCheck_exact q).mp hq
  rw [← he.2]
  exact Ordinal.opow_pos _ Ordinal.omega0_pos

theorem base_public_bound (q : Nat) (hq : baseCheck q = true) : base q < finiteBaseLimit :=
  (lt_finiteBaseLimit_iff_code _).mpr ⟨q, ((baseCheck_exact q).mp hq).1, rfl⟩

noncomputable def parameters (p : Nat) : Ordinal.{0} := unionInterpretation p

/-- Actual public comparison, including original admission of both codes. -/
def parameterCheck (q p : Nat) : Bool := Alexander313.HereditaryOrdinalFormation.unionLess p q

theorem parameterCheck_primrec : Primrec₂ parameterCheck :=
  (Alexander313.HereditaryOrdinalFormation.unionLess_primrec.comp Primrec.snd Primrec.fst).to₂

theorem parameterCheck_exact (q p : Nat) : parameterCheck q p = true ↔
    unionCheck p = true ∧ unionCheck q = true ∧ parameters p < base q :=
  Alexander313.HereditaryOrdinalFormation.unionLess_exact p q

theorem parameter_sound (q p : Nat) (hp : parameterCheck q p = true) : parameters p < base q :=
  ((parameterCheck_exact q p).mp hp).2.2

/-- Every ordinal below the actual coded base already has an original public code. -/
theorem parameter_complete (q : Nat) (hq : baseCheck q = true)
    (ξ : Ordinal.{0}) (hξ : ξ < base q) :
    ∃ p, parameterCheck q p = true ∧ parameters p = ξ := by
  obtain ⟨p, hp, hv⟩ := (lt_finiteBaseLimit_iff_code ξ).mp
    (hξ.trans (base_public_bound q hq))
  exact ⟨p, (parameterCheck_exact q p).mpr
    ⟨hp, ((baseCheck_exact q).mp hq).1, by simpa only [parameters, hv] using hξ⟩, hv⟩

theorem parameter_complete_canonical (q : Nat) (hq : baseCheck q = true)
    (ξ : Ordinal.{0}) (hξ : ξ < base q) :
    ∃ p, Canonical.check p = true ∧ parameterCheck q p = true ∧ parameters p = ξ := by
  obtain ⟨p, hp, hv⟩ := (Canonical.lt_finiteBaseLimit_iff_code ξ).mp
    (hξ.trans (base_public_bound q hq))
  exact ⟨p, hp, (parameterCheck_exact q p).mpr
    ⟨Canonical.check_original hp, ((baseCheck_exact q).mp hq).1,
      by simpa only [parameters, hv] using hξ⟩, hv⟩

noncomputable def denote (q : Nat) (t : RelativeTerm Nat) : Ordinal.{0} :=
  t.eval parameters (globalCollapse (base q))

noncomputable def finiteDenote (q n : Nat) (t : RelativeTerm Nat) : Ordinal.{0} :=
  t.eval parameters (sourceFiniteCollapse (base q) n)

noncomputable def interpretation (q c : Nat) : Ordinal.{0} :=
  denote q ((decode c).getD (.parameter 0))

@[simp] theorem interpretation_code (q : Nat) (t : RelativeTerm Nat) :
    interpretation q t.code = denote q t := by
  simp only [interpretation, decode_code, Option.getD_some]

/-- Represented atomic payloads; rejected public codes never inherit their default value. -/
def Payloads (q : Nat) : RelativeTerm Nat → Prop
  | .parameter p => parameterCheck q p = true
  | .sum a b => Payloads q a ∧ Payloads q b
  | .theta _ a => Payloads q a

theorem payloads_iff_parameters (q : Nat) (t : RelativeTerm Nat) :
    Payloads q t ↔ ∀ p ∈ t.parameters, parameterCheck q p = true := by
  induction t with
  | parameter p => simp [Payloads, RelativeTerm.parameters]
  | sum a b iha ihb =>
    simp only [Payloads, RelativeTerm.parameters, Finset.mem_union, iha, ihb]
    constructor
    · rintro ⟨ha, hb⟩ p (hp | hp)
      · exact ha p hp
      · exact hb p hp
    · intro h
      exact ⟨fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩
  | theta k a ih => exact ih

def admissible (q n : Nat) (t : RelativeTerm Nat) : Prop :=
  Payloads q t ∧ Admissible parameters (omegaSequence (base q))
    (sourceFiniteCollapse (base q) n) n 0 t

def parameterState (context : Nat × Nat) (p : Nat) : Bool × Nat :=
  (parameterCheck context.1 p, 0)

def thetaState (context : Nat × Nat) (k : Nat) (a : Bool × Nat) : Bool × Nat :=
  SourceOne.thetaState context.2 k a

def stateCode (context : Nat × Nat) (c : Nat) : Bool × Nat :=
  ValueFold.code parameterState SourceOne.sumState thetaState (false, 0) context c

def state (context : Nat × Nat) (t : RelativeTerm Nat) : Bool × Nat :=
  ValueFold.term parameterState SourceOne.sumState thetaState context t

theorem parameterState_primrec : Primrec₂ parameterState :=
  ((parameterCheck_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).pair
    (Primrec.const 0)).to₂

theorem thetaState_primrec :
    Primrec (fun p : (Nat × Nat) × (Nat × (Bool × Nat)) => thetaState p.1 p.2.1 p.2.2) :=
  SourceOne.thetaState_primrec.comp
    ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)

theorem stateCode_primrec : Primrec₂ stateCode :=
  ValueFold.code_primrec parameterState SourceOne.sumState thetaState (false, 0)
    parameterState_primrec SourceOne.sumState_primrec thetaState_primrec

theorem state_primrec : Primrec₂ state :=
  ValueFold.term_primrec parameterState SourceOne.sumState thetaState (false, 0)
    parameterState_primrec SourceOne.sumState_primrec thetaState_primrec

@[simp] theorem stateCode_code (q n : Nat) (t : RelativeTerm Nat) :
    stateCode (q, n) t.code = state (q, n) t :=
  ValueFold.code_term parameterState SourceOne.sumState thetaState (false, 0) (q, n) t

@[simp] theorem state_sort (q n : Nat) (t : RelativeTerm Nat) :
    (state (q, n) t).2 = t.outerSort := by
  induction t <;> simp_all [state, ValueFold.term, parameterState, thetaState,
    SourceOne.sumState, SourceOne.thetaState, outerSort]

def finiteCheck (q n : Nat) (t : RelativeTerm Nat) : Bool := (state (q, n) t).1

@[simp] theorem finiteCheck_parameter (q n p : Nat) :
    finiteCheck q n (.parameter p) = parameterCheck q p := rfl

@[simp] theorem finiteCheck_sum (q n : Nat) (a b : RelativeTerm Nat) :
    finiteCheck q n (.sum a b) = (finiteCheck q n a && finiteCheck q n b) := rfl

@[simp] theorem finiteCheck_theta (q n k : Nat) (a : RelativeTerm Nat) :
    finiteCheck q n (.theta k a) =
      ((finiteCheck q n a && decide (k < n)) && decide (a.outerSort ≤ k + 2)) := by
  change ((finiteCheck q n a && decide (k < n)) && decide ((state (q, n) a).2 ≤ k + 2)) = _
  rw [state_sort]

theorem finiteCheck_primrec :
    Primrec (fun p : (Nat × Nat) × RelativeTerm Nat => finiteCheck p.1.1 p.1.2 p.2) :=
  Primrec.fst.comp state_primrec

theorem finiteCheck_exact (q n : Nat) (t : RelativeTerm Nat) :
    finiteCheck q n t = true ↔ admissible q n t := by
  induction t with
  | parameter p =>
    constructor
    · intro hp
      exact ⟨hp, .parameter (by simpa only [omegaSequence_zero] using parameter_sound q p hp)⟩
    · rintro ⟨hp, ha⟩; exact hp
  | sum a b iha ihb =>
    constructor
    · intro hc
      have hs := Bool.and_eq_true_iff.mp hc
      have ha := iha.mp hs.1
      have hb := ihb.mp hs.2
      exact ⟨⟨ha.1, hb.1⟩, .sum ha.2 hb.2⟩
    · rintro ⟨hp, ha⟩
      cases ha with
      | sum ha hb =>
        simp only [finiteCheck_sum, iha.mpr ⟨hp.1, ha⟩, ihb.mpr ⟨hp.2, hb⟩, Bool.true_and]
  | theta k a ih =>
    constructor
    · intro hc
      have hs : finiteCheck q n a = true ∧ k < n ∧ a.outerSort ≤ k + 2 := by
        simpa only [finiteCheck_theta, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using hc
      have ha := ih.mp hs.1
      exact ⟨ha.1, .theta (Nat.zero_le k) hs.2.1
        ((source_eval_lt_iff_outerSort_le (base q) parameters n a ha.2 (k + 2)
          (by omega)).mpr hs.2.2) ha.2⟩
    · rintro ⟨hp, ha⟩
      cases ha with
      | theta h0k hkn hsort ha =>
        have hs := (source_eval_lt_iff_outerSort_le (base q) parameters n a ha
          (k + 2) (by omega)).mp hsort
        simp only [finiteCheck_theta, ih.mpr ⟨hp, ha⟩, hkn, hs, decide_true, Bool.true_and]

def finiteCheckCode (q n c : Nat) : Bool := isCode c && (stateCode (q, n) c).1

theorem finiteCheckCode_primrec :
    Primrec (fun p : (Nat × Nat) × Nat => finiteCheckCode p.1.1 p.1.2 p.2) :=
  Primrec.and.comp (isCode_primrec.comp Primrec.snd) (Primrec.fst.comp stateCode_primrec)

@[simp] theorem finiteCheckCode_code (q n : Nat) (t : RelativeTerm Nat) :
    finiteCheckCode q n t.code = finiteCheck q n t := by
  simp only [finiteCheckCode, isCode_code, stateCode_code, Bool.true_and, finiteCheck]

theorem finiteCheckCode_exact (q n c : Nat) : finiteCheckCode q n c = true ↔
    ∃ t : RelativeTerm Nat, t.code = c ∧ admissible q n t := by
  constructor
  · intro hc
    have hs := Bool.and_eq_true_iff.mp hc
    obtain ⟨t, ht⟩ := isCode_sound c hs.1
    refine ⟨t, ht, (finiteCheck_exact q n t).mp ?_⟩
    simpa only [← ht, stateCode_code, finiteCheck] using hs.2
  · rintro ⟨t, rfl, ht⟩
    rw [finiteCheckCode_code]
    exact (finiteCheck_exact q n t).mpr ht

theorem finiteCheck_transfer (q n : Nat) (t : RelativeTerm Nat)
    (ht : finiteCheck q n t = true) (n' : Nat) (hheight : t.height ≤ n') :
    finiteCheck q n' t = true := by
  induction t generalizing n n' with
  | parameter p => exact ht
  | sum a b iha ihb =>
    have hs := Bool.and_eq_true_iff.mp ht
    have ha := (le_max_left a.height b.height).trans hheight
    have hb := (le_max_right a.height b.height).trans hheight
    simp only [finiteCheck_sum, iha n hs.1 n' ha, ihb n hs.2 n' hb, Bool.true_and]
  | theta k a ih =>
    have hs : finiteCheck q n a = true ∧ k < n ∧ a.outerSort ≤ k + 2 := by
      simpa only [finiteCheck_theta, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using ht
    have ha := (le_max_right (k + 1) a.height).trans hheight
    have hk : k < n' := by
      have hk' := (le_max_left (k + 1) a.height).trans hheight
      omega
    simp only [finiteCheck_theta, ih n hs.1 n' ha, hk, hs.2.2, decide_true, Bool.true_and]

def check (q : Nat) (t : RelativeTerm Nat) : Bool :=
  baseCheck q && finiteCheck q (SourceOne.PublicCodes.fragment t) t

def checkCode (q c : Nat) : Bool := baseCheck q && finiteCheckCode q (heightCode c + 1) c

theorem check_primrec : Primrec₂ check := by
  have hf := finiteCheck_primrec.comp
    ((Primrec.fst.pair (SourceOne.PublicCodes.fragment_primrec.comp Primrec.snd)).pair Primrec.snd)
  exact (Primrec.and.comp (baseCheck_primrec.comp Primrec.fst) hf).to₂

theorem checkCode_primrec : Primrec₂ checkCode := by
  have hf := finiteCheckCode_primrec.comp
    ((Primrec.fst.pair (Primrec.succ.comp (heightCode_primrec.comp Primrec.snd))).pair Primrec.snd)
  exact (Primrec.and.comp (baseCheck_primrec.comp Primrec.fst) hf).to₂

@[simp] theorem checkCode_code (q : Nat) (t : RelativeTerm Nat) : checkCode q t.code = check q t := by
  simp only [checkCode, heightCode_code, finiteCheckCode_code, check, SourceOne.PublicCodes.fragment]

theorem check_exact (q : Nat) (t : RelativeTerm Nat) : check q t = true ↔
    baseCheck q = true ∧ ∃ n, admissible q n t := by
  constructor
  · intro ht
    have hs := Bool.and_eq_true_iff.mp ht
    exact ⟨hs.1, SourceOne.PublicCodes.fragment t,
      (finiteCheck_exact q _ t).mp hs.2⟩
  · rintro ⟨hq, n, hn⟩
    have hc := finiteCheck_transfer q n t ((finiteCheck_exact q n t).mpr hn)
      (SourceOne.PublicCodes.fragment t) (SourceOne.PublicCodes.height_le_fragment t)
    simp only [check, hq, hc, Bool.true_and]

theorem checkCode_exact (q c : Nat) : checkCode q c = true ↔
    ∃ t : RelativeTerm Nat, t.code = c ∧ check q t = true := by
  constructor
  · intro hc
    have hs := Bool.and_eq_true_iff.mp hc
    obtain ⟨t, ht, ha⟩ := (finiteCheckCode_exact q _ c).mp hs.2
    refine ⟨t, ht, (check_exact q t).mpr ⟨hs.1, _, ha⟩⟩
  · rintro ⟨t, rfl, ht⟩; simpa only [checkCode_code] using ht

theorem checked_admissible (q : Nat) (t : RelativeTerm Nat) (ht : check q t = true) :
    admissible q (SourceOne.PublicCodes.fragment t) t :=
  (finiteCheck_exact q _ t).mp (Bool.and_eq_true_iff.mp ht).2

/-- Finite/global agreement at every genuine theta call; no outside-domain default is used. -/
theorem denote_eq_finite (q n : Nat) (hq : baseCheck q = true) (t : RelativeTerm Nat)
    (ht : Admissible parameters (omegaSequence (base q)) (sourceFiniteCollapse (base q) n) n 0 t) :
    denote q t = finiteDenote q n t := by
  induction ht with
  | parameter hp => rfl
  | @sum a b ha hb iha ihb =>
    change denote q a + denote q b = finiteDenote q n a + finiteDenote q n b
    rw [iha, ihb]
  | @theta k a h0k hkn hsort ha ih =>
    change globalCollapse (base q) k (denote q a) =
      sourceFiniteCollapse (base q) n k (finiteDenote q n a)
    rw [ih]
    have hn : 0 < n := by omega
    have hnotation : sourceNotation (base q) n 0 (finiteDenote q n a) := by
      rw [sourceNotation, if_pos hn]
      exact ha.denote
    have hb := source_finite_collapse_argument_lt_boundary (base q) (base_pos q hq)
      n 0 k h0k hkn hnotation hsort
    exact globalCollapse_finite_agreement (base q) (base_pos q hq) n k hkn _ hb

theorem checked_globalNotation (q : Nat) (t : RelativeTerm Nat) (ht : check q t = true) :
    GlobalNotation (base q) 0 (denote q t) := by
  have hq := (Bool.and_eq_true_iff.mp ht).1
  have ha := checked_admissible q t ht
  rw [denote_eq_finite q _ hq t ha.2]
  apply sourceNotation_to_globalNotation (base q) (base_pos q hq)
    (SourceOne.PublicCodes.fragment t) 0 (SourceOne.PublicCodes.fragment_pos t)
  rw [sourceNotation, if_pos (SourceOne.PublicCodes.fragment_pos t)]
  exact ha.2.denote

theorem denote_lt_iff_outerSort_le (q : Nat) (t : RelativeTerm Nat) (ht : check q t = true)
    (k : Nat) (hk : 0 < k) : denote q t < omegaSequence (base q) k ↔ t.outerSort ≤ k := by
  have ha := checked_admissible q t ht
  rw [denote_eq_finite q _ (Bool.and_eq_true_iff.mp ht).1 t ha.2]
  exact source_eval_lt_iff_outerSort_le (base q) parameters _ t ha.2 k hk

theorem checked_parameters (q : Nat) (t : RelativeTerm Nat) (ht : check q t = true)
    (p : Nat) (hp : p ∈ t.parameters) :
    unionCheck p = true ∧ parameters p < base q := by
  have hc := (payloads_iff_parameters q t).mp (checked_admissible q t ht).1 p hp
  have hs := (parameterCheck_exact q p).mp hc
  exact ⟨hs.1, hs.2.2⟩

/-- The actual argument supplied to each checked finite theta is in the
finite source argument domain, and hence in the genuine global-call domain. -/
theorem checked_argument_domain (q n k : Nat) (hq : baseCheck q = true)
    (a : RelativeTerm Nat) (ht : finiteCheck q n (.theta k a) = true) :
    denote q a < finiteBoundary (base q) n (k + 1) ∧
      denote q a < globalBoundary (base q) (k + 1) := by
  have ha := ((finiteCheck_exact q n (.theta k a)).mp ht).2
  cases ha with
  | theta h0k hkn hsort ha =>
    have hn : 0 < n := by omega
    have hs : sourceNotation (base q) n 0 (finiteDenote q n a) := by
      rw [sourceNotation, if_pos hn]
      exact ha.denote
    have hb := source_finite_collapse_argument_lt_boundary (base q) (base_pos q hq)
      n 0 k h0k hkn hs hsort
    have hg := sourceNotation_to_globalNotation (base q) (base_pos q hq) n 0 hn hs
    rw [denote_eq_finite q n hq a ha]
    exact ⟨hb, globalNotation_sorted_lt_boundary (base q) (base_pos q hq) 0 k h0k hg hsort⟩

theorem sourceNotation_iff_checked (q : Nat) (hq : baseCheck q = true)
    (n : Nat) (hn : 0 < n) (ξ : Ordinal.{0}) : sourceNotation (base q) n 0 ξ ↔
    ∃ t : RelativeTerm Nat, admissible q n t ∧ finiteDenote q n t = ξ := by
  rw [sourceNotation, if_pos hn]
  constructor
  · intro hξ
    induction hξ with
    | @parameter ξ hp =>
      obtain ⟨p, hcp, hv⟩ := parameter_complete q hq ξ
        (by simpa only [omegaSequence_zero] using hp)
      refine ⟨.parameter p, ⟨hcp, .parameter ?_⟩, hv⟩
      simpa only [hv] using hp
    | add ha hb iha ihb =>
      obtain ⟨a, ha, hva⟩ := iha
      obtain ⟨b, hb, hvb⟩ := ihb
      refine ⟨.sum a b, ⟨⟨ha.1, hb.1⟩, .sum ha.2 hb.2⟩, ?_⟩
      change finiteDenote q n a + finiteDenote q n b = _
      rw [hva, hvb]
    | @collapse k ξ h0k hkn hsmall hξ ih =>
      obtain ⟨a, ha, hv⟩ := ih
      refine ⟨.theta k a, ⟨ha.1, .theta h0k hkn ?_ ha.2⟩, ?_⟩
      · change finiteDenote q n a < omegaSequence (base q) (k + 2)
        rw [hv]; exact hsmall
      · change sourceFiniteCollapse (base q) n k (finiteDenote q n a) = _
        rw [hv]
  · rintro ⟨t, ht, rfl⟩; exact ht.2.denote

theorem globalNotation_iff_checked (q : Nat) (hq : baseCheck q = true) (ξ : Ordinal.{0}) :
    GlobalNotation (base q) 0 ξ ↔ ∃ t : RelativeTerm Nat, check q t = true ∧ denote q t = ξ := by
  constructor
  · intro hξ
    obtain ⟨n, hn, hfinite⟩ := globalNotation_finite_witness (base q) (base_pos q hq) 0 hξ
    obtain ⟨t, ht, hv⟩ := (sourceNotation_iff_checked q hq n hn ξ).mp hfinite
    exact ⟨t, (check_exact q t).mpr ⟨hq, n, ht⟩, (denote_eq_finite q n hq t ht.2).trans hv⟩
  · rintro ⟨t, ht, rfl⟩; exact checked_globalNotation q t ht

theorem globalNotation_iff_code (q : Nat) (hq : baseCheck q = true) (ξ : Ordinal.{0}) :
    GlobalNotation (base q) 0 ξ ↔ ∃ c, checkCode q c = true ∧ interpretation q c = ξ := by
  rw [globalNotation_iff_checked q hq ξ]
  constructor
  · rintro ⟨t, ht, hv⟩
    exact ⟨t.code, by simpa only [checkCode_code] using ht,
      by simpa only [interpretation_code] using hv⟩
  · rintro ⟨c, hc, hv⟩
    obtain ⟨t, ht, hct⟩ := (checkCode_exact q c).mp hc
    exact ⟨t, hct, by simpa only [← ht, interpretation_code] using hv⟩

def lowCheck (q : Nat) (t : RelativeTerm Nat) : Bool := check q t && decide (t.outerSort ≤ 1)

def lowCheckCode (q c : Nat) : Bool :=
  checkCode q c && decide (SourceOne.PublicCodes.outerSortCode c ≤ 1)

theorem lowCheck_primrec : Primrec₂ lowCheck :=
  (Primrec.and.comp check_primrec
    ((Primrec.nat_le.comp (outerSort_primrec.comp Primrec.snd) (Primrec.const 1)).decide)).to₂

theorem lowCheckCode_primrec : Primrec₂ lowCheckCode :=
  (Primrec.and.comp checkCode_primrec
    ((Primrec.nat_le.comp (SourceOne.PublicCodes.outerSortCode_primrec.comp Primrec.snd)
      (Primrec.const 1)).decide)).to₂

@[simp] theorem lowCheckCode_code (q : Nat) (t : RelativeTerm Nat) :
    lowCheckCode q t.code = lowCheck q t := by
  simp only [lowCheckCode, lowCheck, checkCode_code, SourceOne.PublicCodes.outerSortCode_code]

theorem lowCheckCode_exact (q c : Nat) : lowCheckCode q c = true ↔
    ∃ t : RelativeTerm Nat, t.code = c ∧ lowCheck q t = true := by
  constructor
  · intro hc
    have hs := Bool.and_eq_true_iff.mp hc
    obtain ⟨t, ht, hct⟩ := (checkCode_exact q c).mp hs.1
    refine ⟨t, ht, ?_⟩
    simpa only [← ht, lowCheckCode_code] using hc
  · rintro ⟨t, rfl, ht⟩; simpa only [lowCheckCode_code] using ht

theorem lt_boundary_iff_checked (q : Nat) (hq : baseCheck q = true) (ξ : Ordinal.{0}) :
    ξ < globalBoundary (base q) 0 ↔ ∃ t : RelativeTerm Nat, lowCheck q t = true ∧ denote q t = ξ := by
  rw [← globalNotation_low_iff_lt_boundary (base q) (base_pos q hq) 0 ξ]
  constructor
  · rintro ⟨hξ, hsmall⟩
    obtain ⟨t, ht, hv⟩ := (globalNotation_iff_checked q hq ξ).mp hξ
    have hs : t.outerSort ≤ 1 := (denote_lt_iff_outerSort_le q t ht 1 (by omega)).mp
      (by simpa only [hv] using hsmall)
    exact ⟨t, by simp only [lowCheck, ht, hs, decide_true, Bool.true_and], hv⟩
  · rintro ⟨t, ht, rfl⟩
    have hs : check q t = true ∧ t.outerSort ≤ 1 := by
      simpa only [lowCheck, Bool.and_eq_true, decide_eq_true_eq] using ht
    exact ⟨checked_globalNotation q t hs.1,
      (denote_lt_iff_outerSort_le q t hs.1 1 (by omega)).mpr hs.2⟩

theorem lt_boundary_iff_code (q : Nat) (hq : baseCheck q = true) (ξ : Ordinal.{0}) :
    ξ < globalBoundary (base q) 0 ↔ ∃ c, lowCheckCode q c = true ∧ interpretation q c = ξ := by
  rw [lt_boundary_iff_checked q hq ξ]
  constructor
  · rintro ⟨t, ht, hv⟩
    exact ⟨t.code, by simpa only [lowCheckCode_code] using ht,
      by simpa only [interpretation_code] using hv⟩
  · rintro ⟨c, hc, hv⟩
    obtain ⟨t, ht, hct⟩ := (lowCheckCode_exact q c).mp hc
    exact ⟨t, hct, by simpa only [← ht, interpretation_code] using hv⟩

theorem checked_low_bound (q c : Nat) (hc : lowCheckCode q c = true) :
    interpretation q c < globalBoundary (base q) 0 := by
  have hg := (Bool.and_eq_true_iff.mp hc).1
  have hq := (Bool.and_eq_true_iff.mp hg).1
  exact (lt_boundary_iff_code q hq _).mpr ⟨c, hc, rfl⟩

theorem checkCode_invalid_base (q c : Nat) (hq : baseCheck q = false) : checkCode q c = false := by
  simp only [checkCode, hq, Bool.false_and]

theorem checkCode_malformed (q c : Nat) (hc : isCode c = false) : checkCode q c = false := by
  simp only [checkCode, finiteCheckCode, hc, Bool.false_and, Bool.and_false]

theorem checkCode_rejected_payload (q : Nat) (t : RelativeTerm Nat) (p : Nat)
    (hp : p ∈ t.parameters) (hbad : unionCheck p = false) : checkCode q t.code = false := by
  cases hc : checkCode q t.code with
  | false => rfl
  | true =>
    have ht : check q t = true := by simpa only [checkCode_code] using hc
    have hv := (checked_parameters q t ht p hp).1
    rw [hbad] at hv
    cases hv

/-- Changing only an admitted public spelling of the same epsilon base
does not change any literal native parameter admission. -/
theorem parameterCheck_invariant (q v p : Nat) (hq : baseCheck q = true)
    (hv : baseCheck v = true) (he : base q = base v) : parameterCheck q p = parameterCheck v p := by
  apply Bool.eq_iff_iff.mpr
  simp only [parameterCheck_exact, ((baseCheck_exact q).mp hq).1,
    ((baseCheck_exact v).mp hv).1, he, true_and]

theorem finiteCheck_invariant (q v n : Nat) (hq : baseCheck q = true)
    (hv : baseCheck v = true) (he : base q = base v) (t : RelativeTerm Nat) :
    finiteCheck q n t = finiteCheck v n t := by
  induction t with
  | parameter p => exact parameterCheck_invariant q v p hq hv he
  | sum a b iha ihb => simp only [finiteCheck_sum, iha, ihb]
  | theta k a ih => simp only [finiteCheck_theta, ih]

theorem finiteCheckCode_invariant (q v n c : Nat) (hq : baseCheck q = true)
    (hv : baseCheck v = true) (he : base q = base v) : finiteCheckCode q n c = finiteCheckCode v n c := by
  cases hc : isCode c with
  | false => simp only [finiteCheckCode, hc, Bool.false_and]
  | true =>
    obtain ⟨t, ht⟩ := isCode_sound c hc
    rw [← ht, finiteCheckCode_code, finiteCheckCode_code]
    exact finiteCheck_invariant q v n hq hv he t

theorem checkCode_invariant (q v c : Nat) (hq : baseCheck q = true)
    (hv : baseCheck v = true) (he : base q = base v) : checkCode q c = checkCode v c := by
  simp only [checkCode, hq, hv, Bool.true_and]
  exact finiteCheckCode_invariant q v _ c hq hv he

theorem lowCheckCode_invariant (q v c : Nat) (hq : baseCheck q = true)
    (hv : baseCheck v = true) (he : base q = base v) : lowCheckCode q c = lowCheckCode v c := by
  simp only [lowCheckCode, checkCode_invariant q v c hq hv he]

theorem denote_invariant (q v : Nat) (he : base q = base v) (t : RelativeTerm Nat) :
    denote q t = denote v t := by
  simp only [denote, he]

theorem finiteDenote_invariant (q v n : Nat) (he : base q = base v) (t : RelativeTerm Nat) :
    finiteDenote q n t = finiteDenote v n t := by
  simp only [finiteDenote, he]

theorem interpretation_invariant (q v c : Nat) (he : base q = base v) :
    interpretation q c = interpretation v c :=
  denote_invariant q v he _

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext
