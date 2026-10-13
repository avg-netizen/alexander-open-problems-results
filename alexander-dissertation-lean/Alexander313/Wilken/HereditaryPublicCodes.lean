import Alexander313.Wilken.HereditaryCodeGrammar

/-!
# Actual finite hereditary low intervals

`finiteBase 0 = 1` and `finiteBase (r+1) = globalBoundary (finiteBase r) 0`.
Every base is positive and strictly increases. This is a sequence starting
at one, not the prescribed sequence υ with υ₀=0. No υ-index identification
is asserted here.

At level `r+1` a parameter payload is a low accepted numerical tree code at
level `r`, and its denotation is that earlier tree's actual global source
denotation. The inductive coverage proof below constructs representations
of all parameters, rather than assuming a coverage oracle. Admission uses
the actual finite source `Admissible` predicate and the proved outer-sort
law. Finite/global fidelity proves every legitimate global call is inside
its actual source domain.

Consequently the literal checker covers every existing `GlobalNotation`
at each base and exactly every ordinal below the next actual boundary.
Codes are noncanonical, and denotation remains noncomputable. The lower
endpoint test for an individual block is still stated semantically.
There is no uniform-in-level primitive-recursiveness claim, no ordinal
comparison/normalization procedure, and no tracking or R₁/R₂ algorithm.
The final tagged checker describes the entire finite-level union below
its actual supremum; a uniform `Program` recognizing it is not asserted.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary

noncomputable def finiteBase : Nat → Ordinal.{0}
  | 0 => 1
  | r + 1 => globalBoundary (finiteBase r) 0

@[simp] theorem finiteBase_zero : finiteBase 0 = 1 := rfl

@[simp] theorem finiteBase_succ (r : Nat) :
    finiteBase (r + 1) = globalBoundary (finiteBase r) 0 := rfl

theorem finiteBase_pos (r : Nat) : 0 < finiteBase r := by
  induction r with
  | zero => simp only [finiteBase_zero]; exact zero_lt_one
  | succ r ih =>
    have h := globalBoundary_base_lt (finiteBase r) ih 0
    exact ih.trans (by simpa only [omegaSequence_zero, finiteBase_succ] using h)

theorem finiteBase_step (r : Nat) : finiteBase r < finiteBase (r + 1) := by
  simpa only [omegaSequence_zero, finiteBase_succ] using
    globalBoundary_base_lt (finiteBase r) (finiteBase_pos r) 0

theorem finiteBase_lt_cardinal (r : Nat) :
    finiteBase (r + 1) < omegaSequence (finiteBase r) 1 :=
  globalBoundary_lt_cardinal (finiteBase r) (finiteBase_pos r) 0

/-- Rejected numerical payloads have an auxiliary default interpretation.
    Every public coverage and admission statement checks the literal image. -/
noncomputable def interpretation : Nat → Nat → Ordinal.{0}
  | 0, c =>
      ((RelativeTerm.decode c).getD (.parameter 0)).eval SourceOne.parameters (globalCollapse 1)
  | r + 1, c =>
      ((RelativeTerm.decode c).getD (.parameter 0)).eval (interpretation r)
        (globalCollapse (finiteBase (r + 1)))

noncomputable def parameters : Nat → Nat → Ordinal.{0}
  | 0, p => SourceOne.parameters p
  | r + 1, p => interpretation r p

noncomputable def denote (r : Nat) (t : RelativeTerm Nat) : Ordinal.{0} :=
  t.eval (parameters r) (globalCollapse (finiteBase r))

noncomputable def finiteDenote (r n : Nat) (t : RelativeTerm Nat) : Ordinal.{0} :=
  t.eval (parameters r) (sourceFiniteCollapse (finiteBase r) n)

@[simp] theorem parameters_zero (p : Nat) : parameters 0 p = SourceOne.parameters p := rfl

@[simp] theorem parameters_succ (r p : Nat) : parameters (r + 1) p = interpretation r p := rfl

@[simp] theorem interpretation_code (r : Nat) (t : RelativeTerm Nat) :
    interpretation r t.code = denote r t := by
  cases r <;> simp only [interpretation, RelativeTerm.decode_code, Option.getD_some,
    denote, finiteBase_zero] <;> rfl

@[simp] theorem denote_zero (t : RelativeTerm Nat) :
    denote 0 t = SourceOne.PublicCodes.denote t := rfl

@[simp] theorem interpretation_zero (c : Nat) :
    interpretation 0 c = SourceOne.PublicCodes.interpretation c := rfl

/-- Every literal parameter payload is recursively represented. This extra
    condition excludes rejected codes whose auxiliary interpretation is zero. -/
def Payloads (r : Nat) : RelativeTerm Nat → Prop
  | .parameter p => parameterCheck r p = true
  | .sum a b => Payloads r a ∧ Payloads r b
  | .theta _ a => Payloads r a

theorem payloads_iff_parameters (r : Nat) (t : RelativeTerm Nat) :
    Payloads r t ↔ ∀ p ∈ t.parameters, parameterCheck r p = true := by
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

/-- Actual finite source admission together with represented payloads. -/
def admissible (r n : Nat) (t : RelativeTerm Nat) : Prop :=
  Payloads r t ∧
    Admissible (parameters r) (omegaSequence (finiteBase r))
      (sourceFiniteCollapse (finiteBase r) n) n 0 t

/-- Every source call in an admitted tree agrees with a genuine finite
    source call. The total global function's outside-domain default is unused. -/
theorem denote_eq_finite (r n : Nat) (t : RelativeTerm Nat)
    (ht : Admissible (parameters r) (omegaSequence (finiteBase r))
      (sourceFiniteCollapse (finiteBase r) n) n 0 t) :
    denote r t = finiteDenote r n t := by
  induction ht with
  | parameter hp => rfl
  | @sum a b ha hb iha ihb =>
    change denote r a + denote r b = finiteDenote r n a + finiteDenote r n b
    rw [iha, ihb]
  | @theta k a h0k hkn hsort ha ih =>
    change globalCollapse (finiteBase r) k (denote r a) =
      sourceFiniteCollapse (finiteBase r) n k (finiteDenote r n a)
    rw [ih]
    have hn : 0 < n := by omega
    have hnotation : sourceNotation (finiteBase r) n 0 (finiteDenote r n a) := by
      rw [sourceNotation, if_pos hn]
      exact ha.denote
    have hbound := source_finite_collapse_argument_lt_boundary (finiteBase r)
      (finiteBase_pos r) n 0 k h0k hkn hnotation hsort
    exact globalCollapse_finite_agreement (finiteBase r) (finiteBase_pos r) n k hkn _ hbound

private structure LevelFacts (r : Nat) : Prop where
  parameter_sound : ∀ p, parameterCheck r p = true → parameters r p < finiteBase r
  parameter_complete : ∀ ξ, ξ < finiteBase r →
    ∃ p, parameterCheck r p = true ∧ parameters r p = ξ
  finite_exact : ∀ n t, finiteCheck r n t = true ↔ admissible r n t
  global_exact : ∀ ξ, GlobalNotation (finiteBase r) 0 ξ ↔
    ∃ t : RelativeTerm Nat, check r t = true ∧ denote r t = ξ
  low_exact : ∀ ξ, ξ < finiteBase (r + 1) ↔
    ∃ c : Nat, lowCheckCode r c = true ∧ interpretation r c = ξ

/-- Internal induction step. Its two premises are proved from the preceding
    literal level below; no exported theorem assumes parameter coverage. -/
private theorem buildLevel (r : Nat)
    (hsound : ∀ p, parameterCheck r p = true → parameters r p < finiteBase r)
    (hcomplete : ∀ ξ, ξ < finiteBase r →
      ∃ p, parameterCheck r p = true ∧ parameters r p = ξ) : LevelFacts r := by
  have hfinite : ∀ n t, finiteCheck r n t = true ↔ admissible r n t := by
    intro n t
    induction t with
    | parameter p =>
      constructor
      · intro hc
        have hp : parameterCheck r p = true := by
          simpa only [finiteCheck_parameter] using hc
        exact ⟨hp, .parameter (by simpa only [omegaSequence_zero] using hsound p hp)⟩
      · rintro ⟨hp, ha⟩
        exact hp
    | sum a b iha ihb =>
      constructor
      · intro hc
        have hs : finiteCheck r n a = true ∧ finiteCheck r n b = true := by
          simpa only [finiteCheck_sum, Bool.and_eq_true] using hc
        have ha := iha.mp hs.1
        have hb := ihb.mp hs.2
        exact ⟨⟨ha.1, hb.1⟩, .sum ha.2 hb.2⟩
      · rintro ⟨hp, ha⟩
        cases ha with
        | sum ha hb =>
          have hca := iha.mpr ⟨hp.1, ha⟩
          have hcb := ihb.mpr ⟨hp.2, hb⟩
          simp only [finiteCheck_sum, hca, hcb, Bool.true_and]
    | theta k a ih =>
      constructor
      · intro hc
        have hs : finiteCheck r n a = true ∧ k < n ∧ a.outerSort ≤ k + 2 := by
          simpa only [finiteCheck_theta, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using hc
        have ha := ih.mp hs.1
        have hsort := (source_eval_lt_iff_outerSort_le (finiteBase r) (parameters r)
          n a ha.2 (k + 2) (by omega)).mpr hs.2.2
        exact ⟨ha.1, .theta (Nat.zero_le k) hs.2.1 hsort ha.2⟩
      · rintro ⟨hp, ha⟩
        cases ha with
        | theta h0k hkn hsort ha =>
          have hc := ih.mpr ⟨hp, ha⟩
          have hs := (source_eval_lt_iff_outerSort_le (finiteBase r) (parameters r)
            n a ha (k + 2) (by omega)).mp hsort
          simp only [finiteCheck_theta, hc, hkn, hs, decide_true, Bool.true_and]
  have hcheck : ∀ t, check r t = true ↔ ∃ n, admissible r n t := by
    intro t
    constructor
    · intro h
      exact ⟨SourceOne.PublicCodes.fragment t, (hfinite _ t).mp h⟩
    · rintro ⟨n, h⟩
      exact finiteCheck_transfer r n t ((hfinite n t).mpr h)
        (SourceOne.PublicCodes.fragment t) (SourceOne.PublicCodes.height_le_fragment t)
  have hchecked : ∀ t, check r t = true → GlobalNotation (finiteBase r) 0 (denote r t) := by
    intro t ht
    have ha := (hfinite (SourceOne.PublicCodes.fragment t) t).mp ht
    rw [denote_eq_finite r (SourceOne.PublicCodes.fragment t) t ha.2]
    apply sourceNotation_to_globalNotation (finiteBase r) (finiteBase_pos r)
      (SourceOne.PublicCodes.fragment t) 0 (SourceOne.PublicCodes.fragment_pos t)
    rw [sourceNotation, if_pos (SourceOne.PublicCodes.fragment_pos t)]
    exact ha.2.denote
  have hsort : ∀ t, check r t = true → ∀ q, 0 < q →
      (denote r t < omegaSequence (finiteBase r) q ↔ t.outerSort ≤ q) := by
    intro t ht q hq
    have ha := (hfinite (SourceOne.PublicCodes.fragment t) t).mp ht
    rw [denote_eq_finite r (SourceOne.PublicCodes.fragment t) t ha.2]
    exact source_eval_lt_iff_outerSort_le (finiteBase r) (parameters r)
      (SourceOne.PublicCodes.fragment t) t ha.2 q hq
  have hsource : ∀ n, 0 < n → ∀ ξ, sourceNotation (finiteBase r) n 0 ξ ↔
      ∃ t : RelativeTerm Nat, admissible r n t ∧ finiteDenote r n t = ξ := by
    intro n hn ξ
    rw [sourceNotation, if_pos hn]
    constructor
    · intro hξ
      induction hξ with
      | @parameter ξ hp =>
        have hsmall : ξ < finiteBase r := by simpa only [omegaSequence_zero] using hp
        obtain ⟨p, hcheckp, hvalue⟩ := hcomplete ξ hsmall
        refine ⟨.parameter p, ⟨hcheckp, .parameter ?_⟩, hvalue⟩
        simpa only [hvalue] using hp
      | add ha hb iha ihb =>
        obtain ⟨a, ha, hva⟩ := iha
        obtain ⟨b, hb, hvb⟩ := ihb
        refine ⟨.sum a b, ⟨⟨ha.1, hb.1⟩, .sum ha.2 hb.2⟩, ?_⟩
        change finiteDenote r n a + finiteDenote r n b = _
        rw [hva, hvb]
      | @collapse k ξ h0k hkn hsmall hξ ih =>
        obtain ⟨a, ha, hva⟩ := ih
        refine ⟨.theta k a, ⟨ha.1, .theta h0k hkn ?_ ha.2⟩, ?_⟩
        · change finiteDenote r n a < omegaSequence (finiteBase r) (k + 2)
          rw [hva]
          exact hsmall
        · change sourceFiniteCollapse (finiteBase r) n k (finiteDenote r n a) = _
          rw [hva]
    · rintro ⟨t, ht, rfl⟩
      exact ht.2.denote
  have hglobal : ∀ ξ, GlobalNotation (finiteBase r) 0 ξ ↔
      ∃ t : RelativeTerm Nat, check r t = true ∧ denote r t = ξ := by
    intro ξ
    constructor
    · intro hξ
      obtain ⟨n, hn, hfiniteξ⟩ := globalNotation_finite_witness (finiteBase r)
        (finiteBase_pos r) 0 hξ
      obtain ⟨t, ht, hvalue⟩ := (hsource n hn ξ).mp hfiniteξ
      exact ⟨t, (hcheck t).mpr ⟨n, ht⟩, (denote_eq_finite r n t ht.2).trans hvalue⟩
    · rintro ⟨t, ht, rfl⟩
      exact hchecked t ht
  have hlow : ∀ ξ, ξ < finiteBase (r + 1) ↔
      ∃ t : RelativeTerm Nat, lowCheck r t = true ∧ denote r t = ξ := by
    intro ξ
    rw [finiteBase_succ, ← globalNotation_low_iff_lt_boundary (finiteBase r) (finiteBase_pos r) 0 ξ]
    constructor
    · rintro ⟨hξ, hsmall⟩
      obtain ⟨t, ht, hvalue⟩ := (hglobal ξ).mp hξ
      have hs : t.outerSort ≤ 1 :=
        (hsort t ht 1 (by omega)).mp (by simpa only [hvalue] using hsmall)
      exact ⟨t, by simp only [lowCheck, ht, hs, decide_true, Bool.true_and], hvalue⟩
    · rintro ⟨t, ht, rfl⟩
      have hs : check r t = true ∧ t.outerSort ≤ 1 := by
        simpa only [lowCheck, Bool.and_eq_true, decide_eq_true_eq] using ht
      exact ⟨hchecked t hs.1, (hsort t hs.1 1 (by omega)).mpr hs.2⟩
  have hlowcode : ∀ ξ, ξ < finiteBase (r + 1) ↔
      ∃ c : Nat, lowCheckCode r c = true ∧ interpretation r c = ξ := by
    intro ξ
    constructor
    · intro hξ
      obtain ⟨t, ht, hvalue⟩ := (hlow ξ).mp hξ
      exact ⟨t.code, by simpa only [lowCheckCode_code] using ht,
        by simpa only [interpretation_code] using hvalue⟩
    · rintro ⟨c, hc, hvalue⟩
      obtain ⟨t, ht, hcheckt⟩ := (lowCheckCode_iff r c).mp hc
      apply (hlow ξ).mpr
      refine ⟨t, hcheckt, ?_⟩
      simpa only [← ht, interpretation_code] using hvalue
  exact ⟨hsound, hcomplete, hfinite, hglobal, hlowcode⟩

/-- The literal preceding level proves both parameter soundness and complete
    parameter coverage. This is a finite induction, with no supplied oracle. -/
private theorem levelFacts (r : Nat) : LevelFacts r := by
  induction r with
  | zero =>
    apply buildLevel 0
    · intro p hp
      have hzero : p = 0 := by simpa only [parameterCheck_zero, beq_iff_eq] using hp
      rw [hzero]
      change (0 : Ordinal.{0}) < 1
      exact zero_lt_one
    · intro ξ hξ
      have hzero : ξ = 0 := by simpa [finiteBase_zero] using hξ
      refine ⟨0, rfl, ?_⟩
      simpa only [parameters_zero, SourceOne.parameters, Nat.cast_zero] using hzero.symm
  | succ r ih =>
    apply buildLevel (r + 1)
    · intro p hp
      apply (ih.low_exact (interpretation r p)).mpr
      exact ⟨p, hp, rfl⟩
    · intro ξ hξ
      obtain ⟨p, hp, hvalue⟩ := (ih.low_exact ξ).mp hξ
      exact ⟨p, hp, hvalue⟩

theorem parameter_sound (r p : Nat) (hp : parameterCheck r p = true) :
    parameters r p < finiteBase r := (levelFacts r).parameter_sound p hp

theorem parameter_complete (r : Nat) (ξ : Ordinal.{0}) (hξ : ξ < finiteBase r) :
    ∃ p : Nat, parameterCheck r p = true ∧ parameters r p = ξ :=
  (levelFacts r).parameter_complete ξ hξ

theorem finiteCheck_iff (r n : Nat) (t : RelativeTerm Nat) :
    finiteCheck r n t = true ↔ admissible r n t := (levelFacts r).finite_exact n t

theorem check_iff_finite_admissible (r : Nat) (t : RelativeTerm Nat) :
    check r t = true ↔ ∃ n, admissible r n t := by
  constructor
  · intro ht
    exact ⟨SourceOne.PublicCodes.fragment t, (finiteCheck_iff r _ t).mp ht⟩
  · rintro ⟨n, ht⟩
    exact finiteCheck_transfer r n t ((finiteCheck_iff r n t).mpr ht)
      (SourceOne.PublicCodes.fragment t) (SourceOne.PublicCodes.height_le_fragment t)

theorem finiteCheckCode_exact (r n c : Nat) :
    finiteCheckCode r n c = true ↔
      ∃ t : RelativeTerm Nat, t.code = c ∧ admissible r n t := by
  rw [finiteCheckCode_iff]
  simp only [finiteCheck_iff]

theorem checked_sourceNotation (r n : Nat) (hn : 0 < n) (t : RelativeTerm Nat)
    (ht : finiteCheck r n t = true) : sourceNotation (finiteBase r) n 0 (finiteDenote r n t) := by
  rw [sourceNotation, if_pos hn]
  exact ((finiteCheck_iff r n t).mp ht).2.denote

theorem checked_globalNotation (r : Nat) (t : RelativeTerm Nat) (ht : check r t = true) :
    GlobalNotation (finiteBase r) 0 (denote r t) :=
  ((levelFacts r).global_exact (denote r t)).mpr ⟨t, ht, rfl⟩

theorem denote_lt_iff_outerSort_le (r : Nat) (t : RelativeTerm Nat) (ht : check r t = true)
    (q : Nat) (hq : 0 < q) : denote r t < omegaSequence (finiteBase r) q ↔ t.outerSort ≤ q := by
  have ha := (finiteCheck_iff r (SourceOne.PublicCodes.fragment t) t).mp ht
  rw [denote_eq_finite r (SourceOne.PublicCodes.fragment t) t ha.2]
  exact source_eval_lt_iff_outerSort_le (finiteBase r) (parameters r)
    (SourceOne.PublicCodes.fragment t) t ha.2 q hq

theorem globalNotation_iff_checked (r : Nat) (ξ : Ordinal.{0}) :
    GlobalNotation (finiteBase r) 0 ξ ↔
      ∃ t : RelativeTerm Nat, check r t = true ∧ denote r t = ξ :=
  (levelFacts r).global_exact ξ

theorem globalNotation_iff_code (r : Nat) (ξ : Ordinal.{0}) :
    GlobalNotation (finiteBase r) 0 ξ ↔
      ∃ c : Nat, checkCode r c = true ∧ interpretation r c = ξ := by
  constructor
  · intro hξ
    obtain ⟨t, ht, hvalue⟩ := (globalNotation_iff_checked r ξ).mp hξ
    exact ⟨t.code, by simpa only [checkCode_code] using ht,
      by simpa only [interpretation_code] using hvalue⟩
  · rintro ⟨c, hc, hvalue⟩
    obtain ⟨t, ht, hcheckt⟩ := (checkCode_iff r c).mp hc
    apply (globalNotation_iff_checked r ξ).mpr
    refine ⟨t, hcheckt, ?_⟩
    simpa only [← ht, interpretation_code] using hvalue

/-- Exact coverage of the actual low interval at every finite iterated base. -/
theorem lt_nextBase_iff_code (r : Nat) (ξ : Ordinal.{0}) :
    ξ < finiteBase (r + 1) ↔
      ∃ c : Nat, lowCheckCode r c = true ∧ interpretation r c = ξ :=
  (levelFacts r).low_exact ξ

theorem lt_nextBase_iff_checked (r : Nat) (ξ : Ordinal.{0}) :
    ξ < finiteBase (r + 1) ↔
      ∃ t : RelativeTerm Nat, lowCheck r t = true ∧ denote r t = ξ := by
  rw [lt_nextBase_iff_code]
  constructor
  · rintro ⟨c, hc, hvalue⟩
    obtain ⟨t, ht, hcheckt⟩ := (lowCheckCode_iff r c).mp hc
    refine ⟨t, hcheckt, ?_⟩
    simpa only [← ht, interpretation_code] using hvalue
  · rintro ⟨t, ht, hvalue⟩
    exact ⟨t.code, by simpa only [lowCheckCode_code] using ht,
      by simpa only [interpretation_code] using hvalue⟩

/-- The individual block has exact code coverage. Its lower endpoint is a
    semantic condition here, not a claimed executable ordinal comparison. -/
theorem finiteBlock_iff_code (r : Nat) (ξ : Ordinal.{0}) :
    (finiteBase r ≤ ξ ∧ ξ < finiteBase (r + 1)) ↔
      ∃ c : Nat, lowCheckCode r c = true ∧
        finiteBase r ≤ interpretation r c ∧ interpretation r c = ξ := by
  constructor
  · rintro ⟨hlo, hhi⟩
    obtain ⟨c, hc, hvalue⟩ := (lt_nextBase_iff_code r ξ).mp hhi
    exact ⟨c, hc, by simpa only [hvalue] using hlo, hvalue⟩
  · rintro ⟨c, hc, hlo, hvalue⟩
    exact ⟨by simpa only [hvalue] using hlo, (lt_nextBase_iff_code r ξ).mpr ⟨c, hc, hvalue⟩⟩

/-- Opening any successor-level leaf gives an actual earlier low tree. -/
theorem parameter_representation (r p : Nat) (hp : parameterCheck (r + 1) p = true) :
    ∃ t : RelativeTerm Nat, t.code = p ∧ lowCheck r t = true ∧
      denote r t = parameters (r + 1) p := by
  obtain ⟨t, ht, hcheckt⟩ := (lowCheckCode_iff r p).mp hp
  refine ⟨t, ht, hcheckt, ?_⟩
  simp only [parameters_succ, ← ht, interpretation_code]

theorem admissible_parameter_representation (r n : Nat) (t : RelativeTerm Nat)
    (ht : admissible (r + 1) n t) (p : Nat) (hp : p ∈ t.parameters) :
    ∃ a : RelativeTerm Nat, a.code = p ∧ lowCheck r a = true ∧
      denote r a = parameters (r + 1) p :=
  parameter_representation r p ((payloads_iff_parameters (r + 1) t).mp ht.1 p hp)

/-- Concrete zero representations, with one literal earlier tree at each leaf. -/
def zeroTree : Nat → RelativeTerm Nat
  | 0 => .parameter 0
  | r + 1 => .parameter (zeroTree r).code

theorem zeroTree_lowCheck (r : Nat) : lowCheck r (zeroTree r) = true := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change lowCheckCode r (zeroTree r).code && decide ((0 : Nat) ≤ 1) = true
    rw [lowCheckCode_code, ih]
    rfl

theorem zeroTree_denote (r : Nat) : denote r (zeroTree r) = 0 := by
  induction r with
  | zero => simp only [denote, zeroTree, RelativeTerm.eval, parameters_zero,
      SourceOne.parameters, Nat.cast_zero]
  | succ r ih =>
    change interpretation r (zeroTree r).code = 0
    rw [interpretation_code, ih]

/-- The actual supremum of this sequence starting at one. It is not named
    or identified with any υ-index. -/
noncomputable def finiteBaseLimit : Ordinal.{0} := ⨆ r : Nat, finiteBase r

theorem finiteBaseLimit_cofinal (ξ : Ordinal.{0}) :
    ξ < finiteBaseLimit ↔ ∃ r : Nat, ξ < finiteBase r := by
  unfold finiteBaseLimit
  exact Ordinal.lt_iSup_iff

theorem finiteBase_lt_limit (r : Nat) : finiteBase r < finiteBaseLimit :=
  (finiteBase_step r).trans_le (Ordinal.le_iSup finiteBase (r + 1))

theorem finiteBaseLimit_pos : 0 < finiteBaseLimit :=
  (finiteBase_pos 0).trans (finiteBase_lt_limit 0)

/-- Literal level-tagged recognition. Fixed-level primitive recursive
    recognition above does not by itself prove this uniform function PR. -/
def unionCheck (c : Nat) : Bool := lowCheckCode c.unpair.1 c.unpair.2

noncomputable def unionInterpretation (c : Nat) : Ordinal.{0} :=
  interpretation c.unpair.1 c.unpair.2

@[simp] theorem unionCheck_pair (r c : Nat) : unionCheck (Nat.pair r c) = lowCheckCode r c := by
  simp only [unionCheck, Nat.unpair_pair]

@[simp] theorem unionInterpretation_pair (r c : Nat) :
    unionInterpretation (Nat.pair r c) = interpretation r c := by
  simp only [unionInterpretation, Nat.unpair_pair]

theorem unionCheck_iff (c : Nat) : unionCheck c = true ↔
    ∃ (r : Nat) (t : RelativeTerm Nat), c = Nat.pair r t.code ∧ lowCheck r t = true := by
  constructor
  · intro hc
    obtain ⟨t, ht, hcheckt⟩ := (lowCheckCode_iff c.unpair.1 c.unpair.2).mp hc
    refine ⟨c.unpair.1, t, ?_, hcheckt⟩
    rw [ht]
    exact (Nat.pair_unpair c).symm
  · rintro ⟨r, t, rfl, ht⟩
    simpa only [unionCheck_pair, lowCheckCode_code] using ht

/-- Exact coverage of the finite hereditary union's actual low interval,
    including ordinals below the starting base one. -/
theorem lt_finiteBaseLimit_iff_code (ξ : Ordinal.{0}) :
    ξ < finiteBaseLimit ↔
      ∃ c : Nat, unionCheck c = true ∧ unionInterpretation c = ξ := by
  constructor
  · intro hξ
    obtain ⟨r, hr⟩ := (finiteBaseLimit_cofinal ξ).mp hξ
    obtain ⟨c, hc, hvalue⟩ := (lt_nextBase_iff_code r ξ).mp (hr.trans (finiteBase_step r))
    exact ⟨Nat.pair r c, by simpa only [unionCheck_pair] using hc,
      by simpa only [unionInterpretation_pair] using hvalue⟩
  · rintro ⟨c, hc, hvalue⟩
    have hsmall := (lt_nextBase_iff_code c.unpair.1 (unionInterpretation c)).mpr
      ⟨c.unpair.2, hc, rfl⟩
    have hξsmall : ξ < finiteBase (c.unpair.1 + 1) := by simpa only [hvalue] using hsmall
    exact hξsmall.trans (finiteBase_lt_limit (c.unpair.1 + 1))

end Alexander313.Wilken.RelativeTerm.Hereditary
