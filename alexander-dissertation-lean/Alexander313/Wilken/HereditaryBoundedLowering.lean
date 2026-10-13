import Alexander313.Wilken.HereditaryOmegaPowers

/-!
# Actual bounded lowering between finite public hereditary levels

The original guard retains r<=s, literal original admission at s, and the
true strict bound below finiteBase(r+1). A genuine cross-level comparison
uses the constructed endpoint base code. The bound itself proves that the
original input is low. Exactly s-r adjacent lowering steps execute, with
every intermediate caller bound derived by real finite-base monotonicity.

The native result is normalized and originally low at the requested level r.
Its canonical union code has the same actual ordinal value and is unique
independently of spelling, starting level and descent path. Native normal
forms are not assumed unique by value. Execution and guards are PR; the
guarded partial routine has exactly the original bounded caller domain.
These are finite public bases, not arbitrary temporary epsilon translations.
All proof terms remain uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.BoundedLowering

open ThetaCourse

theorem checked_small_low (s c : Nat) (hc : checkCode s c = true)
    (hb : interpretation s c < finiteBase (s + 1)) : lowCheckCode s c = true := by
  obtain ⟨t, rfl, ht⟩ := (checkCode_iff s c).mp hc
  have hsmall : denote s t < omegaSequence (finiteBase s) 1 := by
    simpa only [interpretation_code] using hb.trans (finiteBase_lt_cardinal s)
  have hsort := (denote_lt_iff_outerSort_le s t ht 1 (Nat.zero_lt_succ 0)).mp hsmall
  simp only [lowCheckCode_code, lowCheck, ht, hsort, decide_true, Bool.true_and]

def endpointCode (r : Nat) : Nat := Nat.pair (r + 1) (BaseArithmetic.freshCode (r + 1))

theorem endpointCode_primrec : Primrec endpointCode :=
  Primrec₂.natPair.comp Primrec.succ (BaseArithmetic.freshCode_primrec.comp Primrec.succ)

theorem endpointCode_checked (r : Nat) : unionCheck (endpointCode r) = true := by
  simpa only [endpointCode, unionCheck_pair] using
    BaseArithmetic.checkCode_old (r + 1) _ (BaseArithmetic.fresh_checked (r + 1))

theorem endpointCode_value (r : Nat) : unionInterpretation (endpointCode r) = finiteBase (r + 1) := by
  simp only [endpointCode, unionInterpretation_pair, BaseArithmetic.fresh_value]

def checkInput (r s c : Nat) : Bool :=
  decide (r ≤ s) && (checkCode s c &&
    Alexander313.HereditaryOrdinalFormation.unionLess (Nat.pair s c) (endpointCode r))

theorem checkInput_primrec : Primrec (fun p : Nat × (Nat × Nat) => checkInput p.1 p.2.1 p.2.2) := by
  have hr : Primrec (fun p : Nat × (Nat × Nat) => p.1) := Primrec.fst
  have hs : Primrec (fun p : Nat × (Nat × Nat) => p.2.1) := Primrec.fst.comp Primrec.snd
  have hc : Primrec (fun p : Nat × (Nat × Nat) => p.2.2) := Primrec.snd.comp Primrec.snd
  exact Primrec.and.comp (Primrec.nat_le.comp hr hs).decide
    (Primrec.and.comp (Uniform.hereditaryCheckCode_primrec.comp hs hc)
      (Alexander313.HereditaryOrdinalFormation.unionLess_primrec.comp
        (Primrec₂.natPair.comp hs hc) (endpointCode_primrec.comp hr)))

theorem checkInput_exact (r s c : Nat) : checkInput r s c = true ↔
    r ≤ s ∧ checkCode s c = true ∧ interpretation s c < finiteBase (r + 1) := by
  simp only [checkInput, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hrs, hc, hb⟩
    have ht := (Alexander313.HereditaryOrdinalFormation.unionLess_exact _ _).mp hb
    exact ⟨hrs, hc, by simpa only [unionInterpretation_pair, endpointCode_value] using ht.2.2⟩
  · rintro ⟨hrs, hc, hb⟩
    have hl : lowCheckCode s c = true := checked_small_low s c hc
      (hb.trans_le (BaseAtoms.bases_strictMono.monotone (Nat.succ_le_succ hrs)))
    refine ⟨hrs, hc, (Alexander313.HereditaryOrdinalFormation.unionLess_exact _ _).mpr ?_⟩
    exact ⟨by simpa only [unionCheck_pair] using hl, endpointCode_checked r,
      by simpa only [unionInterpretation_pair, endpointCode_value] using hb⟩

/-- The endpoint inequality supplies the real adjacent bound at every step. -/
theorem loop_spec (r n c : Nat) (hc : checkCode (r + n) c = true)
    (hb : interpretation (r + n) c < finiteBase (r + 1)) :
    ∃ d : Nat, OmegaPowers.lowerLoop (Nat.pair (r + n) c) n = Nat.pair r d ∧
      lowCheckCode r d = true ∧ interpretation r d = interpretation (r + n) c := by
  induction n generalizing c with
  | zero =>
    exact ⟨c, by simp only [OmegaPowers.lowerLoop, Nat.add_zero],
      checked_small_low r c (by simpa only [Nat.add_zero] using hc)
        (by simpa only [Nat.add_zero] using hb), by simp only [Nat.add_zero]⟩
  | succ n ih =>
    have he : r + (n + 1) = (r + n) + 1 := by omega
    have hc' : checkCode ((r + n) + 1) c = true := by simpa only [he] using hc
    have hb' : interpretation ((r + n) + 1) c < finiteBase (r + 1) := by simpa only [he] using hb
    have hbound : interpretation ((r + n) + 1) c < finiteBase ((r + n) + 1) :=
      hb'.trans_le (BaseAtoms.bases_strictMono.monotone (by omega))
    have hg := (Lowering.checkInput_exact (r + n) c).mpr ⟨hc', hbound⟩
    have hs := Lowering.lowerCode_spec (r + n) c hg
    have hn : checkCode (r + n) (Lowering.lowerCode (r + n) c) = true :=
      (Bool.and_eq_true_iff.mp (by simpa only [lowCheckCode_eq] using hs.1)).1
    obtain ⟨d, hd, hdc, hdv⟩ := ih (Lowering.lowerCode (r + n) c) hn (hs.2.trans_lt hb')
    have hnz : (((r + n) + 1) == 0) = false := by simp
    have hstep : OmegaPowers.lowerStep (Nat.pair ((r + n) + 1) c) =
        Nat.pair (r + n) (Lowering.lowerCode (r + n) c) := by
      simp only [OmegaPowers.lowerStep, Nat.unpair_pair, Nat.add_sub_cancel,
        hnz, hg, Bool.cond_false, Bool.cond_true]
    refine ⟨d, ?_, hdc, ?_⟩
    · rw [OmegaPowers.lowerLoop_shift, he, hstep]
      exact hd
    · exact hdv.trans (hs.2.trans (by rw [he]))

def rawResult (r s c : Nat) : Nat :=
  (OmegaPowers.lowerLoop (Nat.pair s c) (s - r)).unpair.2

theorem rawResult_primrec : Primrec (fun p : Nat × (Nat × Nat) => rawResult p.1 p.2.1 p.2.2) :=
  Primrec.snd.comp (Primrec.unpair.comp (OmegaPowers.lowerLoop_primrec.comp
    (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
    (Primrec.nat_sub.comp (Primrec.fst.comp Primrec.snd) Primrec.fst)))

theorem rawResult_spec (r s c : Nat) (h : checkInput r s c = true) :
    lowCheckCode r (rawResult r s c) = true ∧ interpretation r (rawResult r s c) = interpretation s c := by
  have hs := (checkInput_exact r s c).mp h
  have he : r + (s - r) = s := by omega
  obtain ⟨d, hd, hdc, hdv⟩ := loop_spec r (s - r) c
    (by simpa only [he] using hs.2.1) (by simpa only [he] using hs.2.2)
  have hd' : OmegaPowers.lowerLoop (Nat.pair s c) (s - r) = Nat.pair r d := by simpa only [he] using hd
  have hr : rawResult r s c = d := by simp only [rawResult, hd', Nat.unpair_pair]
  exact ⟨by rw [hr]; exact hdc, by rw [hr]; simpa only [he] using hdv⟩

def lowerCode (r s c : Nat) : Nat := cond (checkInput r s c)
  (Theta.Normalization.normalizeCode r (rawResult r s c)) 0

theorem lowerCode_primrec : Primrec (fun p : Nat × (Nat × Nat) => lowerCode p.1 p.2.1 p.2.2) :=
  checkInput_primrec.cond
    (Theta.Normalization.Effective.normalizeCode_primrec.comp Primrec.fst rawResult_primrec) (Primrec.const 0)

theorem lowerCode_spec (r s c : Nat) (h : checkInput r s c = true) :
    Theta.acceptedLowCode r (lowerCode r s c) = true ∧
      interpretation r (lowerCode r s c) = interpretation s c := by
  have hs := rawResult_spec r s c h
  have hn := Theta.Normalization.normalizeCode_acceptedLow r _ hs.1
  simp only [lowerCode, h, Bool.cond_true]
  exact ⟨hn.1, hn.2.trans hs.2⟩

theorem lowerCode_low (r s c : Nat) (h : checkInput r s c = true) : lowCheckCode r (lowerCode r s c) = true :=
  ((Theta.acceptedLowCode_iff r _).mp (lowerCode_spec r s c h).1).1

theorem lowerCode_normal (r s c : Nat) (h : checkInput r s c = true) :
    Theta.Normal r (rawTree (lowerCode r s c)) :=
  ((Theta.acceptedLowCode_iff r _).mp (lowerCode_spec r s c h).1).2

def canonicalLower (r s c : Nat) : Nat := cond (checkInput r s c)
  (Canonical.canonicalize (Nat.pair r (lowerCode r s c))) 0

theorem canonicalLower_primrec : Primrec (fun p : Nat × (Nat × Nat) => canonicalLower p.1 p.2.1 p.2.2) :=
  checkInput_primrec.cond
    (Canonical.Effective.canonicalize_primrec.comp (Primrec₂.natPair.comp Primrec.fst lowerCode_primrec)) (Primrec.const 0)

theorem canonicalLower_checked (r s c : Nat) (h : checkInput r s c = true) :
    Canonical.check (canonicalLower r s c) = true := by
  simp only [canonicalLower, h, Bool.cond_true]
  exact Canonical.canonicalize_check _ (by simpa only [unionCheck_pair] using lowerCode_low r s c h)

theorem canonicalLower_value (r s c : Nat) (h : checkInput r s c = true) :
    unionInterpretation (canonicalLower r s c) = interpretation s c := by
  simp only [canonicalLower, h, Bool.cond_true]
  exact (Canonical.canonicalize_value _ (by simpa only [unionCheck_pair] using lowerCode_low r s c h)).trans
    (by simpa only [unionInterpretation_pair] using (lowerCode_spec r s c h).2)

theorem canonicalLower_original (r s c : Nat) (h : checkInput r s c = true) :
    unionCheck (canonicalLower r s c) = true ∧
      Theta.Normal (canonicalLower r s c).unpair.1 (rawTree (canonicalLower r s c).unpair.2) := by
  have hs := canonicalLower_checked r s c h
  exact ⟨Canonical.check_original hs, Canonical.check_normal hs⟩

def lower (r s c : Nat) : Part Nat := cond (checkInput r s c) (Part.some (canonicalLower r s c)) Part.none

theorem lower_partrec : Partrec (fun p : Nat × (Nat × Nat) => lower p.1 p.2.1 p.2.2) :=
  Partrec.cond checkInput_primrec.to_comp canonicalLower_primrec.to_comp.partrec Partrec.none

theorem lower_domain (r s c : Nat) : (lower r s c).Dom ↔
    r ≤ s ∧ checkCode s c = true ∧ interpretation s c < finiteBase (r + 1) := by
  rw [← checkInput_exact]
  cases h : checkInput r s c <;> simp [lower, h]

def graph (r s c q : Nat) : Bool := checkInput r s c &&
  (Canonical.check q && (q == canonicalLower r s c))

theorem graph_primrec : Primrec (fun p : (Nat × (Nat × Nat)) × Nat => graph p.1.1 p.1.2.1 p.1.2.2 p.2) :=
  Primrec.and.comp (checkInput_primrec.comp Primrec.fst)
    (Primrec.and.comp (Canonical.Effective.check_primrec.comp Primrec.snd)
      (Primrec.beq.comp Primrec.snd (canonicalLower_primrec.comp Primrec.fst)))

theorem graph_exact (r s c q : Nat) : graph r s c q = true ↔
    r ≤ s ∧ checkCode s c = true ∧ interpretation s c < finiteBase (r + 1) ∧
      Canonical.check q = true ∧ unionInterpretation q = interpretation s c := by
  simp only [graph, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨h, hq, he⟩
    have hs := (checkInput_exact r s c).mp h
    exact ⟨hs.1, hs.2.1, hs.2.2, hq, by rw [he]; exact canonicalLower_value r s c h⟩
  · rintro ⟨hrs, hc, hb, hq, hv⟩
    have h := (checkInput_exact r s c).mpr ⟨hrs, hc, hb⟩
    exact ⟨h, hq, Canonical.check_value_injective q _ hq (canonicalLower_checked r s c h)
      (hv.trans (canonicalLower_value r s c h).symm)⟩

theorem lower_graph_iff (r s c q : Nat) : q ∈ lower r s c ↔ graph r s c q = true := by
  cases h : checkInput r s c with
  | false => simp [lower, graph, h]
  | true =>
    simp [lower, graph, h]
    rintro rfl
    exact canonicalLower_checked r s c h

theorem lower_returns (r s c : Nat) (h : checkInput r s c = true) :
    canonicalLower r s c ∈ lower r s c := by simp [lower, h]

theorem lower_unique (r s c : Nat) (h : checkInput r s c = true) : ∃! q, q ∈ lower r s c := by
  refine ⟨canonicalLower r s c, lower_returns r s c h, ?_⟩
  intro q hq
  have hs := (graph_exact r s c q).mp ((lower_graph_iff r s c q).mp hq)
  exact Canonical.check_value_injective _ _ hs.2.2.2.1 (canonicalLower_checked r s c h)
    (hs.2.2.2.2.trans (canonicalLower_value r s c h).symm)

theorem canonicalLower_invariant (r s c r' s' c' : Nat) (h : checkInput r s c = true)
    (h' : checkInput r' s' c' = true) (he : interpretation s c = interpretation s' c') :
    canonicalLower r s c = canonicalLower r' s' c' :=
  Canonical.check_value_injective _ _ (canonicalLower_checked r s c h) (canonicalLower_checked r' s' c' h')
    ((canonicalLower_value r s c h).trans (he.trans (canonicalLower_value r' s' c' h').symm))

theorem lowerCode_same_endpoint (r c : Nat) (h : checkInput r r c = true) :
    lowerCode r r c = Theta.Normalization.normalizeCode r c := by
  simp only [lowerCode, h, Bool.cond_true, rawResult, Nat.sub_self, OmegaPowers.lowerLoop, Nat.unpair_pair]

theorem checkInput_reversed (r s c : Nat) (hrs : s < r) : checkInput r s c = false := by
  cases h : checkInput r s c with
  | false => rfl
  | true => exact False.elim ((not_le_of_gt hrs) ((checkInput_exact r s c).mp h).1)

theorem checkInput_boundary (r s c : Nat) (he : interpretation s c = finiteBase (r + 1)) : checkInput r s c = false := by
  cases h : checkInput r s c with
  | false => rfl
  | true => have hb := ((checkInput_exact r s c).mp h).2.2; rw [he] at hb; exact False.elim (lt_irrefl _ hb)

theorem checkInput_target_base (r : Nat) : checkInput r r (BaseArithmetic.freshCode r) = true :=
  (checkInput_exact _ _ _).mpr ⟨le_rfl,
    (Bool.and_eq_true_iff.mp (by simpa only [lowCheckCode_eq] using
      BaseArithmetic.checkCode_old r _ (BaseArithmetic.fresh_checked r))).1,
    by rw [BaseArithmetic.fresh_value]; exact finiteBase_step r⟩

theorem checkInput_intermediate (r t s c : Nat) (h : checkInput r s c = true) (hrt : r ≤ t) (hts : t ≤ s) :
    checkInput t s c = true := by
  have hs := (checkInput_exact r s c).mp h
  exact (checkInput_exact t s c).mpr ⟨hts, hs.2.1,
    hs.2.2.trans_le (BaseAtoms.bases_strictMono.monotone (Nat.succ_le_succ hrt))⟩

theorem checkInput_lowered (r t s c : Nat) (h : checkInput r s c = true) (hrt : r ≤ t) (hts : t ≤ s) :
    checkInput r t (lowerCode t s c) = true := by
  have ht := checkInput_intermediate r t s c h hrt hts
  have hc := (Bool.and_eq_true_iff.mp (by simpa only [lowCheckCode_eq] using lowerCode_low t s c ht)).1
  exact (checkInput_exact _ _ _).mpr ⟨hrt, hc,
    ((lowerCode_spec t s c ht).2).trans_lt ((checkInput_exact r s c).mp h).2.2⟩

theorem canonicalLower_compose (r t s c : Nat) (h : checkInput r s c = true) (hrt : r ≤ t) (hts : t ≤ s) :
    canonicalLower r t (lowerCode t s c) = canonicalLower r s c := by
  have ht := checkInput_intermediate r t s c h hrt hts
  exact canonicalLower_invariant _ _ _ _ _ _ (checkInput_lowered r t s c h hrt hts) h (lowerCode_spec t s c ht).2

end Alexander313.Wilken.RelativeTerm.Hereditary.BoundedLowering
