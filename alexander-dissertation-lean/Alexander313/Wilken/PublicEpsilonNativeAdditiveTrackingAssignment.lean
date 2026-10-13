import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingAssignmentSupport
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingBranchBounds

/-!
# Full native additive tracking assignment with genuine joint bounds

Every original RAW LOW positive additive principal at least the literal
coded epsilon base reaches a genuine M or singleton leaf by actual factor
removal. Strict canonical MNF length decrease proves termination; the
measure is not an input or numerical program bound. Actual frames unwind
through the printed append/greatest-replacement procedure. Joint tracking,
all-entry upper bounds and canonical final-factor bounds derive every
recursive factor<=headword FINAL caller. Actual derivations retain every
literal source branch. No assigned word, tracker, factorization, endpoint,
cover, representative or termination oracle. Source-only uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.Assignment

open PublicEpsilonUnboundedIota SourceTrackingSequences
open AssignmentSupport
open Alexander313.Wilken.MultiplicativeNormalForm

abbrev inputCheck := SourceLocalization.RootAdapter.inputCheck
abbrev execute := AssignmentSupport.execute

theorem inputCheck_primrec : Primrec₂ inputCheck := SourceLocalization.RootAdapter.inputCheck_primrec

theorem inputCheck_exact (q current : Nat) : inputCheck q current = true ↔
    lowCheckCode q current = true ∧ base q ≤ interpretation q current ∧
      Ordinal.IsPrincipal (· + ·) (interpretation q current) :=
  SourceLocalization.RootAdapter.inputCheck_exact q current

def Invariant (q input : Nat) (word : List Nat) : Prop :=
  SourceTrackingRaw.trackingCheck q word = true ∧
    (∀ d ∈ word, interpretation q d ≤ interpretation q input) ∧
      lf (interpretation q input) ≤ interpretation q (lastCode word) ∧
        lf (interpretation q (lastCode word)) = lf (interpretation q input)

def Result (q input : Nat) (word : List Nat) : Prop :=
  Invariant q input word ∧ Derivation q input word

theorem leaf_input (q current : Nat) (word : List Nat) (hl : Leaf q current word) :
    inputCheck q current = true := by
  rcases hl with ⟨hm, he⟩ | ⟨hm, hs, he⟩
  · exact SourceMultiplicativePrincipal.rootAdapter_input q current hm
  · have hs := (Factor.singletonCheck_exact q current).mp hs
    exact (inputCheck_exact q current).mpr ⟨hs.1, hs.2.1, hs.2.2.1⟩

theorem leaf_result (q current : Nat) (word : List Nat) (hl : Leaf q current word) :
    Result q current word := by
  rcases hl with ⟨hm, rfl⟩ | ⟨hm, hs, rfl⟩
  · have hc := SourceMultiplicativePrincipal.rootAdapter_input q current hm
    have hmul := ((SourceMultiplicativePrincipal.inputCheck_exact q current).mp hm).2.2
    refine ⟨⟨tracking_raw q _ (SourceMultiplicativeTracking.rawWord_checked q current hc),
      fun d hd => (ReplacementSupport.rawWord_low_bound q current hc d hd).2, ?_, ?_⟩,
      .multiplicative current hm⟩
    · rw [SourceMultiplicativeTracking.rawWord_last, lf_multiplicative hmul]
    · rw [SourceMultiplicativeTracking.rawWord_last]
  · have hi := (Factor.singletonCheck_exact q current).mp hs
    have hq := (HeightBoundary.input_spec q current hi.1).2.1
    have hp := (base_pos q hq).trans_le hi.2.1
    have hpre := MultiplicativeFactorRemoval.factorPrefix_reduced _
      (canonicalMNF_reduced (interpretation q current))
    have hpos := (isMNF_product_principal hpre.1).1
    have hlf : lf (interpretation q current) ≤ interpretation q current := by
      exact (Ordinal.le_mul_right _ hpos).trans_eq (source_prefix_last hp hi.2.2.1).symm
    refine ⟨⟨Factor.singletonWord_checked q current hs, ?_, ?_, ?_⟩,
      .singleton current hm hs⟩
    · intro d hd
      rw [List.mem_singleton.mp hd]
    · simpa only [lastCode_singleton] using hlf
    · simp only [lastCode_singleton]

theorem split_flags (q input prefix factor : Nat)
    (hf : (prefix, factor) ∈ Factor.execute q input) :
    SourceMultiplicativePrincipal.inputCheck q input = false ∧ Factor.singletonCheck q input = false := by
  have hc := (Factor.execute_spec q input (prefix, factor) hf).1
  have hs := Bool.and_eq_true.mp hc
  have hm : SourceMultiplicativePrincipal.inputCheck q input = false := by
    simpa only [Bool.not_eq_true'] using (Bool.and_eq_true.mp hs.1).2
  refine ⟨hm, ?_⟩
  change ((SourceLocalization.RootAdapter.inputCheck q input &&
    !SourceMultiplicativePrincipal.inputCheck q input) &&
      !Normalization.lessRawCode q (FactorSupport.cutoffCode q) input) = false
  simpa only [hs.1, hs.2] using (rfl : (true && !true) = false)

/-- The real recursive source clauses are distinguished by actual guards;
no independently supplied tracking assignment defines the result. -/
theorem derivation_flags (q current : Nat) (word : List Nat) (hd : Derivation q current word) :
    (SourceMultiplicativePrincipal.inputCheck q current = true ∧
      word = SourceMultiplicativeTracking.rawWord q current) ∨
    (SourceMultiplicativePrincipal.inputCheck q current = false ∧
      Factor.singletonCheck q current = true ∧ word = [current]) ∨
    (SourceMultiplicativePrincipal.inputCheck q current = false ∧
      Factor.singletonCheck q current = false ∧
      ∃ prefix factor heads, (prefix, factor) ∈ Factor.execute q current ∧
        Derivation q prefix heads ∧ word ∈ Branches.execute ((q, factor), heads)) := by
  cases hd with
  | multiplicative current hm => exact Or.inl ⟨hm, rfl⟩
  | singleton current hm hs => exact Or.inr (Or.inl ⟨hm, hs, rfl⟩)
  | split input prefix factor heads out hf hh ho =>
    exact Or.inr (Or.inr ⟨(split_flags q input prefix factor hf).1,
      (split_flags q input prefix factor hf).2, prefix, factor, heads, hf, hh, ho⟩)

/-- Actual factor and branch executions are single-valued; induction over
the real source construction therefore gives literal whole-word uniqueness. -/
theorem derivation_unique (q current : Nat) (word other : List Nat)
    (hd : Derivation q current word) (he : Derivation q current other) : word = other := by
  induction hd generalizing other with
  | multiplicative current hm =>
    rcases derivation_flags q current other he with ⟨hm', hout⟩ |
      ⟨hm', hs, hout⟩ | ⟨hm', hs, hrest⟩
    · exact hout.symm
    · rw [hm] at hm'; cases hm'
    · rw [hm] at hm'; cases hm'
  | singleton current hm hs =>
    rcases derivation_flags q current other he with ⟨hm', hout⟩ |
      ⟨hm', hs', hout⟩ | ⟨hm', hs', hrest⟩
    · rw [hm] at hm'; cases hm'
    · exact hout.symm
    · rw [hs] at hs'; cases hs'
  | split input prefix factor heads out hf hd ho ih =>
    have hflags := split_flags q input prefix factor hf
    rcases derivation_flags q input other he with ⟨hm', hout⟩ |
      ⟨hm', hs', hout⟩ | ⟨hm', hs', prefix', factor', heads', hf', hd', ho'⟩
    · rw [hflags.1] at hm'; cases hm'
    · rw [hflags.2] at hs'; cases hs'
    · have heq : (prefix, factor) = (prefix', factor') := Part.mem_unique hf hf'
      have hp : prefix = prefix' := congrArg Prod.fst heq
      have ht : factor = factor' := congrArg Prod.snd heq
      subst prefix'; subst factor'
      have hword : heads = heads' := ih heads' hd'
      subst heads'
      exact Part.mem_unique ho ho'

/-- Strong induction is solely the mathematical termination proof. The
executing procedure sees only original codes and actual factor outputs. -/
theorem down_returns (q current : Nat) (hc : inputCheck q current = true) (frames : List Frame) :
    ∃ leaf, leaf ∈ down ((q, current), frames) := by
  let R : Nat → Prop := fun n => ∀ current,
    (canonicalMNF (interpretation q current)).length = n → inputCheck q current = true →
      ∀ frames, ∃ leaf, leaf ∈ down ((q, current), frames)
  have hall : ∀ n, R n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro current he hc frames
      cases hm : SourceMultiplicativePrincipal.inputCheck q current with
      | true =>
        refine ⟨(current, (SourceMultiplicativeTracking.rawWord q current, frames)), ?_⟩
        apply PFun.mem_fix_iff.mpr
        exact Or.inl (by simp only [downStep, hm, Bool.cond_true]; exact Part.mem_some _)
      | false =>
        cases hs : Factor.singletonCheck q current with
        | true =>
          refine ⟨(current, ([current], frames)), ?_⟩
          apply PFun.mem_fix_iff.mpr
          exact Or.inl (by simp only [downStep, hm, hs, Bool.cond_false, Bool.cond_true];
            exact Part.mem_some _)
        | false =>
          have hinput := (inputCheck_exact q current).mp hc
          have hnon : ¬MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal
              (interpretation q current) := by
            intro hmul
            have ht := (SourceMultiplicativePrincipal.inputCheck_exact q current).mpr
              ⟨hinput.1, hinput.2.1, hmul⟩
            rw [hm] at ht
            cases ht
          have hsplit : Factor.splitCheck q current = true :=
            (Factor.branches_exhaustive q current hc hnon).resolve_left
              (fun ht => by rw [hs] at ht; cases ht)
          obtain ⟨⟨prefix, factor⟩, hf⟩ := Part.dom_iff_mem.mp
            ((Factor.execute_domain q current).mpr hsplit)
          obtain ⟨_, _, _, _, _, hp, _, _, _, _, _, _, hlt⟩ :=
            Factor.execute_spec q current (prefix, factor) hf
          have hlt : (canonicalMNF (interpretation q prefix)).length < n := hlt.trans_eq he
          obtain ⟨leaf, hl⟩ := ih _ hlt prefix rfl hp ((current, (prefix, factor)) :: frames)
          refine ⟨leaf, PFun.mem_fix_iff.mpr (Or.inr
            ⟨((q, prefix), (current, (prefix, factor)) :: frames), ?_, hl⟩)⟩
          simpa only [downStep, hm, hs, Bool.cond_false] using Part.mem_map
            (fun split => Sum.inr ((q, split.1), (current, split) :: frames)) hf
  exact hall _ current rfl hc frames

/-- The actual first descent step already forces the original source guard,
so invalid original inputs are outside the complete partial domain. -/
theorem down_input (p : DownState) (leaf : LeafOutput) (ho : leaf ∈ down p) :
    inputCheck p.1.1 p.1.2 = true := by
  rcases PFun.mem_fix_iff.mp ho with hstop | ⟨next, hn, hrest⟩
  · exact leaf_input _ _ _ (downStep_stop p leaf hstop).2.2
  · obtain ⟨prefix, factor, hm, hs, hf, he⟩ := downStep_continue p next hn
    have hi := (Factor.splitCheck_exact _ _).mp (Factor.execute_spec _ _ _ hf).1
    exact (inputCheck_exact _ _).mpr ⟨hi.1, hi.2.1, hi.2.2.1⟩

/-- The joint child bounds derive the genuine factor<=FINAL footnote caller.
All source-output upper bounds and the final-factor equality then come from
the actually executed printed branch. -/
theorem frame_result (q input prefix factor : Nat) (heads out : List Nat)
    (hf : (prefix, factor) ∈ Factor.execute q input)
    (hh : Result q prefix heads)
    (ho : out ∈ Branches.execute ((q, factor), heads)) : Result q input out := by
  obtain ⟨hcheck, hlp, hcp, hlf, hcf, hp, hbp, hlt, hm, hone, hv, hlast, hcount⟩ :=
    Factor.execute_spec q input (prefix, factor) hf
  have hb : interpretation q factor ≤ interpretation q (lastCode heads) :=
    (Factor.Bounds.execute_last_le_prefix_last q input (prefix, factor) hf).trans hh.1.2.2.1
  have hq := (HeightBoundary.input_spec q prefix hlp).2.1
  have hpos := (base_pos q hq).trans_le hbp
  have hs := BranchBounds.execute_spec q factor heads out hh.1.1 hlf hm hone hb
    (interpretation q prefix) hpos hh.1.2.1 ho
  refine ⟨⟨hs.1, ?_, ?_, ?_⟩, .split input prefix factor heads out hf hh.2 ho⟩
  · intro d hd
    exact (hs.2.2.2.1 d hd).trans_eq hv.symm
  · rw [← hlast]
    exact hs.2.2.1
  · exact hs.2.2.2.2.trans hlast

/-- Finite actual frame induction supplies both terminating unwind and the
entire chronological source derivation; every recursive caller is derived. -/
theorem up_returns_result (q current : Nat) (frames : List Frame) (target : Nat)
    (hs : Stack q current frames target) (word : List Nat) (hw : Result q current word) :
    ∃ out, out ∈ up ((q, word), frames) ∧ Result q target out := by
  induction hs generalizing word with
  | nil current =>
    refine ⟨word, PFun.mem_fix_iff.mpr (Or.inl ?_), hw⟩
    rw [upStep_nil]
    exact Part.mem_some _
  | cons input prefix factor frames target hf hs ih =>
    obtain ⟨hcheck, hlp, hcp, hlf, hcf, hp, hbp, hlt, hm, hone, hv, hlast, hcount⟩ :=
      Factor.execute_spec q input (prefix, factor) hf
    have hb : interpretation q factor ≤ interpretation q (lastCode word) :=
      (Factor.Bounds.execute_last_le_prefix_last q input (prefix, factor) hf).trans hw.1.2.2.1
    obtain ⟨next, hn⟩ := Branches.execute_returns q factor word hw.1.1 hlf hm hb
    have hnext := frame_result q input prefix factor word next hf hw hn
    obtain ⟨out, ho, hout⟩ := ih next hnext
    refine ⟨out, PFun.mem_fix_iff.mpr (Or.inr ⟨((q, next), frames), ?_, ho⟩), hout⟩
    rw [upStep_cons]
    exact Part.mem_map _ hn

theorem up_result (q current : Nat) (frames : List Frame) (target : Nat)
    (hs : Stack q current frames target) (word out : List Nat)
    (hw : Result q current word) (ho : out ∈ up ((q, word), frames)) : Result q target out := by
  obtain ⟨actual, ha, hr⟩ := up_returns_result q current frames target hs word hw
  have he : out = actual := Part.mem_unique ho ha
  simpa only [he] using hr

theorem execute_partrec : Partrec₂ execute := AssignmentSupport.execute_partrec

theorem execute_returns (q current : Nat) (hc : inputCheck q current = true) :
    ∃ out, out ∈ execute q current := by
  obtain ⟨leaf, hl⟩ := down_returns q current hc []
  have hs := down_relation ((q, current), []) leaf hl
  have hstack := hs.2 current (.nil current)
  obtain ⟨out, ho, hr⟩ := up_returns_result q leaf.1 leaf.2.2 current hstack leaf.2.1
    (leaf_result q leaf.1 leaf.2.1 hs.1)
  exact ⟨out, Part.mem_bind hl ho⟩

/-- Every actual output realizes the complete original Definition3.20
clauses and the joint Proposition3.21 bounds, including canonical LF. -/
theorem execute_spec (q current : Nat) (out : List Nat) (ho : out ∈ execute q current) :
    inputCheck q current = true ∧ Result q current out := by
  obtain ⟨leaf, hl, hu⟩ := Part.mem_bind_iff.mp ho
  have hs := down_relation ((q, current), []) leaf hl
  exact ⟨down_input ((q, current), []) leaf hl,
    up_result q leaf.1 leaf.2.2 current (hs.2 current (.nil current)) leaf.2.1 out
      (leaf_result q leaf.1 leaf.2.1 hs.1) hu⟩

theorem execute_domain (q current : Nat) : (execute q current).Dom ↔ inputCheck q current = true := by
  constructor
  · intro hd
    obtain ⟨out, ho⟩ := Part.dom_iff_mem.mp hd
    exact (execute_spec q current out ho).1
  · intro hc
    exact Part.dom_iff_mem.mpr (execute_returns q current hc)

theorem execute_last_bounds (q current : Nat) (out : List Nat) (ho : out ∈ execute q current) :
    lf (interpretation q current) ≤ interpretation q (lastCode out) ∧
      interpretation q (lastCode out) ≤ interpretation q current ∧
        lf (interpretation q (lastCode out)) = lf (interpretation q current) := by
  have hs := (execute_spec q current out ho).2.1
  have hne := ((SourceTrackingRaw.trackingCheck_conditions q out).mp hs.1).1
  exact ⟨hs.2.2.1, hs.2.1 _ (lastCode_mem out hne), hs.2.2.2⟩

theorem execute_tracking (q current : Nat) (out : List Nat) (ho : out ∈ execute q current) :
    SourceTrackingRaw.trackingCheck q out = true := (execute_spec q current out ho).2.1.1

theorem execute_nonempty (q current : Nat) (out : List Nat) (ho : out ∈ execute q current) :
    out ≠ [] := ((SourceTrackingRaw.trackingCheck_conditions q out).mp
      (execute_tracking q current out ho)).1

/-- The actual canonical final decomposition is the printed NF clause;
its last factor equals the original input's LF by joint induction. -/
theorem execute_prefix_last (q current : Nat) (out : List Nat) (ho : out ∈ execute q current) :
    interpretation q (lastCode out) =
      factorProduct (factorPrefix (canonicalMNF (interpretation q (lastCode out)))) *
        lf (interpretation q current) := by
  have ht := (SourceTrackingRaw.trackingCheck_conditions q out).mp
    (execute_tracking q current out ho)
  simpa only [(execute_last_bounds q current out ho).2.2] using
    source_prefix_last ht.2.2.2.1 ht.2.2.2.2.1

theorem derivation_input (q current : Nat) (word : List Nat) (hd : Derivation q current word) :
    inputCheck q current = true := by
  rcases derivation_flags q current word hd with ⟨hm, he⟩ |
    ⟨hm, hs, he⟩ | ⟨hm, hs, prefix, factor, heads, hf, hh, ho⟩
  · exact leaf_input q current word (Or.inl ⟨hm, he⟩)
  · exact leaf_input q current word (Or.inr ⟨hm, hs, he⟩)
  · have hi := (Factor.splitCheck_exact _ _).mp (Factor.execute_spec _ _ _ hf).1
    exact (inputCheck_exact _ _).mpr ⟨hi.1, hi.2.1, hi.2.2.1⟩

/-- The real partial program executes exactly the finite original source
clauses. The source relation is a proved correspondence, not a program oracle. -/
theorem execute_iff_derivation (q current : Nat) (word : List Nat) :
    word ∈ execute q current ↔ Derivation q current word := by
  constructor
  · intro ho; exact (execute_spec q current word ho).2.2
  · intro hd
    obtain ⟨actual, ha⟩ := execute_returns q current (derivation_input q current word hd)
    have he := derivation_unique q current word actual hd (execute_spec q current actual ha).2.2
    simpa only [he] using ha

theorem execute_multiplicative (q current : Nat)
    (hm : SourceMultiplicativePrincipal.inputCheck q current = true) :
    SourceMultiplicativeTracking.rawWord q current ∈ execute q current :=
  (execute_iff_derivation q current _).mpr (.multiplicative current hm)

theorem execute_singleton (q current : Nat)
    (hm : SourceMultiplicativePrincipal.inputCheck q current = false)
    (hs : Factor.singletonCheck q current = true) : [current] ∈ execute q current :=
  (execute_iff_derivation q current _).mpr (.singleton current hm hs)

/-- Every genuine factor-removal recursion uses the very same executing
procedure for its child, then the actual printed append/insertion program. -/
theorem execute_factor (q current prefix factor : Nat) (heads out : List Nat)
    (hf : (prefix, factor) ∈ Factor.execute q current)
    (hh : heads ∈ execute q prefix) (ho : out ∈ Branches.execute ((q, factor), heads)) :
    out ∈ execute q current :=
  (execute_iff_derivation q current out).mpr
    (.split current prefix factor heads out hf ((execute_iff_derivation q prefix heads).mp hh) ho)

/-- Actual factor outputs and actual recursive child execution, rather
than an unrelated assigned headword, witness every non-leaf source branch. -/
theorem execute_clauses (q current : Nat) (out : List Nat) (ho : out ∈ execute q current) :
    (SourceMultiplicativePrincipal.inputCheck q current = true ∧
      out = SourceMultiplicativeTracking.rawWord q current) ∨
    (SourceMultiplicativePrincipal.inputCheck q current = false ∧
      Factor.singletonCheck q current = true ∧ out = [current]) ∨
    (SourceMultiplicativePrincipal.inputCheck q current = false ∧
      Factor.singletonCheck q current = false ∧
      ∃ prefix factor heads, (prefix, factor) ∈ Factor.execute q current ∧
        heads ∈ execute q prefix ∧ out ∈ Branches.execute ((q, factor), heads)) := by
  rcases derivation_flags q current out (execute_spec q current out ho).2.2 with
    hmul | hsingle | ⟨hm, hs, prefix, factor, heads, hf, hh, hout⟩
  · exact Or.inl hmul
  · exact Or.inr (Or.inl hsingle)
  · exact Or.inr (Or.inr ⟨hm, hs, prefix, factor, heads, hf,
      (execute_iff_derivation q prefix heads).mpr hh, hout⟩)

theorem execute_at_base (q current : Nat) (hc : inputCheck q current = true)
    (he : interpretation q current = base q) : [current] ∈ execute q current := by
  have hi := (inputCheck_exact q current).mp hc
  have hq := (HeightBoundary.input_spec q current hi.1).2.1
  have hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q current) := by
    rw [he]
    exact SourceMultiplicativePrincipal.epsilon_multiplicative _ (SourceChi.epsilon_base q hq)
  have hg := (SourceMultiplicativePrincipal.inputCheck_exact q current).mpr ⟨hi.1, hi.2.1, hm⟩
  simpa only [SourceMultiplicativeTracking.Spelling.rawWord_at_base q current hc he] using
    execute_multiplicative q current hg

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.Assignment
