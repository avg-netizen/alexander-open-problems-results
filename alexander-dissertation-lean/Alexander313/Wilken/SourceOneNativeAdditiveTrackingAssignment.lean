import Alexander313.Wilken.SourceOneNativeAdditiveTrackingAssignmentSupport
import Alexander313.Wilken.SourceOneNativeMultiplicativeTrackingSpelling

/-!
# Full original source-one additive tracking assignment

The actual original RAW LOW additive principal at least one is repeatedly
factored until its genuine multiplicative leaf. Source-one nonmultiplicative
inputs already lie above the printed singleton cutoff, by the actual factor
caller theorem. Strict canonical MNF length decrease proves descent without
an executing numerical bound. Every real frame is then unwound by the actual
append/greatest-insertion dispatcher. The joint tracker, member bound and LF
bounds derive each recursive factor-to-FINAL caller. The entire procedure
agrees with the actual finite source clauses, using itself for every child.
No assigned word, tracker, factorization, endpoint or Native base-one grammar.
Source-only uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.Assignment

open NativeContext.SourceTrackingSequences
open AssignmentSupport
open SourceMultiplicativeTracking (rawWord)
open Alexander313.Wilken.MultiplicativeNormalForm

abbrev inputCheck := SourceLocalization.RootAdapter.inputCheck
abbrev execute := AssignmentSupport.execute

theorem inputCheck_primrec : Primrec inputCheck := SourceLocalization.RootAdapter.inputCheck_primrec

theorem inputCheck_exact (current : Nat) : inputCheck current = true ↔
    lowCheckCode 0 current = true ∧ 1 ≤ interpretation 0 current ∧
      Ordinal.IsPrincipal (· + ·) (interpretation 0 current) :=
  SourceLocalization.RootAdapter.inputCheck_exact current

def Invariant (input : Nat) (word : List Nat) : Prop :=
  SourceTrackingRaw.trackingCheck word = true ∧
    (∀ d ∈ word, interpretation 0 d ≤ interpretation 0 input) ∧
      lf (interpretation 0 input) ≤ interpretation 0 (lastCode word) ∧
        lf (interpretation 0 (lastCode word)) = lf (interpretation 0 input)

def Result (input : Nat) (word : List Nat) : Prop := Invariant input word ∧ Derivation input word

theorem leaf_result (current : Nat)
    (hm : SourceMultiplicativePrincipal.inputCheck current = true) : Result current (rawWord current) := by
  have hc := SourceMultiplicativePrincipal.rootAdapter_input current hm
  have hmul := ((SourceMultiplicativePrincipal.inputCheck_exact current).mp hm).2.2
  refine ⟨⟨SourceMultiplicativeTracking.rawWord_checked current hc,
    multiplicative_word_bound current hm, ?_, ?_⟩, .multiplicative current hm⟩
  · simpa only [SourceMultiplicativeTracking.rawWord_last, lf_multiplicative hmul] using
      (le_rfl : interpretation 0 current ≤ interpretation 0 current)
  · simp only [SourceMultiplicativeTracking.rawWord_last]

theorem split_nonmultiplicative (input prefix factor : Nat)
    (hf : (prefix, factor) ∈ Factor.execute input) :
    SourceMultiplicativePrincipal.inputCheck input = false := by
  have hc := (Factor.execute_spec input (prefix, factor) hf).1
  exact by simpa only [Bool.not_eq_true'] using (Bool.and_eq_true.mp hc).2

theorem derivation_flags (current : Nat) (word : List Nat) (hd : Derivation current word) :
    (SourceMultiplicativePrincipal.inputCheck current = true ∧ word = rawWord current) ∨
      (SourceMultiplicativePrincipal.inputCheck current = false ∧
        ∃ prefix factor heads, (prefix, factor) ∈ Factor.execute current ∧
          Derivation prefix heads ∧ word ∈ Branches.execute (factor, heads)) := by
  cases hd with
  | multiplicative current hm => exact Or.inl ⟨hm, rfl⟩
  | split input prefix factor heads out hf hh ho =>
    exact Or.inr ⟨split_nonmultiplicative input prefix factor hf, prefix, factor, heads, hf, hh, ho⟩

/-- Single-valued actual factor and branch executions yield literal source
word uniqueness. No independently assigned tracker is used. -/
theorem derivation_unique (current : Nat) (word other : List Nat)
    (hd : Derivation current word) (he : Derivation current other) : word = other := by
  induction hd generalizing other with
  | multiplicative current hm =>
    rcases derivation_flags current other he with ⟨hm', hout⟩ | ⟨hm', hrest⟩
    · exact hout.symm
    · rw [hm] at hm'; cases hm'
  | split input prefix factor heads out hf hd ho ih =>
    have hm := split_nonmultiplicative input prefix factor hf
    rcases derivation_flags input other he with ⟨hm', hout⟩ |
      ⟨hm', prefix', factor', heads', hf', hd', ho'⟩
    · rw [hm] at hm'; cases hm'
    · have heq : (prefix, factor) = (prefix', factor') := Part.mem_unique hf hf'
      have hp : prefix = prefix' := congrArg Prod.fst heq
      have ht : factor = factor' := congrArg Prod.snd heq
      subst prefix'; subst factor'
      have hw : heads = heads' := ih heads' hd'
      subst heads'
      exact Part.mem_unique ho ho'

/-- The actual factor bound and the child LF bound supply the printed
factor<=headword FINAL requirement as a conclusion of joint induction. -/
theorem frame_result (input prefix factor : Nat) (heads out : List Nat)
    (hf : (prefix, factor) ∈ Factor.execute input) (hh : Result prefix heads)
    (ho : out ∈ Branches.execute (factor, heads)) : Result input out := by
  obtain ⟨hcheck, hp, hfactor, hcaller, hone, hlt, hm, hfactorone, hv, hlast, hcount⟩ :=
    Factor.execute_spec input (prefix, factor) hf
  have hlow := ((Theta.acceptedLowCode_iff 0 factor).mp hfactor).1
  have hb : interpretation 0 factor ≤ interpretation 0 (lastCode heads) :=
    (Factor.Bounds.execute_last_le_prefix_last input (prefix, factor) hf).trans hh.1.2.2.1
  have hpos := Order.one_le_iff_pos.mp hone
  have hs := BranchBounds.execute_spec factor heads out hh.1.1 hlow hm hfactorone hb
    (interpretation 0 prefix) hpos hh.1.2.1 ho
  refine ⟨⟨hs.1, ?_, ?_, ?_⟩, .split input prefix factor heads out hf hh.2 ho⟩
  · intro d hd
    exact (hs.2.2.2.1 d hd).trans_eq hv.symm
  · rw [← hlast]
    exact hs.2.2.1
  · exact hs.2.2.2.2.trans hlast

/-- Finite actual frames give both a terminating unwind and the real
recursive derivation. Every child caller and strengthened bound is derived. -/
theorem up_returns_result (current : Nat) (frames : List Frame) (target : Nat)
    (hs : Frames current frames target) (word : List Nat) (hw : Result current word) :
    ∃ out, out ∈ up (word, frames) ∧ Result target out := by
  induction hs generalizing word with
  | nil current =>
    refine ⟨word, PFun.mem_fix_iff.mpr (Or.inl ?_), hw⟩
    rw [upStep_nil]
    exact Part.mem_some _
  | push input pair frames target hf hs ih =>
    obtain ⟨hcheck, hp, hfactor, hcaller, hone, hlt, hm, hfactorone, hv, hlast, hcount⟩ :=
      Factor.execute_spec input pair hf
    have hlow := ((Theta.acceptedLowCode_iff 0 pair.2).mp hfactor).1
    have hb : interpretation 0 pair.2 ≤ interpretation 0 (lastCode word) :=
      (Factor.Bounds.execute_last_le_prefix_last input pair hf).trans hw.1.2.2.1
    obtain ⟨next, hn⟩ := Branches.execute_returns pair.2 word hw.1.1 hlow hm hb
    have hnext := frame_result input pair.1 pair.2 word next hf hw hn
    obtain ⟨out, ho, hout⟩ := ih next hnext
    refine ⟨out, PFun.mem_fix_iff.mpr (Or.inr ⟨(next, frames), ?_, ho⟩), hout⟩
    rw [upStep_cons]
    exact Part.mem_map _ hn

theorem up_result (current : Nat) (frames : List Frame) (target : Nat)
    (hs : Frames current frames target) (word out : List Nat)
    (hw : Result current word) (ho : out ∈ up (word, frames)) : Result target out := by
  obtain ⟨actual, ha, hr⟩ := up_returns_result current frames target hs word hw
  have he : out = actual := Part.mem_unique ho ha
  simpa only [he] using hr

theorem execute_partrec : Partrec execute := AssignmentSupport.execute_partrec

theorem execute_returns (current : Nat) (hc : inputCheck current = true) :
    ∃ out, out ∈ execute current := by
  obtain ⟨leaf, hl⟩ := down_returns current hc []
  obtain ⟨terminal, hm, he, hs⟩ := down_frames (current, []) leaf hl current (.nil current)
  have hr : Result terminal leaf.1 := by simpa only [he] using leaf_result terminal hm
  obtain ⟨out, ho, hout⟩ := up_returns_result terminal leaf.2 current hs leaf.1 hr
  refine ⟨out, ?_⟩
  simpa only [AssignmentSupport.execute, hc, Bool.cond_true] using Part.mem_bind hl ho

/-- Every actual result satisfies the genuine original grammar, complete
source clauses and strengthened Proposition3.21 bounds. -/
theorem execute_spec (current : Nat) (out : List Nat) (ho : out ∈ execute current) :
    inputCheck current = true ∧ Result current out := by
  cases hc : inputCheck current with
  | false => simp only [AssignmentSupport.execute, hc, Bool.cond_false, Part.notMem_none] at ho
  | true =>
    have hrun : out ∈ (down (current, [])).bind up := by
      simpa only [AssignmentSupport.execute, hc, Bool.cond_true] using ho
    obtain ⟨leaf, hl, hu⟩ := Part.mem_bind_iff.mp hrun
    obtain ⟨terminal, hm, he, hs⟩ := down_frames (current, []) leaf hl current (.nil current)
    have hr : Result terminal leaf.1 := by simpa only [he] using leaf_result terminal hm
    exact ⟨hc, up_result terminal leaf.2 current hs leaf.1 out hr hu⟩

theorem execute_domain (current : Nat) : (execute current).Dom ↔ inputCheck current = true := by
  constructor
  · intro hd
    obtain ⟨out, ho⟩ := Part.dom_iff_mem.mp hd
    exact (execute_spec current out ho).1
  · intro hc
    exact Part.dom_iff_mem.mpr (execute_returns current hc)

theorem execute_tracking (current : Nat) (out : List Nat) (ho : out ∈ execute current) :
    SourceTrackingRaw.trackingCheck out = true := (execute_spec current out ho).2.1.1

theorem execute_nonempty (current : Nat) (out : List Nat) (ho : out ∈ execute current) :
    out ≠ [] := ((SourceTrackingRaw.trackingCheck_exact out).mp (execute_tracking current out ho)).1

theorem execute_all_bounds (current : Nat) (out : List Nat) (ho : out ∈ execute current) :
    ∀ d ∈ out, interpretation 0 d ≤ interpretation 0 current := (execute_spec current out ho).2.1.2.1

theorem execute_last_bounds (current : Nat) (out : List Nat) (ho : out ∈ execute current) :
    lf (interpretation 0 current) ≤ interpretation 0 (lastCode out) ∧
      interpretation 0 (lastCode out) ≤ interpretation 0 current ∧
        lf (interpretation 0 (lastCode out)) = lf (interpretation 0 current) := by
  have hs := (execute_spec current out ho).2.1
  exact ⟨hs.2.2.1, hs.2.1 _ (lastCode_mem out (execute_nonempty current out ho)), hs.2.2.2⟩

theorem execute_prefix_last (current : Nat) (out : List Nat) (ho : out ∈ execute current) :
    interpretation 0 (lastCode out) =
      factorProduct (factorPrefix (canonicalMNF (interpretation 0 (lastCode out)))) *
        lf (interpretation 0 current) := by
  have ht := (SourceTrackingRaw.trackingCheck_exact out).mp (execute_tracking current out ho)
  simpa only [(execute_last_bounds current out ho).2.2] using
    source_prefix_last ht.2.2.2.1 ht.2.2.2.2.1

theorem derivation_input (current : Nat) (word : List Nat) (hd : Derivation current word) :
    inputCheck current = true := by
  rcases derivation_flags current word hd with ⟨hm, he⟩ |
    ⟨hm, prefix, factor, heads, hf, hh, ho⟩
  · exact SourceMultiplicativePrincipal.rootAdapter_input current hm
  · exact (Bool.and_eq_true.mp (Factor.execute_spec current (prefix, factor) hf).1).1

/-- The executing procedure corresponds exactly to the original finite
recursive clauses; the relation is a conclusion of the actual computation. -/
theorem execute_iff_derivation (current : Nat) (word : List Nat) :
    word ∈ execute current ↔ Derivation current word := by
  constructor
  · intro ho; exact (execute_spec current word ho).2.2
  · intro hd
    obtain ⟨actual, ha⟩ := execute_returns current (derivation_input current word hd)
    have he := derivation_unique current word actual hd (execute_spec current actual ha).2.2
    simpa only [he] using ha

theorem execute_multiplicative (current : Nat)
    (hm : SourceMultiplicativePrincipal.inputCheck current = true) : rawWord current ∈ execute current :=
  (execute_iff_derivation current _).mpr (.multiplicative current hm)

/-- The actual child is produced by this same partial procedure, then the
real printed append/insertion dispatcher acts on its literal original word. -/
theorem execute_factor (current prefix factor : Nat) (heads out : List Nat)
    (hf : (prefix, factor) ∈ Factor.execute current) (hh : heads ∈ execute prefix)
    (ho : out ∈ Branches.execute (factor, heads)) : out ∈ execute current :=
  (execute_iff_derivation current out).mpr
    (.split current prefix factor heads out hf ((execute_iff_derivation prefix heads).mp hh) ho)

theorem execute_clauses (current : Nat) (out : List Nat) (ho : out ∈ execute current) :
    (SourceMultiplicativePrincipal.inputCheck current = true ∧ out = rawWord current) ∨
      (SourceMultiplicativePrincipal.inputCheck current = false ∧
        ∃ prefix factor heads, (prefix, factor) ∈ Factor.execute current ∧
          heads ∈ execute prefix ∧ out ∈ Branches.execute (factor, heads)) := by
  rcases derivation_flags current out (execute_spec current out ho).2.2 with
    hmul | ⟨hm, prefix, factor, heads, hf, hh, hout⟩
  · exact Or.inl hmul
  · exact Or.inr ⟨hm, prefix, factor, heads, hf,
      (execute_iff_derivation prefix heads).mpr hh, hout⟩

theorem execute_at_one (current : Nat) (hc : inputCheck current = true)
    (he : interpretation 0 current = 1) : [current] ∈ execute current := by
  have hi := (inputCheck_exact current).mp hc
  have hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 current) := by
    rw [he]
    exact ⟨zero_lt_one, Ordinal.isPrincipal_add_one, Ordinal.isPrincipal_mul_one⟩
  have hg := (SourceMultiplicativePrincipal.inputCheck_exact current).mpr ⟨hi.1, hi.2.1, hm⟩
  simpa only [SourceMultiplicativeTracking.Spelling.rawWord_at_one current hc he] using
    execute_multiplicative current hg

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.Assignment
