import Alexander313.Wilken.SourceOneNativeAdditiveTrackingFactorBounds
import Alexander313.Wilken.SourceOneNativeAdditiveTrackingBranchBounds
import Alexander313.Wilken.SourceOneNativeMultiplicativeTrackingRecurrence

/-!
# Genuine original source-one factor descent and finite unwind

Actual multiplicative leaves use the independent source-zero localization
word. Its original member bounds are derived from the real proper prefix.
The downward partial fixpoint executes genuine factor removal and records
each unchanged input and its actual prefix/factor pair. Proof-only MNF
length strictly decreases. A separate upward partial fixpoint executes the
actual printed append/insertion branch on every stored frame. No numerical
fuel, assigned headword, final=input equality or Native base-one grammar.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.AssignmentSupport

open NativeContext.SourceTrackingSequences (lastCode)
open Alexander313.Wilken.MultiplicativeNormalForm
open SourceMultiplicativeTracking (rawWord)

/-- Every original M leaf member comes from actual localization or the
unchanged current raw code; a tracking-image bound is not assumed. -/
theorem multiplicative_word_bound (c : Nat)
    (hc : SourceMultiplicativePrincipal.inputCheck c = true) :
    ∀ d ∈ rawWord c, interpretation 0 d ≤ interpretation 0 c := by
  have hr := SourceMultiplicativePrincipal.rootInput c hc
  have hv := SourceLocalization.RootAdapter.rootCode_value c
    (SourceMultiplicativePrincipal.rootAdapter_input c hc)
  intro d hd
  cases hs : SourceMultiplicativeTracking.Support.select c
      (SourceMultiplicativeTracking.Support.table
        (SourceMultiplicativeTracking.Prefix.properPrefix
          (SourceLocalization.RootAdapter.rootCode c))) with
  | none =>
    have he := SourceMultiplicativeTracking.Recurrence.rawWord_none c hs
    rw [he] at hd
    simpa only [List.mem_singleton.mp hd] using
      (le_rfl : interpretation 0 c ≤ interpretation 0 c)
  | some entry =>
    have he : rawWord c = entry.2 ++ [c] := by
      simp only [rawWord, SourceMultiplicativeTracking.Support.extend, hs]
    rw [he] at hd
    rcases List.mem_append.mp hd with hd | hd
    · have hentry := SourceMultiplicativeTracking.Support.select_mem c _ entry hs
      have hm := SourceMultiplicativeTracking.Support.buildRev_word_mem
        (SourceMultiplicativeTracking.Prefix.properPrefix
          (SourceLocalization.RootAdapter.rootCode c)).reverse entry hentry d hd
      have hb := SourceMultiplicativeTracking.Prefix.properPrefix_le_root _ hr d (List.mem_reverse.mp hm)
      exact hb.trans_eq hv
    · simpa only [List.mem_singleton.mp hd] using
        (le_rfl : interpretation 0 c ≤ interpretation 0 c)

abbrev Frame := Nat × Factor.Output
abbrev DownState := Nat × List Frame
abbrev UpState := List Nat × List Frame

/-- Every frame is an actual original factor execution, with its real
prefix as the current source value. Initial empty frames are derived. -/
inductive Frames : Nat → List Frame → Nat → Prop
  | nil (c : Nat) : Frames c [] c
  | push (c : Nat) (pair : Factor.Output) (saved : List Frame) (root : Nat)
      (ho : pair ∈ Factor.execute c) (hs : Frames c saved root) :
      Frames pair.1 ((c, pair) :: saved) root

/-- The genuine recursive source clauses use the same original grammar
and retain actual factor and printed-branch executions. -/
inductive Derivation : Nat → List Nat → Prop
  | multiplicative (current : Nat)
      (checked : SourceMultiplicativePrincipal.inputCheck current = true) :
      Derivation current (rawWord current)
  | split (input prefix factor : Nat) (heads out : List Nat)
      (factorization : (prefix, factor) ∈ Factor.execute input)
      (headword : Derivation prefix heads)
      (branches : out ∈ Branches.execute (factor, heads)) : Derivation input out

def downStep (p : DownState) : Part (UpState ⊕ DownState) :=
  cond (SourceMultiplicativePrincipal.inputCheck p.1)
    (Part.some (Sum.inl (rawWord p.1, p.2)))
    ((Factor.execute p.1).map fun pair => Sum.inr (pair.1, (p.1, pair) :: p.2))

theorem downStep_partrec : Partrec downStep := by
  have hm := SourceMultiplicativePrincipal.inputCheck_primrec.comp Primrec.fst
  have hl := Primrec.sumInl.comp
    ((SourceMultiplicativeTracking.rawWord_primrec.comp Primrec.fst).pair Primrec.snd)
  have he := Factor.execute_partrec.comp Primrec.fst.to_comp
  have hf : Computable₂ (fun p : DownState => fun pair : Factor.Output =>
      Sum.inr (pair.1, (p.1, pair) :: p.2) : UpState ⊕ DownState) :=
    (Primrec.sumInr.comp ((Primrec.fst.comp Primrec.snd).pair
      (Primrec.list_cons.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)
        (Primrec.snd.comp Primrec.fst)))).to_comp.to₂
  exact Partrec.cond hm.to_comp hl.to_comp.partrec (Partrec.map he hf)

theorem downStep_leaf (c : Nat) (saved : List Frame)
    (hm : SourceMultiplicativePrincipal.inputCheck c = true) :
    downStep (c, saved) = Part.some (Sum.inl (rawWord c, saved)) := by
  simp only [downStep, hm, Bool.cond_true]

theorem downStep_factor (c : Nat) (saved : List Frame)
    (hm : SourceMultiplicativePrincipal.inputCheck c = false) :
    downStep (c, saved) = (Factor.execute c).map
      (fun pair => Sum.inr (pair.1, (c, pair) :: saved)) := by
  simp only [downStep, hm, Bool.cond_false]

theorem downStep_stop (p : DownState) (out : UpState) (ho : Sum.inl out ∈ downStep p) :
    SourceMultiplicativePrincipal.inputCheck p.1 = true ∧ out = (rawWord p.1, p.2) := by
  rcases p with ⟨c, saved⟩
  cases hm : SourceMultiplicativePrincipal.inputCheck c with
  | true =>
    rw [downStep_leaf c saved hm] at ho
    exact ⟨hm, by simpa only [Part.mem_some_iff, Sum.inl.injEq] using ho⟩
  | false =>
    rw [downStep_factor c saved hm] at ho
    obtain ⟨pair, hp, he⟩ := (Part.mem_map_iff _).mp ho
    simp only [Sum.inr_ne_inl] at he

theorem downStep_continue (p next : DownState) (hn : Sum.inr next ∈ downStep p) :
    ∃ pair, pair ∈ Factor.execute p.1 ∧ next = (pair.1, (p.1, pair) :: p.2) := by
  rcases p with ⟨c, saved⟩
  cases hm : SourceMultiplicativePrincipal.inputCheck c with
  | true =>
    rw [downStep_leaf c saved hm] at hn
    simp only [Part.mem_some_iff, Sum.inr_ne_inl] at hn
  | false =>
    rw [downStep_factor c saved hm] at hn
    obtain ⟨pair, hp, he⟩ := (Part.mem_map_iff _).mp hn
    exact ⟨pair, hp, Sum.inr.inj he.symm⟩

def down : DownState → Part UpState := PFun.fix downStep

theorem down_partrec : Partrec down := Partrec.fix downStep_partrec

/-- Genuine canonical MNF length is only a proof measure; the procedure
receives no bound and executes the actual prefix/factor algorithm. -/
theorem down_returns (c : Nat) (hc : SourceLocalization.RootAdapter.inputCheck c = true)
    (saved : List Frame) : ∃ out, out ∈ down (c, saved) := by
  let P : Nat → Prop := fun n => ∀ d : Nat,
    (canonicalMNF (interpretation 0 d)).length = n →
      SourceLocalization.RootAdapter.inputCheck d = true →
        ∀ frames : List Frame, ∃ out, out ∈ down (d, frames)
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro d hn hd frames
      cases hm : SourceMultiplicativePrincipal.inputCheck d with
      | true =>
        exact ⟨(rawWord d, frames), PFun.mem_fix_iff.mpr (Or.inl
          (by rw [downStep_leaf d frames hm]; exact Part.mem_some _))⟩
      | false =>
        have hf : Factor.inputCheck d = true := by
          simp only [Factor.inputCheck, hd, hm, Bool.not_false, Bool.and_true]
        obtain ⟨pair, hp⟩ := Part.dom_iff_mem.mp ((Factor.execute_domain d).mpr hf)
        obtain ⟨_, _, _, hcaller, _, _, _, _, _, _, hcount⟩ := Factor.execute_spec d pair hp
        have hcount' : (canonicalMNF (interpretation 0 pair.1)).length < n := by
          simpa only [hn] using hcount
        obtain ⟨out, ho⟩ := ih _ hcount' pair.1 rfl hcaller ((d, pair) :: frames)
        exact ⟨out, PFun.mem_fix_iff.mpr (Or.inr
          ⟨(pair.1, (d, pair) :: frames),
            by rw [downStep_factor d frames hm]; exact Part.mem_map _ hp, ho⟩)⟩
  exact hP _ c rfl hc saved

/-- Fixpoint membership derives every stored frame and the independent M
leaf. No source word, factorization or endpoint is a supplied input. -/
theorem down_frames (p : DownState) (out : UpState) (ho : out ∈ down p)
    (root : Nat) (hs : Frames p.1 p.2 root) :
    ∃ leaf, SourceMultiplicativePrincipal.inputCheck leaf = true ∧
      out.1 = rawWord leaf ∧ Frames leaf out.2 root := by
  let C : DownState → Prop := fun s => ∀ root : Nat, Frames s.1 s.2 root →
    ∃ leaf, SourceMultiplicativePrincipal.inputCheck leaf = true ∧
      out.1 = rawWord leaf ∧ Frames leaf out.2 root
  have h : C p := by
    apply PFun.fixInduction (C := C) ho
    intro s hmem ih root hframes
    rcases PFun.mem_fix_iff.mp hmem with hstop | ⟨next, hn, hout⟩
    · obtain ⟨hm, he⟩ := downStep_stop s out hstop
      exact ⟨s.1, hm, by rw [he], by rw [he]; exact hframes⟩
    · obtain ⟨pair, hp, hnext⟩ := downStep_continue s next hn
      apply ih next hn root
      rw [hnext]
      exact Frames.push s.1 pair s.2 root hp hframes
  exact h root hs

def upStep (p : UpState) : Part (List Nat ⊕ UpState) :=
  cond (p.2.length == 0) (Part.some (Sum.inl p.1))
    ((Branches.execute (((p.2.head?).getD (0, (0, 0))).2.2, p.1)).map
      (fun out => Sum.inr (out, p.2.tail)))

theorem upStep_partrec : Partrec upStep := by
  have hz := Primrec.beq.comp (Primrec.list_length.comp Primrec.snd) (Primrec.const 0)
  have hh := Primrec.option_getD.comp (Primrec.list_head?.comp Primrec.snd) (Primrec.const (0, (0, 0)))
  have he : Partrec (fun p : UpState => Branches.execute (((p.2.head?).getD (0, (0, 0))).2.2, p.1)) :=
    Branches.execute_partrec.comp
      (((Primrec.snd.comp Primrec.snd).comp hh).pair Primrec.fst).to_comp
  have hm : Computable₂ (fun p : UpState => fun out : List Nat =>
      Sum.inr (out, p.2.tail) : List Nat ⊕ UpState) :=
    (Primrec.sumInr.comp (Primrec.snd.pair
      (Primrec.list_tail.comp (Primrec.snd.comp Primrec.fst)))).to_comp.to₂
  exact Partrec.cond hz.to_comp (Primrec.sumInl.comp Primrec.fst).to_comp.partrec
    (Partrec.map he hm)

theorem upStep_nil (word : List Nat) : upStep (word, []) = Part.some (Sum.inl word) := by
  simp only [upStep, List.length_nil, beq_self_eq_true, Bool.cond_true]

theorem upStep_cons (word : List Nat) (frame : Frame) (saved : List Frame) :
    upStep (word, frame :: saved) =
      (Branches.execute (frame.2.2, word)).map (fun out => Sum.inr (out, saved)) := by
  simp [upStep]

theorem upStep_stop (p : UpState) (out : List Nat) (ho : Sum.inl out ∈ upStep p) :
    p.2 = [] ∧ out = p.1 := by
  rcases p with ⟨word, saved⟩
  cases saved with
  | nil =>
    rw [upStep_nil] at ho
    exact ⟨rfl, by simpa only [Part.mem_some_iff, Sum.inl.injEq] using ho⟩
  | cons frame saved =>
    rw [upStep_cons] at ho
    obtain ⟨nextword, hw, he⟩ := (Part.mem_map_iff _).mp ho
    simp only [Sum.inr_ne_inl] at he

theorem upStep_continue (p next : UpState) (hn : Sum.inr next ∈ upStep p) :
    ∃ frame saved word, p.2 = frame :: saved ∧
      word ∈ Branches.execute (frame.2.2, p.1) ∧ next = (word, saved) := by
  rcases p with ⟨word, saved⟩
  cases saved with
  | nil =>
    rw [upStep_nil] at hn
    simp only [Part.mem_some_iff, Sum.inr_ne_inl] at hn
  | cons frame saved =>
    rw [upStep_cons] at hn
    obtain ⟨nextword, hw, he⟩ := (Part.mem_map_iff _).mp hn
    exact ⟨frame, saved, nextword, rfl, hw, Sum.inr.inj he.symm⟩

def up : UpState → Part (List Nat) := PFun.fix upStep

theorem up_partrec : Partrec up := Partrec.fix upStep_partrec

def execute (current : Nat) : Part (List Nat) :=
  cond (SourceLocalization.RootAdapter.inputCheck current)
    ((down (current, [])).bind up) Part.none

theorem execute_partrec : Partrec execute := by
  have hd := down_partrec.comp (Primrec.id.pair (Primrec.const [])).to_comp
  have hu : Partrec₂ (fun _ : Nat => fun out : UpState => up out) :=
    (up_partrec.comp Primrec.snd.to_comp).to₂
  exact Partrec.cond SourceLocalization.RootAdapter.inputCheck_primrec.to_comp
    (Partrec.bind hd hu) Partrec.none

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.AssignmentSupport
