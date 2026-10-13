import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingBranches
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingFactorBounds
import Alexander313.Wilken.PublicEpsilonNativeMultiplicativeTrackingSpelling

/-!
# Executing factor descent and chronological unwind

The actual original RAW P input is factored repeatedly. Every written frame
retains its original input, computed prefix and computed final factor. The
first genuine M or singleton leaf supplies its actual finite word. A separate
finite stack loop unwinds the exact frames through the printed branch procedure.
No assigned word, factor stack, caller or numerical termination bound is given.
The semantic MNF measure and full joint correctness are proved in Assignment.
Source-only uncompiled candidate.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.AssignmentSupport

open PublicEpsilonUnboundedIota

/-- Every genuine original high root is an admitted raw epsilon input.
The raw parser is constructed by the existing exact original LOW criterion. -/
theorem high_root_raw_input (q root : Nat) (hr : Mu.inputCheck q root = true) :
    SourceTrackingRaw.Support.inputCheck q root = true :=
  (SourceTrackingRaw.Support.inputCheck_exact q root).mpr
    ⟨RootLowCollapse.root_low q root hr, Mu.root_base_lt q root hr,
      RootLowCollapse.root_epsilon q root hr⟩

/-- The genuine original root reference remains a RAW reference after the
actual raw parser has reconstructed each high root. Both values and mu are
identified by the proved same-source spelling theorem. -/
theorem reference_raw (q : Nat) (xs : List Nat)
    (hr : SourceTrackingSequences.Reference q xs) : SourceTrackingRaw.Reference q xs := by
  have hraw : ∀ c ∈ xs, SourceTrackingRaw.Support.inputCheck q c = true :=
    fun c hc => high_root_raw_input q c (hr.nodes c hc)
  refine ⟨hraw, ?_⟩
  induction hr with
  | nil =>
    simpa only [SourceTrackingRaw.Support.rootWord_nil] using
      (SourceTrackingSequences.Reference.nil : SourceTrackingSequences.Reference q [])
  | one a ha =>
    have hs := SourceTrackingRaw.Support.rootCode_spec q a (high_root_raw_input q a ha)
    simpa only [SourceTrackingRaw.Support.rootWord_cons, SourceTrackingRaw.Support.rootWord_nil] using
      SourceTrackingSequences.Reference.one (SourceTrackingRaw.Support.rootCode q a) hs.2.1
  | cons a b rest ha hab hcover tail ih =>
    have hca := high_root_raw_input q a ha
    have hcb := high_root_raw_input q b tail.first
    have hsa := SourceTrackingRaw.Support.rootCode_spec q a hca
    have hsb := SourceTrackingRaw.Support.rootCode_spec q b hcb
    have hmu := SourceTrackingRaw.Support.muValue_eq q a a hca ha rfl
    change Mu.sourceValue q (SourceTrackingRaw.Support.rootCode q a) = Mu.sourceValue q a at hmu
    simpa only [SourceTrackingRaw.Support.rootWord_cons] using
      SourceTrackingSequences.Reference.cons (SourceTrackingRaw.Support.rootCode q a)
        (SourceTrackingRaw.Support.rootCode q b) (SourceTrackingRaw.Support.rootWord q rest)
        hsa.2.1 (by simpa only [hsa.2.2, hsb.2.2] using hab)
        (by simpa only [hsb.2.2, hmu] using hcover) ih

/-- Original root-prefix tracking implies the genuine RAW recognizer.
The final raw code is retained and its actual cover is transported through
same-source mu spelling invariance; the two checkers are not identified by
unfolding or value equality alone. -/
theorem tracking_raw (q : Nat) (xs : List Nat)
    (ht : SourceTrackingSequences.trackingCheck q xs = true) :
    SourceTrackingRaw.trackingCheck q xs = true := by
  obtain ⟨hne, hr, hl, hp, hprincipal, hbound⟩ :=
    (SourceTrackingSequences.trackingCheck_exact q xs).mp ht
  apply (SourceTrackingRaw.trackingCheck_conditions q xs).mpr
  refine ⟨hne, reference_raw q _ hr, hl, hp, hprincipal, ?_⟩
  by_cases he : Hereditary.FinePredecessor.stripLast xs = []
  · simpa only [if_pos he] using hbound
  · have ha := hr.nodes _ (SourceTrackingSequences.lastCode_mem _ he)
    have hc := high_root_raw_input q _ ha
    have hm := SourceTrackingRaw.Support.muValue_eq q _ _ hc ha rfl
    rw [if_neg he] at hbound ⊢
    exact ⟨hbound.1, by simpa only [hm] using hbound.2⟩

abbrev Frame := Nat × (Nat × Nat)
abbrev DownState := (Nat × Nat) × List Frame
abbrev LeafOutput := Nat × (List Nat × List Frame)
abbrev UpState := (Nat × List Nat) × List Frame

def Leaf (q current : Nat) (word : List Nat) : Prop :=
  (SourceMultiplicativePrincipal.inputCheck q current = true ∧
      word = SourceMultiplicativeTracking.rawWord q current) ∨
    (SourceMultiplicativePrincipal.inputCheck q current = false ∧
      Factor.singletonCheck q current = true ∧ word = [current])

/-- Frames retain the actual original factor execution, rather than a
semantic factorization chosen independently of the computation. -/
inductive Stack (q : Nat) : Nat → List Frame → Nat → Prop
  | nil (current : Nat) : Stack q current [] current
  | cons (input prefix factor : Nat) (frames : List Frame) (target : Nat)
      (split : (prefix, factor) ∈ Factor.execute q input)
      (rest : Stack q input frames target) :
      Stack q prefix ((input, (prefix, factor)) :: frames) target

/-- Actual source clauses retain the computed M leaf, literal singleton,
or genuine computed prefix/factor and recursively constructed headword. -/
inductive Derivation (q : Nat) : Nat → List Nat → Prop
  | multiplicative (current : Nat)
      (checked : SourceMultiplicativePrincipal.inputCheck q current = true) :
      Derivation q current (SourceMultiplicativeTracking.rawWord q current)
  | singleton (current : Nat)
      (nonM : SourceMultiplicativePrincipal.inputCheck q current = false)
      (checked : Factor.singletonCheck q current = true) : Derivation q current [current]
  | split (input prefix factor : Nat) (heads out : List Nat)
      (factorization : (prefix, factor) ∈ Factor.execute q input)
      (headword : Derivation q prefix heads)
      (branches : out ∈ Branches.execute ((q, factor), heads)) : Derivation q input out

def downStep (p : DownState) : Part (LeafOutput ⊕ DownState) :=
  cond (SourceMultiplicativePrincipal.inputCheck p.1.1 p.1.2)
    (Part.some (Sum.inl (p.1.2, (SourceMultiplicativeTracking.rawWord p.1.1 p.1.2, p.2))))
    (cond (Factor.singletonCheck p.1.1 p.1.2)
      (Part.some (Sum.inl (p.1.2, ([p.1.2], p.2))))
      ((Factor.execute p.1.1 p.1.2).map fun split =>
        Sum.inr ((p.1.1, split.1), (p.1.2, split) :: p.2)))

theorem downStep_partrec : Partrec downStep := by
  have hq : Primrec (fun p : DownState => p.1.1) := Primrec.fst.comp Primrec.fst
  have hc : Primrec (fun p : DownState => p.1.2) := Primrec.snd.comp Primrec.fst
  have hs : Primrec (fun p : DownState => p.2) := Primrec.snd
  have hm := SourceMultiplicativePrincipal.inputCheck_primrec.comp hq hc
  have hz := Factor.singletonCheck_primrec.comp hq hc
  have hw := SourceMultiplicativeTracking.rawWord_primrec.comp hq hc
  have hn := Primrec.list_cons.comp hc (Primrec.const [])
  have hleaf := Primrec.sumInl.comp (hc.pair (hw.pair hs))
  have hsingle := Primrec.sumInl.comp (hc.pair (hn.pair hs))
  have he := Partrec.comp Factor.execute_partrec (hq.pair hc).to_comp
  have hout : Computable₂ (fun p : DownState => fun split : Nat × Nat =>
      Sum.inr ((p.1.1, split.1), (p.1.2, split) :: p.2) : LeafOutput ⊕ DownState) :=
    (Primrec.sumInr.comp
      (((hq.comp Primrec.fst).pair (Primrec.fst.comp Primrec.snd)).pair
        (Primrec.list_cons.comp ((hc.comp Primrec.fst).pair Primrec.snd)
          (hs.comp Primrec.fst)))).to_comp.to₂
  exact Partrec.cond hm.to_comp hleaf.to_comp.partrec
    (Partrec.cond hz.to_comp hsingle.to_comp.partrec (Partrec.map he hout))

theorem downStep_stop (p : DownState) (out : LeafOutput)
    (ho : Sum.inl out ∈ downStep p) :
    out.1 = p.1.2 ∧ out.2.2 = p.2 ∧ Leaf p.1.1 p.1.2 out.2.1 := by
  cases hm : SourceMultiplicativePrincipal.inputCheck p.1.1 p.1.2 with
  | true =>
    have he : out = (p.1.2, (SourceMultiplicativeTracking.rawWord p.1.1 p.1.2, p.2)) := by
      simpa only [downStep, hm, Bool.cond_true, Part.mem_some_iff, Sum.inl.injEq] using ho
    rw [he]
    exact ⟨rfl, rfl, Or.inl ⟨hm, rfl⟩⟩
  | false =>
    cases hz : Factor.singletonCheck p.1.1 p.1.2 with
    | true =>
      have he : out = (p.1.2, ([p.1.2], p.2)) := by
        simpa only [downStep, hm, hz, Bool.cond_false, Bool.cond_true,
          Part.mem_some_iff, Sum.inl.injEq] using ho
      rw [he]
      exact ⟨rfl, rfl, Or.inr ⟨hm, hz, rfl⟩⟩
    | false =>
      have ho : Sum.inl out ∈ (Factor.execute p.1.1 p.1.2).map
          (fun split => Sum.inr ((p.1.1, split.1), (p.1.2, split) :: p.2)) := by
        simpa only [downStep, hm, hz, Bool.cond_false] using ho
      obtain ⟨split, hsplit, he⟩ := (Part.mem_map_iff _).mp ho
      simp only [Sum.inr_ne_inl] at he

theorem downStep_continue (p next : DownState)
    (hn : Sum.inr next ∈ downStep p) :
    ∃ prefix factor, SourceMultiplicativePrincipal.inputCheck p.1.1 p.1.2 = false ∧
      Factor.singletonCheck p.1.1 p.1.2 = false ∧
      (prefix, factor) ∈ Factor.execute p.1.1 p.1.2 ∧
      next = ((p.1.1, prefix), (p.1.2, (prefix, factor)) :: p.2) := by
  cases hm : SourceMultiplicativePrincipal.inputCheck p.1.1 p.1.2 with
  | true => simp only [downStep, hm, Bool.cond_true, Part.mem_some_iff, Sum.inr_ne_inl] at hn
  | false =>
    cases hz : Factor.singletonCheck p.1.1 p.1.2 with
    | true =>
      simp only [downStep, hm, hz, Bool.cond_false, Bool.cond_true,
        Part.mem_some_iff, Sum.inr_ne_inl] at hn
    | false =>
      have hn : Sum.inr next ∈ (Factor.execute p.1.1 p.1.2).map
          (fun split => Sum.inr ((p.1.1, split.1), (p.1.2, split) :: p.2)) := by
        simpa only [downStep, hm, hz, Bool.cond_false] using hn
      obtain ⟨⟨prefix, factor⟩, hs, he⟩ := (Part.mem_map_iff _).mp hn
      exact ⟨prefix, factor, hm, hz, hs, Sum.inr.inj he.symm⟩

def down : DownState → Part LeafOutput := PFun.fix downStep

theorem down_partrec : Partrec down := Partrec.fix downStep_partrec

/-- Actual fix induction records every original computed frame, including
its exact prefix code, and the actual terminal branch. -/
theorem down_relation (p : DownState) (out : LeafOutput) (ho : out ∈ down p) :
    Leaf p.1.1 out.1 out.2.1 ∧
      ∀ target, Stack p.1.1 p.1.2 p.2 target → Stack p.1.1 out.1 out.2.2 target := by
  let C : DownState → Prop := fun s => Leaf s.1.1 out.1 out.2.1 ∧
    ∀ target, Stack s.1.1 s.1.2 s.2 target → Stack s.1.1 out.1 out.2.2 target
  apply PFun.fixInduction (C := C) ho
  intro s hs ih
  rcases PFun.mem_fix_iff.mp hs with hstop | ⟨next, hn, hout⟩
  · obtain ⟨hc, hframes, hl⟩ := downStep_stop s out hstop
    exact ⟨by simpa only [hc] using hl, fun target hstack => by
      simpa only [hc, hframes] using hstack⟩
  · obtain ⟨prefix, factor, hm, hz, hsplit, he⟩ := downStep_continue s next hn
    have hnext := ih next hn
    rw [he] at hnext
    exact ⟨hnext.1, fun target hstack =>
      hnext.2 target (.cons s.1.2 prefix factor s.2 target hsplit hstack)⟩

def upStep (p : UpState) : Part (List Nat ⊕ UpState) :=
  cond (p.2.length == 0) (Part.some (Sum.inl p.1.2))
    ((Branches.execute ((p.1.1, ((p.2.head?).getD (0, (0, 0))).2.2), p.1.2)).map
      fun word => Sum.inr ((p.1.1, word), p.2.tail))

theorem upStep_partrec : Partrec upStep := by
  have hq : Primrec (fun p : UpState => p.1.1) := Primrec.fst.comp Primrec.fst
  have hw : Primrec (fun p : UpState => p.1.2) := Primrec.snd.comp Primrec.fst
  have hs : Primrec (fun p : UpState => p.2) := Primrec.snd
  have hh := Primrec.option_getD.comp (Primrec.list_head?.comp hs) (Primrec.const (0, (0, 0)))
  have hf := Primrec.snd.comp (Primrec.snd.comp hh)
  have hz := Primrec.beq.comp (Primrec.list_length.comp hs) (Primrec.const 0)
  have he := Partrec.comp Branches.execute_partrec ((hq.pair hf).pair hw).to_comp
  have hout : Computable₂ (fun p : UpState => fun word : List Nat =>
      Sum.inr ((p.1.1, word), p.2.tail) : List Nat ⊕ UpState) :=
    (Primrec.sumInr.comp (((hq.comp Primrec.fst).pair Primrec.snd).pair
      (Primrec.list_tail.comp (hs.comp Primrec.fst)))).to_comp.to₂
  exact Partrec.cond hz.to_comp (Primrec.sumInl.comp hw).to_comp.partrec (Partrec.map he hout)

theorem upStep_nil (q : Nat) (word : List Nat) :
    upStep ((q, word), []) = Part.some (Sum.inl word) := by
  simp only [upStep, List.length_nil, beq_self_eq_true, Bool.cond_true]

theorem upStep_cons (q : Nat) (word : List Nat) (frame : Frame) (frames : List Frame) :
    upStep ((q, word), frame :: frames) =
      (Branches.execute ((q, frame.2.2), word)).map
        (fun out => Sum.inr ((q, out), frames)) := by
  simp [upStep]

theorem upStep_stop (p : UpState) (out : List Nat) (ho : Sum.inl out ∈ upStep p) :
    p.2 = [] ∧ out = p.1.2 := by
  rcases p with ⟨⟨q, word⟩, frames⟩
  cases frames with
  | nil =>
    rw [upStep_nil] at ho
    exact ⟨rfl, by simpa only [Part.mem_some_iff, Sum.inl.injEq] using ho⟩
  | cons frame frames =>
    rw [upStep_cons] at ho
    obtain ⟨next, hn, he⟩ := (Part.mem_map_iff _).mp ho
    simp only [Sum.inr_ne_inl] at he

theorem upStep_continue (p next : UpState) (hn : Sum.inr next ∈ upStep p) :
    ∃ frame frames word, p.2 = frame :: frames ∧
      word ∈ Branches.execute ((p.1.1, frame.2.2), p.1.2) ∧
      next = ((p.1.1, word), frames) := by
  rcases p with ⟨⟨q, oldWord⟩, frames⟩
  cases frames with
  | nil =>
    rw [upStep_nil] at hn
    simp only [Part.mem_some_iff, Sum.inr_ne_inl] at hn
  | cons frame frames =>
    rw [upStep_cons] at hn
    obtain ⟨word, hw, he⟩ := (Part.mem_map_iff _).mp hn
    exact ⟨frame, frames, word, rfl, hw, Sum.inr.inj he.symm⟩

def up : UpState → Part (List Nat) := PFun.fix upStep

theorem up_partrec : Partrec up := Partrec.fix upStep_partrec

def execute (q current : Nat) : Part (List Nat) :=
  (down ((q, current), [])).bind (fun leaf => up ((q, leaf.2.1), leaf.2.2))

theorem execute_partrec : Partrec₂ execute := by
  have hd := down_partrec.comp (Primrec.id.pair (Primrec.const [])).to_comp
  have he : Partrec₂ (fun p : Nat × Nat => fun leaf : LeafOutput =>
      up ((p.1, leaf.2.1), leaf.2.2)) :=
    (up_partrec.comp
      (((Primrec.fst.comp Primrec.fst).pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))).pair
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).to_comp).to₂
  exact (Partrec.bind hd he).to₂

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.AssignmentSupport
