import Alexander313.Wilken.PublicEpsilonNativeRootAboveHeadCollapseSupport
import Alexander313.Wilken.PublicEpsilonNativeRootEndpointCollapseSupport

/-!
# Actual relative collapse below the original divided head

The original high root and admitted Normal theta-zero-sort argument feed
real source comparisons: the computed cardinal head is positive, strictly
below the original root's divided head, and its genuine source collapse
is at most the root. The actual principal-word decomposition derives all
notation, division and LOW residual callers. Real native addition builds
Gamma+(beta+rho), and its admitted Normal theta-zero node has exactly the
beta-relative collapse value. No selected endpoint, supplied beta code,
notation, hull, target admission or relative-collapse oracle. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RootBelowHeadCollapse

open ThetaCourse

abbrev Query := RootAboveHeadCollapse.Query
abbrev argumentCheck := RootAboveHeadCollapse.argumentCheck
abbrev headCode := RootAboveHeadCollapse.headCode

def tailCode (c : Nat) : Nat := Decomposition.lowCode 0 c

theorem tailCode_primrec : Primrec tailCode :=
  Decomposition.lowCode_primrec.comp (Primrec.const 0) Primrec.id

theorem parts_accepted (q c : Nat) (hc : argumentCheck q c = true) :
    Comparison.acceptedCode q (headCode c) = true ∧
      Comparison.acceptedCode q (tailCode c) = true :=
  Decomposition.parts_accepted q 0 c ((RootAboveHeadCollapse.argumentCheck_exact q c).mp hc).1

theorem delta_accepted (q b : Nat) (hb : RootLowCollapse.rootCheck q b = true) :
    Comparison.acceptedCode q (RootEndpointCollapse.deltaCode b) = true :=
  (Decomposition.parts_accepted q 0 _ (RootEndpointCollapse.argument_accepted q b hb)).1

def headBelow (q b c : Nat) : Bool :=
  Normalization.lessRawCode q (headCode c) (RootEndpointCollapse.deltaCode b)

theorem headBelow_primrec : Primrec (fun p : Query => headBelow p.1 p.2.1 p.2.2) :=
  Normalization.Effective.lessRawCode_primrec.comp (Primrec.fst.pair
    ((RootAboveHeadCollapse.headCode_primrec.comp (Primrec.snd.comp Primrec.snd)).pair
      (RootEndpointCollapse.deltaCode_primrec.comp (Primrec.fst.comp Primrec.snd))))

theorem headBelow_exact (q b c : Nat) (hb : RootLowCollapse.rootCheck q b = true)
    (hc : argumentCheck q c = true) : headBelow q b c = true ↔
    interpretation q (headCode c) < interpretation q (RootEndpointCollapse.deltaCode b) := by
  simpa only [headBelow, ((Comparison.acceptedCode_exact q _).mp
    (parts_accepted q c hc).1).1, ((Comparison.acceptedCode_exact q _).mp
      (delta_accepted q b hb)).1, true_and] using
    Normalization.lessRawCode_exact q (headCode c) (RootEndpointCollapse.deltaCode b)

def branchCheck (q b c : Nat) : Bool := !FixedPoint.zeroCheck (headCode c) &&
  (headBelow q b c && !RootAboveHeadCollapse.headAbove q b c)

theorem branchCheck_primrec : Primrec (fun p : Query => branchCheck p.1 p.2.1 p.2.2) :=
  Primrec.and.comp (Primrec.not.comp (FixedPoint.zeroCheck_primrec.comp
    (RootAboveHeadCollapse.headCode_primrec.comp (Primrec.snd.comp Primrec.snd))))
    (Primrec.and.comp headBelow_primrec
      (Primrec.not.comp RootAboveHeadCollapse.headAbove_primrec))

/-- Every branch test executes on genuine original callers. -/
theorem branchCheck_exact (q b c : Nat) (hb : RootLowCollapse.rootCheck q b = true)
    (hc : argumentCheck q c = true) : branchCheck q b c = true ↔
    0 < interpretation q (headCode c) ∧
      interpretation q (headCode c) < interpretation q (RootEndpointCollapse.deltaCode b) ∧
      globalCollapse (base q) 0 (interpretation q (headCode c)) ≤ interpretation q b := by
  have hz := FixedPoint.zeroCheck_exact q (headCode c) (parts_accepted q c hc).1
  have hl := headBelow_exact q b c hb hc
  have ha := RootAboveHeadCollapse.headAbove_exact q b c hb hc
  simp only [branchCheck, Bool.and_eq_true, Bool.not_eq_true']
  constructor
  · rintro ⟨hnz, hlt, hna⟩
    refine ⟨pos_iff_ne_zero.mpr ?_, hl.mp hlt, le_of_not_gt ?_⟩
    · intro he
      have hh := hz.mpr he
      simp only [hnz, Bool.false_eq_true] at hh
    · intro hh
      have ht := ha.mpr hh
      simp only [hna, Bool.false_eq_true] at ht
  · rintro ⟨hp, hlt, hle⟩
    refine ⟨?_, hl.mpr hlt, ?_⟩
    · cases he : FixedPoint.zeroCheck (headCode c) with
      | false => rfl
      | true => exact False.elim (hp.ne' (hz.mp he))
    · cases he : RootAboveHeadCollapse.headAbove q b c with
      | false => rfl
      | true => exact False.elim ((not_lt_of_ge hle) (ha.mp he))

def inputCheck (q b c : Nat) : Bool := RootLowCollapse.rootCheck q b &&
  (argumentCheck q c && branchCheck q b c)

theorem inputCheck_primrec : Primrec (fun p : Query => inputCheck p.1 p.2.1 p.2.2) :=
  Primrec.and.comp
    (RootLowCollapse.rootCheck_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
    (Primrec.and.comp (RootAboveHeadCollapse.argumentCheck_primrec.comp Primrec.fst
      (Primrec.snd.comp Primrec.snd)) branchCheck_primrec)

theorem inputCheck_guards (q b c : Nat) (hi : inputCheck q b c = true) :
    RootLowCollapse.rootCheck q b = true ∧ argumentCheck q c = true ∧ branchCheck q b c = true := by
  simpa only [inputCheck, Bool.and_eq_true, and_assoc] using hi

/-- The complete original computed below-head branch, with no endpoint
or supplied semantic, notation or target-caller condition. -/
theorem inputCheck_exact (q b c : Nat) : inputCheck q b c = true ↔
    RootLowCollapse.rootCheck q b = true ∧ argumentCheck q c = true ∧
      0 < interpretation q (headCode c) ∧
      interpretation q (headCode c) < interpretation q (RootEndpointCollapse.deltaCode b) ∧
      globalCollapse (base q) 0 (interpretation q (headCode c)) ≤ interpretation q b := by
  constructor
  · intro hi
    have hs := inputCheck_guards q b c hi
    exact ⟨hs.1, hs.2.1, (branchCheck_exact q b c hs.1 hs.2.1).mp hs.2.2⟩
  · rintro ⟨hb, hc, hs⟩
    exact Bool.and_eq_true.mpr ⟨hb, Bool.and_eq_true.mpr
      ⟨hc, (branchCheck_exact q b c hb hc).mpr hs⟩⟩

theorem argument_high (q b c : Nat) (hi : inputCheck q b c = true) :
    1 < (rawTree c).outerSort := by
  have hs := (inputCheck_exact q b c).mp hi
  have hc := (RootAboveHeadCollapse.argumentCheck_exact q c).mp hs.2.1
  have ht := (Comparison.acceptedCode_exact q c).mp hc.1
  have hd := RootAboveHeadCollapse.head_spec q c hs.2.1
  have hhigh : omegaSequence (base q) 1 ≤ interpretation q c :=
    (Ordinal.le_of_dvd hs.2.2.1.ne' hd.2.2.1).trans
      (Decomposition.parts_le q 0 c hc.1).1
  apply lt_of_not_ge
  intro hl
  have hh := (denote_lt_iff_outerSort_le q _ (Arithmetic.raw_checked q c ht.1) 1 (by omega)).mpr hl
  rw [Arithmetic.raw_value q c ht.1] at hh
  exact (not_lt_of_ge hhigh) hh

def insertedTailCode (q b c : Nat) : Nat := Arithmetic.addCode q b (tailCode c)

theorem insertedTailCode_primrec : Primrec (fun p : Query => insertedTailCode p.1 p.2.1 p.2.2) :=
  Arithmetic.addCode_primrec.comp (Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair
    (tailCode_primrec.comp (Primrec.snd.comp Primrec.snd))))

theorem insertedTailCode_spec (q b c : Nat) (hi : inputCheck q b c = true) :
    Comparison.acceptedCode q (insertedTailCode q b c) = true ∧
      interpretation q (insertedTailCode q b c) = interpretation q b + interpretation q (tailCode c) ∧
      interpretation q (insertedTailCode q b c) < omegaSequence (base q) 1 := by
  have hs := inputCheck_guards q b c hi
  have ht := Arithmetic.addCode_spec q b (tailCode c) (RootLowCollapse.root_original q b hs.1)
    ((Comparison.acceptedCode_exact q _).mp (parts_accepted q c hs.2.1).2).1
  refine ⟨ht.1, ht.2.1, ?_⟩
  rw [show interpretation q (insertedTailCode q b c) = interpretation q b +
    interpretation q (tailCode c) from ht.2.1]
  exact (omegaSequence_add_closed (base q) 0) (RootLowCollapse.root_lt_first q b hs.1)
    (RootAboveHeadCollapse.head_spec q c hs.2.1).2.2.2.1

def shiftedArgumentCode (q b c : Nat) : Nat :=
  Arithmetic.addCode q (headCode c) (insertedTailCode q b c)

theorem shiftedArgumentCode_primrec :
    Primrec (fun p : Query => shiftedArgumentCode p.1 p.2.1 p.2.2) :=
  Arithmetic.addCode_primrec.comp (Primrec.fst.pair
    ((RootAboveHeadCollapse.headCode_primrec.comp (Primrec.snd.comp Primrec.snd)).pair
      insertedTailCode_primrec))

theorem shiftedArgumentCode_spec (q b c : Nat) (hi : inputCheck q b c = true) :
    Comparison.acceptedCode q (shiftedArgumentCode q b c) = true ∧
      interpretation q (shiftedArgumentCode q b c) =
        interpretation q (headCode c) + (interpretation q b + interpretation q (tailCode c)) ∧
      interpretation q (shiftedArgumentCode q b c) < omegaSequence (base q) 2 := by
  have hs := inputCheck_guards q b c hi
  have ht := insertedTailCode_spec q b c hi
  have ha := Arithmetic.addCode_spec q (headCode c) (insertedTailCode q b c)
    ((Comparison.acceptedCode_exact q _).mp (parts_accepted q c hs.2.1).1).1
    ((Comparison.acceptedCode_exact q _).mp ht.1).1
  refine ⟨ha.1, ?_, ?_⟩
  · simpa only [shiftedArgumentCode, ht.2.1] using ha.2.1
  · rw [show interpretation q (shiftedArgumentCode q b c) =
      interpretation q (headCode c) + interpretation q (insertedTailCode q b c) from ha.2.1]
    exact (omegaSequence_add_closed (base q) 1)
      (RootAboveHeadCollapse.head_spec q c hs.2.1).2.1
      (ht.2.2.trans (omegaSequence_step (base q) 1))

theorem relative_collapse_value (q b c : Nat) (hi : inputCheck q b c = true) :
    globalCollapse (interpretation q b) 0 (interpretation q c) =
      globalCollapse (base q) 0 (interpretation q (shiftedArgumentCode q b c)) := by
  have hs := (inputCheck_exact q b c).mp hi
  have hroot := RootEndpointCollapse.argument_accepted q b hs.1
  have hd := RootAboveHeadCollapse.head_spec q c hs.2.1
  have heq := RelativeHighRewrite.global_relative_tail_eq_of_source_head_below (base q)
    (base_pos q (RootLowCollapse.source_checked q b hs.1))
    (interpretation q (RootEndpointCollapse.argumentCode b))
    (interpretation q (RootEndpointCollapse.deltaCode b))
    (interpretation q (Decomposition.lowCode 0 (RootEndpointCollapse.argumentCode b)))
    (interpretation q (headCode c)) (RootEndpointCollapse.argument_notation q b hs.1)
    (RootEndpointCollapse.argument_sorted q b hs.1)
    (Decomposition.highPart_dvd q 0 _ hroot) (Decomposition.lowPart_bound q 0 _ hroot)
    (Decomposition.parts_reconstruct q 0 _ hroot).symm hd.1 hd.2.2.1 hs.2.2.1 hs.2.2.2.1
    (by rw [← RootEndpointCollapse.root_value q b hs.1]; exact hs.2.2.2.2)
    (interpretation q (tailCode c)) hd.2.2.2.1
  rw [← RootEndpointCollapse.root_value q b hs.1] at heq
  rw [hd.2.2.2.2] at heq
  rw [(shiftedArgumentCode_spec q b c hi).2.1]
  exact heq

def collapseCode (q b c : Nat) : Nat := cond (inputCheck q b c)
  (OmegaPowers.thetaCode (shiftedArgumentCode q b c)) 0

theorem collapseCode_primrec : Primrec (fun p : Query => collapseCode p.1 p.2.1 p.2.2) :=
  inputCheck_primrec.cond (OmegaPowers.thetaCode_primrec.comp shiftedArgumentCode_primrec)
    (Primrec.const 0)

/-- Every caller and the checked Normal LOW output are derived from the
actual original computed below-head branch. -/
theorem collapseCode_spec (q b c : Nat) (hi : inputCheck q b c = true) :
    lowCheckCode q (collapseCode q b c) = true ∧
      Comparison.acceptedCode q (collapseCode q b c) = true ∧
      interpretation q (collapseCode q b c) =
        globalCollapse (interpretation q b) 0 (interpretation q c) := by
  have hs := shiftedArgumentCode_spec q b c hi
  have ht := RootEndpointCollapse.thetaCode_sorted_spec q _ hs.1 hs.2.2
  simp only [collapseCode, hi, Bool.cond_true]
  exact ⟨ht.1, ht.2.1, ht.2.2.trans (relative_collapse_value q b c hi).symm⟩

theorem collapseCode_rejected (q b c : Nat) (hi : inputCheck q b c = false) :
    collapseCode q b c = 0 := by simp only [collapseCode, hi, Bool.cond_false]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RootBelowHeadCollapse
