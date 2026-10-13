import Alexander313.Wilken.PublicEpsilonNativeRootPositiveCollapse
import Alexander313.Wilken.HereditaryNativeRelativeHighRewriteGlobal

/-!
# Genuine unbounded HIGH relative collapse above the original root

The original Normal argument supplies its actual cardinal head and tail.
The finite native theta constructor checks the head-collapse comparison
with the ORIGINAL root. In the branch where that actual head collapse is
strictly above beta, the genuine global high-tail theorem proves that the
SAME theta-zero source node has the beta-relative collapse value.

Every notation, head divisibility, sorted bound and finite/global caller
is derived. The head is arbitrary, with no comparison to the root's own
head and no selected public-return endpoint or supplied beta code. The
complementary source-head-at-most-beta branch remains separate. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RootAboveHeadCollapse

open ThetaCourse

abbrev Query := Nat × (Nat × Nat)

def argumentCheck (q c : Nat) : Bool := Comparison.acceptedCode q c &&
  decide ((rawTree c).outerSort ≤ 2)

theorem argumentCheck_primrec : Primrec₂ argumentCheck :=
  (Primrec.and.comp Comparison.acceptedCode_primrec
    ((Primrec.nat_le.comp (outerSort_primrec.comp (rawTree_primrec.comp Primrec.snd))
      (Primrec.const 2)).decide)).to₂

theorem argumentCheck_exact (q c : Nat) : argumentCheck q c = true ↔
    Comparison.acceptedCode q c = true ∧ (rawTree c).outerSort ≤ 2 := by
  simp only [argumentCheck, Bool.and_eq_true, decide_eq_true_eq]

def headCode (c : Nat) : Nat := Decomposition.highCode 0 c

theorem headCode_primrec : Primrec headCode :=
  Decomposition.highCode_primrec.comp (Primrec.const 0) Primrec.id

def headNodeCode (c : Nat) : Nat :=
  (.theta 0 (Decomposition.highPartTerm 0 c) : RelativeTerm Nat).code

theorem headNodeCode_primrec : Primrec headNodeCode := code_primrec.comp
  (theta_primrec.comp (Primrec.const 0)
    (Decomposition.highPartTerm_primrec.comp (Primrec.const 0) Primrec.id))

theorem argument_sorted (q c : Nat) (hc : argumentCheck q c = true) :
    interpretation q c < omegaSequence (base q) 2 := by
  have hs := (argumentCheck_exact q c).mp hc
  have ht := (Comparison.acceptedCode_exact q c).mp hs.1
  rw [← Arithmetic.raw_value q c ht.1]
  exact (denote_lt_iff_outerSort_le q _ (Arithmetic.raw_checked q c ht.1) 2 (by omega)).mpr hs.2

/-- The original ANF cut gives the actual head, tail and every caller. -/
theorem head_spec (q c : Nat) (hc : argumentCheck q c = true) :
    GlobalNotation (base q) 1 (interpretation q (headCode c)) ∧
      interpretation q (headCode c) < omegaSequence (base q) 2 ∧
      omegaSequence (base q) 1 ∣ interpretation q (headCode c) ∧
      interpretation q (Decomposition.lowCode 0 c) < omegaSequence (base q) 1 ∧
      interpretation q (headCode c) + interpretation q (Decomposition.lowCode 0 c) =
        interpretation q c := by
  have hi : Decomposition.inputCheck q c = true := ((argumentCheck_exact q c).mp hc).1
  have hn := FixedPoint.checked_notation_at q (Decomposition.highPartTerm 0 c)
    (Decomposition.parts_checked q 0 c hi).1 1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [headCode, Decomposition.highCode, interpretation_code] using hn
  · exact (Decomposition.parts_le q 0 c hi).1.trans_lt (argument_sorted q c hc)
  · exact Decomposition.highPart_dvd q 0 c hi
  · exact Decomposition.lowPart_bound q 0 c hi
  · exact Decomposition.parts_reconstruct q 0 c hi

/-- The computed comparison uses an actual admitted Normal LOW head node.
No source-collapse or argument-caller premise is supplied. -/
theorem headNodeCode_spec (q c : Nat) (hc : argumentCheck q c = true) :
    lowCheckCode q (headNodeCode c) = true ∧
      Comparison.acceptedCode q (headNodeCode c) = true ∧
      interpretation q (headNodeCode c) =
        globalCollapse (base q) 0 (interpretation q (headCode c)) := by
  have hi : Decomposition.inputCheck q c = true := ((argumentCheck_exact q c).mp hc).1
  have ht := (Decomposition.parts_checked q 0 c hi).1
  have hs : (Decomposition.highPartTerm 0 c).outerSort ≤ 2 :=
    (denote_lt_iff_outerSort_le q _ ht 2 (by omega)).mp
      (Decomposition.parts_sort q 0 c hi (argument_sorted q c hc)).1
  have hn := RootPositiveCollapse.theta_checked q 0 _ ht hs
  refine ⟨?_, ?_, ?_⟩
  · simp only [headNodeCode, lowCheckCode_code, lowCheck, hn, RelativeTerm.outerSort,
      decide_true, Bool.true_and]
  · exact (Comparison.acceptedCode_exact _ _).mpr
      ⟨by simpa only [headNodeCode, checkCode_code] using hn,
        by simpa only [headNodeCode, rawTree_code, Comparison.Normal] using
          (Decomposition.parts_normal q 0 c hi).1⟩
  · simpa only [headNodeCode, headCode, Decomposition.highCode, interpretation_code] using
      (show denote q (.theta 0 (Decomposition.highPartTerm 0 c)) =
        globalCollapse (base q) 0 (denote q (Decomposition.highPartTerm 0 c)) from rfl)

def headAbove (q b c : Nat) : Bool := Normalization.lessRawCode q b (headNodeCode c)

theorem headAbove_primrec : Primrec (fun p : Query => headAbove p.1 p.2.1 p.2.2) :=
  Normalization.Effective.lessRawCode_primrec.comp
    (Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair
      (headNodeCode_primrec.comp (Primrec.snd.comp Primrec.snd))))

theorem headAbove_exact (q b c : Nat) (ha : RootLowCollapse.rootCheck q b = true)
    (hc : argumentCheck q c = true) : headAbove q b c = true ↔
    interpretation q b < globalCollapse (base q) 0 (interpretation q (headCode c)) := by
  have hs := headNodeCode_spec q c hc
  simpa only [headAbove, (RootLowCollapse.root_original q b ha),
    ((Comparison.acceptedCode_exact q _).mp hs.2.1).1, hs.2.2, true_and] using
      Normalization.lessRawCode_exact q b (headNodeCode c)

def inputCheck (q b c : Nat) : Bool := RootLowCollapse.rootCheck q b &&
  (argumentCheck q c && headAbove q b c)

theorem inputCheck_primrec : Primrec (fun p : Query => inputCheck p.1 p.2.1 p.2.2) :=
  Primrec.and.comp (RootLowCollapse.rootCheck_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
    (Primrec.and.comp (argumentCheck_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd))
      headAbove_primrec)

theorem inputCheck_guards (q b c : Nat) (hi : inputCheck q b c = true) :
    RootLowCollapse.rootCheck q b = true ∧ argumentCheck q c = true ∧ headAbove q b c = true := by
  simpa only [inputCheck, Bool.and_eq_true, and_assoc] using hi

/-- The genuine computed branch on every original admitted Normal argument
at theta-zero sort; there is no original-head cutoff or endpoint guard. -/
theorem inputCheck_exact (q b c : Nat) : inputCheck q b c = true ↔
    RootLowCollapse.rootCheck q b = true ∧ argumentCheck q c = true ∧
      interpretation q b < globalCollapse (base q) 0 (interpretation q (headCode c)) := by
  constructor
  · intro hi
    have hs := inputCheck_guards q b c hi
    exact ⟨hs.1, hs.2.1, (headAbove_exact q b c hs.1 hs.2.1).mp hs.2.2⟩
  · rintro ⟨ha, hc, hh⟩
    exact Bool.and_eq_true.mpr ⟨ha,
      Bool.and_eq_true.mpr ⟨hc, (headAbove_exact q b c ha hc).mpr hh⟩⟩

/-- The computed branch actually forces a positive divisible HIGH head. -/
theorem head_positive (q b c : Nat) (hi : inputCheck q b c = true) :
    0 < interpretation q (headCode c) := by
  have hs := (inputCheck_exact q b c).mp hi
  apply pos_iff_ne_zero.mpr
  intro hz
  have hq := RootLowCollapse.source_checked q b hs.1
  have hh := hs.2.2
  rw [hz, globalCollapse_zero (base q) (base_pos q hq)
    (BaseTransformation.base_additive q hq) 0, omegaSequence_zero] at hh
  exact (not_lt_of_ge (RootLowCollapse.root_base_le q b hs.1)) hh

/-- The genuine head comparison rejects every LOW argument; HIGH is a
derived fact, rather than an additional purported mathematical caller. -/
theorem argument_high (q b c : Nat) (hi : inputCheck q b c = true) :
    1 < (rawTree c).outerSort := by
  have hc := (inputCheck_guards q b c hi).2.1
  have ha := (argumentCheck_exact q c).mp hc
  have ht := (Comparison.acceptedCode_exact q c).mp ha.1
  have hd := head_spec q c hc
  have hhigh : omegaSequence (base q) 1 ≤ interpretation q c :=
    (Ordinal.le_of_dvd (head_positive q b c hi).ne' hd.2.2.1).trans
      (Decomposition.parts_le q 0 c ha.1).1
  apply lt_of_not_ge
  intro hs
  have hl := (denote_lt_iff_outerSort_le q _ (Arithmetic.raw_checked q c ht.1) 1 (by omega)).mpr hs
  rw [Arithmetic.raw_value q c ht.1] at hl
  exact (not_lt_of_ge hhigh) hl

theorem relative_collapse_value (q b c : Nat) (hi : inputCheck q b c = true) :
    globalCollapse (interpretation q b) 0 (interpretation q c) =
      globalCollapse (base q) 0 (interpretation q c) := by
  have hs := (inputCheck_exact q b c).mp hi
  have hd := head_spec q c hs.2.1
  rw [← hd.2.2.2.2]
  exact RelativeHighRewrite.global_relative_tail_eq_of_source_head_above (base q)
    (interpretation q b) (base_pos q (RootLowCollapse.source_checked q b hs.1))
    (RootLowCollapse.root_base_le q b hs.1) (RootLowCollapse.root_lt_first q b hs.1)
    (interpretation q (headCode c)) hd.1 hd.2.1 hd.2.2.1 hs.2.2
    (interpretation q (Decomposition.lowCode 0 c)) hd.2.2.2.1

def collapseCode (q b c : Nat) : Nat := cond (inputCheck q b c)
  (RootPositiveCollapse.nodeCode 0 c) 0

theorem collapseCode_primrec : Primrec (fun p : Query => collapseCode p.1 p.2.1 p.2.2) :=
  inputCheck_primrec.cond
    (RootPositiveCollapse.nodeCode_primrec.comp (Primrec.const 0) (Primrec.snd.comp Primrec.snd))
    (Primrec.const 0)

/-- This finite unbounded HIGH branch returns the actual beta-relative
theta-zero value as an admitted Normal LOW node at ORIGINAL q. -/
theorem collapseCode_spec (q b c : Nat) (hi : inputCheck q b c = true) :
    lowCheckCode q (collapseCode q b c) = true ∧
      Comparison.acceptedCode q (collapseCode q b c) = true ∧
      interpretation q (collapseCode q b c) =
        globalCollapse (interpretation q b) 0 (interpretation q c) := by
  have hs := (inputCheck_guards q b c hi).2.1
  have ha := (argumentCheck_exact q c).mp hs
  have ht := (Comparison.acceptedCode_exact q c).mp ha.1
  have hn := RootPositiveCollapse.theta_checked q 0 (rawTree c)
    (Arithmetic.raw_checked q c ht.1) ha.2
  simp only [collapseCode, hi, Bool.cond_true, RootPositiveCollapse.nodeCode]
  refine ⟨?_, ?_, ?_⟩
  · simp only [lowCheckCode_code, lowCheck, hn, RelativeTerm.outerSort, decide_true, Bool.true_and]
  · exact (Comparison.acceptedCode_exact _ _).mpr
      ⟨by simpa only [checkCode_code] using hn,
        by simpa only [rawTree_code, Comparison.Normal] using ht.2⟩
  · simp only [interpretation_code]
    change globalCollapse (base q) 0 (denote q (rawTree c)) = _
    rw [Arithmetic.raw_value q c ht.1]
    exact (relative_collapse_value q b c hi).symm

theorem collapseCode_eq (q b c : Nat) (hi : inputCheck q b c = true) :
    collapseCode q b c = RootPositiveCollapse.nodeCode 0 c := by
  simp only [collapseCode, hi, Bool.cond_true]

theorem collapseCode_rejected (q b c : Nat) (hi : inputCheck q b c = false) :
    collapseCode q b c = 0 := by simp only [collapseCode, hi, Bool.cond_false]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RootAboveHeadCollapse
