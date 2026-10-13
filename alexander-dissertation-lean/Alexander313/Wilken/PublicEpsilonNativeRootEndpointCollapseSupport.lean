import Alexander313.Wilken.PublicEpsilonNativeRootLowCollapse
import Alexander313.Wilken.HereditaryNativeRelativeEndpointRewrite
import Alexander313.Wilken.HereditaryNativeDirectZeta

/-!
# A finite relative collapse at the original divided head

The unchanged original high-root guard and EVERY original raw LOW tail
derive the source argument A+1+rho. Actual native addition normalizes that
argument, and the real theta-zero checker admits its collapse. The genuine
same-head minimum equation identifies its value with theta_beta(Delta+rho).
There is no selected public-return endpoint or extra admission/caller guard.
This is the original-head scalar branch; larger hidden heads and a complete
unbounded return fold remain separate. Source-only, uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RootEndpointCollapse

open ThetaCourse

abbrev Query := RootLowCollapse.Query
abbrev rootCheck := RootLowCollapse.rootCheck
abbrev inputCheck := RootLowCollapse.inputCheck

def argumentCode (b : Nat) : Nat := Localization.argumentCode b

theorem argumentCode_primrec : Primrec argumentCode := Localization.argumentCode_primrec

theorem argument_accepted (q b : Nat) (ha : rootCheck q b = true) :
    Comparison.acceptedCode q (argumentCode b) = true :=
  DirectZeta.argument_input q b (Bool.and_eq_true.mp ha).1

theorem argument_sorted (q b : Nat) (ha : rootCheck q b = true) :
    interpretation q (argumentCode b) < omegaSequence (base q) 2 :=
  DirectZeta.argument_sorted q b (Bool.and_eq_true.mp ha).1

theorem argument_not_low (q b : Nat) (ha : rootCheck q b = true) :
    omegaSequence (base q) 1 ≤ interpretation q (argumentCode b) := by
  obtain ⟨t, he, ht, hn, hh⟩ := (RootLowCollapse.rootCheck_exact q b).mp ha
  have hc := FixedPoint.checked_theta_argument q 0 t ht
  have hhigh : omegaSequence (base q) 1 ≤ denote q t := by
    apply le_of_not_gt
    intro hl
    exact (not_le_of_gt hh) ((denote_lt_iff_outerSort_le q t hc 1 (by omega)).mp hl)
  simpa only [argumentCode, he, Localization.argumentCode_theta, interpretation_code] using hhigh

theorem argument_notation (q b : Nat) (ha : rootCheck q b = true) :
    GlobalNotation (base q) 1 (interpretation q (argumentCode b)) := by
  have hc := ((Comparison.acceptedCode_exact q _).mp (argument_accepted q b ha)).1
  rw [← Arithmetic.raw_value q _ hc]
  exact FixedPoint.checked_notation_at q _ (Arithmetic.raw_checked q _ hc) 1

theorem root_value (q b : Nat) (ha : rootCheck q b = true) :
    interpretation q b = globalCollapse (base q) 0 (interpretation q (argumentCode b)) := by
  obtain ⟨t, he, ht, hn, hh⟩ := (RootLowCollapse.rootCheck_exact q b).mp ha
  simpa only [he, argumentCode, Localization.argumentCode_theta, interpretation_code] using
    (show denote q (.theta 0 t) = globalCollapse (base q) 0 (denote q t) from rfl)

def deltaCode (b : Nat) : Nat := Decomposition.highCode 0 (argumentCode b)

theorem deltaCode_primrec : Primrec deltaCode :=
  Decomposition.highCode_primrec.comp (Primrec.const 0) argumentCode_primrec

theorem delta_positive (q b : Nat) (ha : rootCheck q b = true) :
    0 < interpretation q (deltaCode b) := by
  apply lt_of_le_of_ne (zero_le _)
  intro hz
  have hzero : interpretation q (Decomposition.highCode 0 (argumentCode b)) = 0 := hz.symm
  have hv := Decomposition.parts_reconstruct q 0 _ (argument_accepted q b ha)
  have hl := Decomposition.lowPart_bound q 0 _ (argument_accepted q b ha)
  rw [hzero, zero_add] at hv
  exact (not_lt_of_ge (argument_not_low q b ha)) (hv ▸ hl)

def firstCode (q b : Nat) : Nat :=
  Arithmetic.addCode q (argumentCode b) (OmegaPowerHeight.numeralCode 1)

theorem firstCode_primrec : Primrec₂ firstCode :=
  (Arithmetic.addCode_primrec.comp (Primrec.fst.pair
    ((argumentCode_primrec.comp Primrec.snd).pair
      (Primrec.const (OmegaPowerHeight.numeralCode 1))))).to₂

theorem firstCode_spec (q b : Nat) (ha : rootCheck q b = true) :
    Comparison.acceptedCode q (firstCode q b) = true ∧
      interpretation q (firstCode q b) = interpretation q (argumentCode b) + 1 := by
  have hu := OmegaPowerHeight.numeralCode_spec q 1 (RootLowCollapse.source_checked q b ha)
  have hs := Arithmetic.addCode_spec q _ _
    ((Comparison.acceptedCode_exact q _).mp (argument_accepted q b ha)).1
    ((Comparison.acceptedCode_exact q _).mp hu.2.1).1
  exact ⟨hs.1, by simpa only [firstCode, hu.2.2.1, Nat.cast_one] using hs.2.1⟩

def successorArgumentCode (q b c : Nat) : Nat := Arithmetic.addCode q (firstCode q b) c

theorem successorArgumentCode_primrec :
    Primrec (fun p : Query => successorArgumentCode p.1 p.2.1 p.2.2) :=
  Arithmetic.addCode_primrec.comp (Primrec.fst.pair
    ((firstCode_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd)).pair
      (Primrec.snd.comp Primrec.snd)))

theorem successorArgumentCode_spec (q b c : Nat) (hi : inputCheck q b c = true) :
    Comparison.acceptedCode q (successorArgumentCode q b c) = true ∧
      interpretation q (successorArgumentCode q b c) =
        (interpretation q (argumentCode b) + 1) + interpretation q c ∧
      interpretation q (successorArgumentCode q b c) < omegaSequence (base q) 2 := by
  have h := (RootLowCollapse.inputCheck_exact q b c).mp hi
  have hf := firstCode_spec q b h.1
  have hs := Arithmetic.addCode_spec q (firstCode q b) c
    ((Comparison.acceptedCode_exact q _).mp hf.1).1 (Bool.and_eq_true.mp h.2).1
  refine ⟨hs.1, ?_, ?_⟩
  · simpa only [successorArgumentCode, hf.2] using hs.2.1
  · have hu := OmegaPowerHeight.numeralCode_spec q 1 (RootLowCollapse.source_checked q b h.1)
    have hone : (1 : Ordinal.{0}) < omegaSequence (base q) 2 := by
      have hh := (HeightBoundary.input_spec q _ hu.1).2.2
      rw [hu.2.2.1, Nat.cast_one] at hh
      exact hh.trans (omegaSequence_step (base q) 1)
    have hc := (HeightBoundary.input_spec q c h.2).2.2.trans (omegaSequence_step (base q) 1)
    rw [show interpretation q (successorArgumentCode q b c) =
        (interpretation q (argumentCode b) + 1) + interpretation q c from
      by simpa only [successorArgumentCode, hf.2] using hs.2.1]
    exact (omegaSequence_add_closed (base q) 1)
      ((omegaSequence_add_closed (base q) 1) (argument_sorted q b h.1) hone) hc

/-- This real theta checker applies to sorted HIGH as well as LOW arguments. -/
theorem thetaCode_sorted_spec (q c : Nat) (hc : Comparison.acceptedCode q c = true)
    (hs : interpretation q c < omegaSequence (base q) 2) :
    lowCheckCode q (OmegaPowers.thetaCode c) = true ∧
      Comparison.acceptedCode q (OmegaPowers.thetaCode c) = true ∧
      interpretation q (OmegaPowers.thetaCode c) = globalCollapse (base q) 0 (interpretation q c) := by
  have hi := (Comparison.acceptedCode_exact q c).mp hc
  have ht := SourceChi.Powers.checked_theta_zero q (rawTree c) (Arithmetic.raw_checked q c hi.1)
    (by rw [Arithmetic.raw_value q c hi.1]; exact hs)
  have hn : Comparison.Normal q (rawTree (OmegaPowers.thetaCode c)) := by
    simpa only [OmegaPowers.thetaCode, rawTree_code, Comparison.Normal] using hi.2
  refine ⟨?_, (Comparison.acceptedCode_exact q _).mpr
    ⟨by simpa only [OmegaPowers.thetaCode, checkCode_code] using ht, hn⟩, ?_⟩
  · simp only [OmegaPowers.thetaCode, lowCheckCode_code, lowCheck, ht,
      RelativeTerm.outerSort, Nat.zero_add, le_refl, decide_true, Bool.true_and]
  · change globalCollapse (base q) 0 (denote q (rawTree c)) = _
    rw [Arithmetic.raw_value q c hi.1]

def collapseCode (q b c : Nat) : Nat := cond (inputCheck q b c)
  (OmegaPowers.thetaCode (successorArgumentCode q b c)) 0

theorem collapseCode_primrec : Primrec (fun p : Query => collapseCode p.1 p.2.1 p.2.2) :=
  RootLowCollapse.inputCheck_primrec.cond
    (OmegaPowers.thetaCode_primrec.comp successorArgumentCode_primrec) (Primrec.const 0)

/-- EVERY original RAW LOW tail has a finite accepted Normal LOW relative
collapse at the ORIGINAL divided head, with no selected-return endpoint. -/
theorem collapseCode_spec (q b c : Nat) (hi : inputCheck q b c = true) :
    lowCheckCode q (collapseCode q b c) = true ∧
      Comparison.acceptedCode q (collapseCode q b c) = true ∧
      interpretation q (collapseCode q b c) = globalCollapse (interpretation q b) 0
        (interpretation q (deltaCode b) + interpretation q c) := by
  have h := (RootLowCollapse.inputCheck_exact q b c).mp hi
  have hs := successorArgumentCode_spec q b c hi
  have ht := thetaCode_sorted_spec q _ hs.1 hs.2.2
  have hA := argument_accepted q b h.1
  have he := Decomposition.parts_reconstruct q 0 _ hA
  have heq := RelativeEndpointRewrite.global_relative_endpoint_tail_eq (base q)
    (base_pos q (RootLowCollapse.source_checked q b h.1)) (interpretation q (argumentCode b))
    (interpretation q (deltaCode b)) (interpretation q (Decomposition.lowCode 0 (argumentCode b)))
    (argument_notation q b h.1) (argument_sorted q b h.1)
    (Decomposition.highPart_dvd q 0 _ hA) (delta_positive q b h.1)
    (Decomposition.lowPart_bound q 0 _ hA) he.symm (interpretation q c)
    (HeightBoundary.input_spec q c h.2).2.2
  simp only [collapseCode, hi, Bool.cond_true]
  refine ⟨ht.1, ht.2.1, ?_⟩
  rw [ht.2.2, hs.2.1, root_value q b h.1, heq]
  apply congrArg (globalCollapse (base q) 0)
  rw [← add_assoc, ← add_assoc, he]

theorem collapseCode_rejected (q b c : Nat) (hi : inputCheck q b c = false) :
    collapseCode q b c = 0 := by simp only [collapseCode, hi, Bool.cond_false]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RootEndpointCollapse
