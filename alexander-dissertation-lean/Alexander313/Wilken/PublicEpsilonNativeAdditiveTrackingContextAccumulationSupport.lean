import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingFactorUpdatePath
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingContextInitialization
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingAssignmentCoverPrefix
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingIntervalFrameProducts
import Alexander313.Wilken.MultiplicativeLastFactorProduct

/-!
# Real chronological updates and genuine reset provenance

The actual factor-removal Segment and reverse Unwind supply every observed
dispatcher membership in chronological order. Real factor results derive
all LOW, Normal, nonunit M and descending callers. An observed conditional
reset has an independently executing lower Assignment, with actual LF equal
to its processed factor. Any such genuine lower Assignment below the fixed
raised M replacement has the needed FIRST cover by actual M-right order.
These are operational ingredients for retained-cut iteration; no arbitrary
old suffix, accumulated cut identity or full raised comparison is assumed.
Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.ContextAccumulationSupport

open PublicEpsilonUnboundedIota SourceTrackingSequences
open Alexander313.Wilken.MultiplicativeNormalForm MultiplicativePrincipalArithmetic
open IntervalFrames
open ReplacementFidelity (SameEntry)

private theorem updates_append {q : Nat} {heads middle out : List Nat}
    {first rest : List Nat} (ha : FactorUpdatePath.Updates q heads first middle)
    (hb : FactorUpdatePath.Updates q middle rest out) :
    FactorUpdatePath.Updates q heads (first ++ rest) out := by
  induction ha generalizing rest out with
  | nil heads => exact hb
  | cons heads factor first next middle hstep htail ih =>
    exact .cons heads factor (first ++ rest) next out hstep (ih hb)

theorem unwind_updates {q : Nat} {frames : List Frame} {heads out : List Nat}
    (hu : Unwind q frames heads out) :
    FactorUpdatePath.Updates q heads (frames.reverse.map (fun frame => frame.2.2)) out := by
  induction hu with
  | nil heads => exact .nil heads
  | cons current child factor frames heads middle out ht ho ih =>
    have hs : FactorUpdatePath.Updates q middle [factor] out :=
      .cons middle factor [] out out ho (.nil out)
    simpa only [List.reverse_cons, List.map_append, List.map_singleton] using updates_append ih hs

private theorem segment_lf_le_factor {q target bound current : Nat} {frames : List Frame}
    (hs : Segment q target bound current frames) :
    ∀ frame ∈ frames, lf (interpretation q current) ≤ interpretation q frame.2.2 := by
  induction hs with
  | nil terminal hv => intro frame hm; exact False.elim (List.not_mem_nil hm)
  | cons current child factor frames hf hsmall ht ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hlf, _⟩ :=
      Factor.execute_spec q current (child, factor) hf
    intro frame hm
    rw [← hlf]
    rcases List.mem_cons.mp hm with rfl | hm
    · exact le_rfl
    · exact (Factor.Bounds.execute_last_le_prefix_last q current (child, factor) hf).trans
        (ih frame hm)

/-- The actual chronological factors decrease; this is derived from the
real removed LF and the genuine removed-factor-to-child-LF bound. -/
theorem segment_descending {q target bound current : Nat} {frames : List Frame}
    (hs : Segment q target bound current frames) :
    (frames.reverse.map (fun frame => frame.2.2)).Pairwise
      (fun a b => interpretation q b ≤ interpretation q a) := by
  induction hs with
  | nil terminal hv => exact List.Pairwise.nil
  | cons current child factor frames hf hsmall ht ih =>
    simp only [List.reverse_cons, List.map_append, List.map_singleton]
    apply List.pairwise_append.mpr
    refine ⟨ih, by simp, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton.mp hb]
    obtain ⟨frame, hm, he⟩ := List.mem_map.mp ha
    rw [← he]
    exact (Factor.Bounds.execute_last_le_prefix_last q current (child, factor) hf).trans
      (segment_lf_le_factor ht frame (List.mem_reverse.mp hm))

theorem segment_factor_callers {q target bound current : Nat} {frames : List Frame}
    (hs : Segment q target bound current frames) :
    ∀ factor ∈ frames.reverse.map (fun frame => frame.2.2),
      lowCheckCode q factor = true ∧ Comparison.acceptedCode q factor = true ∧
      IsMultiplicativePrincipal (interpretation q factor) ∧
      1 < interpretation q factor ∧ interpretation q factor < interpretation q bound := by
  intro factor hm
  obtain ⟨frame, hf, rfl⟩ := List.mem_map.mp hm
  have hs' := segment_factor_bounds hs frame (List.mem_reverse.mp hf)
  obtain ⟨_, _, _, hl, ha, _, _, _, hM, hone, _, _, _⟩ :=
    Factor.execute_spec q frame.1 frame.2 hs'.1
  exact ⟨hl, ha, hM, hone, hs'.2⟩

/-- Every actually observed reset carries its processed LF, supplying
the next real descending factor caller without a separate LF premise. -/
theorem reset_assignment_last (q head factor : Nat) (out : List Nat)
    (hh : SourceTrackingRaw.Support.inputCheck q head = true)
    (hf : lowCheckCode q factor = true)
    (hm : IsMultiplicativePrincipal (interpretation q factor))
    (hone : 1 < interpretation q factor)
    (ho : out ∈ ConditionalReplacement.execute q head factor) :
    ∃ input word,
      interpretation (ReplacementSupport.raisedBaseCode q head) input =
        interpretation q head * interpretation q factor ∧
      base (ReplacementSupport.raisedBaseCode q head) <
        interpretation (ReplacementSupport.raisedBaseCode q head) input ∧
      word ∈ Assignment.execute (ReplacementSupport.raisedBaseCode q head) input ∧
      lf (interpretation (ReplacementSupport.raisedBaseCode q head) input) = interpretation q factor ∧
      List.Forall₂ (SameEntry q (ReplacementSupport.raisedBaseCode q head)) word out := by
  obtain ⟨input, word, hl, hv, hs, ha, hr⟩ :=
    ContextInitialization.conditional_assignment q head factor out hh hf hm hone ho
  have he := (SourceTrackingRaw.Support.inputCheck_exact q head).mp hh
  have hp := EpsilonOffsets.epsilon_pos_principal he.2.2
  exact ⟨input, word, hv, hs, ha, by
    rw [hv]
    exact LastFactorProduct.lf_principal_mul _ _ hp.1 hp.2 hm hone, hr⟩

/-- Independently executing any lower P input below the genuine greater
M input derives the actual returned raised FIRST bound. -/
theorem assignment_first_le_raised (q head greater input : Nat) (word ys : List Nat)
    (hh : SourceTrackingRaw.Support.inputCheck q head = true)
    (hg : lowCheckCode q greater = true)
    (hm : IsMultiplicativePrincipal (interpretation q greater))
    (hhead : interpretation q head < interpretation q greater)
    (ho : word ∈ Assignment.execute (ReplacementSupport.raisedBaseCode q head) input)
    (hlt : interpretation (ReplacementSupport.raisedBaseCode q head) input < interpretation q greater)
    (hy : ys ∈ Replacement.raisedReplacement q head greater) :
    interpretation (ReplacementSupport.raisedBaseCode q head) (Insertion.firstCode word) ≤
      interpretation q (Insertion.firstCode ys) := by
  obtain ⟨rightWord, hr, ht, hv, hlen, hchecked⟩ :=
    Replacement.raisedReplacement_spec q head greater ys hh hg hm hhead hy
  obtain ⟨right, hs, hword⟩ := (Part.mem_map_iff _).mp hr
  have hi := ReplacementSupport.raisedSearch_multiplicative q head greater right hh hg hm hhead hs
  have hs' := ReplacementSupport.raisedSearch_spec q head greater right hh hg hs
  have har : rightWord ∈ Assignment.execute (ReplacementSupport.raisedBaseCode q head) right := by
    rw [← hword]
    exact Assignment.execute_multiplicative _ right hi
  have hlex := AssignmentCoverPrefix.execute_right_multiplicative_lex _ input right word rightWord
    hi (by rw [hs'.2.2]; exact hlt) ho har
  have hwordNe := Assignment.execute_nonempty _ input word ho
  have hysNe : ys ≠ [] := by
    intro he
    have hl := hlen
    rw [he, List.length_nil] at hl
    exact ((SourceTrackingSequences.trackingCheck_exact _ rightWord).mp ht).1
      (List.length_eq_zero_iff.mp hl.symm)
  have hlex' : List.Lex (· < ·)
      (word.map (interpretation (ReplacementSupport.raisedBaseCode q head))) (ys.map (interpretation q)) := by
    simpa only [← hv] using hlex
  cases word with
  | nil => exact False.elim (hwordNe rfl)
  | cons a as =>
    cases ys with
    | nil => exact False.elim (hysNe rfl)
    | cons b bs =>
      simp only [Insertion.firstCode, List.head?_cons, Option.getD_some]
      exact List.head_le_of_lt hlex'

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.ContextAccumulationSupport
