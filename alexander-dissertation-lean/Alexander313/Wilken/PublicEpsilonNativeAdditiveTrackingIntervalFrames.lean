import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingIntervalFactors

/-!
# Actual native factor frames down to a semantic recursive prefix

Real factor execution decreases canonical MNF length and retains the true
quotient prefix. Its positive remaining factor product bounds every child
below by the greater prefix. Descent therefore stops at an admitted native
code of that SAME value, without injecting Normal syntax into literal code
equality. The actual complete execution supplies every reverse branch update.
An independent execution at the original prefix has the same bottom VALUES.
No factor stack, fuel, bottom word or accumulated lexical bound is supplied.
Comparison of the accumulated updates with the greater update stays separate.
Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.IntervalFrames

open PublicEpsilonUnboundedIota
open Alexander313.Wilken.MultiplicativeNormalForm

abbrev Frame := AssignmentSupport.Frame

/-- Every descending call is an actual source membership. The terminal
code has the greater prefix VALUE, rather than a claimed literal spelling. -/
inductive Segment (q target bound : Nat) : Nat → List Frame → Prop
  | nil (terminal : Nat) (hv : interpretation q terminal = interpretation q target) :
      Segment q target bound terminal []
  | cons (current child factor : Nat) (frames : List Frame)
      (hf : (child, factor) ∈ Factor.execute q current)
      (hsmall : interpretation q factor < interpretation q bound)
      (ht : Segment q target bound child frames) :
      Segment q target bound current ((current, (child, factor)) :: frames)

/-- The literal reverse unwind uses only actual independently executing
printed branch updates and asserts no order comparison. -/
inductive Unwind (q : Nat) : List Frame → List Nat → List Nat → Prop
  | nil (heads : List Nat) : Unwind q [] heads heads
  | cons (current child factor : Nat) (frames : List Frame)
      (heads middle out : List Nat) (ht : Unwind q frames heads middle)
      (ho : out ∈ Branches.execute ((q, factor), middle)) :
      Unwind q ((current, (child, factor)) :: frames) heads out

theorem segment_factor_bounds {q target bound current : Nat} {frames : List Frame}
    (hs : Segment q target bound current frames) :
    ∀ frame ∈ frames, frame.2 ∈ Factor.execute q frame.1 ∧
      interpretation q frame.2.2 < interpretation q bound := by
  induction hs with
  | nil terminal hv => intro frame hf; exact False.elim (List.not_mem_nil hf)
  | cons current child factor frames hf hsmall ht ih =>
    intro frame hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨hf, hsmall⟩
    · exact ih frame hm

/-- Actual MNF-count descent derives the complete finite segment from
the genuine interval; its measure is a proof, never numerical input fuel. -/
theorem interval_segment_returns (q greater prefix factor current : Nat)
    (hf : (prefix, factor) ∈ Factor.execute q greater)
    (hc : Assignment.inputCheck q current = true)
    (hl : interpretation q prefix < interpretation q current)
    (hr : interpretation q current < interpretation q greater) :
    ∃ frames, Segment q prefix factor current frames := by
  let P : Nat → Prop := fun n => ∀ c : Nat,
    (canonicalMNF (interpretation q c)).length = n →
      Assignment.inputCheck q c = true → interpretation q prefix < interpretation q c →
        interpretation q c < interpretation q greater →
          ∃ frames, Segment q prefix factor c frames
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro c hn hcaller hleft hright
      obtain ⟨child, last, hstep, hstack, hremaining, hchild, hlast⟩ :=
        IntervalFactors.interval_factor_returns q greater prefix factor c hf hcaller hleft hright
      obtain ⟨_, _, _, _, _, hnext, _, hlt, _, _, _, _, hcount⟩ :=
        Factor.execute_spec q c (child, last) hstep
      have hpositive : 0 < factorProduct (factorPrefix
          (canonicalMNF (interpretation q c / interpretation q prefix))) :=
        (isMNF_product_principal
          (MultiplicativeFactorRemoval.factorPrefix_reduced _ (canonicalMNF_reduced _)).1).1
      have hfloor : interpretation q prefix ≤ interpretation q child := by
        rw [hchild]
        exact Ordinal.le_mul_left _ hpositive
      rcases lt_or_eq_of_le hfloor with hstrict | hequal
      · have hcount' : (canonicalMNF (interpretation q child)).length < n := by
          simpa only [hn] using hcount
        obtain ⟨frames, hs⟩ := ih _ hcount' child rfl hnext hstrict (hlt.trans hright)
        exact ⟨(c, (child, last)) :: frames, .cons c child last frames hstep hlast hs⟩
      · exact ⟨[(c, (child, last))],
          .cons c child last [] hstep hlast (.nil child hequal.symm)⟩
  exact hP _ current rfl hc hl hr

/-- A complete independently executed smaller assignment supplies its
actual terminal word and every actual update in the reverse frame unwind. -/
theorem segment_execute_unwind {q target bound current : Nat} {frames : List Frame}
    (hs : Segment q target bound current frames) (out : List Nat)
    (ho : out ∈ Assignment.execute q current) :
    ∃ terminal heads, interpretation q terminal = interpretation q target ∧
      heads ∈ Assignment.execute q terminal ∧ Unwind q frames heads out := by
  induction hs generalizing out with
  | nil terminal hv => exact ⟨terminal, out, hv, ho, .nil out⟩
  | cons current child factor frames hf hsmall ht ih =>
    obtain ⟨middle, hm, hb⟩ := IntervalFactors.actual_factor_child q current child factor out hf ho
    obtain ⟨terminal, heads, hv, hh, hu⟩ := ih middle hm
    exact ⟨terminal, heads, hv, hh, .cons current child factor frames heads middle out hu hb⟩

/-- The actual smaller execution has a finite real factor segment and
genuine reverse branch memberships. The independent original-prefix
execution agrees with its actual bottom in VALUES, not necessarily codes. -/
theorem execute_interval_frames (q greater prefix factor current : Nat) (out : List Nat)
    (hf : (prefix, factor) ∈ Factor.execute q greater)
    (ho : out ∈ Assignment.execute q current)
    (hl : interpretation q prefix < interpretation q current)
    (hr : interpretation q current < interpretation q greater) :
    ∃ frames terminal heads original,
      Segment q prefix factor current frames ∧
      interpretation q terminal = interpretation q prefix ∧
      heads ∈ Assignment.execute q terminal ∧ original ∈ Assignment.execute q prefix ∧
      heads.map (interpretation q) = original.map (interpretation q) ∧
      Unwind q frames heads out := by
  obtain ⟨frames, hs⟩ := interval_segment_returns q greater prefix factor current hf
    (Assignment.execute_spec q current out ho).1 hl hr
  obtain ⟨terminal, heads, hv, hh, hu⟩ := segment_execute_unwind hs out ho
  have hp := (Factor.execute_spec q greater (prefix, factor) hf).2.2.2.2.2.1
  obtain ⟨original, ht⟩ := Assignment.execute_returns q prefix hp
  exact ⟨frames, terminal, heads, original, hs, hv, hh, ht,
    Assignment.ValueInvariance.execute_values_eq q terminal prefix heads original hh ht hv, hu⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.IntervalFrames
