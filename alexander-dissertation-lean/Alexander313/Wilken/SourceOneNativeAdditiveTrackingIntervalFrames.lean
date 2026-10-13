import Alexander313.Wilken.SourceOneNativeAdditiveTrackingIntervalFactors

/-!
# Genuine original factor frames above an executed recursive prefix

The actual smaller interval input descends by the real original factor
program until its child is the executed greater prefix. The remaining
quotient factors have positive product, so every intermediate child stays
at least at that prefix. Actual canonical MNF length gives finite descent;
the equality case identifies the literal original return codes through
their canonical public witnesses. Every recorded factor is strictly below
the greater final factor. Complete independent assignment execution then
extracts the actual branch unwind from the SAME prefix assignment.
No supplied fuel, prefix spelling, child word or update execution is used.
Comparison of these accumulated updates with the single greater update
remains separate. Source-only uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.IntervalFrames

open Alexander313.Wilken.MultiplicativeNormalForm

abbrev Frame := AssignmentSupport.Frame

/-- The original descending calls and strict smaller factors are real
program memberships. The terminal code is the actual greater prefix. -/
inductive Segment (target bound : Nat) : Nat → List Frame → Prop
  | nil : Segment target bound target []
  | cons (current child factor : Nat) (frames : List Frame)
      (hf : (child, factor) ∈ Factor.execute current)
      (hsmall : interpretation 0 factor < interpretation 0 bound)
      (ht : Segment target bound child frames) :
      Segment target bound current ((current, (child, factor)) :: frames)

/-- The actual printed updates are unwound in the reverse order of the
real descending factor frames. This relation asserts no lexical bound. -/
inductive Unwind : List Frame → List Nat → List Nat → Prop
  | nil (heads : List Nat) : Unwind [] heads heads
  | cons (current child factor : Nat) (frames : List Frame)
      (heads middle out : List Nat) (ht : Unwind frames heads middle)
      (ho : out ∈ Branches.execute (factor, middle)) :
      Unwind ((current, (child, factor)) :: frames) heads out

theorem segment_factor_bounds {target bound current : Nat} {frames : List Frame}
    (hs : Segment target bound current frames) :
    ∀ frame ∈ frames, frame.2 ∈ Factor.execute frame.1 ∧
      interpretation 0 frame.2.2 < interpretation 0 bound := by
  induction hs with
  | nil => intro frame hf; exact False.elim (List.not_mem_nil hf)
  | cons current child factor frames hf hsmall ht ih =>
    intro frame hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨hf, hsmall⟩
    · exact ih frame hm

/-- The original interval alone derives the complete finite segment.
Its proof measure is actual canonical MNF length, never an input fuel. -/
theorem interval_segment_returns (greater prefix factor current : Nat)
    (hf : (prefix, factor) ∈ Factor.execute greater)
    (hc : Assignment.inputCheck current = true)
    (hl : interpretation 0 prefix < interpretation 0 current)
    (hr : interpretation 0 current < interpretation 0 greater) :
    ∃ frames, Segment prefix factor current frames := by
  let P : Nat → Prop := fun n => ∀ c : Nat,
    (canonicalMNF (interpretation 0 c)).length = n →
      Assignment.inputCheck c = true → interpretation 0 prefix < interpretation 0 c →
        interpretation 0 c < interpretation 0 greater →
          ∃ frames, Segment prefix factor c frames
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro c hn hcaller hleft hright
      obtain ⟨child, last, hstep, hstack, hremaining, hchild, hlast⟩ :=
        IntervalFactors.interval_factor_returns greater prefix factor c hf hcaller hleft hright
      obtain ⟨_, _, _, hnext, _, hlt, _, _, _, _, hcount⟩ :=
        Factor.execute_spec c (child, last) hstep
      have hpositive : 0 < factorProduct (factorPrefix
          (canonicalMNF (interpretation 0 c / interpretation 0 prefix))) :=
        (isMNF_product_principal
          (MultiplicativeFactorRemoval.factorPrefix_reduced _ (canonicalMNF_reduced _)).1).1
      have hfloor : interpretation 0 prefix ≤ interpretation 0 child := by
        rw [hchild]
        exact Ordinal.le_mul_left _ hpositive
      rcases lt_or_eq_of_le hfloor with hstrict | hequal
      · have hcount' : (canonicalMNF (interpretation 0 child)).length < n := by
          simpa only [hn] using hcount
        obtain ⟨frames, hs⟩ := ih _ hcount' child rfl hnext hstrict (hlt.trans hright)
        exact ⟨(c, (child, last)) :: frames, .cons c child last frames hstep hlast hs⟩
      · have he : child = prefix := FactorPrefixSupport.execute_prefix_eq c greater
          (child, last) (prefix, factor) hstep hf hequal.symm
        subst child
        exact ⟨[(c, (prefix, last))], .cons c prefix last [] hstep hlast .nil⟩
  exact hP _ current rfl hc hl hr

/-- A full independently executed smaller assignment identifies its
SAME prefix child and every actual accumulated branch update. -/
theorem segment_execute_unwind {target bound current : Nat} {frames : List Frame}
    (hs : Segment target bound current frames) (out : List Nat)
    (ho : out ∈ Assignment.execute current) :
    ∃ heads, heads ∈ Assignment.execute target ∧ Unwind frames heads out := by
  induction hs generalizing out with
  | nil => exact ⟨out, ho, .nil out⟩
  | cons current child factor frames hf hsmall ht ih =>
    obtain ⟨middle, hm, hb⟩ := FrameFactorOrder.actual_factor_child current child factor out hf ho
    obtain ⟨heads, hh, hu⟩ := ih middle hm
    exact ⟨heads, hh, .cons current child factor frames heads middle out hu hb⟩

/-- Every actual interval assignment has a finite real factor segment,
strictly smaller factors and a genuine SAME-prefix branch unwind. -/
theorem execute_interval_frames (greater prefix factor current : Nat) (out : List Nat)
    (hf : (prefix, factor) ∈ Factor.execute greater)
    (ho : out ∈ Assignment.execute current)
    (hl : interpretation 0 prefix < interpretation 0 current)
    (hr : interpretation 0 current < interpretation 0 greater) :
    ∃ frames heads, Segment prefix factor current frames ∧
      heads ∈ Assignment.execute prefix ∧ Unwind frames heads out := by
  have hc := (Assignment.execute_spec current out ho).1
  obtain ⟨frames, hs⟩ := interval_segment_returns greater prefix factor current hf hc hl hr
  obtain ⟨heads, hh, hu⟩ := segment_execute_unwind hs out ho
  exact ⟨frames, heads, hs, hh, hu⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.IntervalFrames
