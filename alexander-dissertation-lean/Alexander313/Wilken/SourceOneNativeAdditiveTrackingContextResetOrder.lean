import Alexander313.Wilken.SourceOneNativeAdditiveTrackingContextRelatedFirstCut
import Alexander313.Wilken.SourceOneNativeAdditiveTrackingConditionalOrderSupport
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingAssignmentCoverPrefix

/-!
# A genuine conditional reset lies before the fixed raised replacement

The smaller actual reset constructs a complete lower Assignment at the
head-factor product. Genuine multiplicative closure puts this input below
the greater factor. The independently executing greater raised replacement
is the actual M leaf at the same lower base. The proved full-P-left/M-right
order therefore compares complete reset values, without requiring the
greater factor to stay below the smaller current tracker FINAL. Its FIRST
cover follows from this derived order and real admitted output callers.
No arbitrary old suffix assignment or accumulated composition is assumed.
Source-only uncompiled candidates on original source zero.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.ContextResetOrder

open NativeContext.SourceTrackingSequences (lastCode)

theorem conditional_before_raised (head factor greater : Nat) (xs ys : List Nat)
    (hh : SourceTrackingRaw.Support.inputCheck head = true)
    (hf : lowCheckCode 0 factor = true) (hg : lowCheckCode 0 greater = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor))
    (hmg : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 greater))
    (hone : 1 < interpretation 0 factor)
    (hhead : interpretation 0 head < interpretation 0 greater)
    (hlt : interpretation 0 factor < interpretation 0 greater)
    (hx : xs ∈ ConditionalReplacement.execute head factor)
    (hy : ys ∈ Replacement.raisedReplacement head greater) :
    List.Lex (· < ·) (xs.map (interpretation 0)) (ys.map (interpretation 0)) := by
  obtain ⟨input, word, hless, hstrict, ha, hrel⟩ :=
    ContextInitialization.conditional_assignment_below head factor xs hh hf hm hone hx
      (interpretation 0 greater) hmg hhead hlt
  obtain ⟨rightWord, hr, he, ht, hv, hlen, hchecked⟩ :=
    Replacement.raisedReplacement_spec head greater ys hh hg hmg hhead hy
  obtain ⟨right, hs, hword⟩ := (Part.mem_map_iff _).mp hr
  have hi := ReplacementSupport.raisedSearch_multiplicative head greater right hh hg hmg hhead hs
  have hs' := ReplacementSupport.raisedSearch_spec head greater right hg hs
  have har : rightWord ∈ NativeContext.SourceAdditiveTracking.Assignment.execute
      (ReplacementSupport.raisedBaseCode head) right := by
    rw [← hword]
    exact NativeContext.SourceAdditiveTracking.Assignment.execute_multiplicative _ right hi
  rw [ContextRelatedFirstCut.relation_values hrel, hv]
  exact NativeContext.SourceAdditiveTracking.AssignmentCoverPrefix.execute_right_multiplicative_lex
    _ input right word rightWord hi (by rw [hs'.2.2]; exact hless) ha har

/-- Covering the fixed greater raised FIRST covers any actual smaller
conditional reset FIRST, with its original LOW caller derived from the
actual admitted reset relation. -/
theorem cover_conditional_reset (head factor greater previous : Nat) (xs ys : List Nat)
    (hh : SourceTrackingRaw.Support.inputCheck head = true)
    (hf : lowCheckCode 0 factor = true) (hg : lowCheckCode 0 greater = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor))
    (hmg : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 greater))
    (hone : 1 < interpretation 0 factor)
    (hhead : interpretation 0 head < interpretation 0 greater)
    (hlt : interpretation 0 factor < interpretation 0 greater)
    (hx : xs ∈ ConditionalReplacement.execute head factor)
    (hy : ys ∈ Replacement.raisedReplacement head greater)
    (hcover : Insertion.coverCheck previous (Insertion.firstCode ys) = true) :
    Insertion.coverCheck previous (Insertion.firstCode xs) = true := by
  obtain ⟨input, word, hl, hv, hs, ha, hrel⟩ :=
    ContextInitialization.conditional_assignment head factor xs hh hf hm hone hx
  have hnx : xs ≠ [] := by
    intro he
    have hlength := hrel.length_eq
    rw [he, List.length_nil] at hlength
    exact (NativeContext.SourceAdditiveTracking.Assignment.execute_nonempty _ input word ha)
      (List.length_eq_zero_iff.mp hlength)
  obtain ⟨rightWord, hr, he, ht, hv, hlen, hchecked⟩ :=
    Replacement.raisedReplacement_spec head greater ys hh hg hmg hhead hy
  have hny : ys ≠ [] := by
    intro hn
    have hlength := hlen
    rw [hn, List.length_nil] at hlength
    exact ((NativeContext.SourceTrackingSequences.trackingCheck_exact _ rightWord).mp ht).1
      (List.length_eq_zero_iff.mp hlength.symm)
  have hfirst := ConditionalOrderSupport.lex_first_le xs ys hnx hny
    (conditional_before_raised head factor greater xs ys hh hf hg hm hmg hone hhead hlt hx hy)
  have hmem : Insertion.firstCode xs ∈ xs := by
    cases he : xs with
    | nil => exact False.elim (hnx he)
    | cons a as =>
      simp only [Insertion.firstCode, he, List.head?_cons, Option.getD_some]
      exact List.mem_cons_self
  have hc := (Insertion.coverCheck_exact previous _).mp hcover
  exact (Insertion.coverCheck_exact previous _).mpr
    ⟨hc.1, ((Theta.acceptedLowCode_iff 0 _).mp
      (ContextRelatedFirstCut.relation_checked hrel _ hmem)).1, hfirst.trans hc.2.2⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.ContextResetOrder
