import Alexander313.Wilken.HereditaryEvaluationReferenceHeight
import Alexander313.Wilken.HereditaryGlobalHSmallSupport

/-!
# Genuine reference cardinality from actual height calls

Every strictly larger epsilon parsed by the real LOW search has positive
canonical height. Actual independent public-mu edges therefore give a
strictly descending positive height at every further reference entry.
Induction derives the whole remaining reference length from the actual
first call; later searches and heights are constructed inside the proof.
For a segmented global tail, the genuine gap derives proper admission.
Initial-one/endpoint height and component-length bounds remain separate.
Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationReferenceCardinality

open NativeContext
open NativeContext.PublicEpsilonUnboundedIota
open EvaluationReferenceHeight

theorem execute_epsilon_positive (gamma beta height : Nat)
    (hh : height ∈ execute gamma beta)
    (hlt : unionInterpretation gamma < unionInterpretation beta)
    (he : Ordinal.omega0 ^ unionInterpretation beta = unionInterpretation beta) :
    0 < height := by
  obtain ⟨hi, d, hd, hv⟩ := (execute_graph gamma beta height).mp hh
  have hr := parsed_high gamma beta d hi hd hlt he
  have hn := RootLowCollapse.root_accepted gamma _ hr
  have hp : 0 < CanonicalHeight.canonicalHeightCode gamma (PublicMts.nativeRoot gamma d) := by
    rw [CanonicalHeight.canonicalHeightCode_normal gamma _ hn]
    obtain ⟨t, ht, _, _, _⟩ := (rootCheck_exact gamma _).mp hr
    rw [ht, RelativeTerm.heightCode_code]
    change 0 < max (0 + 1) t.height
    exact (show 0 < (1 : Nat) from Nat.zero_lt_one).trans_le (le_max_left _ _)
  rw [← parsed_height gamma beta d hi hd, ← hv] at hp
  exact hp

/-- The only supplied height is an actual incoming search result. Every
later height and its strict comparison are derived from the independent
reference, including the positive terminal height. -/
theorem continuation_length_le (gamma beta height : Nat) (rest : List Nat)
    (hh : height ∈ execute gamma beta)
    (hlt : unionInterpretation gamma < unionInterpretation beta)
    (he : Ordinal.omega0 ^ unionInterpretation beta = unionInterpretation beta)
    (hr : PublicTrackingSequences.Reference (beta :: rest)) :
    (beta :: rest).length ≤ height := by
  induction rest generalizing gamma beta height with
  | nil =>
    simpa only [List.length_singleton] using
      Nat.succ_le_of_lt (execute_epsilon_positive gamma beta height hh hlt he)
  | cons next rest ih =>
    cases hr with
    | cons beta next rest hbeta hnext hcover ht =>
      have hs := ht.epsilons next List.mem_cons_self
      have hc : unionInterpretation next ≤ publicMuValue beta := by
        simpa only [publicMuValue, SkPublicRecurrence.muValue] using hcover
      have hi := adjacency_caller beta next hbeta hs.1 hs.2.1 hnext hc
      obtain ⟨nextHeight, hn⟩ := execute_returns beta next hi
      have hd := execute_strict_descent gamma beta next height nextHeight hh hn hlt he hc
      have hb := ih beta next nextHeight hn hnext hs.2.1 ht
      simp only [List.length_cons] at hb ⊢
      omega

/-- Independent proper-reference admission derives the actual first
height call and bounds all subsequent reference entries by that result. -/
theorem reference_returns_bound (gamma beta : Nat) (rest : List Nat)
    (hr : PublicTrackingSequences.Reference (gamma :: beta :: rest)) :
    ∃ height, height ∈ execute gamma beta ∧ (beta :: rest).length ≤ height := by
  cases hr with
  | cons gamma beta rest hgamma hlt hcover ht =>
    have hs := ht.epsilons beta List.mem_cons_self
    have hc : unionInterpretation beta ≤ publicMuValue gamma := by
      simpa only [publicMuValue, SkPublicRecurrence.muValue] using hcover
    obtain ⟨height, hh⟩ := execute_returns gamma beta
      (adjacency_caller gamma beta hgamma hs.1 hs.2.1 hlt hc)
    exact ⟨height, hh, continuation_length_le gamma beta height rest hh hlt hs.2.1 ht⟩

/-- The actual strict initial source gap supplies every proper-mu caller;
no proper-tail or independently chosen height chain is an extra premise. -/
theorem global_tail_returns_bound (m gamma beta : Nat) (rest : List Nat)
    (hr : GlobalTrackingSequences.EpsilonReference (gamma :: beta :: rest))
    (hg : GlobalTrackingSequences.TailGap m (gamma :: beta :: rest)) :
    ∃ height, height ∈ execute gamma beta ∧ (gamma :: beta :: rest).length ≤ height + 1 := by
  have hp := (GlobalTrackingSequences.SmallHSupport.epsilonReference_in_gap m _ hr hg).1
  obtain ⟨height, hh, hb⟩ := reference_returns_bound gamma beta rest hp
  exact ⟨height, hh, by simpa only [List.length_cons] using Nat.succ_le_succ hb⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationReferenceCardinality
