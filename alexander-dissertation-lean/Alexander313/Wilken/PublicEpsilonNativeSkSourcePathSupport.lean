import Alexander313.Wilken.PublicEpsilonNativeSkContextFidelity

/-!
# Genuine original-source LOW witnesses along the entire native sk path

Every continuing native root is returned using its actual contextual mu
equation and the original representative's own successor interval. A final
stopping LOW value uses the genuine whole-tree source return. Induction on
the actual finite recurrence therefore derives a Normal LOW original-q
representative for every entry, rather than assuming a global endpoint.
These witnesses justify the real finite-code search at the SAME original
source. No spelling, representative, boundary or mu oracle is supplied.
Semantic witnesses do not assert Par preservation. Uncompiled candidates.
-/

noncomputable section

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.SkSourcePathSupport

open SkIteration

/-- Whole LOW source return at an already derived original current root.
The actual next source code, its Normality and SAME value are conclusions. -/
theorem low_return (q root r current c : Nat)
    (ha : Mu.inputCheck q root = true) (hc : Mu.inputCheck r current = true)
    (hv : interpretation q root = interpretation r current)
    (hl : lowCheckCode (betaCode r current) c = true) :
    lowCheckCode q (ContextTranslation.ReturnSupport.returnedCode q root (rawTree c)) = true ∧
      Comparison.acceptedCode q (ContextTranslation.ReturnSupport.returnedCode q root (rawTree c)) = true ∧
      interpretation q (ContextTranslation.ReturnSupport.returnedCode q root (rawTree c)) =
        interpretation (betaCode r current) c := by
  have hb := SkContextFidelity.betaCode_eq_of_value_eq q root r current ha hc hv
  have hcheck : checkCode (betaCode r current) c = true := (Bool.and_eq_true.mp hl).1
  have ht : check (betaCode q root) (rawTree c) = true := by
    rw [hb]
    exact Arithmetic.raw_checked _ _ hcheck
  obtain ⟨t, he, hlow⟩ := (lowCheckCode_exact _ c).mp hl
  have hs : (rawTree c).outerSort ≤ 1 := by
    simpa only [← he, rawTree_code] using of_decide_eq_true (Bool.and_eq_true.mp hlow).2
  have hr := ContextTranslation.ReturnSupport.returnedCode_spec q root ha (rawTree c) ht
  have hrl := ContextTranslation.ReturnSupport.returnedCode_low q root ha (rawTree c) ht hs
  refine ⟨hrl, hr.1, ?_⟩
  rw [hb] at hr
  exact hr.2.trans (Arithmetic.raw_value _ _ hcheck)

/-- Original current value and mu fidelity propagate along every genuine
continuation. Every word entry has a derived original-q Normal LOW code,
including a final emitted value which need not be a HIGH root. -/
theorem path_source_low {cutoff r current : Nat} {word : SkIteration.Support.Word}
    (hp : Path cutoff (r, current) word) (q root : Nat)
    (ha : Mu.inputCheck q root = true)
    (hv : interpretation q root = interpretation r current)
    (hm : Mu.sourceValue q root = Mu.sourceValue r current) :
    ∀ entry ∈ word, ∃ d : Nat, lowCheckCode q d = true ∧
      Comparison.acceptedCode q d = true ∧ interpretation q d = interpretation entry.1 entry.2 := by
  induction hp generalizing root with
  | stop r current hc hcut hbound =>
    intro entry he
    rw [List.mem_singleton.mp he]
    exact ⟨root, RootLowCollapse.root_low q root ha, RootLowCollapse.root_accepted q root ha, hv⟩
  | nextStop r current out helig ho hh =>
    intro entry he
    have hc := ((SkIteration.Support.eligible_exact cutoff r current).mp helig).1
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨root, RootLowCollapse.root_low q root ha, RootLowCollapse.root_accepted q root ha, hv⟩
    · rw [List.mem_singleton.mp he]
      exact ⟨ContextTranslation.ReturnSupport.returnedCode q root (rawTree out.2),
        low_return q root r current out.2 ha hc hv (SkNextSearch.execute_spec _ _ _ out ho).2.1⟩
  | nextContinue r current out tail helig ho hh ht ih =>
    intro entry he
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨root, RootLowCollapse.root_low q root ha, RootLowCollapse.root_accepted q root ha, hv⟩
    · have hs := SkContextFidelity.continued_source q root r current cutoff out ha ho hh hv hm
      exact ih (ContextTranslation.Return.returnedRoot q root out.2) hs.1 hs.2.1 hs.2.2.2.1 entry he

/-- The actual whole original native query derives every original-q LOW
representative; no provenance premise remains at this public endpoint. -/
theorem execute_source_low (q root cutoff : Nat) (word : SkIteration.Support.Word)
    (hw : word ∈ SkIteration.execute ((q, root), cutoff)) :
    ∀ entry ∈ word, ∃ d : Nat, lowCheckCode q d = true ∧
      Comparison.acceptedCode q d = true ∧ interpretation q d = interpretation entry.1 entry.2 := by
  have hs := SkIteration.execute_spec q root cutoff word hw
  have ha := ((SkIteration.inputCheck_exact q root cutoff).mp hs.1).1
  exact path_source_low hs.2.1 q root ha rfl rfl

/-- The genuine original source boundary for every chronological value is
derived from the actual LOW witness, not inferred from a global endpoint. -/
theorem execute_source_boundary (q root cutoff : Nat) (word : SkIteration.Support.Word)
    (hw : word ∈ SkIteration.execute ((q, root), cutoff)) :
    ∀ entry ∈ word, interpretation entry.1 entry.2 < globalBoundary (base q) 0 := by
  intro entry he
  obtain ⟨d, hl, hn, hv⟩ := execute_source_low q root cutoff word hw entry he
  exact hv ▸ checked_low_bound q d hl

/-- Each actual canonical public entry admits the real original-q finite
search. Termination is derived independently for all changing contexts. -/
theorem execute_entry_search (q root cutoff : Nat) (word : SkIteration.Support.Word)
    (hw : word ∈ SkIteration.execute ((q, root), cutoff)) (entry : Context) (he : entry ∈ word) :
    ∃ d, d ∈ SkNextSearch.Support.search q (UniformPublicReturn.publicCode entry.1 entry.2) := by
  have hs := SkIteration.execute_spec q root cutoff word hw
  have ha := ((SkIteration.inputCheck_exact q root cutoff).mp hs.1).1
  have hp := UniformPublicReturn.publicCode_spec entry.1 entry.2
    ((UniformPublicReturn.inputCheck_exact _ _).mpr (hs.2.2.2 entry he).1)
  exact SkNextSearch.Support.search_returns q _ (source_checked q root ha) hp.1
    (by rw [hp.2]; exact execute_source_boundary q root cutoff word hw entry he)

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.SkSourcePathSupport
