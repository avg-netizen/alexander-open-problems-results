import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingContextFirstCutSupport

/-!
# A genuine lower assignment begins at an observed conditional reset

An arbitrary original suffix is not identified with a lower-context word.
When its actual selector is NONE, the actual first conditional row replaces
the suffix. That row independently executes a lower full Assignment at
head times factor: a raised M leaf after genuine absorption, or a real
ordinary singleton below head^omega. Actual source return supplies the
complete relation, and both branches start strictly above the lower base.
No old suffix assignment, retained cut or accumulated update is assumed.
Source-only uncompiled candidates on the original admitted native context.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.ContextInitialization

open PublicEpsilonUnboundedIota ReplacementSupport
open ReplacementFidelity (SameEntry)
open MultiplicativePrincipalArithmetic

private theorem positive_mul_multiplicative {head factor : Ordinal.{0}}
    (hp : 0 < head) (hm : IsMultiplicativePrincipal factor)
    (hone : 1 < factor) (hlt : head < factor) : head * factor = factor := by
  apply le_antisymm
  · apply (Ordinal.mul_le_iff_of_isSuccLimit
      (Ordinal.isSuccLimit_of_isPrincipal_add hone hm.2.1)).mpr
    intro a ha
    exact (hm.2.2 hlt ha).le
  · exact Ordinal.le_mul_right factor hp

private theorem small_product_bounds {head factor : Ordinal.{0}}
    (hp : 0 < head) (hf : 1 < factor) (hsmall : factor ≤ head) :
    head < head * factor ∧ ¬IsMultiplicativePrincipal (head * factor) ∧
      head * factor ≤ head ^ Ordinal.omega0 := by
  have hstrict : head < head * factor := by
    simpa only [Ordinal.mul_one] using mul_lt_mul_of_pos_left hf hp
  refine ⟨hstrict, ?_, ?_⟩
  · intro hm
    exact (lt_irrefl (head * factor)) (hm.2.2 hstrict (hsmall.trans_lt hstrict))
  · have hexp : (1 + 1 : Ordinal.{0}) ≤ Ordinal.omega0 := by
      simpa only [one_add_one_eq_two] using (Ordinal.natCast_lt_omega0 2).le
    calc
      head * factor ≤ head * head := mul_le_mul_right hsmall head
      _ = head ^ (1 + 1 : Ordinal.{0}) := by rw [Ordinal.opow_add, Ordinal.opow_one]
      _ ≤ head ^ Ordinal.omega0 := Ordinal.opow_le_opow_right hp hexp

/-- The actual independently executing conditional reset derives the
entire genuine lower assignment and its actual original-source return. -/
theorem conditional_assignment (q head factor : Nat) (out : List Nat)
    (hh : SourceTrackingRaw.Support.inputCheck q head = true)
    (hf : lowCheckCode q factor = true)
    (hm : IsMultiplicativePrincipal (interpretation q factor))
    (hone : 1 < interpretation q factor)
    (ho : out ∈ ConditionalReplacement.execute q head factor) :
    ∃ input word,
      lowCheckCode (raisedBaseCode q head) input = true ∧
      interpretation (raisedBaseCode q head) input = interpretation q head * interpretation q factor ∧
      base (raisedBaseCode q head) < interpretation (raisedBaseCode q head) input ∧
      word ∈ Assignment.execute (raisedBaseCode q head) input ∧
      List.Forall₂ (SameEntry q (raisedBaseCode q head)) word out := by
  have hhead := (SourceTrackingRaw.Support.inputCheck_exact q head).mp hh
  have hprincipal := EpsilonOffsets.epsilon_pos_principal hhead.2.2
  have hbase := (raisedBaseCode_spec q head hh).2.1
  cases hc : ConditionalReplacement.raisedCheck q head factor with
  | true =>
    have hlt := (ConditionalReplacement.raisedCheck_exact q head factor hhead.1 hf).mp hc
    have hr : out ∈ Replacement.raisedReplacement q head factor := by
      simpa only [ConditionalReplacement.execute, hc, Bool.cond_true] using ho
    obtain ⟨word, hw, hout⟩ := Part.mem_bind_iff.mp hr
    obtain ⟨input, hs, he⟩ := (Part.mem_map_iff _).mp hw
    have hi := raisedSearch_multiplicative q head factor input hh hf hm hlt hs
    have hv := raisedSearch_spec q head factor input hh hf hs
    have ha : word ∈ Assignment.execute (raisedBaseCode q head) input := by
      rw [← he]
      exact Assignment.execute_multiplicative _ input hi
    have hlow := ((SourceTrackingRaw.trackingCheck_exact _ word).mp
      (Assignment.execute_tracking _ input word ha)).source_domain
    have hword : ∀ c ∈ word, lowCheckCode (raisedBaseCode q head) c = true :=
      fun c hc => (hlow c hc).1
    have hrel := Replacement.returnWord_relation q (raisedBaseCode q head) word out hout hword
    refine ⟨input, word, hv.1,
      hv.2.2.trans (positive_mul_multiplicative hprincipal.1 hm hone hlt).symm,
      by rw [hbase, hv.2.2]; exact hlt, ha, ?_⟩
    simpa only [Replacement.contextWord, List.forall₂_map_left_iff] using hrel
  | false =>
    have hsmall : interpretation q factor ≤ interpretation q head := by
      apply le_of_not_gt
      intro hlt
      have ht := (ConditionalReplacement.raisedCheck_exact q head factor hhead.1 hf).mpr hlt
      rw [hc] at ht
      exact Bool.false_ne_true ht
    have hs : out ∈ Replacement.smallReplacement q head factor := by
      simpa only [ConditionalReplacement.execute, hc, Bool.cond_false] using ho
    obtain ⟨d, hout, hdLow, hdAccepted, hv⟩ :=
      Replacement.smallReplacement_spec q head factor out hs hprincipal.1 hprincipal.2 hm
    obtain ⟨input, hi⟩ := raisedSearch_returns q head d hh hdLow
    have hsinput := raisedSearch_spec q head d input hh hdLow hi
    have hinput : interpretation (raisedBaseCode q head) input =
        interpretation q head * interpretation q factor := hsinput.2.2.trans hv
    have hproduct := small_product_bounds hprincipal.1 hone hsmall
    have hnot : SourceMultiplicativePrincipal.inputCheck (raisedBaseCode q head) input = false := by
      apply Bool.eq_false_of_not_eq_true
      intro ht
      have hm' := ((SourceMultiplicativePrincipal.inputCheck_exact _ input).mp ht).2.2
      rw [hinput] at hm'
      exact hproduct.2.1 hm'
    have hsingle : Factor.singletonCheck (raisedBaseCode q head) input = true := by
      apply (Factor.singletonCheck_exact _ input).mpr
      rw [hinput, hbase]
      exact ⟨hsinput.1, hproduct.1.le,
        Ordinal.isPrincipal_add_mul_of_isPrincipal_add (interpretation q head) (ne_of_gt hone) hm.2.1,
        hproduct.2.1, hproduct.2.2⟩
    refine ⟨input, [input], hsinput.1, hinput,
      by rw [hinput, hbase]; exact hproduct.1,
      Assignment.execute_singleton _ input hnot hsingle, ?_⟩
    rw [hout]
    exact .cons ⟨hdLow, hdAccepted, hsinput.2.2.symm⟩ .nil

theorem conditional_assignment_below (q head factor : Nat) (out : List Nat)
    (hh : SourceTrackingRaw.Support.inputCheck q head = true)
    (hf : lowCheckCode q factor = true)
    (hm : IsMultiplicativePrincipal (interpretation q factor))
    (hone : 1 < interpretation q factor)
    (ho : out ∈ ConditionalReplacement.execute q head factor)
    (greater : Ordinal.{0}) (hgreater : IsMultiplicativePrincipal greater)
    (hhead : interpretation q head < greater) (hfactor : interpretation q factor < greater) :
    ∃ input word,
      interpretation (raisedBaseCode q head) input < greater ∧
      base (raisedBaseCode q head) < interpretation (raisedBaseCode q head) input ∧
      word ∈ Assignment.execute (raisedBaseCode q head) input ∧
      List.Forall₂ (SameEntry q (raisedBaseCode q head)) word out := by
  obtain ⟨input, word, hl, hv, hs, hw, hr⟩ := conditional_assignment q head factor out hh hf hm hone ho
  exact ⟨input, word, hv.trans_lt (hgreater.2.2 hhead hfactor), hs, hw, hr⟩

/-- Actual default selection derives a lower assignment despite an
arbitrary nonempty old suffix after the head. Retention remains separate. -/
theorem suffix_default_assignment (q head factor : Nat) (after : List Nat)
    (rows : List InsertionSupport.Row)
    (hh : SourceTrackingRaw.Support.inputCheck q head = true)
    (hf : lowCheckCode q factor = true)
    (hm : IsMultiplicativePrincipal (interpretation q factor))
    (hone : 1 < interpretation q factor)
    (hr : rows ∈ InsertionSupport.executeRows q factor (head :: after))
    (hno : Insertion.choose q rows = none) :
    ∃ input word,
      interpretation (raisedBaseCode q head) input = interpretation q head * interpretation q factor ∧
      base (raisedBaseCode q head) < interpretation (raisedBaseCode q head) input ∧
      word ∈ Assignment.execute (raisedBaseCode q head) input ∧
      List.Forall₂ (SameEntry q (raisedBaseCode q head)) word (Insertion.word q rows) := by
  have hrel := InsertionSupport.executeRows_relation q factor (head :: after) rows hr
  obtain ⟨row, rest, hrow, ht, hrows⟩ := List.forall₂_cons_left_iff.mp hrel
  have hcond : row.2 ∈ ConditionalReplacement.execute q head factor := by
    simpa only [hrow.1] using hrow.2
  obtain ⟨input, word, hl, hv, hs, hw, hmapped⟩ := conditional_assignment q head factor row.2 hh hf hm hone hcond
  have hword : Insertion.word q rows = row.2 := by
    simp only [Insertion.word, hno, hrows, List.head?_cons, Option.getD_some]
  exact ⟨input, word, hv, hs, hw, by simpa only [hword] using hmapped⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.ContextInitialization
