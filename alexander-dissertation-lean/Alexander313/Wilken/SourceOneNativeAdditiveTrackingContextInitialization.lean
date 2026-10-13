import Alexander313.Wilken.SourceOneNativeAdditiveTrackingContextSuffixFirstCut

/-!
# Genuine lower Assignment provenance at an observed conditional reset

An arbitrary old suffix is not identified with a lower-context word. When
the actual suffix selector returns NONE, its real output is its first row
replacement. That independently executing conditional replacement has a
genuine lower Assignment: the raised branch is the real M leaf, while the
ordinary branch is the real singleton at head times factor, below head^omega.
Both branches start strictly above the lower base. Actual original finite
return provides the complete entry relation. No initial suffix assignment,
whole cut retention or accumulated update equation is supplied or concluded.
Source-only uncompiled candidates; the original source remains literal zero.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.ContextInitialization

open MultiplicativePrincipalArithmetic
open ReplacementSupport

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

/-- A real conditional row reset derives a complete, independently executing
lower Assignment strictly above its genuine base. Its input is the actual
head-factor product, including absorption in the raised M branch. -/
theorem conditional_assignment (head factor : Nat) (out : List Nat)
    (hh : SourceTrackingRaw.Support.inputCheck head = true)
    (hf : lowCheckCode 0 factor = true)
    (hm : IsMultiplicativePrincipal (interpretation 0 factor))
    (hone : 1 < interpretation 0 factor)
    (ho : out ∈ ConditionalReplacement.execute head factor) :
    ∃ input word,
      NativeContext.lowCheckCode (raisedBaseCode head) input = true ∧
      NativeContext.interpretation (raisedBaseCode head) input =
        interpretation 0 head * interpretation 0 factor ∧
      NativeContext.base (raisedBaseCode head) <
        NativeContext.interpretation (raisedBaseCode head) input ∧
      word ∈ NativeContext.SourceAdditiveTracking.Assignment.execute (raisedBaseCode head) input ∧
      List.Forall₂ (Replacement.EntryMatches (raisedBaseCode head)) word out := by
  have hhead := (SourceTrackingRaw.Support.inputCheck_exact head).mp hh
  have hp := (EpsilonOffsets.epsilon_pos_principal hhead.2.2).1
  have hbase := (raisedBaseCode_spec head hh).2.1
  cases hc : ConditionalReplacement.raisedCheck head factor with
  | true =>
    have hlt := (ConditionalReplacement.raisedCheck_exact head factor hhead.1 hf).mp hc
    have hr : out ∈ Replacement.raisedReplacement head factor := by
      simpa only [ConditionalReplacement.execute, hc, Bool.cond_true] using ho
    obtain ⟨word, hw, hout, htrack, hvalues, hlength, hchecked⟩ :=
      Replacement.raisedReplacement_spec head factor out hh hf hm hlt hr
    obtain ⟨input, hs, he⟩ := (Part.mem_map_iff _).mp hw
    have hi := raisedSearch_multiplicative head factor input hh hf hm hlt hs
    have hv := raisedSearch_spec head factor input hf hs
    have ha : word ∈ NativeContext.SourceAdditiveTracking.Assignment.execute (raisedBaseCode head) input := by
      rw [← he]
      exact NativeContext.SourceAdditiveTracking.Assignment.execute_multiplicative _ input hi
    have hsword := raisedWord_spec head factor word hh hf hm hlt hw
    refine ⟨input, word, hv.1, ?_, ?_, ha, ?_⟩
    · exact hv.2.2.trans (positive_mul_multiplicative hp hm hone hlt).symm
    · rw [hbase, hv.2.2]; exact hlt
    · rw [hout]
      exact Replacement.returnWord_relation head word
        (fun c hc => (hsword.2.2 c hc).1) (fun c hc => (hsword.2.2 c hc).2.2)
  | false =>
    have hsmall : interpretation 0 factor ≤ interpretation 0 head := by
      apply le_of_not_gt
      intro hlt
      have ht := (ConditionalReplacement.raisedCheck_exact head factor hhead.1 hf).mpr hlt
      rw [hc] at ht
      exact Bool.false_ne_true ht
    have hs : out ∈ Product.smallReplacement head factor := by
      simpa only [ConditionalReplacement.execute, hc, Bool.cond_false] using ho
    obtain ⟨d, hout, hd, hv⟩ := Product.smallReplacement_spec head factor out hs
    have hdLow := ((Theta.acceptedLowCode_iff 0 d).mp hd).1
    obtain ⟨input, hi⟩ := raisedSearch_returns head d hh hdLow
    have hsinput := raisedSearch_spec head d input hdLow hi
    have hinput : NativeContext.interpretation (raisedBaseCode head) input =
        interpretation 0 head * interpretation 0 factor := hsinput.2.2.trans hv
    have hproduct := small_product_bounds hp hone hsmall
    have hnot : NativeContext.SourceMultiplicativePrincipal.inputCheck (raisedBaseCode head) input = false := by
      apply Bool.eq_false_of_not_eq_true
      intro ht
      have hm' := ((NativeContext.SourceMultiplicativePrincipal.inputCheck_exact _ input).mp ht).2.2
      rw [hinput] at hm'
      exact hproduct.2.1 hm'
    have hprincipal : Ordinal.IsPrincipal (· + ·)
        (NativeContext.interpretation (raisedBaseCode head) input) := by
      rw [hinput]
      exact Ordinal.isPrincipal_add_mul_of_isPrincipal_add (interpretation 0 head) (ne_of_gt hone) hm.2.1
    have hsingle : NativeContext.SourceAdditiveTracking.Factor.singletonCheck (raisedBaseCode head) input = true := by
      apply (NativeContext.SourceAdditiveTracking.Factor.singletonCheck_exact _ input).mpr
      rw [hinput, hbase]
      exact ⟨hsinput.1, hproduct.1.le, by simpa only [hinput] using hprincipal,
        hproduct.2.1, hproduct.2.2⟩
    refine ⟨input, [input], hsinput.1, hinput, ?_,
      NativeContext.SourceAdditiveTracking.Assignment.execute_singleton _ input hnot hsingle, ?_⟩
    · rw [hinput, hbase]; exact hproduct.1
    · rw [hout]
      exact .cons ⟨hd, hsinput.2.2.symm⟩ .nil

/-- Complete value provenance is derived from the actual reset execution;
the old suffix is not a premise or an independently supplied assigned word. -/
theorem conditional_assignment_values (head factor : Nat) (out : List Nat)
    (hh : SourceTrackingRaw.Support.inputCheck head = true)
    (hf : lowCheckCode 0 factor = true)
    (hm : IsMultiplicativePrincipal (interpretation 0 factor))
    (hone : 1 < interpretation 0 factor)
    (ho : out ∈ ConditionalReplacement.execute head factor) :
    ∃ input word,
      NativeContext.interpretation (raisedBaseCode head) input =
        interpretation 0 head * interpretation 0 factor ∧
      NativeContext.base (raisedBaseCode head) < NativeContext.interpretation (raisedBaseCode head) input ∧
      word ∈ NativeContext.SourceAdditiveTracking.Assignment.execute (raisedBaseCode head) input ∧
      out.map (interpretation 0) = word.map (NativeContext.interpretation (raisedBaseCode head)) := by
  obtain ⟨input, word, hl, hv, hs, hw, hr⟩ := conditional_assignment head factor out hh hf hm hone ho
  refine ⟨input, word, hv, hs, hw, ?_⟩
  induction hr with
  | nil => rfl
  | cons he ht ih => simp only [List.map_cons, he.2, ih]

/-- A genuine greater M factor bounds the reset's entire actual lower
input, rather than only its final value or the residual factor alone. -/
theorem conditional_assignment_below (head factor : Nat) (out : List Nat)
    (hh : SourceTrackingRaw.Support.inputCheck head = true)
    (hf : lowCheckCode 0 factor = true)
    (hm : IsMultiplicativePrincipal (interpretation 0 factor))
    (hone : 1 < interpretation 0 factor)
    (ho : out ∈ ConditionalReplacement.execute head factor)
    (greater : Ordinal.{0}) (hgreater : IsMultiplicativePrincipal greater)
    (hhead : interpretation 0 head < greater) (hfactor : interpretation 0 factor < greater) :
    ∃ input word,
      NativeContext.interpretation (raisedBaseCode head) input < greater ∧
      NativeContext.base (raisedBaseCode head) < NativeContext.interpretation (raisedBaseCode head) input ∧
      word ∈ NativeContext.SourceAdditiveTracking.Assignment.execute (raisedBaseCode head) input ∧
      List.Forall₂ (Replacement.EntryMatches (raisedBaseCode head)) word out := by
  obtain ⟨input, word, hl, hv, hs, hw, hr⟩ := conditional_assignment head factor out hh hf hm hone ho
  exact ⟨input, word, hv.trans_lt (hgreater.2.2 hhead hfactor), hs, hw, hr⟩

/-- The actual default suffix table is its real first replacement. This
observed reset derives lower Assignment provenance despite an arbitrary
nonempty old suffix after the selected head. -/
theorem suffix_default_assignment (head factor : Nat) (after : List Nat)
    (rows : List InsertionSupport.Row)
    (hh : SourceTrackingRaw.Support.inputCheck head = true)
    (hf : lowCheckCode 0 factor = true)
    (hm : IsMultiplicativePrincipal (interpretation 0 factor))
    (hone : 1 < interpretation 0 factor)
    (hr : rows ∈ InsertionSupport.executeRows factor (head :: after))
    (hno : Insertion.choose rows = none) :
    ∃ input word,
      NativeContext.interpretation (raisedBaseCode head) input =
        interpretation 0 head * interpretation 0 factor ∧
      NativeContext.base (raisedBaseCode head) < NativeContext.interpretation (raisedBaseCode head) input ∧
      word ∈ NativeContext.SourceAdditiveTracking.Assignment.execute (raisedBaseCode head) input ∧
      List.Forall₂ (Replacement.EntryMatches (raisedBaseCode head)) word (Insertion.word rows) := by
  have hrel := InsertionSupport.executeRows_relation factor (head :: after) rows hr
  obtain ⟨row, rest, hrow, ht, hrows⟩ := List.forall₂_cons_left_iff.mp hrel
  have hcond : row.2 ∈ ConditionalReplacement.execute head factor := by
    simpa only [hrow.1] using hrow.2
  obtain ⟨input, word, hl, hv, hs, hw, hmapped⟩ := conditional_assignment head factor row.2 hh hf hm hone hcond
  have hword : Insertion.word rows = row.2 := by
    simp only [Insertion.word, hno, hrows, List.head?_cons, Option.getD_some]
  exact ⟨input, word, hv, hs, hw, by simpa only [hword] using hmapped⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.ContextInitialization
