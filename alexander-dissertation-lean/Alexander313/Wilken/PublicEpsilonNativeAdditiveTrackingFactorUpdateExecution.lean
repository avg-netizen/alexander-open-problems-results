import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingFactorUpdateValues

/-!
# The actual principal product constructs every descending next assignment

The current actual Assignment and descending nonunit M factor license the
real logarithm/add/power product producer. Its original LOW output derives
the complete next Assignment caller. The proved factor-update identity then
identifies its independently executed whole word with the actual update.
The next canonical LF is the processed factor, supplying the subsequent
descending caller. No next code, child word or update equation is supplied.
Source-only uncompiled candidates; contextual retained cuts remain separate.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.FactorUpdateExecution

open PublicEpsilonUnboundedIota SourceTrackingSequences
open Alexander313.Wilken.MultiplicativeNormalForm MultiplicativePrincipalArithmetic

theorem product_update_returns (q current factor : Nat) (heads out : List Nat)
    (hh : heads ∈ Assignment.execute q current)
    (hf : lowCheckCode q factor = true)
    (hm : IsMultiplicativePrincipal (interpretation q factor))
    (hone : 1 < interpretation q factor)
    (hbase : base q < interpretation q current)
    (hcut : interpretation q factor ≤ lf (interpretation q current))
    (ho : out ∈ Branches.execute ((q, factor), heads)) :
    ∃ next nextWord,
      next ∈ ReplacementSupport.product q current factor ∧
      lowCheckCode q next = true ∧ Comparison.acceptedCode q next = true ∧
      interpretation q next = interpretation q current * interpretation q factor ∧
      base q < interpretation q next ∧
      nextWord ∈ Assignment.execute q next ∧
      out.map (interpretation q) = nextWord.map (interpretation q) ∧
      lf (interpretation q next) = interpretation q factor := by
  have hc := (Assignment.inputCheck_exact q current).mp (Assignment.execute_spec q current heads hh).1
  have hq := (HeightBoundary.input_spec q current hc.1).2.1
  have hpos := (base_pos q hq).trans hbase
  have hlarge := (LogEndZero.one_lt_base q hq).trans hbase
  obtain ⟨next, hn⟩ := ReplacementSupport.product_returns q current factor hc.1 hf
  have hp := ReplacementSupport.product_spec q current factor next hn hpos hc.2.2 hm.1 hm.2.1
  have hlt : interpretation q current < interpretation q next := by
    rw [hp.2.2]
    simpa only [mul_one] using mul_lt_mul_of_pos_left hone hpos
  have hprincipal : Ordinal.IsPrincipal (· + ·) (interpretation q next) := by
    rw [hp.2.2]
    exact Ordinal.isPrincipal_add_mul_of_isPrincipal_add (interpretation q current)
      (ne_of_gt hone) hm.2.1
  have hi := (Assignment.inputCheck_exact q next).mpr
    ⟨hp.1, (hbase.trans hlt).le, hprincipal⟩
  obtain ⟨nextWord, hw⟩ := Assignment.execute_returns q next hi
  have hvalues := FactorUpdateValues.execute_update_values q current factor next heads nextWord out
    hh hw hf hm hone hbase hcut hp.2.2 ho
  have hlast : lf (interpretation q next) = interpretation q factor := by
    rw [hp.2.2]
    exact (AppendFactor.prefix_last hlarge hc.2.2 hm hone hcut).2.1
  exact ⟨next, nextWord, hn, hp.1, hp.2.1, hp.2.2, hbase.trans hlt, hw, hvalues, hlast⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.FactorUpdateExecution
