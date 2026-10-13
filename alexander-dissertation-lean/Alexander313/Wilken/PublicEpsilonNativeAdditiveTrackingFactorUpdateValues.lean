import Alexander313.Wilken.MultiplicativeNormalFormAppendFactor
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingAssignmentValueInvariance
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingAssignmentCoverPrefixSupport
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingProperPrefix
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingSingletonIntervalOrderSupport

/-!
# Actual descending factor updates execute the same complete assignment

A genuine next input has the current positive additive principal multiplied
by a nonunit multiplicative factor at most its actual last MNF factor.
Reduced MNF uniqueness identifies the actual next removal's child and last
in VALUES. Actual independently executing child and branch covariance then
identify the complete next assignment. The real numerical singleton cutoff
is handled separately: no factor-removal call is invented below base^omega.
No source syntax equality, initial contextual suffix, accumulated assignment
or retained cut is assumed. Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.FactorUpdateValues

open PublicEpsilonUnboundedIota SourceTrackingSequences
open Hereditary.FinePredecessor (stripLast stripLast_split)
open Alexander313.Wilken.MultiplicativeNormalForm MultiplicativePrincipalArithmetic

theorem epsilon_cut_lt (q c : Nat) (hc : lowCheckCode q c = true)
    (hb : base q < interpretation q c)
    (he : Ordinal.omega0 ^ interpretation q c = interpretation q c) :
    base q ^ Ordinal.omega0 < interpretation q c := by
  have hi := (SourceTrackingRaw.Support.inputCheck_exact q c).mpr ⟨hc, hb, he⟩
  have hr := SourceTrackingRaw.Support.rootCode_spec q c hi
  simpa only [hr.2.2] using
    AssignmentCoverPrefixSupport.base_power_lt_high q _ hr.2.1

/-- Below the real small-input cutoff, every proper epsilon would exceed
the input. Complete actual source clauses then retain its literal final. -/
theorem small_assignment_singleton (q current : Nat) (heads : List Nat)
    (ho : heads ∈ Assignment.execute q current)
    (hcut : interpretation q current ≤ base q ^ Ordinal.omega0) : heads = [current] := by
  have hprefix : stripLast heads = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro d hd
    have hs := ProperPrefix.execute_prefix_interval q current heads ho d hd
    exact (epsilon_cut_lt q d hs.1 hs.2.1 hs.2.2.1).not_ge
      (hs.2.2.2.le.trans hcut)
  have hlast : lastCode heads = current := by
    rcases Assignment.execute_clauses q current heads ho with ⟨hm, he⟩ |
      ⟨hm, hs, he⟩ | ⟨hm, hs, prefix, factor, child, hf, hh, hb⟩
    · rw [he]
      exact SourceMultiplicativeTracking.rawWord_last q current
    · simpa only [he, lastCode_singleton]
    · exact False.elim (((Factor.splitCheck_exact q current).mp
        (Factor.execute_spec q current (prefix, factor) hf).1).2.2.2.2.not_ge hcut)
  obtain ⟨last, hs, _⟩ := stripLast_split heads (Assignment.execute_nonempty q current heads ho)
  have hshape : heads = [last] := by simpa only [hprefix, List.nil_append] using hs
  have he : last = current := by simpa only [hshape, lastCode_singleton] using hlast
  exact hshape.trans (congrArg (fun c => [c]) he)

/-- Both independent actual full executions and the actual current
dispatcher membership determine the next whole VALUES. The real factor
program and its child witness are derived above its cutoff. -/
theorem execute_update_values (q current factor next : Nat)
    (heads nextWord out : List Nat)
    (hh : heads ∈ Assignment.execute q current)
    (hn : nextWord ∈ Assignment.execute q next)
    (hf : lowCheckCode q factor = true)
    (hm : IsMultiplicativePrincipal (interpretation q factor))
    (hone : 1 < interpretation q factor)
    (hbase : base q < interpretation q current)
    (hcut : interpretation q factor ≤ lf (interpretation q current))
    (hv : interpretation q next = interpretation q current * interpretation q factor)
    (ho : out ∈ Branches.execute ((q, factor), heads)) :
    out.map (interpretation q) = nextWord.map (interpretation q) := by
  have hc := (Assignment.inputCheck_exact q current).mp (Assignment.execute_spec q current heads hh).1
  have ht := (Assignment.inputCheck_exact q next).mp (Assignment.execute_spec q next nextWord hn).1
  have hq := (HeightBoundary.input_spec q current hc.1).2.1
  have hlarge : 1 < interpretation q current := (LogEndZero.one_lt_base q hq).trans hbase
  have hp := AppendFactor.prefix_last hlarge hc.2.2 hm hone hcut
  have hnon : ¬IsMultiplicativePrincipal (interpretation q next) := by
    rw [hv]
    exact hp.2.2
  have hb : interpretation q factor ≤ interpretation q (lastCode heads) :=
    hcut.trans (Assignment.execute_last_bounds q current heads hh).1
  by_cases hbig : base q ^ Ordinal.omega0 < interpretation q next
  · have hs := (Factor.splitCheck_exact q next).mpr ⟨ht.1, ht.2.1, ht.2.2, hnon, hbig⟩
    obtain ⟨pair, hd⟩ := Part.dom_iff_mem.mp ((Factor.execute_domain q next).mpr hs)
    rcases pair with ⟨child, last⟩
    have hs := Factor.execute_spec q next (child, last) hd
    obtain ⟨_, hchildLow, _, hlastLow, _, _, _, _, _, _, _, hlastValue, _⟩ := hs
    have hchild : interpretation q child = interpretation q current :=
      (Factor.Bounds.execute_prefix_value q next (child, last) hd).trans
        (by rw [hv]; exact hp.1)
    have hlast : interpretation q last = interpretation q factor :=
      hlastValue.trans (by rw [hv]; exact hp.2.1)
    obtain ⟨other, he, hoNext⟩ := IntervalFactors.actual_factor_child q next child last nextWord hd hn
    have hvalues := Assignment.ValueInvariance.execute_values_eq q current child heads other
      hh he hchild.symm
    have hlastBound : interpretation q last ≤ interpretation q (lastCode other) :=
      (Factor.Bounds.execute_last_le_prefix_last q next (child, last) hd).trans
        (Assignment.execute_last_bounds q child other he).1
    exact Assignment.ValueInvariance.branches_values_eq q factor last heads other
      (Assignment.execute_tracking q current heads hh) (Assignment.execute_tracking q child other he)
      hf hlastLow hm hb hlastBound hlast.symm hvalues out nextWord ho hoNext
  · have hsmall : interpretation q next ≤ base q ^ Ordinal.omega0 := le_of_not_gt hbig
    have hlt : interpretation q current < interpretation q next := by
      rw [hv]
      simpa only [mul_one] using mul_lt_mul_of_pos_left hone (zero_lt_one.trans hlarge)
    have hcurrentSmall := hlt.le.trans hsmall
    have hheads := small_assignment_singleton q current heads hh hcurrentSmall
    have hno : Ordinal.omega0 ^ interpretation q current ≠ interpretation q current := by
      intro he
      exact (epsilon_cut_lt q current hc.1 hbase he).not_ge hcurrentSmall
    have hhRaw : SourceTrackingRaw.trackingCheck q [current] = true := by
      simpa only [hheads] using Assignment.execute_tracking q current heads hh
    have hoSmall : out ∈ Branches.execute ((q, factor), [current]) := by simpa only [hheads] using ho
    have hbSmall : interpretation q factor ≤ interpretation q current := by
      simpa only [hheads, lastCode_singleton] using hb
    obtain ⟨d, hout, hproduct⟩ := SingletonIntervalOrderSupport.branches_singleton_non_epsilon
      q current factor out hhRaw hf hm hbSmall hno hoSmall
    have hs := (Factor.singletonCheck_exact q next).mpr ⟨ht.1, ht.2.1, ht.2.2, hnon, hsmall⟩
    have hfalse : SourceMultiplicativePrincipal.inputCheck q next = false :=
      Bool.eq_false_of_not_eq_true (fun hm => hnon ((SourceMultiplicativePrincipal.inputCheck_exact q next).mp hm).2.2)
    have hnext : nextWord = [next] := Part.mem_unique hn (Assignment.execute_singleton q next hfalse hs)
    simp only [hout, hnext, List.map_singleton, hproduct, hv]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.FactorUpdateValues
