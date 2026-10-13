import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingIntervalFactors
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingAssignmentValueInvariance

/-!
# Actual native frame order at equal semantic recursive prefixes

Different written native factor prefixes need not have equal syntax.
Their two independently executing assignments have equal whole VALUE
words. The true child last-factor bound licenses the smaller dispatcher
again at the greater child's literal word. Its independently returned
output agrees in values with the original smaller output, by the genuine
executing branch invariance theorem. Same-written-child factor order then
compares that actual output to the greater one. Every virtual execution
caller derives from original factor memberships and full assignments.
No source syntax injection or strict different-prefix comparison is used.
Source-only uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.FactorPrefixOrder

open SourceTrackingSequences
open Alexander313.Wilken.MultiplicativeNormalForm

theorem execute_equal_prefix_values_lex (q leftInput rightInput : Nat)
    (leftPair rightPair : Factor.Output) (xs ys : List Nat)
    (hl : leftPair ∈ Factor.execute q leftInput)
    (hr : rightPair ∈ Factor.execute q rightInput)
    (hx : xs ∈ Assignment.execute q leftInput)
    (hy : ys ∈ Assignment.execute q rightInput)
    (hprefix : interpretation q leftPair.1 = interpretation q rightPair.1)
    (hlt : interpretation q leftInput < interpretation q rightInput) :
    List.Lex (· < ·) (xs.map (interpretation q)) (ys.map (interpretation q)) := by
  obtain ⟨heads, hh, hbx⟩ := IntervalFactors.actual_factor_child q leftInput
    leftPair.1 leftPair.2 xs hl hx
  obtain ⟨other, ht, hby⟩ := IntervalFactors.actual_factor_child q rightInput
    rightPair.1 rightPair.2 ys hr hy
  have hvalues := Assignment.ValueInvariance.execute_values_eq q leftPair.1 rightPair.1
    heads other hh ht hprefix
  have hs := (Assignment.execute_spec q leftPair.1 heads hh).2.1
  have hu := (Assignment.execute_spec q rightPair.1 other ht).2.1
  obtain ⟨_, _, _, hll, _, _, _, _, hml, _, hprodleft, _, _⟩ :=
    Factor.execute_spec q leftInput leftPair hl
  obtain ⟨_, _, _, hlr, _, _, _, _, hmr, honer, hprodright, _, _⟩ :=
    Factor.execute_spec q rightInput rightPair hr
  have hbl := (Factor.Bounds.execute_last_le_prefix_last q leftInput leftPair hl).trans hs.2.2.1
  have hbr := (Factor.Bounds.execute_last_le_prefix_last q rightInput rightPair hr).trans hu.2.2.1
  have hvirtual : interpretation q leftPair.2 ≤ interpretation q (lastCode other) := by
    have he : interpretation q leftPair.2 ≤ lf (interpretation q rightPair.1) := by
      rw [← hprefix]
      exact Factor.Bounds.execute_last_le_prefix_last q leftInput leftPair hl
    exact he.trans hu.2.2.1
  obtain ⟨out, ho⟩ := Branches.execute_returns q leftPair.2 other hu.1 hll hml hvirtual
  have he := Assignment.ValueInvariance.branches_values_eq q leftPair.2 leftPair.2
    heads other hs.1 hu.1 hll hll hml hbl hvirtual rfl hvalues xs out hbx ho
  have hfactor : interpretation q leftPair.2 < interpretation q rightPair.2 := by
    apply lt_of_not_ge
    intro hge
    have hmul := mul_le_mul_right hge (interpretation q leftPair.1)
    exact hlt.not_ge (by rw [hprodleft, hprodright, ← hprefix]; exact hmul)
  have hlex := FrameFactorOrder.branches_factors_lex q other hu.1 leftPair.2 rightPair.2
    hll hlr hml hmr honer hvirtual hbr hfactor out ys ho hby
  simpa only [he] using hlex

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.FactorPrefixOrder
