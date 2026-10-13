import Alexander313.Wilken.PublicEpsilonNativeTrackingEndpointSupport
import Alexander313.Wilken.PublicEpsilonNativeLocalizationValueInvariance
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingInsertionFidelitySupport
import Alexander313.Wilken.PublicEpsilonNativeLocalizationRootAdapter
import Alexander313.Wilken.SourceCollapseSuccessors

/-!
# Actual covered nodes occur in genuine ordinary localization

The real adjacent-collapse interval forces the argument of every node in
the interval to be smaller than the preceding root's argument. A genuine
localization that first crossed that root without selecting its VALUE would
force the opposite strict argument inequality. Both callers derive from
the original checked Normal theta-zero syntax. Finite ordered membership
then gives a VALUE subsequence, including a non-epsilon final principal.
No written-support membership, prefix, endpoint or localization is supplied
as an oracle. Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.LocalizationSupport

open SourceLocalization
open PublicEpsilonUnboundedIota
open Hereditary.FinePredecessor (stripLast stripLast_split)
open SourceTrackingSequences (lastCode lastCode_mem lastCode_append_singleton)

/-- The actual source adjacent interval applies to every admitted Normal
theta-zero node, including a non-epsilon final node. -/
theorem node_adjacent_argument_lt (q a b : Nat) (ha : Node q a) (hb : Node q b)
    (hab : value q a < value q b)
    (hbs : value q b < Enclosure.sourceAlphaPlus q a) :
    argumentValue q b < argumentValue q a := by
  obtain ⟨x, rfl, hx, hn⟩ := ha
  obtain ⟨y, rfl, hy, hm⟩ := hb
  have hq := (Bool.and_eq_true.mp hx).1
  let an := FixedPoint.sourceOrdinal q 0 x (FixedPoint.checked_theta_argument q 0 x hx)
  let bn := FixedPoint.sourceOrdinal q 0 y (FixedPoint.checked_theta_argument q 0 y hy)
  have hv : globalCollapse (base q) 0 an.val < globalCollapse (base q) 0 bn.val := by
    simpa only [value, interpretation_code] using hab
  have hs : globalCollapse (base q) 0 bn.val < globalCollapse (base q) 0 (an.val + 1) := by
    simpa only [value, Enclosure.sourceAlphaPlus, Hereditary.Localization.argumentCode_theta,
      interpretation_code] using hbs
  have ht := SourceCollapseSuccessors.global_adjacent_argument_lt (base q) (base_pos q hq)
    0 an bn (FixedPoint.checked_theta_sort q 0 x hx)
      (FixedPoint.checked_theta_sort q 0 y hy) hv hs
  simpa only [argumentValue, argumentCode_theta, interpretation_code] using ht

/-- A genuine support path cannot skip the value of a node whose own
argument-successor endpoint strictly contains the final root. -/
theorem sourcePath_interval_mem (q root a current : Nat) (tail : List Nat)
    (hr : Node q root) (ha : Node q a)
    (hp : SourcePath q (support root) (current :: tail))
    (hca : value q current < value q a) (har : value q a ≤ value q root)
    (hrplus : value q root < Enclosure.sourceAlphaPlus q a) :
    ∃ d ∈ tail, value q d = value q a := by
  revert hca
  induction hp with
  | stop current hc hmax =>
    intro hca
    exact False.elim ((hca.trans_le har).not_ge (hmax root (support_root q root hr)))
  | next current d tail hc hcd hds harg hrest ih =>
    intro hca
    by_cases he : value q d = value q a
    · exact ⟨d, List.mem_cons_self, he⟩
    · by_cases hda : value q d < value q a
      · obtain ⟨e, he, hv⟩ := ih hda
        exact ⟨e, List.mem_cons_of_mem _ he, hv⟩
      · have had : value q a < value q d :=
          lt_of_le_of_ne (le_of_not_gt hda) (Ne.symm he)
        have hd := hrest.nodes d List.mem_cons_self
        have hpfull := SourcePath.next current d tail hc hcd hds harg hrest
        have hag := sourcePath_interval_argument_lt hr hpfull a ha hca had
        have hdag := node_adjacent_argument_lt q a d ha hd had
          ((support_bound q root d hr hds).trans_lt hrplus)
        exact False.elim (hag.not_ge hdag.le)

theorem nativePath_interval_mem (q root a : Nat)
    (hr : SourceLocalization.inputCheck q root = true) (ha : Node q a)
    (hbase : base q < value q a) (har : value q a ≤ value q root)
    (hrplus : value q root < Enclosure.sourceAlphaPlus q a) :
    value q a ∈ (nativePath q root).map (value q) := by
  obtain ⟨tail, he⟩ := nativePath_head q root
  have hp := nativePath_source q root hr
  rw [he] at hp
  have hc : value q (baseRaw q) < value q a := by
    rw [baseRaw_value q (node_baseCheck q root ((SourceLocalization.inputCheck_exact q root).mp hr))]
    exact hbase
  obtain ⟨d, hd, hv⟩ := sourcePath_interval_mem q root a (baseRaw q) tail
    ((SourceLocalization.inputCheck_exact q root).mp hr) ha hp hc har hrplus
  rw [he]
  exact List.mem_map.mpr ⟨d, List.mem_cons_of_mem _ hd, hv⟩

/-- Ordered finite membership yields an actual subsequence; it does not
identify the original written codes. -/
theorem strict_sublist_of_subset (xs ys : List Ordinal.{0})
    (hx : xs.Pairwise (· < ·)) (hy : ys.Pairwise (· < ·))
    (hm : ∀ a ∈ xs, a ∈ ys) : xs.Sublist ys := by
  revert hx hy hm
  induction ys generalizing xs with
  | nil =>
    intro hx hy hm
    cases xs with
    | nil => exact .slnil
    | cons a xs => exact False.elim (List.not_mem_nil (hm a List.mem_cons_self))
  | cons b ys ih =>
    intro hx hy hm
    have hyt := (List.pairwise_cons.mp hy).2
    cases xs with
    | nil => exact List.nil_sublist _
    | cons a xs =>
      have hxt := (List.pairwise_cons.mp hx).2
      by_cases he : a = b
      · subst a
        have htail : ∀ c ∈ xs, c ∈ ys := by
          intro c hc
          rcases List.mem_cons.mp (hm c (List.mem_cons_of_mem _ hc)) with he | hm
          · exact False.elim (((List.pairwise_cons.mp hx).1 c hc).ne he.symm)
          · exact hm
        exact .cons_cons b (ih xs hxt hyt htail)
      · have ha : a ∈ ys := (List.mem_cons.mp (hm a List.mem_cons_self)).resolve_left he
        have hba : b < a := (List.pairwise_cons.mp hy).1 a ha
        have htail : ∀ c ∈ a :: xs, c ∈ ys := by
          intro c hc
          rcases List.mem_cons.mp (hm c hc) with heq | hm
          · subst c
            rcases List.mem_cons.mp hc with heq | hc
            · exact False.elim (he heq.symm)
            · exact False.elim (hba.not_ge ((List.pairwise_cons.mp hx).1 b hc).le)
          · exact hm
        exact .cons b (ih (a :: xs) hx hyt htail)

theorem reference_suffix (q : Nat) (before tail : List Nat)
    (hr : SourceTrackingRaw.Reference q (before ++ tail)) : SourceTrackingRaw.Reference q tail := by
  revert hr
  induction before with
  | nil => intro hr; exact hr
  | cons a before ih =>
    intro hr
    exact ih (InsertionFidelitySupport.reference_tail q a (before ++ tail) hr)

theorem reference_last_cover (q : Nat) (xs : List Nat) (d : Nat)
    (hr : SourceTrackingRaw.Reference q (xs ++ [d])) (hne : xs ≠ []) :
    interpretation q d ≤ SourceTrackingRaw.Support.muValue q (lastCode xs) := by
  revert hne hr
  induction xs with
  | nil => intro hne hr; exact False.elim (hne rfl)
  | cons a xs ih =>
    intro hne hr
    cases xs with
    | nil => simpa only [SourceTrackingSequences.lastCode_singleton] using hr.cover
    | cons b xs =>
      have ht := InsertionFidelitySupport.reference_tail q a ((b :: xs) ++ [d]) hr
      have hc := ih (List.cons_ne_nil _ _) ht
      simpa only [SkTracking.Support.lastCode_cons_nonempty a (b :: xs) (List.cons_ne_nil _ _)] using hc

/-- Every actual adjacent cut derives its real source mu cover, including
the final-entry case. No assigned word clause supplies the inequality. -/
theorem tracking_cut_cover (q : Nat) (word prefix : List Nat) (d : Nat) (after : List Nat)
    (hw : SourceTrackingRaw.trackingCheck q word = true)
    (he : word = prefix ++ d :: after) (hne : prefix ≠ []) :
    interpretation q d ≤ SourceTrackingRaw.Support.muValue q (lastCode prefix) := by
  cases after with
  | nil =>
    have ht := (SourceTrackingRaw.trackingCheck_conditions q word).mp hw
    rw [he, SourceTrackingSequences.stripLast_append_singleton,
      lastCode_append_singleton, if_neg hne] at ht
    exact ht.2.2.2.2.2.2
  | cons b after =>
    have hr := InsertionFidelitySupport.tracking_prefix_reference q word (prefix ++ [d]) b after hw
      (by simpa only [List.append_assoc, List.cons_append, List.nil_append] using he)
    exact reference_last_cover q prefix d hr hne

theorem reference_le_last (q : Nat) (xs : List Nat)
    (hr : SourceTrackingRaw.Reference q xs) (hne : xs ≠ []) :
    ∀ c ∈ xs, interpretation q c ≤ interpretation q (lastCode xs) := by
  obtain ⟨d, he, hd⟩ := stripLast_split xs hne
  have hl : lastCode xs = d := by simp only [lastCode, hd, Option.getD_some]
  have hs := hr.strict
  rw [he, List.map_append, List.map_singleton] at hs
  intro c hc
  rw [he] at hc
  rcases List.mem_append.mp hc with hc | hc
  · rw [hl]
    exact ((List.pairwise_append.mp hs).2.2 _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
      _ List.mem_cons_self).le
  · simpa only [hl, List.mem_singleton.mp hc] using (le_refl (interpretation q d))

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.LocalizationSupport
