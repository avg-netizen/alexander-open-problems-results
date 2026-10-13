import Alexander313.Wilken.SourceOneNativeAdditiveTrackingAssignmentCoverPrefixSupport
import Alexander313.Wilken.SourceOneNativeAdditiveTrackingAssignmentValueInvariance

/-!
# Genuine covered prefixes of the complete original source-one assignment

Induction follows the independently executing factor and branch clauses.
The actual descending factor bound and epsilon product closure place the
child above a covered HIGH root. If the derived prefix fills the child,
its genuine strict epsilon FINAL forces append. Otherwise the next actual
replacement FIRST is mu-covered, and the greatest insertion keeps that
whole written prefix. No assigned prefix, output bound or numerical
selection position is an input. Full nonmultiplicative order is separate.
Original check zero is retained; no Native base-one parser. Uncompiled.
-/

noncomputable section

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.CoverPrefix

open CoverPrefixSupport
open NativeContext.SourceTrackingSequences (lastCode lastCode_append_singleton)
open Hereditary.FinePredecessor (stripLast stripLast_split)
open SourceMultiplicativeTracking (rawWord word)

theorem derivation_cover_prefix (input : Nat) (out : List Nat)
    (hd : AssignmentSupport.Derivation input out) :
    ∀ b : Nat, rootCheck b = true → interpretation 0 b < interpretation 0 input →
      interpretation 0 input ≤ Mu.sourceValue b →
      ((rawWord b).map (interpretation 0)).IsPrefix (out.map (interpretation 0)) := by
  induction hd with
  | multiplicative input hm =>
    intro b hb hlt hcover
    have hi := SourceMultiplicativePrincipal.rootAdapter_input input hm
    have hir := SourceLocalization.RootAdapter.rootInput input hi
    rw [SourceMultiplicativeTracking.RawRecurrence.rawWord_values_word b
      (SourceMultiplicativeTracking.OrderSupport.rootCheck_node_input b hb),
      SourceMultiplicativeTracking.OrderSupport.rawWord_values_root input hi]
    apply SourceMultiplicativeTracking.OrderSupport.covered_word_prefix _ b hir hb
    · rw [SourceLocalization.RootAdapter.rootCode_value input hi]
      exact hlt
    · rw [SourceLocalization.RootAdapter.rootCode_value input hi]
      exact hcover
  | split input prefix factor heads out hf hd ho ih =>
    intro b hb hlt hcover
    obtain ⟨hcheck, hprefixLow, hfactorLow, hcaller, hone, hpinput,
      hm, hfactorone, hproduct, hlast, hcount⟩ := Factor.execute_spec input (prefix, factor) hf
    have hfactor := ((Theta.acceptedLowCode_iff 0 factor).mp hfactorLow).1
    have hfactorPrefix := Factor.Bounds.execute_last_le_prefix input (prefix, factor) hf
    have hbmul := (SourceMultiplicativePrincipal.inputCheck_exact b).mp (high_multiplicative b hb)
    have hbp : interpretation 0 b ≤ interpretation 0 prefix := by
      by_contra hn
      have hprefixLt : interpretation 0 prefix < interpretation 0 b := lt_of_not_ge hn
      have hinputLt : interpretation 0 input < interpretation 0 b := by
        rw [hproduct]
        exact hbmul.2.2.2.2 hprefixLt (hfactorPrefix.trans_lt hprefixLt)
      exact hinputLt.not_ge hlt.le
    have hheads := (Assignment.execute_iff_derivation prefix heads).mpr hd
    have hh := Assignment.execute_tracking prefix heads hheads
    have hheadBounds := Assignment.execute_all_bounds prefix heads hheads
    have hfactorLast : interpretation 0 factor ≤ interpretation 0 (lastCode heads) :=
      (Factor.Bounds.execute_last_le_prefix_last input (prefix, factor) hf).trans
        (Assignment.execute_last_bounds prefix heads hheads).1
    have hprefix : ((rawWord b).map (interpretation 0)).IsPrefix
        (heads.map (interpretation 0)) := by
      rcases lt_or_eq_of_le hbp with hbprefix | heq
      · exact ih b hb hbprefix (hpinput.le.trans hcover)
      · have hvalues := Assignment.ValueInvariance.execute_values_eq prefix b heads (rawWord b)
          hheads (Assignment.execute_multiplicative b (high_multiplicative b hb)) heq.symm
        rw [hvalues]
        exact List.prefix_refl _
    rcases Branches.execute_branch factor heads out ho with ⟨ha, hout⟩ | ⟨ha, hout⟩
    · rw [hout, List.map_append]
      exact hprefix.trans (List.prefix_append _ _)
    · obtain ⟨retained, hretained, hvalues⟩ := List.prefix_map_iff.mp hprefix
      obtain ⟨remaining, hheadsEq⟩ := hretained
      have hretainedNe : retained ≠ [] := by
        intro he
        have hempty : rawWord b = [] := List.map_eq_nil_iff.mp (by
          simpa only [he, List.map_nil] using hvalues)
        exact Assignment.execute_nonempty b _
          (Assignment.execute_multiplicative b (high_multiplicative b hb)) hempty
      cases remaining with
      | nil =>
        have hvaluesHeads : heads.map (interpretation 0) = (rawWord b).map (interpretation 0) := by
          rw [← hheadsEq, List.append_nil]
          exact hvalues.symm
        have happend := append_of_high_word_values b hb heads hh hvaluesHeads factor hfactor
          (hfactorPrefix.trans (hpinput.le.trans hcover))
        rw [happend] at ha
        cases ha
      | cons next after =>
        obtain ⟨d, hretainedEq, hlastRetained⟩ := stripLast_split retained hretainedNe
        have hlast : lastCode retained = d := by rw [hretainedEq, lastCode_append_singleton]
        have hvalue : interpretation 0 d = interpretation 0 b := by
          have hv := Hereditary.SourceAdditiveTrackingWordBounds.lastCode_values_eq _ _ retained
            (rawWord b) hretainedNe hvalues.symm
          simpa only [hlast, SourceMultiplicativeTracking.rawWord_last] using hv
        have hprefixRef : SourceTrackingRaw.Reference retained := by
          have hr := ((SourceTrackingRaw.trackingCheck_exact heads).mp hh).2.1
          have hs : stripLast heads = retained ++ stripLast (next :: after) := by
            rw [← hheadsEq]
            exact InsertionFidelity.stripLast_append_nonempty retained _ (List.cons_ne_nil _ _)
          rw [hs] at hr
          exact InsertionFidelity.reference_prefix retained _ hr
        have hdmem : d ∈ retained := by
          rw [hretainedEq]
          exact List.mem_append_right _ List.mem_cons_self
        have hdRaw := hprefixRef.nodes d hdmem
        have hmu := SourceTrackingRaw.Support.muValue_eq d b hdRaw hb hvalue
        have hcut : heads = stripLast retained ++ d :: next :: after := by
          calc
            heads = retained ++ next :: after := hheadsEq.symm
            _ = (stripLast retained ++ [d]) ++ next :: after :=
              congrArg (fun xs : List Nat => xs ++ next :: after) hretainedEq
            _ = stripLast retained ++ d :: next :: after := by
              simp only [List.append_assoc, List.cons_append, List.nil_append]
        have hretains := insertion_retains_cut heads hh factor hfactor hm hfactorLast
          (interpretation 0 prefix) (Order.one_le_iff_pos.mp hone) hheadBounds
          (stripLast retained) d next after hcut hdRaw
          (by rw [hmu, ← hproduct]; exact hcover) out hout
        have hretains : retained.IsPrefix out := by
          rw [hretainedEq]
          exact hretains
        have hmap := hretains.map (interpretation 0)
        rw [← hvalues] at hmap
        exact hmap

/-- Every actual complete original assignment retains the independent
multiplicative word of any genuinely covering original HIGH root. -/
theorem execute_cover_prefix (b input : Nat) (out : List Nat)
    (hb : rootCheck b = true) (ho : out ∈ Assignment.execute input)
    (hlt : interpretation 0 b < interpretation 0 input)
    (hcover : interpretation 0 input ≤ Mu.sourceValue b) :
    ((rawWord b).map (interpretation 0)).IsPrefix (out.map (interpretation 0)) :=
  derivation_cover_prefix input out (Assignment.execute_iff_derivation input out |>.mp ho)
    b hb hlt hcover

/-- Both procedures execute independently; the left word is identified
by the genuine multiplicative leaf, without an assignment-word premise. -/
theorem execute_high_cover_prefix (b input : Nat) (left out : List Nat)
    (hb : rootCheck b = true) (hl : left ∈ Assignment.execute b)
    (ho : out ∈ Assignment.execute input)
    (hlt : interpretation 0 b < interpretation 0 input)
    (hcover : interpretation 0 input ≤ Mu.sourceValue b) :
    (left.map (interpretation 0)).IsPrefix (out.map (interpretation 0)) := by
  have he : left = rawWord b := Part.mem_unique hl
    (Assignment.execute_multiplicative b (high_multiplicative b hb))
  rw [he]
  exact execute_cover_prefix b input out hb ho hlt hcover

/-- The genuine greatest selected right endpoint compares the complete
left assignment with the independent multiplicative word procedure. -/
theorem execute_node_right_lex (left right : Nat) (out : List Nat)
    (ho : out ∈ Assignment.execute left)
    (hr : Localization.inputCheck 0 right = true)
    (hlt : interpretation 0 left < interpretation 0 right) :
    List.Lex (· < ·) (out.map (interpretation 0)) ((word right).map (interpretation 0)) := by
  have aux : ∀ n : Nat, ∀ right : Nat, (SourceMultiplicativeTracking.Prefix.properPrefix right).length = n →
      Localization.inputCheck 0 right = true → ∀ left : Nat, ∀ out : List Nat,
      out ∈ Assignment.execute left → interpretation 0 left < interpretation 0 right →
      List.Lex (· < ·) (out.map (interpretation 0)) ((word right).map (interpretation 0)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro right hn hr left out ho hlt
      cases hs : SourceMultiplicativeTracking.Support.select right
          (SourceMultiplicativeTracking.Support.table (SourceMultiplicativeTracking.Prefix.properPrefix right)) with
      | none =>
        have hw := SourceMultiplicativeTracking.Recurrence.word_none right hs
        cases he : out with
        | nil => exact False.elim (Assignment.execute_nonempty left _ ho he)
        | cons a as =>
          simp only [hw, he, List.map_cons, List.map_singleton]
          exact List.Lex.rel ((Assignment.execute_all_bounds left out ho a
            (by simpa only [he] using (List.mem_cons_self : a ∈ a :: as))).trans_lt hlt)
      | some e =>
        have he := SourceMultiplicativeTracking.Recurrence.selected_node right right e hr hs
        have hei := SourceMultiplicativeTracking.OrderSupport.rootCheck_node_input e.1 he.2.1
        have hshort : (SourceMultiplicativeTracking.Prefix.properPrefix e.1).length < n := by
          simpa only [hn] using SourceMultiplicativeTracking.Recurrence.selected_prefix_shorter
            right right e hr hs
        rw [SourceMultiplicativeTracking.Recurrence.word_some_values right e hr hs]
        rcases lt_trichotomy (interpretation 0 left) (interpretation 0 e.1) with hl | hv | hg
        · exact List.Lex.append_right (· < ·) [interpretation 0 right]
            (ih _ hshort e.1 rfl hei left out ho hl)
        · have hvalues := Assignment.ValueInvariance.execute_values_eq left e.1 out (rawWord e.1)
            ho (Assignment.execute_multiplicative e.1 (high_multiplicative e.1 he.2.1)) hv
          rw [hvalues, SourceMultiplicativeTracking.RawRecurrence.rawWord_values_word e.1 hei]
          simpa only [List.append_nil] using List.Lex.append_left (· < ·)
            (List.Lex.nil : List.Lex (· < ·) ([] : List Ordinal.{0}) [interpretation 0 right])
            ((word e.1).map (interpretation 0))
        · have hp := execute_cover_prefix e.1 left out he.2.1 ho hg (hlt.le.trans he.2.2)
          rw [SourceMultiplicativeTracking.RawRecurrence.rawWord_values_word e.1 hei] at hp
          exact SourceMultiplicativeTracking.OrderSupport.prefix_singleton_lex _ _ _ hp
            (fun v hv => by
              obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hv
              exact (Assignment.execute_all_bounds left out ho d hd).trans_lt hlt)
  exact aux _ right rfl hr left out ho hlt

/-- The complete original procedure strictly compares every additive
principal left input against a larger multiplicative right input. -/
theorem execute_right_multiplicative_lex (left right : Nat) (xs ys : List Nat)
    (hx : xs ∈ Assignment.execute left) (hy : ys ∈ Assignment.execute right)
    (hr : SourceMultiplicativePrincipal.inputCheck right = true)
    (hlt : interpretation 0 left < interpretation 0 right) :
    List.Lex (· < ·) (xs.map (interpretation 0)) (ys.map (interpretation 0)) := by
  have he : ys = rawWord right := Part.mem_unique hy (Assignment.execute_multiplicative right hr)
  have hi := SourceMultiplicativePrincipal.rootAdapter_input right hr
  rw [he, SourceMultiplicativeTracking.OrderSupport.rawWord_values_root right hi]
  apply execute_node_right_lex left _ xs hx (SourceLocalization.RootAdapter.rootInput right hi)
  rw [SourceLocalization.RootAdapter.rootCode_value right hi]
  exact hlt

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.CoverPrefix
