import Alexander313.Wilken.PublicEpsilonNativeMultiplicativeTrackingOrder
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingAssignmentValueInvariance
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingProperPrefix

/-!
# Actual greatest insertion retains a genuinely covered earlier prefix

A real passing transition forces the right-priority executing selector to
retain every earlier original head. Actual conditional executions and joint
source bounds construct that passing transition. These finite facts do not
assume a selected index, replacement word or assigned tracking prefix.
The final full-assignment induction is separate. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.AssignmentCoverPrefixSupport

open PublicEpsilonUnboundedIota SourceTrackingSequences
open Hereditary.FinePredecessor (stripLast stripLast_split)
open InsertionSupport (Row)
open Hereditary.SourceAdditiveTrackingWordBounds (lastCode_values_eq)

/-- Genuine epsilon closure excludes every small singleton leaf above
an original covering HIGH epsilon. -/
theorem base_power_lt_high (q b : Nat) (hb : Mu.inputCheck q b = true) :
    base q ^ Ordinal.omega0 < interpretation q b := by
  have hq := (HeightBoundary.input_spec q b (RootLowCollapse.root_low q b hb)).2.1
  have heq := SourceChi.epsilon_base q hq
  have heb := RootLowCollapse.root_epsilon q b hb
  have hm := SourceMultiplicativePrincipal.epsilon_multiplicative _ heb
  have hmul : base q * Ordinal.omega0 < interpretation q b :=
    hm.2.2 (Mu.root_base_lt q b hb) (epsilon_omega_lt heb)
  calc
    base q ^ Ordinal.omega0 = Ordinal.omega0 ^ (base q * Ordinal.omega0) := by
      rw [Ordinal.opow_mul, heq]
    _ < Ordinal.omega0 ^ interpretation q b := omegaPower_strictMono hmul
    _ = interpretation q b := heb

/-- A factor-removal prefix cannot lie below a directly covering epsilon:
the actual descending last factor lies below that prefix as well. -/
theorem factor_prefix_ge_high (q b current prefix factor : Nat)
    (hb : Mu.inputCheck q b = true)
    (hf : (prefix, factor) ∈ Factor.execute q current)
    (hbc : interpretation q b < interpretation q current) :
    interpretation q b ≤ interpretation q prefix := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hv, _, _⟩ :=
    Factor.execute_spec q current (prefix, factor) hf
  have hfactor := Factor.Bounds.execute_last_le_prefix q current (prefix, factor) hf
  by_contra hn
  have hp : interpretation q prefix < interpretation q b := lt_of_not_ge hn
  have hm := SourceMultiplicativePrincipal.epsilon_multiplicative _
    (RootLowCollapse.root_epsilon q b hb)
  have hproduct := hm.2.2 hp (hfactor.trans_lt hp)
  exact (not_lt_of_ge hbc.le) (hv.trans_lt hproduct)

/-- Once the actual selector passes anywhere, prepending another row
preserves that later transition and increments its retained-head count. -/
theorem choose_prepend (q : Nat) (row : Row) (rows : List Row) (n : Nat) (word : List Nat)
    (hs : Insertion.choose q rows = some (n, word)) :
    Insertion.choose q (row :: rows) = some (n + 1, word) := by
  cases rows with
  | nil => simp only [Insertion.choose_nil, Option.none_ne_some] at hs
  | cons a rest =>
    cases rest with
    | nil => simp only [Insertion.choose_singleton, Option.none_ne_some] at hs
    | cons b rest =>
      rw [Insertion.choose_pair, hs]

/-- A genuine passing adjacency is never replaced by an earlier default:
right-priority selection retains at least all heads through its predecessor. -/
theorem choose_after_passing (q : Nat) (before : List Row) (previous current : Row)
    (after : List Row)
    (hc : Insertion.coverCheck q previous.1 (Insertion.firstCode current.2) = true) :
    ∃ n word, Insertion.choose q (before ++ previous :: current :: after) = some (n, word) ∧
      before.length + 1 ≤ n := by
  induction before with
  | nil =>
    cases hs : Insertion.choose q (current :: after) with
    | none =>
      refine ⟨1, current.2, ?_, by simp only [List.length_nil]; exact le_rfl⟩
      simp only [List.nil_append, Insertion.choose_pair, hs, hc, Bool.cond_true]
    | some e =>
      refine ⟨e.1 + 1, e.2, ?_, by simp only [List.length_nil]; omega⟩
      simp only [List.nil_append, Insertion.choose_pair, hs]
  | cons row before ih =>
    obtain ⟨n, word, hs, hn⟩ := ih
    refine ⟨n + 1, word, ?_, by simpa only [List.length_cons] using Nat.add_le_add_right hn 1⟩
    simpa only [List.cons_append] using choose_prepend q row _ n word hs

/-- A literal original row prefix before a real passing transition is a
literal prefix of the actually computed insertion word. -/
theorem word_retains_passing_prefix (q : Nat) (before : List Row) (previous current : Row)
    (after : List Row)
    (hc : Insertion.coverCheck q previous.1 (Insertion.firstCode current.2) = true) :
    ((before ++ [previous]).map Prod.fst).IsPrefix
      (Insertion.word q (before ++ previous :: current :: after)) := by
  obtain ⟨n, word, hs, hn⟩ := choose_after_passing q before previous current after hc
  have hlen : (before ++ [previous]).length ≤ n := by
    simpa only [List.length_append, List.length_singleton] using hn
  have he : before ++ previous :: current :: after = (before ++ [previous]) ++ current :: after := by
    simp only [List.append_assoc, List.singleton_append]
  have hp : (before ++ [previous]).IsPrefix
      ((before ++ previous :: current :: after).take n) := by
    have ht := List.take_prefix_take_left (l := before ++ previous :: current :: after) hlen
    have hh : (before ++ previous :: current :: after).take (before ++ [previous]).length =
        before ++ [previous] := by rw [he, List.take_left]
    rw [hh] at ht
    exact ht
  rw [Insertion.word, hs]
  exact (hp.map Prod.fst).trans
    (List.prefix_append (((before ++ previous :: current :: after).take n).map Prod.fst) word)

/-- The actual row executions and original all-entry upper bound derive
the cover of the first replacement immediately after a covered prefix.
Greatest insertion therefore preserves that prefix literally. -/
theorem insertion_retains_covered_prefix (q factor : Nat) (heads prefix : List Nat)
    (current : Nat) (after out : List Nat)
    (hh : SourceTrackingRaw.trackingCheck q heads = true)
    (hf : lowCheckCode q factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q factor))
    (hb : interpretation q factor ≤ interpretation q (lastCode heads))
    (eta : Ordinal.{0}) (heta : 0 < eta)
    (hbound : ∀ d ∈ heads, interpretation q d ≤ eta)
    (he : heads = prefix ++ current :: after) (hne : prefix ≠ [])
    (hraw : SourceTrackingRaw.Support.inputCheck q (lastCode prefix) = true)
    (hcover : eta * interpretation q factor ≤ SourceTrackingRaw.Support.muValue q (lastCode prefix))
    (ho : out ∈ Insertion.execute ((q, factor), heads)) : prefix.IsPrefix out := by
  obtain ⟨rows, hr, hout⟩ := (Part.mem_map_iff _).mp ho
  have hrel := InsertionSupport.executeRows_relation q factor heads rows hr
  have hheads := InsertionSupport.relation_heads q factor hrel
  have hemap : rows.map Prod.fst = prefix ++ current :: after := hheads.trans he
  obtain ⟨before, rest, hrows, hpref, hrest⟩ := List.map_eq_append_iff.mp hemap
  obtain ⟨row, later, hrestrow, hcurrent, hafter⟩ := List.map_eq_cons_iff.mp hrest
  have hbefore : before ≠ [] := by
    intro hnil
    apply hne
    exact hpref.symm.trans (by rw [hnil]; rfl)
  obtain ⟨previous, hbeforeeq, _⟩ := stripLast_split before hbefore
  have hrowmem : row ∈ rows := by
    rw [hrows, hrestrow]
    exact List.mem_append_right _ List.mem_cons_self
  have hrow := InsertionSupport.relation_members q factor hrel row hrowmem
  have hs := ConditionalReplacement.execute_spec q heads hh row.1 factor hrow.1 hf hm hb row.2 hrow.2
  have hvals := Bounds.conditional_bounds q heads hh row.1 factor hrow.1 hf hm hb eta heta
    (hbound row.1 hrow.1) row.2 hrow.2
  have hfirst : Insertion.firstCode row.2 ∈ row.2 := by
    cases heword : row.2 with
    | nil => exact False.elim (hs.1 heword)
    | cons d ds => simp only [Insertion.firstCode, heword, List.head?_cons, Option.getD_some]; exact List.mem_cons_self
  have hprev : previous.1 = lastCode prefix := by
    have hp : before.map Prod.fst = (stripLast before).map Prod.fst ++ [previous.1] := by
      simpa only [List.map_append, List.map_singleton] using congrArg (List.map Prod.fst) hbeforeeq
    rw [hpref] at hp
    exact ((congrArg lastCode hp).trans (lastCode_append_singleton _ _)).symm
  have hc : Insertion.coverCheck q previous.1 (Insertion.firstCode row.2) = true :=
    (Insertion.coverCheck_exact q _ _).mpr ⟨by simpa only [hprev] using hraw,
      (hs.2.1 _ hfirst).1, by simpa only [hprev] using (hvals.2.2 _ hfirst).trans hcover⟩
  have hkeep := word_retains_passing_prefix q (stripLast before) previous row later hc
  have hwhole : rows = stripLast before ++ previous :: row :: later := by
    have hleft : rows = before ++ row :: later := by rw [hrows, hrestrow]
    have hright := congrArg (fun bs : List Row => bs ++ row :: later) hbeforeeq
    exact hleft.trans (by simpa only [List.append_assoc, List.singleton_append] using hright)
  have hp : (stripLast before ++ [previous]).map Prod.fst = prefix := by rw [← hbeforeeq, hpref]
  simpa only [hp, ← hwhole, hout] using hkeep

theorem high_multiplicative_input (q b : Nat) (hb : Mu.inputCheck q b = true) :
    SourceMultiplicativePrincipal.inputCheck q b = true :=
  (SourceMultiplicativePrincipal.inputCheck_exact q b).mpr
    ⟨RootLowCollapse.root_low q b hb, (Mu.root_base_lt q b hb).le,
      SourceMultiplicativePrincipal.epsilon_multiplicative _ (RootLowCollapse.root_epsilon q b hb)⟩

/-- The independently executing M word of a HIGH epsilon has a genuine
final epsilon strictly above its actual predecessor, with the literal base
fallback for an empty proper prefix. -/
theorem high_word_lastEligible (q b : Nat) (hb : Mu.inputCheck q b = true) :
    BranchesSupport.lastEligibleCheck q (SourceMultiplicativeTracking.rawWord q b) = true := by
  have hm := high_multiplicative_input q b hb
  have ho := Assignment.execute_multiplicative q b hm
  have ht := Assignment.execute_tracking q b _ ho
  apply (BranchesSupport.lastEligibleCheck_exact q _ ht).mpr
  refine ⟨?_, ?_⟩
  · rw [SourceMultiplicativeTracking.rawWord_last]
    exact AssignmentSupport.high_root_raw_input q b hb
  · rw [SourceMultiplicativeTracking.rawWord_last]
    by_cases he : stripLast (SourceMultiplicativeTracking.rawWord q b) = []
    · rw [if_pos he]; exact Mu.root_base_lt q b hb
    · rw [if_neg he]
      exact ProperPrefix.multiplicative_prefix_lt q b hm _ (lastCode_mem _ he)

/-- VALUE equality with the HIGH M word really forces the original append
branch: the actual last-epsilon checker and SAME-source mu spelling are
transported separately, never inferred from an unrelated tracker alone. -/
theorem appendCheck_of_high_word_values (q b factor : Nat) (heads : List Nat)
    (hb : Mu.inputCheck q b = true)
    (hh : SourceTrackingRaw.trackingCheck q heads = true)
    (hv : heads.map (interpretation q) =
      (SourceMultiplicativeTracking.rawWord q b).map (interpretation q))
    (hf : lowCheckCode q factor = true)
    (hcover : interpretation q factor ≤ Mu.sourceValue q b) :
    BranchesSupport.appendCheck q factor heads = true := by
  have hm := high_multiplicative_input q b hb
  have hword := Assignment.execute_tracking q b _ (Assignment.execute_multiplicative q b hm)
  have heq := Assignment.ValueInvariance.lastEligibleCheck_eq q heads
    (SourceMultiplicativeTracking.rawWord q b) hh hword hv
  have hel : BranchesSupport.lastEligibleCheck q heads = true :=
    heq.trans (high_word_lastEligible q b hb)
  have hs := (BranchesSupport.lastEligibleCheck_exact q heads hh).mp hel
  have hlast : interpretation q (lastCode heads) = interpretation q b := by
    have hl := lastCode_values_eq (interpretation q) (interpretation q) heads
      (SourceMultiplicativeTracking.rawWord q b)
      ((SourceTrackingRaw.trackingCheck_conditions q heads).mp hh).1 hv
    simpa only [SourceMultiplicativeTracking.rawWord_last] using hl
  have hmu := SourceTrackingRaw.Support.muValue_eq q (lastCode heads) b hs.1 hb hlast
  exact (BranchesSupport.appendCheck_exact q factor heads hh).mpr
    ⟨hs.1, hs.2, hf, by simpa only [hmu] using hcover⟩

/-- Every actually executed printed branch retains a genuinely covered
HIGH word VALUE prefix. Empty residual heads force the append branch;
nonempty residual heads construct a passing adjacency after that prefix. -/
theorem branches_retains_high_prefix (q b factor : Nat) (heads out : List Nat)
    (hb : Mu.inputCheck q b = true)
    (hh : SourceTrackingRaw.trackingCheck q heads = true)
    (hf : lowCheckCode q factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q factor))
    (hfinal : interpretation q factor ≤ interpretation q (lastCode heads))
    (eta : Ordinal.{0}) (heta : 0 < eta)
    (hbound : ∀ d ∈ heads, interpretation q d ≤ eta)
    (hpref : ((SourceMultiplicativeTracking.rawWord q b).map (interpretation q)).IsPrefix
      (heads.map (interpretation q)))
    (hcover : eta * interpretation q factor ≤ Mu.sourceValue q b)
    (ho : out ∈ Branches.execute ((q, factor), heads)) :
    ((SourceMultiplicativeTracking.rawWord q b).map (interpretation q)).IsPrefix
      (out.map (interpretation q)) := by
  rcases Branches.execute_branch q factor heads out ho with ⟨ha, rfl⟩ | ⟨ha, hins⟩
  · rw [List.map_append]
    exact hpref.trans (List.prefix_append _ _)
  · obtain ⟨vs, hvs⟩ := hpref
    obtain ⟨prefix, rest, he, hp, hr⟩ := List.map_eq_append_iff.mp hvs.symm
    have hne : prefix ≠ [] := by
      intro hn
      have hm := high_multiplicative_input q b hb
      have hw := Assignment.execute_nonempty q b _ (Assignment.execute_multiplicative q b hm)
      apply hw
      apply List.map_eq_nil_iff.mp
      exact hp.symm.trans (by rw [hn]; rfl)
    have hfactor : interpretation q factor ≤ Mu.sourceValue q b :=
      (Ordinal.le_mul_right _ heta).trans hcover
    cases rest with
    | nil =>
      have hv : heads.map (interpretation q) =
          (SourceMultiplicativeTracking.rawWord q b).map (interpretation q) := by
        rw [he, List.append_nil]; exact hp
      have ht := appendCheck_of_high_word_values q b factor heads hb hh hv hf hfactor
      rw [ht] at ha
      cases ha
    | cons current after =>
      have hm := high_multiplicative_input q b hb
      have hw := Assignment.execute_nonempty q b _ (Assignment.execute_multiplicative q b hm)
      have hl : interpretation q (lastCode prefix) = interpretation q b := by
        simpa only [SourceMultiplicativeTracking.rawWord_last] using
          lastCode_values_eq (interpretation q) (interpretation q) prefix
            (SourceMultiplicativeTracking.rawWord q b) hne hp
      have hmem : lastCode prefix ∈ heads := by
        rw [he]
        exact List.mem_append_left _ (lastCode_mem prefix hne)
      have hc := (ConditionalReplacement.tracking_member_principal q heads hh _ hmem).1
      have hraw : SourceTrackingRaw.Support.inputCheck q (lastCode prefix) = true :=
        (SourceTrackingRaw.Support.inputCheck_exact q _).mpr
          ⟨hc, by simpa only [hl] using Mu.root_base_lt q b hb,
            by simpa only [hl] using RootLowCollapse.root_epsilon q b hb⟩
      have hmu := SourceTrackingRaw.Support.muValue_eq q (lastCode prefix) b hraw hb hl
      have hkeep := insertion_retains_covered_prefix q factor heads prefix current after out
        hh hf hm hfinal eta heta hbound he hne hraw (by simpa only [hmu] using hcover) hins
      exact (by simpa only [hp] using hkeep.map (interpretation q))

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.AssignmentCoverPrefixSupport
