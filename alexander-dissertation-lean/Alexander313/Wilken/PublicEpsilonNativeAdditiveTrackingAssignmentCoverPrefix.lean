import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingAssignmentCoverPrefixSupport

/-!
# A real direct mu cover retains the complete independently computed prefix

The source derivation performs genuine factor removal and the actual printed
append or greatest-insertion branch. Epsilon multiplicative closure bounds
every recursive prefix below by the covering HIGH epsilon. Joint execution
bounds derive the transition after its independently computed VALUE prefix.
An empty residual instead forces the actual append test. No assigned prefix,
word, selected index, factorization, cover or recursive caller is supplied.
The full nonM-right lexical comparison remains separate. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.AssignmentCoverPrefix

open PublicEpsilonUnboundedIota SourceTrackingSequences
open AssignmentSupport AssignmentCoverPrefixSupport

/-- The actual finite source clauses, rather than a separately assigned
word, retain every direct covering HIGH epsilon's independent M word. -/
theorem derivation_covered_prefix (q b current : Nat) (out : List Nat)
    (hb : Mu.inputCheck q b = true) (hd : Derivation q current out)
    (hbc : interpretation q b < interpretation q current)
    (hcover : interpretation q current ≤ Mu.sourceValue q b) :
    ((SourceMultiplicativeTracking.rawWord q b).map (interpretation q)).IsPrefix
      (out.map (interpretation q)) := by
  revert hbc hcover
  induction hd with
  | multiplicative current hm =>
    intro hbc hcover
    exact SourceMultiplicativeTracking.Order.rawWord_direct_cover_prefix q b current hb hm hbc hcover
  | singleton current hm hs =>
    intro hbc hcover
    have hi := (Factor.singletonCheck_exact q current).mp hs
    have hsmall : interpretation q current ≤ base q ^ Ordinal.omega0 := hi.2.2.2.2
    exact False.elim ((not_lt_of_ge hbc.le) (hsmall.trans_lt (base_power_lt_high q b hb)))
  | split current prefix factor heads out hf hd ho ih =>
    intro hbc hcover
    obtain ⟨_, hlp, _, hlf, _, hp, hbp, hlt, hm, hone, hv, hlast, hcount⟩ :=
      Factor.execute_spec q current (prefix, factor) hf
    have hh : heads ∈ Assignment.execute q prefix :=
      (Assignment.execute_iff_derivation q prefix heads).mpr hd
    have hs := (Assignment.execute_spec q prefix heads hh).2.1
    have hge := factor_prefix_ge_high q b current prefix factor hb hf hbc
    have hprefix : ((SourceMultiplicativeTracking.rawWord q b).map (interpretation q)).IsPrefix
        (heads.map (interpretation q)) := by
      rcases eq_or_lt_of_le hge with heq | hstrict
      · have hbo := Assignment.execute_multiplicative q b (high_multiplicative_input q b hb)
        have hvalues := Assignment.ValueInvariance.execute_values_eq q prefix b heads
          (SourceMultiplicativeTracking.rawWord q b) hh hbo heq.symm
        rw [hvalues]
        exact List.prefix_refl _
      · exact ih hstrict (hlt.le.trans hcover)
    have hfinal : interpretation q factor ≤ interpretation q (lastCode heads) :=
      (Factor.Bounds.execute_last_le_prefix_last q current (prefix, factor) hf).trans hs.2.2.1
    have hq := (HeightBoundary.input_spec q prefix hlp).2.1
    have hpos : 0 < interpretation q prefix := (base_pos q hq).trans_le hbp
    exact branches_retains_high_prefix q b factor heads out hb hs.1 hlf hm hfinal
      (interpretation q prefix) hpos hs.2.1 hprefix (hv.symm.trans_le hcover) ho

/-- On the unchanged original RAW LOW P domain, a genuine direct mu
cover forces the independently executing complete assignment to preserve
the covering epsilon's full M prefix in VALUES, including nonM inputs. -/
theorem execute_covered_prefix (q b current : Nat) (out : List Nat)
    (hb : Mu.inputCheck q b = true)
    (hbc : interpretation q b < interpretation q current)
    (hcover : interpretation q current ≤ Mu.sourceValue q b)
    (ho : out ∈ Assignment.execute q current) :
    ((SourceMultiplicativeTracking.rawWord q b).map (interpretation q)).IsPrefix
      (out.map (interpretation q)) :=
  derivation_covered_prefix q b current out hb
    ((Assignment.execute_iff_derivation q current out).mp ho) hbc hcover

/-- Both complete procedures execute independently. Their actual values
derive the same direct-cover prefix; no recursive output is an input oracle. -/
theorem execute_direct_cover_prefix (q b current : Nat) (before out : List Nat)
    (hb : Mu.inputCheck q b = true)
    (hbc : interpretation q b < interpretation q current)
    (hcover : interpretation q current ≤ Mu.sourceValue q b)
    (hbefore : before ∈ Assignment.execute q b)
    (ho : out ∈ Assignment.execute q current) :
    (before.map (interpretation q)).IsPrefix (out.map (interpretation q)) := by
  have he := Part.mem_unique hbefore
    (Assignment.execute_multiplicative q b (high_multiplicative_input q b hb))
  rw [he]
  exact execute_covered_prefix q b current out hb hbc hcover ho

/-- The smaller input executes the complete factor/insertion assignment.
The greater side here is the concrete ordinary Node word; it is identified
with a complete assignment only in the genuine M adapter below. -/
theorem execute_left_word_lex (q left right : Nat) (out : List Nat)
    (hr : SourceLocalization.inputCheck q right = true)
    (horder : interpretation q left < interpretation q right)
    (ho : out ∈ Assignment.execute q left) :
    List.Lex (· < ·) (out.map (interpretation q))
      ((SourceMultiplicativeTracking.word q right).map (interpretation q)) := by
  let P : Nat → Prop := fun n => ∀ right,
    (SourceMultiplicativeTracking.properPrefix q right).length = n →
      SourceLocalization.inputCheck q right = true →
      interpretation q left < interpretation q right →
        List.Lex (· < ·) (out.map (interpretation q))
          ((SourceMultiplicativeTracking.word q right).map (interpretation q))
  have hbound := (Assignment.execute_spec q left out ho).2.1.2.1
  have hne : out.map (interpretation q) ≠ [] := by
    intro he
    exact Assignment.execute_nonempty q left out ho (List.map_eq_nil_iff.mp he)
  have hall : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro right hn hr horder
      cases hs : SourceMultiplicativeTracking.Support.select q right
          (SourceMultiplicativeTracking.Support.table q
            (SourceMultiplicativeTracking.properPrefix q right)) with
      | none =>
        have hw : SourceMultiplicativeTracking.word q right = [right] := by
          simp only [SourceMultiplicativeTracking.word, SourceMultiplicativeTracking.Support.extend, hs]
        rw [hw, List.map_cons, List.map_nil]
        cases hx : out.map (interpretation q) with
        | nil => exact False.elim (hne hx)
        | cons a xs =>
          apply List.Lex.rel
          have ha : a ∈ out.map (interpretation q) := by rw [hx]; exact List.mem_cons_self
          obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ha
          exact (hbound d hd).trans_lt horder
      | some e =>
        have he := SourceMultiplicativeTracking.Recurrence.selected_node q right right e hr hs
        have hei := SourceMultiplicativeTracking.OrderSupport.high_node_input q e.1 he.2.1
        have hw := SourceMultiplicativeTracking.Recurrence.word_some_values q right e hr hs
        rw [hw]
        by_cases hbefore : interpretation q left < interpretation q e.1
        · have hlt := (SourceMultiplicativeTracking.Recurrence.selected_prefix_shorter
            q right right e hr hs).trans_eq hn
          exact List.Lex.append_right (· < ·) [interpretation q right]
            (ih _ hlt e.1 rfl hei hbefore)
        · have hel : interpretation q e.1 ≤ interpretation q left := le_of_not_gt hbefore
          by_cases heq : interpretation q left = interpretation q e.1
          · have heo := Assignment.execute_multiplicative q e.1
              (high_multiplicative_input q e.1 he.2.1)
            have hvalues := Assignment.ValueInvariance.execute_values_eq q left e.1 out
              (SourceMultiplicativeTracking.rawWord q e.1) ho heo heq
            rw [hvalues, SourceMultiplicativeTracking.RawRecurrence.rawWord_values_word q e.1 hei]
            exact SourceMultiplicativeTracking.OrderSupport.prefix_lex_singleton _ _ _
              (List.prefix_refl _) (fun a ha =>
                (SourceMultiplicativeTracking.OrderSupport.word_values_bound q e.1 hei a ha).trans_lt
                  (ProperPrefix.properPrefix_lt_root q right hr e.1 he.1))
          · have helt : interpretation q e.1 < interpretation q left :=
              lt_of_le_of_ne hel (Ne.symm heq)
            have hp := execute_covered_prefix q e.1 left out he.2.1 helt
              (horder.le.trans he.2.2) ho
            rw [SourceMultiplicativeTracking.RawRecurrence.rawWord_values_word q e.1 hei] at hp
            exact SourceMultiplicativeTracking.OrderSupport.prefix_lex_singleton _ _ _ hp
              (fun a ha => by
                obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ha
                exact (hbound d hd).trans_lt horder)
  exact hall _ right rfl hr horder

/-- Source Lemma3.22 now holds for every genuine original P input on the
smaller side and every genuine original M input on the greater side.
The nonM-greater factor comparison remains a separate obligation. -/
theorem execute_right_multiplicative_lex (q left right : Nat) (out other : List Nat)
    (hr : SourceMultiplicativePrincipal.inputCheck q right = true)
    (horder : interpretation q left < interpretation q right)
    (ho : out ∈ Assignment.execute q left)
    (ht : other ∈ Assignment.execute q right) :
    List.Lex (· < ·) (out.map (interpretation q)) (other.map (interpretation q)) := by
  have he := Part.mem_unique ht (Assignment.execute_multiplicative q right hr)
  have hra := SourceMultiplicativePrincipal.rootAdapter_input q right hr
  have hri := SourceMultiplicativePrincipal.rootInput q right hr
  have hrv := (SourceLocalization.RootAdapter.rootCode_spec q right hra).2
  rw [he, SourceMultiplicativeTracking.OrderSupport.rawWord_root_values q right hra]
  exact execute_left_word_lex q left (SourceLocalization.RootAdapter.rootCode q right) out hri
    (by simpa only [hrv] using horder) ho

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.AssignmentCoverPrefix
