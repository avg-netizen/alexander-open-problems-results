import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingAssignment

/-!
# Actual native replacement value transport

Original native spellings can differ. Equal LOW values have the same
canonical public emissions, so the actual raised context and actual
raised factor search agree literally. Genuine finite returns preserve
the raised value word. The other conditional branch is the independently
executed principal product. No equality of original spellings or tracker
is inferred from values alone. Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.AssignmentValueSupport

open PublicEpsilonUnboundedIota SourceTrackingSequences

theorem publicCode_eq (q c d : Nat) (hc : lowCheckCode q c = true)
    (hd : lowCheckCode q d = true) (hv : interpretation q c = interpretation q d) :
    UniformPublicReturn.publicCode q c = UniformPublicReturn.publicCode q d :=
  UniformPublicReturn.publicCode_value_invariant q q c d
    ((UniformPublicReturn.inputCheck_exact q c).mpr hc)
    ((UniformPublicReturn.inputCheck_exact q d).mpr hd) hv

/-- The raised word is literally identical because both actual public
inputs to its real search are canonical equal-value emissions. -/
theorem raisedWord_eq (q head other factor otherFactor : Nat)
    (hh : lowCheckCode q head = true) (ht : lowCheckCode q other = true)
    (hf : lowCheckCode q factor = true) (hg : lowCheckCode q otherFactor = true)
    (hv : interpretation q head = interpretation q other)
    (he : interpretation q factor = interpretation q otherFactor) :
    ReplacementSupport.raisedWord q head factor =
      ReplacementSupport.raisedWord q other otherFactor := by
  have hb := publicCode_eq q head other hh ht hv
  have hp := publicCode_eq q factor otherFactor hf hg he
  simp only [ReplacementSupport.raisedWord, ReplacementSupport.raisedSearch,
    ReplacementSupport.raisedBaseCode, hb, hp]

/-- Both real finite returns preserve their common actual raised word;
their original returned code spellings need not agree. -/
theorem raisedReplacement_values_eq (q head other factor otherFactor : Nat)
    (word otherWord : List Nat)
    (hh : SourceTrackingRaw.Support.inputCheck q head = true)
    (ht : SourceTrackingRaw.Support.inputCheck q other = true)
    (hf : lowCheckCode q factor = true) (hg : lowCheckCode q otherFactor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q factor))
    (hlt : interpretation q head < interpretation q factor)
    (hv : interpretation q head = interpretation q other)
    (he : interpretation q factor = interpretation q otherFactor)
    (hw : word ∈ Replacement.raisedReplacement q head factor)
    (ho : otherWord ∈ Replacement.raisedReplacement q other otherFactor) :
    word.map (interpretation q) = otherWord.map (interpretation q) := by
  have hlow := ((SourceTrackingRaw.Support.inputCheck_exact q head).mp hh).1
  have htlow := ((SourceTrackingRaw.Support.inputCheck_exact q other).mp ht).1
  have hm' : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal
      (interpretation q otherFactor) := by simpa only [he] using hm
  have hlt' : interpretation q other < interpretation q otherFactor := by
    simpa only [hv, he] using hlt
  obtain ⟨raised, hra, _, hvalues, _, _⟩ :=
    Replacement.raisedReplacement_spec q head factor word hh hf hm hlt hw
  obtain ⟨otherRaised, hrb, _, hotherValues, _, _⟩ :=
    Replacement.raisedReplacement_spec q other otherFactor otherWord ht hg hm' hlt' ho
  have hp := raisedWord_eq q head other factor otherFactor hlow htlow hf hg hv he
  have hraised : raised = otherRaised := Part.mem_unique (by rw [hp] at hra; exact hra) hrb
  have hb : ReplacementSupport.raisedBaseCode q head =
      ReplacementSupport.raisedBaseCode q other := publicCode_eq q head other hlow htlow hv
  exact hvalues.trans (by rw [hraised, hb]; exact hotherValues.symm)

theorem smallReplacement_values_eq (q head other factor otherFactor : Nat)
    (word otherWord : List Nat)
    (hp : 0 < interpretation q head)
    (hadd : Ordinal.IsPrincipal (· + ·) (interpretation q head))
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q factor))
    (hv : interpretation q head = interpretation q other)
    (he : interpretation q factor = interpretation q otherFactor)
    (hw : word ∈ Replacement.smallReplacement q head factor)
    (ho : otherWord ∈ Replacement.smallReplacement q other otherFactor) :
    word.map (interpretation q) = otherWord.map (interpretation q) := by
  have hp' : 0 < interpretation q other := by simpa only [hv] using hp
  have hadd' : Ordinal.IsPrincipal (· + ·) (interpretation q other) := by
    simpa only [hv] using hadd
  have hm' : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal
      (interpretation q otherFactor) := by simpa only [he] using hm
  obtain ⟨a, rfl, _, _, ha⟩ := Replacement.smallReplacement_spec q head factor word hw hp hadd hm
  obtain ⟨b, rfl, _, _, hb⟩ := Replacement.smallReplacement_spec q other otherFactor otherWord ho hp' hadd' hm'
  simp only [List.map_cons, List.map_nil, ha, hb, hv, he]

/-- Every actual paired written head gets an equal-value conditional
replacement. Both trackers and factor-to-final bounds are genuine
executing premises, not consequences of equal value lists. -/
theorem conditional_values_eq (q : Nat) (heads otherHeads : List Nat)
    (hh : SourceTrackingRaw.trackingCheck q heads = true)
    (ht : SourceTrackingRaw.trackingCheck q otherHeads = true)
    (head other factor otherFactor : Nat) (hhead : head ∈ heads) (hother : other ∈ otherHeads)
    (hf : lowCheckCode q factor = true) (hg : lowCheckCode q otherFactor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q factor))
    (hb : interpretation q factor ≤ interpretation q (lastCode heads))
    (hc : interpretation q otherFactor ≤ interpretation q (lastCode otherHeads))
    (hv : interpretation q head = interpretation q other)
    (he : interpretation q factor = interpretation q otherFactor)
    (word otherWord : List Nat)
    (hw : word ∈ ConditionalReplacement.execute q head factor)
    (ho : otherWord ∈ ConditionalReplacement.execute q other otherFactor) :
    word.map (interpretation q) = otherWord.map (interpretation q) := by
  have hs := ConditionalReplacement.tracking_member_principal q heads hh head hhead
  have hm' : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal
      (interpretation q otherFactor) := by simpa only [he] using hm
  have ha := ConditionalReplacement.execute_spec q heads hh head factor hhead hf hm hb word hw
  have hd := ConditionalReplacement.execute_spec q otherHeads ht other otherFactor hother hg hm' hc otherWord ho
  rcases ha.2.2 with ⟨hlt, hw, _⟩ | ⟨hle, a, rfl, ha⟩
  · rcases hd.2.2 with ⟨hlt', ho, _⟩ | ⟨hle', b, rfl, hb'⟩
    · exact raisedReplacement_values_eq q head other factor otherFactor word otherWord
        (ConditionalReplacement.raised_member_caller q heads hh head factor hhead hlt hb).2
        (ConditionalReplacement.raised_member_caller q otherHeads ht other otherFactor hother hlt' hc).2
        hf hg hm hlt hv he hw ho
    · have hle : interpretation q factor ≤ interpretation q head := by
        simpa only [← hv, ← he] using hle'
      exact False.elim (hlt.not_ge hle)
  · rcases hd.2.2 with ⟨hlt', ho, _⟩ | ⟨hle', b, rfl, hb'⟩
    · have hlt : interpretation q head < interpretation q factor := by
        simpa only [← hv, ← he] using hlt'
      exact False.elim (hlt.not_ge hle)
    · simp only [List.map_cons, List.map_nil, ha, hb', hv, he]

noncomputable def rowValues (q : Nat) (row : InsertionSupport.Row) :
    Ordinal.{0} × List Ordinal.{0} := (interpretation q row.1, row.2.map (interpretation q))

/-- Real chronological replacement relations, with their actual tracker
callers retained, agree at every paired head position. -/
theorem relations_values_eq (q factor otherFactor : Nat) (full otherFull : List Nat)
    (hh : SourceTrackingRaw.trackingCheck q full = true)
    (ht : SourceTrackingRaw.trackingCheck q otherFull = true)
    (hf : lowCheckCode q factor = true) (hg : lowCheckCode q otherFactor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q factor))
    (hb : interpretation q factor ≤ interpretation q (lastCode full))
    (hc : interpretation q otherFactor ≤ interpretation q (lastCode otherFull))
    (he : interpretation q factor = interpretation q otherFactor)
    (heads otherHeads : List Nat) (rows otherRows : List InsertionSupport.Row)
    (hs : ∀ a ∈ heads, a ∈ full) (hu : ∀ a ∈ otherHeads, a ∈ otherFull)
    (hv : heads.map (interpretation q) = otherHeads.map (interpretation q))
    (hr : List.Forall₂ (InsertionSupport.Matches q factor) heads rows)
    (ho : List.Forall₂ (InsertionSupport.Matches q otherFactor) otherHeads otherRows) :
    rows.map (rowValues q) = otherRows.map (rowValues q) := by
  induction heads generalizing otherHeads rows otherRows with
  | nil =>
    cases hr
    have hn : otherHeads = [] := List.map_eq_nil_iff.mp hv.symm
    subst otherHeads
    cases ho
    rfl
  | cons a heads ih =>
    cases hr with
    | cons hrow hrest =>
      cases otherHeads with
      | nil => simp only [List.map_cons, List.map_nil, List.cons_ne_nil] at hv
      | cons b otherHeads =>
        cases ho with
        | cons hother htail =>
          have hvalues := List.cons.inj hv
          have hwords := conditional_values_eq q full otherFull hh ht a b factor otherFactor
            (hs a List.mem_cons_self) (hu b List.mem_cons_self) hf hg hm hb hc
            hvalues.1 he _ _
            (by simpa only [hrow.1] using hrow.2)
            (by simpa only [hother.1] using hother.2)
          have hrows := ih otherHeads _ _
            (fun d hd => hs d (List.mem_cons_of_mem _ hd))
            (fun d hd => hu d (List.mem_cons_of_mem _ hd)) hvalues.2 hrest htail
          simp only [List.map_cons, rowValues, hrow.1, hother.1, hvalues.1, hwords, hrows]

theorem executeRows_values_eq (q factor otherFactor : Nat) (heads otherHeads : List Nat)
    (hh : SourceTrackingRaw.trackingCheck q heads = true)
    (ht : SourceTrackingRaw.trackingCheck q otherHeads = true)
    (hf : lowCheckCode q factor = true) (hg : lowCheckCode q otherFactor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q factor))
    (hb : interpretation q factor ≤ interpretation q (lastCode heads))
    (hc : interpretation q otherFactor ≤ interpretation q (lastCode otherHeads))
    (he : interpretation q factor = interpretation q otherFactor)
    (hv : heads.map (interpretation q) = otherHeads.map (interpretation q))
    (rows otherRows : List InsertionSupport.Row)
    (hr : rows ∈ InsertionSupport.executeRows q factor heads)
    (ho : otherRows ∈ InsertionSupport.executeRows q otherFactor otherHeads) :
    rows.map (rowValues q) = otherRows.map (rowValues q) :=
  relations_values_eq q factor otherFactor heads otherHeads hh ht hf hg hm hb hc he
    heads otherHeads rows otherRows (fun _ h => h) (fun _ h => h) hv
    (InsertionSupport.executeRows_relation q factor heads rows hr)
    (InsertionSupport.executeRows_relation q otherFactor otherHeads otherRows ho)

theorem rawInput_eq (q c d : Nat) (hc : lowCheckCode q c = true)
    (hd : lowCheckCode q d = true) (hv : interpretation q c = interpretation q d) :
    SourceTrackingRaw.Support.inputCheck q c = SourceTrackingRaw.Support.inputCheck q d := by
  apply Bool.eq_iff_iff.mpr
  change (SourceTrackingRaw.Support.inputCheck q c = true) ↔
    SourceTrackingRaw.Support.inputCheck q d = true
  rw [SourceTrackingRaw.Support.inputCheck_exact, SourceTrackingRaw.Support.inputCheck_exact]
  simp only [hc, hd, hv]

theorem coverCheck_eq (q previous other current otherCurrent : Nat)
    (hp : lowCheckCode q previous = true) (ho : lowCheckCode q other = true)
    (hc : lowCheckCode q current = true) (hd : lowCheckCode q otherCurrent = true)
    (hv : interpretation q previous = interpretation q other)
    (he : interpretation q current = interpretation q otherCurrent) :
    Insertion.coverCheck q previous current = Insertion.coverCheck q other otherCurrent := by
  have hi := rawInput_eq q previous other hp ho hv
  cases hr : SourceTrackingRaw.Support.inputCheck q previous with
  | false =>
    have ht : SourceTrackingRaw.Support.inputCheck q other = false := hi.symm.trans hr
    simp only [Insertion.coverCheck, hr, ht, Bool.false_and]
  | true =>
    have ht : SourceTrackingRaw.Support.inputCheck q other = true := hi.symm.trans hr
    have hm := SourceTrackingRaw.Support.muValue_invariant q previous other hr ht hv
    apply Bool.eq_iff_iff.mpr
    change (Insertion.coverCheck q previous current = true) ↔
      Insertion.coverCheck q other otherCurrent = true
    rw [Insertion.coverCheck_exact, Insertion.coverCheck_exact]
    simp only [hr, ht, hc, hd, he, hm]

theorem firstCode_values_eq (q : Nat) (xs ys : List Nat)
    (hv : xs.map (interpretation q) = ys.map (interpretation q)) :
    interpretation q (Insertion.firstCode xs) = interpretation q (Insertion.firstCode ys) := by
  cases xs with
  | nil =>
    have hn : ys = [] := List.map_eq_nil_iff.mp hv.symm
    subst ys
    rfl
  | cons a xs =>
    cases ys with
    | nil => simp only [List.map_cons, List.map_nil, List.cons_ne_nil] at hv
    | cons b ys =>
      simpa only [Insertion.firstCode, List.head?_cons, Option.getD_some] using (List.cons.inj hv).1

theorem firstCode_low (q : Nat) (xs : List Nat) (hne : xs ≠ [])
    (hl : ∀ c ∈ xs, lowCheckCode q c = true) : lowCheckCode q (Insertion.firstCode xs) = true := by
  cases xs with
  | nil => exact False.elim (hne rfl)
  | cons a xs =>
    simpa only [Insertion.firstCode, List.head?_cons, Option.getD_some] using hl a List.mem_cons_self

def ValidRow (q : Nat) (row : InsertionSupport.Row) : Prop :=
  lowCheckCode q row.1 = true ∧ row.2 ≠ [] ∧ ∀ c ∈ row.2, lowCheckCode q c = true

theorem executeRows_valid (q factor : Nat) (heads : List Nat)
    (hh : SourceTrackingRaw.trackingCheck q heads = true)
    (hf : lowCheckCode q factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q factor))
    (hb : interpretation q factor ≤ interpretation q (lastCode heads))
    (rows : List InsertionSupport.Row) (hr : rows ∈ InsertionSupport.executeRows q factor heads) :
    ∀ row ∈ rows, ValidRow q row := by
  have hrel := InsertionSupport.executeRows_relation q factor heads rows hr
  intro row hrow
  have hs := InsertionSupport.relation_members q factor hrel row hrow
  have hp := ConditionalReplacement.tracking_member_principal q heads hh row.1 hs.1
  have hw := ConditionalReplacement.execute_spec q heads hh row.1 factor hs.1 hf hm hb row.2 hs.2
  exact ⟨hp.1, hw.1, fun c hc => (hw.2.1 c hc).1⟩

noncomputable def candidateValues (q : Nat) (c : Insertion.Candidate) :
    Nat × List Ordinal.{0} := (c.1, c.2.map (interpretation q))

/-- The right-priority scan executes the same cover flags on both
concrete row tables and selects the same position and replacement values. -/
theorem choose_values_eq (q : Nat) (rows otherRows : List InsertionSupport.Row)
    (hv : rows.map (rowValues q) = otherRows.map (rowValues q))
    (hr : ∀ row ∈ rows, ValidRow q row) (ho : ∀ row ∈ otherRows, ValidRow q row) :
    (Insertion.choose q rows).map (candidateValues q) =
      (Insertion.choose q otherRows).map (candidateValues q) := by
  induction rows generalizing otherRows with
  | nil =>
    have hn : otherRows = [] := List.map_eq_nil_iff.mp hv.symm
    subst otherRows
    rfl
  | cons a rest ih =>
    cases otherRows with
    | nil => simp only [List.map_cons, List.map_nil, List.cons_ne_nil] at hv
    | cons otherA otherRest =>
      have hvalues := List.cons.inj hv
      cases rest with
      | nil =>
        have hn : otherRest = [] := List.map_eq_nil_iff.mp hvalues.2.symm
        subst otherRest
        rfl
      | cons b later =>
        cases otherRest with
        | nil =>
          have hbad := hvalues.2
          simp only [List.map_cons, List.map_nil, List.cons_ne_nil] at hbad
        | cons otherB otherLater =>
          have hrec := ih (otherB :: otherLater) hvalues.2
            (fun row hm => hr row (List.mem_cons_of_mem _ hm))
            (fun row hm => ho row (List.mem_cons_of_mem _ hm))
          have ha : rowValues q a = rowValues q otherA := hvalues.1
          have hb : rowValues q b = rowValues q otherB := (List.cons.inj hvalues.2).1
          have hcov := coverCheck_eq q a.1 otherA.1 (Insertion.firstCode b.2)
            (Insertion.firstCode otherB.2)
            (hr a List.mem_cons_self).1 (ho otherA List.mem_cons_self).1
            (firstCode_low q b.2 (hr b (by simp)).2.1 (hr b (by simp)).2.2)
            (firstCode_low q otherB.2 (ho otherB (by simp)).2.1 (ho otherB (by simp)).2.2)
            (congrArg Prod.fst ha)
            (firstCode_values_eq q b.2 otherB.2 (congrArg Prod.snd hb))
          cases hl : Insertion.choose q (b :: later) with
          | none =>
            cases ht : Insertion.choose q (otherB :: otherLater) with
            | some c =>
              simp only [hl, ht, Option.map_none, Option.map_some, Option.none_ne_some] at hrec
            | none =>
              have hw : b.2.map (interpretation q) = otherB.2.map (interpretation q) := congrArg Prod.snd hb
              cases hc : Insertion.coverCheck q a.1 (Insertion.firstCode b.2) <;>
                simp only [Insertion.choose_pair, hl, ht, ← hcov, hc, Bool.cond_false,
                  Bool.cond_true, Option.map_none, Option.map_some, candidateValues, hw]
          | some c =>
            cases ht : Insertion.choose q (otherB :: otherLater) with
            | none =>
              simp only [hl, ht, Option.map_none, Option.map_some, Option.some_ne_none] at hrec
            | some d =>
              have he : candidateValues q c = candidateValues q d := by
                simpa only [hl, ht, Option.map_some, Option.some.injEq] using hrec
              have hn : c.1 = d.1 := congrArg Prod.fst he
              have hw : c.2.map (interpretation q) = d.2.map (interpretation q) := congrArg Prod.snd he
              simp only [Insertion.choose_pair, hl, ht, Option.map_some, candidateValues, hn, hw]

theorem default_values_eq (q : Nat) (rows otherRows : List InsertionSupport.Row)
    (hv : rows.map (rowValues q) = otherRows.map (rowValues q)) :
    ((rows.head?.getD (0, [])).2).map (interpretation q) =
      ((otherRows.head?.getD (0, [])).2).map (interpretation q) := by
  cases rows with
  | nil =>
    have hn : otherRows = [] := List.map_eq_nil_iff.mp hv.symm
    subst otherRows
    rfl
  | cons a rows =>
    cases otherRows with
    | nil => simp only [List.map_cons, List.map_nil, List.cons_ne_nil] at hv
    | cons b otherRows =>
      simpa only [List.head?_cons, Option.getD_some] using congrArg Prod.snd (List.cons.inj hv).1

theorem take_heads_values_eq (q n : Nat) (rows otherRows : List InsertionSupport.Row)
    (hv : rows.map (rowValues q) = otherRows.map (rowValues q)) :
    ((rows.take n).map Prod.fst).map (interpretation q) =
      ((otherRows.take n).map Prod.fst).map (interpretation q) := by
  have he := congrArg (fun rs : List (Ordinal.{0} × List Ordinal.{0}) => (rs.take n).map Prod.fst) hv
  simpa only [← List.map_take, List.map_map, rowValues] using he

theorem insertion_word_values_eq (q : Nat) (rows otherRows : List InsertionSupport.Row)
    (hv : rows.map (rowValues q) = otherRows.map (rowValues q))
    (hr : ∀ row ∈ rows, ValidRow q row) (ho : ∀ row ∈ otherRows, ValidRow q row) :
    (Insertion.word q rows).map (interpretation q) =
      (Insertion.word q otherRows).map (interpretation q) := by
  have hc := choose_values_eq q rows otherRows hv hr ho
  cases hl : Insertion.choose q rows with
  | none =>
    cases ht : Insertion.choose q otherRows with
    | some c => simp only [hl, ht, Option.map_none, Option.map_some, Option.none_ne_some] at hc
    | none => simpa only [Insertion.word, hl, ht] using default_values_eq q rows otherRows hv
  | some c =>
    cases ht : Insertion.choose q otherRows with
    | none => simp only [hl, ht, Option.map_none, Option.map_some, Option.some_ne_none] at hc
    | some d =>
      have he : candidateValues q c = candidateValues q d := by
        simpa only [hl, ht, Option.map_some, Option.some.injEq] using hc
      have hn : c.1 = d.1 := congrArg Prod.fst he
      have hw : c.2.map (interpretation q) = d.2.map (interpretation q) := congrArg Prod.snd he
      simpa only [Insertion.word, hl, ht, List.map_append, hn, hw] using
        congrArg (fun prefix => prefix ++ d.2.map (interpretation q))
          (take_heads_values_eq q d.1 rows otherRows hv)

/-- Both concrete partial insertion executions agree in values. Every
replacement row and every cover operand is admitted by the real source
tracker and original factor bound before the scan is compared. -/
theorem insertion_values_eq (q factor otherFactor : Nat) (heads otherHeads : List Nat)
    (hh : SourceTrackingRaw.trackingCheck q heads = true)
    (ht : SourceTrackingRaw.trackingCheck q otherHeads = true)
    (hf : lowCheckCode q factor = true) (hg : lowCheckCode q otherFactor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q factor))
    (hb : interpretation q factor ≤ interpretation q (lastCode heads))
    (hc : interpretation q otherFactor ≤ interpretation q (lastCode otherHeads))
    (he : interpretation q factor = interpretation q otherFactor)
    (hv : heads.map (interpretation q) = otherHeads.map (interpretation q))
    (word otherWord : List Nat)
    (hw : word ∈ Insertion.execute ((q, factor), heads))
    (ho : otherWord ∈ Insertion.execute ((q, otherFactor), otherHeads)) :
    word.map (interpretation q) = otherWord.map (interpretation q) := by
  obtain ⟨rows, hr, rfl⟩ := (Part.mem_map_iff _).mp hw
  obtain ⟨otherRows, hs, rfl⟩ := (Part.mem_map_iff _).mp ho
  have hm' : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal
      (interpretation q otherFactor) := by simpa only [he] using hm
  exact insertion_word_values_eq q rows otherRows
    (executeRows_values_eq q factor otherFactor heads otherHeads hh ht hf hg hm hb hc he hv rows otherRows hr hs)
    (executeRows_valid q factor heads hh hf hm hb rows hr)
    (executeRows_valid q otherFactor otherHeads ht hg hm' hc otherRows hs)

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.AssignmentValueSupport
