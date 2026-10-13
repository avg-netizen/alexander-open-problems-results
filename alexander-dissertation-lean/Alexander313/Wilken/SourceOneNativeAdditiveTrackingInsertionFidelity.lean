import Alexander313.Wilken.SourceOneNativeAdditiveTrackingInsertion

/-!
# Genuine original source-one tracking splice after greatest insertion

Pure reference-prefix and concatenation proofs retain the literal original
head prefix. Actual conditional execution derives each replacement tracker
and first>=head. When the replacement has a proper epsilon prefix its
raised branch forces the selected head into the original proper prefix,
so real original strictness supplies the join. The actual chosen cover
supplies its mu clause. All callers follow from the checked original
headword/factor and honest factor<=FINAL bound; no assigned tracking word,
endpoint, insertion or value-only mu oracle. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.InsertionFidelity

open Hereditary.FinePredecessor (stripLast)
open NativeContext.SourceTrackingSequences (lastCode lastCode_mem lastCode_singleton
  lastCode_append_singleton stripLast_append_singleton stripLast_singleton)
open SkTracking.Support (stripLast_cons_nonempty lastCode_cons_nonempty)
open InsertionSupport (Row)

theorem stripLast_append_nonempty (before rest : List Nat) (hne : rest ≠ []) :
    stripLast (before ++ rest) = before ++ stripLast rest := by
  induction before with
  | nil => simp only [List.nil_append]
  | cons a bs ih =>
    have hrest : bs ++ rest ≠ [] := by
      intro he
      exact hne (List.append_eq_nil_iff.mp he).2
    change stripLast (a :: (bs ++ rest)) = a :: (bs ++ stripLast rest)
    rw [stripLast_cons_nonempty a _ hrest]
    exact congrArg (List.cons a) ih

theorem lastCode_append_nonempty (before rest : List Nat) (hne : rest ≠ []) :
    lastCode (before ++ rest) = lastCode rest := by
  obtain ⟨a, he, hh⟩ := Hereditary.FinePredecessor.stripLast_split rest hne
  calc
    lastCode (before ++ rest) = a := by rw [he, ← List.append_assoc, lastCode_append_singleton]
    _ = lastCode rest := by simp only [lastCode, hh, Option.getD_some]

theorem reference_prefix (before rest : List Nat)
    (hr : SourceTrackingRaw.Reference (before ++ rest)) : SourceTrackingRaw.Reference before := by
  revert hr
  induction before with
  | nil => intro hr; exact .nil
  | cons a bs ih =>
    intro hr
    cases bs with
    | nil => exact .one a hr.first
    | cons b bs =>
      cases hr with
      | cons a b xs ha hab hc tail => exact .cons a b bs ha hab hc (ih tail)

theorem reference_append (before : List Nat) (b : Nat) (rest : List Nat)
    (hr : SourceTrackingRaw.Reference before)
    (ht : SourceTrackingRaw.Reference (b :: rest))
    (hne : before ≠ [])
    (hlt : interpretation 0 (lastCode before) < interpretation 0 b)
    (hc : interpretation 0 b ≤ SourceTrackingRaw.Support.muValue (lastCode before)) :
    SourceTrackingRaw.Reference (before ++ b :: rest) := by
  revert hne hlt hc
  induction hr with
  | nil => intro hn; exact False.elim (hn rfl)
  | one a ha =>
    intro hn hlt hc
    exact .cons a b rest ha
      (by simpa only [lastCode_singleton] using hlt)
      (by simpa only [lastCode_singleton] using hc) ht
  | cons a d ds ha had hcover tail ih =>
    intro hn hlt hc
    have htail := ih (List.cons_ne_nil _ _)
      (by simpa only [lastCode_cons_nonempty a _ (List.cons_ne_nil _ _)] using hlt)
      (by simpa only [lastCode_cons_nonempty a _ (List.cons_ne_nil _ _)] using hc)
    exact .cons a d (ds ++ b :: rest) ha had hcover htail

theorem tracking_member_above_one (word : List Nat)
    (hw : SourceTrackingRaw.trackingCheck word = true) (hne : stripLast word ≠ []) :
    ∀ c ∈ word, 1 < interpretation 0 c := by
  have hs := (SourceTrackingRaw.trackingCheck_exact word).mp hw
  obtain ⟨a, he, hh⟩ := Hereditary.FinePredecessor.stripLast_split word hs.1
  have hlast : lastCode word = a := by simp only [lastCode, hh, Option.getD_some]
  intro c hc
  rw [he] at hc
  rcases List.mem_append.mp hc with hc | hc
  · exact ((SourceTrackingRaw.Support.inputCheck_exact c).mp (hs.2.1.nodes c hc)).2.1
  · have hc : c = a := List.mem_singleton.mp hc
    subst c
    have hb := hs.2.2.2.2.2
    rw [if_neg hne, hlast] at hb
    exact hb.1

/-- The join needs strictness only if the replacement itself has a
proper epsilon prefix. A singleton final value needs the actual cover
and its >1 bound, exactly as in the printed original RAW conditions. -/
theorem tracking_append (before replacement : List Nat)
    (hr : SourceTrackingRaw.Reference before) (hne : before ≠ [])
    (ht : SourceTrackingRaw.trackingCheck replacement = true)
    (hpos : 1 < interpretation 0 (Insertion.firstCode replacement))
    (hc : interpretation 0 (Insertion.firstCode replacement) ≤
      SourceTrackingRaw.Support.muValue (lastCode before))
    (hlt : stripLast replacement ≠ [] →
      interpretation 0 (lastCode before) < interpretation 0 (Insertion.firstCode replacement)) :
    SourceTrackingRaw.trackingCheck (before ++ replacement) = true := by
  have hs := (SourceTrackingRaw.trackingCheck_exact replacement).mp ht
  cases replacement with
  | nil => exact False.elim (hs.1 rfl)
  | cons b rest =>
    cases rest with
    | nil =>
      have hf : Insertion.firstCode [b] = b := rfl
      apply (SourceTrackingRaw.trackingCheck_exact (before ++ [b])).mpr
      have hnonempty : before ++ [b] ≠ [] := by
        intro he
        exact List.cons_ne_nil b [] (List.append_eq_nil_iff.mp he).2
      refine ⟨hnonempty, ?_, ?_, ?_, ?_, ?_⟩
      · rw [stripLast_append_singleton]; exact hr
      · simpa only [lastCode_append_singleton, lastCode_singleton] using hs.2.2.1
      · simpa only [lastCode_append_singleton, lastCode_singleton] using hs.2.2.2.1
      · simpa only [lastCode_append_singleton, lastCode_singleton] using hs.2.2.2.2.1
      · rw [stripLast_append_singleton, if_neg hne, lastCode_append_singleton]
        exact ⟨by simpa only [hf] using hpos, by simpa only [hf] using hc⟩
    | cons c cs =>
      have hrest : c :: cs ≠ [] := List.cons_ne_nil _ _
      have hp : stripLast (b :: c :: cs) = b :: stripLast (c :: cs) :=
        stripLast_cons_nonempty b _ hrest
      have hpne : stripLast (b :: c :: cs) ≠ [] := by rw [hp]; exact List.cons_ne_nil _ _
      have hb : Insertion.firstCode (b :: c :: cs) = b := rfl
      have href := reference_append before b (stripLast (c :: cs)) hr
        (by rw [← hp]; exact hs.2.1) hne
        (by simpa only [hb] using hlt hpne) (by simpa only [hb] using hc)
      have hprefix : stripLast (before ++ b :: c :: cs) = before ++ stripLast (b :: c :: cs) :=
        stripLast_append_nonempty before _ (List.cons_ne_nil _ _)
      have hnewne : stripLast (before ++ b :: c :: cs) ≠ [] := by
        rw [hprefix]
        intro he
        exact hpne (List.append_eq_nil_iff.mp he).2
      have hlast := lastCode_append_nonempty before (b :: c :: cs) (List.cons_ne_nil _ _)
      apply (SourceTrackingRaw.trackingCheck_exact _).mpr
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro he
        exact List.cons_ne_nil b _ (List.append_eq_nil_iff.mp he).2
      · rw [hprefix, hp]; exact href
      · rw [hlast]; exact hs.2.2.1
      · rw [hlast]; exact hs.2.2.2.1
      · rw [hlast]; exact hs.2.2.2.2.1
      · rw [if_neg hnewne, hlast, hprefix, lastCode_append_nonempty before _ hpne]
        simpa only [if_neg hpne] using hs.2.2.2.2.2

/-- Every literal selected-prefix splice is an actual original RAW
tracker. A multi-entry replacement forces the genuinely raised branch,
which derives the original proper head and its strict prefix join. -/
theorem selected_tracking (factor : Nat) (heads : List Nat)
    (hh : SourceTrackingRaw.trackingCheck heads = true)
    (hf : lowCheckCode 0 factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor))
    (hb : interpretation 0 factor ≤ interpretation 0 (lastCode heads))
    (before : List Row) (current : Row) (after : List Row)
    (hbefore : before ≠ [])
    (hheads : heads = before.map Prod.fst ++ current.1 :: after.map Prod.fst)
    (ho : current.2 ∈ ConditionalReplacement.execute current.1 factor)
    (hc : Insertion.coverCheck (lastCode (before.map Prod.fst))
      (Insertion.firstCode current.2) = true) :
    SourceTrackingRaw.trackingCheck (before.map Prod.fst ++ current.2) = true := by
  have hbne : before.map Prod.fst ≠ [] := by
    intro he
    exact hbefore (List.map_eq_nil_iff.mp he)
  have hsource := (SourceTrackingRaw.trackingCheck_exact heads).mp hh
  have hprefix := hsource.2.1
  rw [hheads, stripLast_append_nonempty _ _ (List.cons_ne_nil _ _)] at hprefix
  have hreference := reference_prefix (before.map Prod.fst) _ hprefix
  have hpne : stripLast heads ≠ [] := by
    rw [hheads, stripLast_append_nonempty _ _ (List.cons_ne_nil _ _)]
    intro he
    exact hbne (List.append_eq_nil_iff.mp he).1
  have hmem : current.1 ∈ heads := by
    rw [hheads]
    exact List.mem_append_right _ List.mem_cons_self
  have hs := ConditionalReplacement.execute_spec heads hh current.1 factor hmem hf hm hb current.2 ho
  apply tracking_append (before.map Prod.fst) current.2 hreference hbne hs.2.2.1
  · exact (tracking_member_above_one heads hh hpne current.1 hmem).trans_le hs.2.2.2.1
  · exact ((Insertion.coverCheck_exact _ _).mp hc).2.2
  · intro hproper
    have hraised : interpretation 0 current.1 < interpretation 0 factor := by
      rcases hs.2.2.2.2 with ht | ⟨hle, d, he, hv⟩
      · exact ht.1
      · rw [he, stripLast_singleton] at hproper
        exact False.elim (hproper rfl)
    have hafter : after.map Prod.fst ≠ [] := by
      intro he
      have hehead : heads = before.map Prod.fst ++ [current.1] := by
        simpa only [he] using hheads
      have hbound : interpretation 0 factor ≤ interpretation 0 current.1 := by
        simpa only [hehead, lastCode_append_singleton] using hb
      exact hraised.not_ge hbound
    have hr := hsource.2.1
    rw [hheads, stripLast_append_nonempty _ _ (List.cons_ne_nil _ _),
      stripLast_cons_nonempty current.1 _ hafter] at hr
    have hwhole : SourceTrackingRaw.Reference (before.map Prod.fst ++ [current.1]) :=
      reference_prefix (before.map Prod.fst ++ [current.1]) (stripLast (after.map Prod.fst))
        (by simpa only [List.append_assoc, List.singleton_append] using hr)
    have hstrict : ((before.map Prod.fst).map (interpretation 0) ++
        [interpretation 0 current.1]).Pairwise (· < ·) := by
      simpa only [List.map_append, List.map_singleton] using hwhole.strict
    have hj := (List.pairwise_append.mp hstrict).2.2
      (interpretation 0 (lastCode (before.map Prod.fst)))
      (List.mem_map_of_mem (lastCode_mem _ hbne)) (interpretation 0 current.1)
      (List.mem_singleton_self _)
    exact hj.trans_le hs.2.2.2.1

/-- The executing greatest insertion has an actual original check-zero
RAW tracking image. All rows, branches, strictness and covering callers
are derived from execution and the original joint factor bound. -/
theorem execute_tracking (factor : Nat) (heads out : List Nat)
    (hh : SourceTrackingRaw.trackingCheck heads = true)
    (hf : lowCheckCode 0 factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor))
    (hb : interpretation 0 factor ≤ interpretation 0 (lastCode heads))
    (ho : out ∈ Insertion.execute (factor, heads)) :
    SourceTrackingRaw.trackingCheck out = true := by
  obtain ⟨rows, hr, hheads, hout, hchecked, hcases⟩ :=
    Insertion.execute_spec factor heads out hh hf hm hb ho
  have hrel := InsertionSupport.executeRows_relation factor heads rows hr
  rcases hcases with ⟨first, rest, hrows, he, hnone⟩ |
    ⟨before, current, after, hbefore, hrows, he, hcover, hnone⟩
  · have hmemb : first ∈ rows := by rw [hrows]; exact List.mem_cons_self
    have hc := InsertionSupport.relation_members factor hrel first hmemb
    have ht := ConditionalReplacement.execute_spec heads hh first.1 factor hc.1 hf hm hb first.2 hc.2
    rw [he]; exact ht.2.2.1
  · have hmemb : current ∈ rows := by rw [hrows]; exact List.mem_append_right _ List.mem_cons_self
    have hc := InsertionSupport.relation_members factor hrel current hmemb
    have hsource : heads = before.map Prod.fst ++ current.1 :: after.map Prod.fst := by
      rw [← hheads, hrows, List.map_append, List.map_cons]
    have ht := ConditionalReplacement.execute_spec heads hh current.1 factor hc.1 hf hm hb current.2 hc.2
    have hfirst : Insertion.firstCode current.2 ∈ current.2 := by
      cases hx : current.2 with
      | nil => exact False.elim (ht.1 hx)
      | cons a xs => simp only [Insertion.firstCode, hx, List.head?_cons, Option.getD_some]; exact List.mem_cons_self
    have hlow := ((Theta.acceptedLowCode_iff 0 _).mp (ht.2.1 _ hfirst)).1
    have hraw := (SourceTrackingRaw.trackingCheck_exact heads).mp hh
    have hpref := hraw.2.1
    rw [hsource, stripLast_append_nonempty _ _ (List.cons_ne_nil _ _)] at hpref
    have hbne : before.map Prod.fst ≠ [] := by
      intro hn
      exact hbefore (List.map_eq_nil_iff.mp hn)
    have hcraw := (reference_prefix _ _ hpref).nodes _ (lastCode_mem _ hbne)
    have hcoverCheck := (Insertion.coverCheck_exact _ _).mpr ⟨hcraw, hlow, hcover⟩
    rw [he]
    exact selected_tracking factor heads hh hf hm hb before current after hbefore hsource hc.2 hcoverCheck

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.InsertionFidelity
