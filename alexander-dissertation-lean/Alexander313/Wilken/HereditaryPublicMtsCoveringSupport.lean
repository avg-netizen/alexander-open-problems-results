import Alexander313.Wilken.HereditaryPublicMtsFirstSupport

/-!
# Independent covering and the actual chronological table

A covering begins at the admitted original public root and follows true
independently checked public-mu edges. It is not defined by mts output.
The finite table induction below isolates the two mathematical facts
needed at a marked target: an eligible earlier predecessor exists, and
each actually passing earlier predecessor is marked as well. The source
localization proof must derive both facts; neither is a final caller or
covering oracle. Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts.CoveringSupport

/-- A genuine chronological mu covering, with its actual final code. -/
inductive Covering (root : Nat) : Nat → List Nat → Prop
  | root (hr : MuPublicDictionary.Support.inputCheck root = true) :
      Covering root root [root]
  | append (previous current : Nat) (codes : List Nat)
      (hp : Covering root previous codes)
      (hc : PublicTrackingSequences.adjacencyCheck previous current = true) :
      Covering root current (codes ++ [current])

theorem Covering.nonempty {root current : Nat} {codes : List Nat}
    (hc : Covering root current codes) : codes ≠ [] := by
  cases hc with
  | root hr => exact List.cons_ne_nil _ _
  | append previous current codes hp hnext =>
    intro he
    have hm : current ∈ codes ++ [current] :=
      List.mem_append.mpr (Or.inr List.mem_cons_self)
    rw [he] at hm
    exact List.not_mem_nil hm

theorem Covering.last {root current : Nat} {codes : List Nat}
    (hc : Covering root current codes) :
    NativeContext.SourceTrackingSequences.lastCode codes = current := by
  cases hc with
  | root hr => exact NativeContext.SourceTrackingSequences.lastCode_singleton _
  | append previous current codes hp hnext =>
    exact NativeContext.SourceTrackingSequences.lastCode_append_singleton _ _

theorem Covering.first {root current : Nat} {codes : List Nat}
    (hc : Covering root current codes) : ∃ tail : List Nat, codes = root :: tail := by
  induction hc with
  | root hr => exact ⟨[], rfl⟩
  | append previous current codes hp hnext ih =>
    obtain ⟨tail, ht⟩ := ih
    exact ⟨tail ++ [current], by simp only [ht, List.cons_append]⟩

theorem select_exists (target : Nat) (es : List Support.Entry)
    (ha : ∃ a ∈ es.map Prod.fst, PublicTrackingSequences.adjacencyCheck a target = true) :
    ∃ e, Support.select target es = some e := by
  cases hs : Support.select target es with
  | some e => exact ⟨e, hs⟩
  | none =>
    obtain ⟨a, hm, he⟩ := ha
    obtain ⟨e, hm, hv⟩ := List.mem_map.mp hm
    have hf := (Support.select_none target es).mp hs e hm
    rw [hv] at hf
    exact False.elim (Bool.true_eq_false_eq_False (he.symm.trans hf))

/-- Marked entries of the real table are covered when genuine predecessor
existence and backwards preservation hold at its literal earlier rows.
These explicit pure-list premises are discharged by the source module. -/
theorem rows_covering {root : Nat} {inputs : List Nat} {es : List Support.Entry}
    (hr : Support.Rows root inputs es) (marked : Nat → Prop)
    (hg : MuPublicDictionary.Support.inputCheck root = true)
    (hroot : ∀ c ∈ inputs, c ≠ root)
    (hexists : ∀ before current after, inputs = before ++ current :: after → marked current →
      ∃ a ∈ root :: before, PublicTrackingSequences.adjacencyCheck a current = true)
    (hback : ∀ a ∈ root :: inputs, ∀ c ∈ inputs, marked c →
      PublicTrackingSequences.adjacencyCheck a c = true → a = root ∨ marked a) :
    ∀ e ∈ es, e.1 = root ∨ marked e.1 → Covering root e.1 e.2 := by
  revert hroot hexists hback
  induction hr with
  | initial =>
    intro hroot hexists hback e he hmarked
    have ht : e = (root, [root]) := List.mem_singleton.mp he
    subst e
    exact Covering.root hg
  | append inputs es current hr ih =>
    intro hroot hexists hback e he hmarked
    have hroot' : ∀ c ∈ inputs, c ≠ root :=
      fun c hc => hroot c (List.mem_append.mpr (Or.inl hc))
    have hexists' : ∀ before c after, inputs = before ++ c :: after → marked c →
        ∃ a ∈ root :: before, PublicTrackingSequences.adjacencyCheck a c = true := by
      intro before c after hs hm
      apply hexists before c (after ++ [current])
      · simp only [hs, List.append_assoc, List.cons_append]
      · exact hm
    have hback' : ∀ a ∈ root :: inputs, ∀ c ∈ inputs, marked c →
        PublicTrackingSequences.adjacencyCheck a c = true → a = root ∨ marked a := by
      intro a ha c hc hm hp
      have ha' : a ∈ root :: (inputs ++ [current]) := by
        rcases List.mem_cons.mp ha with ha | ha
        · exact List.mem_cons.mpr (Or.inl ha)
        · exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl ha)))
      exact hback a ha' c (List.mem_append.mpr (Or.inl hc)) hm hp
    have hprev := ih hroot' hexists' hback'
    rcases List.mem_append.mp he with he | he
    · exact hprev e he hmarked
    · have ht : e = (current, Support.extend root current es) := List.mem_singleton.mp he
      subst e
      have hm : marked current := hmarked.resolve_left
        (hroot current (List.mem_append.mpr (Or.inr List.mem_cons_self)))
      obtain ⟨a, ha, hadj⟩ := hexists inputs current [] rfl hm
      have hcodes : es.map Prod.fst = root :: inputs := by
        rw [hr.table_eq, Support.table_codes]
      obtain ⟨chosen, hs⟩ := select_exists current es ⟨a, by rw [hcodes]; exact ha, hadj⟩
      have hchosen := Support.select_mem current es chosen hs
      obtain ⟨chosenBefore, chosenAfter, hsplit, hfailed, hadj'⟩ :=
        Support.select_first current es chosen hs
      have hmember : chosen.1 ∈ root :: (inputs ++ [current]) := by
        have hc : chosen.1 ∈ root :: inputs := by
          rw [← hcodes]
          exact List.mem_map.mpr ⟨chosen, hchosen, rfl⟩
        rcases List.mem_cons.mp hc with hc | hc
        · exact List.mem_cons.mpr (Or.inl hc)
        · exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl hc)))
      have hmarked' := hback chosen.1 hmember current
        (List.mem_append.mpr (Or.inr List.mem_cons_self)) hm hadj'
      have hcover := Covering.append chosen.1 current chosen.2
        (hprev chosen hchosen hmarked') hadj'
      simpa only [Support.extend_some root current es chosen hs] using hcover

theorem table_covering (root : Nat) (inputs : List Nat) (marked : Nat → Prop)
    (hg : MuPublicDictionary.Support.inputCheck root = true)
    (hroot : ∀ c ∈ inputs, c ≠ root)
    (hexists : ∀ before current after, inputs = before ++ current :: after → marked current →
      ∃ a ∈ root :: before, PublicTrackingSequences.adjacencyCheck a current = true)
    (hback : ∀ a ∈ root :: inputs, ∀ c ∈ inputs, marked c →
      PublicTrackingSequences.adjacencyCheck a c = true → a = root ∨ marked a) :
    ∀ e ∈ Support.table root inputs, e.1 = root ∨ marked e.1 → Covering root e.1 e.2 :=
  rows_covering (Support.table_rows root inputs) marked hg hroot hexists hback

theorem word_covering_append (root current : Nat) (before : List Nat) (marked : Nat → Prop)
    (hg : MuPublicDictionary.Support.inputCheck root = true)
    (hroot : ∀ c ∈ before ++ [current], c ≠ root)
    (hexists : ∀ xs c ys, before ++ [current] = xs ++ c :: ys → marked c →
      ∃ a ∈ root :: xs, PublicTrackingSequences.adjacencyCheck a c = true)
    (hback : ∀ a ∈ root :: (before ++ [current]), ∀ c ∈ before ++ [current], marked c →
      PublicTrackingSequences.adjacencyCheck a c = true → a = root ∨ marked a)
    (hm : marked current) :
    Covering root current (Support.word root (before ++ [current])) := by
  have hr := table_covering root (before ++ [current]) marked hg hroot hexists hback
    (current, Support.extend root current (Support.table root before))
    (by rw [Support.table_append_singleton]; exact List.mem_append.mpr (Or.inr List.mem_cons_self))
    (Or.inr hm)
  simpa only [Support.word_append] using hr

end Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts.CoveringSupport
