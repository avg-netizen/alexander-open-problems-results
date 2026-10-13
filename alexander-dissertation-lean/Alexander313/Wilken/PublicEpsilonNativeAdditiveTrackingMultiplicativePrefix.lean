import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingAssignment
import Alexander313.Wilken.PublicEpsilonNativeMultiplicativeTrackingRawRecurrence

/-!
# Independent assignment at every multiplicative output prefix

The actual finite covered table retains its earlier words. A purely written
prefix of any stored word is itself an actual earlier stored word. Genuine
localization VALUE-prefix locality identifies that record with the independently
computed word at its endpoint. Original HIGH callers derive actual M callers,
so the same full additive assignment executes there. Only ordinal-value words
are identified; no written path equality or localization-subsequence clause.
Source-only uncompiled candidate.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.MultiplicativePrefix

open PublicEpsilonUnboundedIota SourceTrackingSequences
open SourceMultiplicativeTracking SourceMultiplicativeTracking.Support

/-- A written position before the newly appended last entry already
belongs to the unchanged earlier word. -/
theorem append_singleton_position (xs before after : List Nat) (last d : Nat)
    (he : xs ++ [last] = before ++ d :: after) :
    (before = xs ∧ d = last ∧ after = []) ∨ ∃ rest, xs = before ++ d :: rest := by
  induction xs generalizing before with
  | nil =>
    cases before with
    | nil =>
      have hs := List.cons.inj (by simpa only [List.nil_append] using he)
      exact Or.inl ⟨rfl, hs.1.symm, hs.2.symm⟩
    | cons b before =>
      have hs := List.cons.inj (by simpa only [List.nil_append, List.cons_append] using he)
      have hn := hs.2
      simp only [List.nil_eq_append_iff, List.cons_ne_nil, and_false] at hn
  | cons a xs ih =>
    cases before with
    | nil =>
      have hs := List.cons.inj (by simpa only [List.cons_append, List.nil_append] using he)
      exact Or.inr ⟨xs, by simpa only [List.nil_append] using
        congrArg (fun x : Nat => x :: xs) hs.1⟩
    | cons b before =>
      have hs := List.cons.inj (by simpa only [List.cons_append] using he)
      rcases ih before hs.2 with ⟨hb, hd, ha⟩ | ⟨rest, hr⟩
      · exact Or.inl ⟨by simp only [hb, hs.1], hd, ha⟩
      · exact Or.inr ⟨rest, by simp only [List.cons_append, hr, hs.1]⟩

/-- Every nonempty written prefix of a stored table word is an actual
stored word in that same finite table, without an admission assumption. -/
theorem buildRev_prefix_record (q : Nat) (xs : List Nat) (e : Entry)
    (hm : e ∈ buildRev q xs) (before after : List Nat) (d : Nat)
    (he : e.2 = before ++ d :: after) :
    ∃ f ∈ buildRev q xs, f.1 = d ∧ f.2 = before ++ [d] := by
  induction xs generalizing e before after d with
  | nil => exact False.elim (List.not_mem_nil hm)
  | cons current rest ih =>
    change e ∈ (current, extend q current (buildRev q rest)) :: buildRev q rest at hm
    rcases List.mem_cons.mp hm with hnew | hold
    · subst e
      cases hs : select q current (buildRev q rest) with
      | none =>
        have he : [] ++ [current] = before ++ d :: after := by
          simpa only [extend, hs] using he
        rcases append_singleton_position [] before after current d he with ⟨hb, hd, ha⟩ | ⟨tail, ht⟩
        · refine ⟨(current, extend q current (buildRev q rest)), List.mem_cons_self, hd.symm, ?_⟩
          simp only [extend, hs, hb, hd, List.nil_append]
        · simp only [List.nil_eq_append_iff, List.cons_ne_nil, and_false] at ht
      | some a =>
        have he : a.2 ++ [current] = before ++ d :: after := by
          simpa only [extend, hs] using he
        rcases append_singleton_position a.2 before after current d he with ⟨hb, hd, ha⟩ | ⟨tail, ht⟩
        · refine ⟨(current, extend q current (buildRev q rest)), List.mem_cons_self, hd.symm, ?_⟩
          simp only [extend, hs, hb, hd]
        · obtain ⟨f, hf, hv, hw⟩ := ih a (select_mem q current _ a hs) before tail d ht
          exact ⟨f, List.mem_cons_of_mem _ hf, hv, hw⟩
    · obtain ⟨f, hf, hv, hw⟩ := ih e hold before after d he
      exact ⟨f, List.mem_cons_of_mem _ hf, hv, hw⟩

/-- The actual table record supplies a real original HIGH/M endpoint.
Its independent localization word has exactly the stored prefix values. -/
theorem table_prefix_values (q root : Nat) (hi : SourceLocalization.inputCheck q root = true)
    (e : Entry) (hm : e ∈ table q (properPrefix q root))
    (before after : List Nat) (d : Nat) (he : e.2 = before ++ d :: after) :
    SourceMultiplicativePrincipal.inputCheck q d = true ∧
      (rawWord q d).map (interpretation q) = (before ++ [d]).map (interpretation q) := by
  obtain ⟨f, hf, hfd, hfw⟩ := buildRev_prefix_record q (properPrefix q root).reverse e hm before after d he
  have hd : d ∈ properPrefix q root := by
    rw [← hfd]
    exact List.mem_reverse.mp (buildRev_code_mem q _ f hf)
  have hhigh := properPrefix_roots q root hi d hd
  have hmul := (SourceMultiplicativePrincipal.inputCheck_exact q d).mpr
    ⟨RootLowCollapse.root_low q d hhigh, (Mu.root_base_lt q d hhigh).le,
      SourceMultiplicativePrincipal.epsilon_multiplicative _ (RootLowCollapse.root_epsilon q d hhigh)⟩
  obtain ⟨a, hshape, hchecked, hnormal, _⟩ := (RootLowCollapse.rootCheck_exact q d).mp hhigh
  have hn : SourceLocalization.inputCheck q d = true :=
    (SourceLocalization.inputCheck_exact q d).mpr ⟨a, hshape, hchecked, hnormal⟩
  have hw := SourceMultiplicativeTracking.RecurrenceSupport.table_entry_word q root hi f hf
  have hr := SourceMultiplicativeTracking.RawRecurrence.rawWord_values_word q d hn
  refine ⟨hmul, ?_⟩
  calc
    (rawWord q d).map (interpretation q) = (word q d).map (interpretation q) := hr
    _ = f.2.map (interpretation q) := by simpa only [hfd] using hw.symm
    _ = (before ++ [d]).map (interpretation q) := congrArg (List.map (interpretation q)) hfw

/-- Every nonempty written prefix of the actual M word agrees with an
independent execution of the SAME full additive procedure at its endpoint. -/
theorem rawWord_prefix (q current : Nat)
    (hm : SourceMultiplicativePrincipal.inputCheck q current = true)
    (before after : List Nat) (d : Nat)
    (he : rawWord q current = before ++ d :: after) :
    SourceMultiplicativePrincipal.inputCheck q d = true ∧
      ∃ out, out ∈ Assignment.execute q d ∧
        out.map (interpretation q) = (before ++ [d]).map (interpretation q) := by
  cases hs : select q current
      (table q (properPrefix q (SourceLocalization.RootAdapter.rootCode q current))) with
  | none =>
    have hh : [] ++ [current] = before ++ d :: after := by
      simpa only [rawWord, extend, hs] using he
    rcases append_singleton_position [] before after current d hh with ⟨hb, hd, ha⟩ | ⟨tail, ht⟩
    · subst d
      refine ⟨hm, rawWord q current, Assignment.execute_multiplicative q current hm, ?_⟩
      simp only [rawWord, extend, hs, hb, List.nil_append]
    · simp only [List.nil_eq_append_iff, List.cons_ne_nil, and_false] at ht
  | some e =>
    have hh : e.2 ++ [current] = before ++ d :: after := by
      simpa only [rawWord, extend, hs] using he
    rcases append_singleton_position e.2 before after current d hh with ⟨hb, hd, ha⟩ | ⟨tail, ht⟩
    · subst d
      refine ⟨hm, rawWord q current, Assignment.execute_multiplicative q current hm, ?_⟩
      simp only [rawWord, extend, hs, hb]
    · have hv := table_prefix_values q (SourceLocalization.RootAdapter.rootCode q current)
        (SourceMultiplicativePrincipal.rootInput q current hm) e
        (select_mem q current _ e hs) before tail d ht
      exact ⟨hv.1, rawWord q d, Assignment.execute_multiplicative q d hv.1, hv.2⟩

/-- The final code is the original M input and every earlier prefix has
an independently computed full assignment with exactly its original values.
This is the complete native source3.21.1 prefix statement. -/
theorem execute_multiplicative_prefix (q current : Nat) (out : List Nat)
    (hm : SourceMultiplicativePrincipal.inputCheck q current = true)
    (ho : out ∈ Assignment.execute q current) :
    lastCode out = current ∧ ∀ before d after, out = before ++ d :: after →
      SourceMultiplicativePrincipal.inputCheck q d = true ∧
        ∃ prefixOut, prefixOut ∈ Assignment.execute q d ∧
          prefixOut.map (interpretation q) = (before ++ [d]).map (interpretation q) := by
  have hh : out = rawWord q current :=
    Part.mem_unique ho (Assignment.execute_multiplicative q current hm)
  rw [hh]
  exact ⟨rawWord_last q current, fun before d after he => rawWord_prefix q current hm before after d he⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.MultiplicativePrefix
