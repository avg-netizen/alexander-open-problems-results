import Alexander313.Wilken.SourceOneNativeAdditiveTrackingAssignment
import Alexander313.Wilken.SourceOneNativeMultiplicativeTrackingRawRecurrence

/-!
# Independent assignment at every multiplicative output prefix

The actual finite covered table retains its earlier words. A purely written
prefix of any stored word is itself an actual earlier stored word. Genuine
localization VALUE-prefix locality identifies that record with the independently
computed word at its endpoint. Original HIGH callers derive actual M callers,
so the same full additive assignment executes there. Only ordinal-value words
are identified. Original source zero is retained; no Native base-one parser,
written path equality or localization-subsequence clause is used.
Source-only uncompiled candidate.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.MultiplicativePrefix

open NativeContext.SourceTrackingSequences
open SourceMultiplicativeTracking SourceMultiplicativeTracking.Support SourceMultiplicativeTracking.Prefix

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
theorem buildRev_prefix_record (xs : List Nat) (e : Entry)
    (hm : e ∈ buildRev xs) (before after : List Nat) (d : Nat)
    (he : e.2 = before ++ d :: after) :
    ∃ f ∈ buildRev xs, f.1 = d ∧ f.2 = before ++ [d] := by
  induction xs generalizing e before after d with
  | nil => exact False.elim (List.not_mem_nil hm)
  | cons current rest ih =>
    change e ∈ (current, extend current (buildRev rest)) :: buildRev rest at hm
    rcases List.mem_cons.mp hm with hnew | hold
    · subst e
      cases hs : select current (buildRev rest) with
      | none =>
        have he : [] ++ [current] = before ++ d :: after := by
          simpa only [extend, hs] using he
        rcases append_singleton_position [] before after current d he with ⟨hb, hd, ha⟩ | ⟨tail, ht⟩
        · refine ⟨(current, extend current (buildRev rest)), List.mem_cons_self, hd.symm, ?_⟩
          simp only [extend, hs, hb, hd, List.nil_append]
        · simp only [List.nil_eq_append_iff, List.cons_ne_nil, and_false] at ht
      | some a =>
        have he : a.2 ++ [current] = before ++ d :: after := by
          simpa only [extend, hs] using he
        rcases append_singleton_position a.2 before after current d he with ⟨hb, hd, ha⟩ | ⟨tail, ht⟩
        · refine ⟨(current, extend current (buildRev rest)), List.mem_cons_self, hd.symm, ?_⟩
          simp only [extend, hs, hb, hd]
        · obtain ⟨f, hf, hv, hw⟩ := ih a (select_mem current _ a hs) before tail d ht
          exact ⟨f, List.mem_cons_of_mem _ hf, hv, hw⟩
    · obtain ⟨f, hf, hv, hw⟩ := ih e hold before after d he
      exact ⟨f, List.mem_cons_of_mem _ hf, hv, hw⟩

/-- The actual table record supplies a real original HIGH/M endpoint.
Its independent localization word has exactly the stored prefix values. -/
theorem table_prefix_values (root : Nat) (hi : Localization.inputCheck 0 root = true)
    (e : Entry) (hm : e ∈ table (properPrefix root))
    (before after : List Nat) (d : Nat) (he : e.2 = before ++ d :: after) :
    SourceMultiplicativePrincipal.inputCheck d = true ∧
      (rawWord d).map (interpretation 0) = (before ++ [d]).map (interpretation 0) := by
  obtain ⟨f, hf, hfd, hfw⟩ := buildRev_prefix_record (properPrefix root).reverse e hm before after d he
  have hd : d ∈ properPrefix root := by
    rw [← hfd]
    exact List.mem_reverse.mp (buildRev_code_mem _ f hf)
  have hhigh := properPrefix_high root hi d hd
  have heps := root_epsilon d hhigh
  have hprincipal : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 d) := by
    apply (MultiplicativePrincipalArithmetic.multiplicativePrincipal_iff _).mpr
    refine Or.inr ⟨interpretation 0 d, ?_⟩
    calc
      interpretation 0 d = Ordinal.omega0 ^ interpretation 0 d := heps.symm
      _ = Ordinal.omega0 ^ (Ordinal.omega0 ^ interpretation 0 d) :=
        congrArg (fun v : Ordinal.{0} => Ordinal.omega0 ^ v) heps.symm
  have hmul := (SourceMultiplicativePrincipal.inputCheck_exact d).mpr
    ⟨root_low d hhigh, (EpsilonOffsets.epsilon_one_lt heps).le, hprincipal⟩
  obtain ⟨a, hshape, hchecked, hnormal, _⟩ := (rootCheck_exact d).mp hhigh
  have hn : Localization.inputCheck 0 d = true :=
    (Localization.inputCheck_exact 0 d).mpr ⟨a, hshape, hchecked, hnormal⟩
  have hw := SourceMultiplicativeTracking.RecurrenceSupport.table_entry_word root hi f hf
  have hr := SourceMultiplicativeTracking.RawRecurrence.rawWord_values_word d hn
  refine ⟨hmul, ?_⟩
  calc
    (rawWord d).map (interpretation 0) = (word d).map (interpretation 0) := hr
    _ = f.2.map (interpretation 0) := by simpa only [hfd] using hw.symm
    _ = (before ++ [d]).map (interpretation 0) := congrArg (List.map (interpretation 0)) hfw

/-- Every nonempty written prefix of the actual original M word agrees with an
independent execution of the SAME full additive procedure at its endpoint. -/
theorem rawWord_prefix (current : Nat)
    (hm : SourceMultiplicativePrincipal.inputCheck current = true)
    (before after : List Nat) (d : Nat)
    (he : rawWord current = before ++ d :: after) :
    SourceMultiplicativePrincipal.inputCheck d = true ∧
      ∃ out, out ∈ Assignment.execute d ∧
        out.map (interpretation 0) = (before ++ [d]).map (interpretation 0) := by
  cases hs : select current
      (table (properPrefix (SourceLocalization.RootAdapter.rootCode current))) with
  | none =>
    have hh : [] ++ [current] = before ++ d :: after := by
      simpa only [rawWord, extend, hs] using he
    rcases append_singleton_position [] before after current d hh with ⟨hb, hd, ha⟩ | ⟨tail, ht⟩
    · subst d
      refine ⟨hm, rawWord current, Assignment.execute_multiplicative current hm, ?_⟩
      simp only [rawWord, extend, hs, hb, List.nil_append]
    · simp only [List.nil_eq_append_iff, List.cons_ne_nil, and_false] at ht
  | some e =>
    have hh : e.2 ++ [current] = before ++ d :: after := by
      simpa only [rawWord, extend, hs] using he
    rcases append_singleton_position e.2 before after current d hh with ⟨hb, hd, ha⟩ | ⟨tail, ht⟩
    · subst d
      refine ⟨hm, rawWord current, Assignment.execute_multiplicative current hm, ?_⟩
      simp only [rawWord, extend, hs, hb]
    · have hv := table_prefix_values (SourceLocalization.RootAdapter.rootCode current)
        (SourceMultiplicativePrincipal.rootInput current hm) e
        (select_mem current _ e hs) before tail d ht
      exact ⟨hv.1, rawWord d, Assignment.execute_multiplicative d hv.1, hv.2⟩

/-- The final code is the original M input and every earlier prefix has
an independently computed full assignment with exactly its original values.
This is the complete original-source-one3.21.1 prefix statement. -/
theorem execute_multiplicative_prefix (current : Nat) (out : List Nat)
    (hm : SourceMultiplicativePrincipal.inputCheck current = true)
    (ho : out ∈ Assignment.execute current) :
    lastCode out = current ∧ ∀ before d after, out = before ++ d :: after →
      SourceMultiplicativePrincipal.inputCheck d = true ∧
        ∃ prefixOut, prefixOut ∈ Assignment.execute d ∧
          prefixOut.map (interpretation 0) = (before ++ [d]).map (interpretation 0) := by
  have hh : out = rawWord current :=
    Part.mem_unique ho (Assignment.execute_multiplicative current hm)
  rw [hh]
  exact ⟨rawWord_last current, fun before d after he => rawWord_prefix current hm before after d he⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.MultiplicativePrefix
