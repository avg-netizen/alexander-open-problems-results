import Alexander313.Wilken.HereditaryFineLocalizationRefinementsSupport

/-!
# Ordinary localization is a subsequence of actual fine localization

The first branch transfers the old selected prefix to the new node's actual
support. Membership follows from literal ANF support retention and the genuine
theta comparison witness; maximality follows from the real high-part barrier.
The fallback uses the already proved endpoint-prefix theorem. Combining these
two constructed branches with FinePath proves the source 2.39 subsequence on
the original weak-normal public domain. Canonical emission compares actual
values without assuming uniqueness of native spellings. The base endpoint is
handled separately; the unqualified printed 2.37 star-equality clause and the
2.35/2.40 lexicographic equivalences are not asserted. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.FineLocalization.Refinements

open Theta Theta.Normalization Localization Localization.Refinements FinePredecessor

private theorem stripLast_append_one {alpha : Type} (xs : List alpha) (a : alpha) :
    stripLast (xs ++ [a]) = xs := by
  simp only [stripLast, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append, List.tail_cons, List.reverse_reverse]

private theorem stripLast_cons_cons (c d : Nat) (tail : List Nat) :
    stripLast (c :: d :: tail) = c :: stripLast (d :: tail) := by
  obtain ⟨pre, he⟩ := endpoint_decomposition d tail
  rw [he]
  change stripLast ((c :: pre) ++ [_]) = c :: stripLast (pre ++ [_])
  rw [stripLast_append_one, stripLast_append_one]

/-- An old maximally selected node below the new prefix is witnessed in its
actual support, even if the witness has a different native spelling. -/
theorem selected_value_in_prefix_support (r root d : Nat) (hr : Node r root)
    (hf : FirstCase r root) (hd : Node r d)
    (hm : ∀ e ∈ support root, value r d ≤ value r e → argumentValue r e ≤ argumentValue r d)
    (hdb : value r d ≤ value r (prefixNode r root))
    (ha : argumentValue r (prefixNode r root) ≤ argumentValue r d) :
    ∃ e ∈ support (prefixNode r root), value r e = value r d := by
  have hb := prefix_node r root hr hf.1
  by_cases he : value r d = value r (prefixNode r root)
  · exact ⟨prefixNode r root, support_root r _ hb, he.symm⟩
  · obtain ⟨s, hs, hds⟩ := reversed_argument_witness r d (prefixNode r root) hd hb
      (lt_of_le_of_ne hdb he) ha
    have hsp : s ∈ RelativeTerm.PrincipalSupport.principalList 0 (prefixArgument r root) := by
      simpa only [prefixNode, argumentCode_theta, ThetaCourse.rawTree_code] using hs
    have hso := prefix_argument_support_subset r root hr s hsp
    have hsr := (nested_support_size r root hr s hso).1
    have hdsCode : value r d ≤ value r s.code := by
      simpa only [value, interpretation_code] using hds
    obtain ⟨e, he, hev⟩ := selected_value_in_support r root d hr hd hm s.code hsr hdsCode
    exact ⟨e, support_trans r _ s.code e hb
      (nested_support_size r _ hb s hs).1 he, hev⟩

/-- At the final old selection, no nested candidate can outrank the new
prefix's argument: that would force a strictly larger divided high part. -/
theorem prefix_final_maximal (r root previous : Nat) (hr : Node r root)
    (hf : FirstCase r root)
    (hm : ∀ e ∈ support root, value r previous < value r e →
      argumentValue r e ≤ argumentValue r root)
    (e : Nat) (he : e ∈ support (prefixNode r root))
    (hpe : value r previous < value r e) :
    argumentValue r e ≤ argumentValue r (prefixNode r root) := by
  have hb := prefix_node r root hr hf.1
  have hen := support_node r _ e hb he
  have heb := support_bound r _ e hb he
  by_cases heq : value r e = value r (prefixNode r root)
  · exact ((node_value_eq_iff_argument_eq r e _ hen hb).mp heq).le
  · have helt := lt_of_le_of_ne heb heq
    have hes : e ∈ support root := by
      rcases prefix_support_cases r root e hr hf.1 he with h | h
      · exact False.elim (heq (by rw [h]))
      · exact h
    have ha := hm e hes hpe
    by_contra hnot
    have harg : argumentValue r (prefixNode r root) ≤ argumentValue r e :=
      (lt_of_not_ge hnot).le
    have hl := SourceHighPartComparison.node_level_lt r e _ hen hb helt harg
    have hle : SourceHighPartComparison.localizationLevel r e ≤
        SourceHighPartComparison.localizationLevel r root :=
      SourceHighPartComparison.highPart_mono (omegaSequence (finiteBase r) 1) ha
    rw [prefix_level_eq r root hr hf.1] at hl
    exact hl.not_ge hle

/-- The selected old prefix, with its root removed, embeds into a genuine
value-membership localization of the constructed first-branch predecessor. -/
theorem first_prefix_valuePath (r root head : Nat) (tail : List Nat)
    (hr : Node r root) (hf : FirstCase r root)
    (hp : SourcePath r (support root) (head :: tail))
    (hend : value r (endpoint (head :: tail)) = value r root)
    (hstart : value r head ≤ value r (prefixNode r root)) :
    ∃ rest, ValuePath r (support (prefixNode r root)) (head :: rest) ∧
      (stripLast (head :: tail)).Sublist (head :: rest) := by
  have hb := prefix_node r root hr hf.1
  have hbr := prefix_strict r root hr hf.1
  have hab := prefix_argument_lt r root hr hf.1
  revert hend hstart
  induction hp with
  | stop c hc hmax =>
    intro hend hstart
    exact False.elim (hbr.not_ge (by simpa only [endpoint, hend] using hstart))
  | next c d tail hc hcd hds harg hrest ih =>
    intro hend hstart
    have hd := hrest.nodes d List.mem_cons_self
    have hdroot := support_bound r root d hr hds
    have hcroot : value r c < value r root := hcd.trans_le hdroot
    have hrootarg : argumentValue r root ≤ argumentValue r d :=
      harg root (support_root r root hr) hcroot
    have hbararg : argumentValue r (prefixNode r root) ≤ argumentValue r d :=
      hab.le.trans hrootarg
    by_cases hdEq : value r d = value r root
    · have htail : tail = [] := by
        cases hrest with
        | stop d hd hmax => rfl
        | next d e tail hd hde hes hearg hepath =>
          exact False.elim (hde.not_ge (by rw [hdEq]; exact support_bound r root e hr hes))
      subst tail
      have hda := (node_value_eq_iff_argument_eq r d root hd hr).mp hdEq
      have hmax : ∀ e ∈ support root, value r c < value r e →
          argumentValue r e ≤ argumentValue r root := by
        intro e he hce
        exact (harg e he hce).trans_eq hda
      by_cases hcEq : value r c = value r (prefixNode r root)
      · refine ⟨[], ValuePath.stop c hc (fun e he =>
          (support_bound r _ e hb he).trans_eq hcEq.symm), ?_⟩
        simpa only [stripLast_cons_cons, stripLast, List.reverse_cons, List.reverse_nil,
          List.tail_cons, List.reverse_nil] using (List.Sublist.refl [c])
      · have hcb := lt_of_le_of_ne hstart hcEq
        refine ⟨[prefixNode r root], ValuePath.next c _ [] hc hcb
          ⟨_, support_root r _ hb, rfl⟩
          (prefix_final_maximal r root c hr hf hmax)
          (ValuePath.stop _ hb (fun e he => support_bound r _ e hb he)), ?_⟩
        simpa only [stripLast_cons_cons, stripLast, List.reverse_cons, List.reverse_nil,
          List.tail_cons, List.reverse_nil] using
            (List.sublist_append_left [c] [prefixNode r root])
    · have hdb : value r d ≤ value r (prefixNode r root) :=
        first_support_below_root r root d hr hf hds (lt_of_le_of_ne hdroot hdEq)
      have hm : ∀ e ∈ support root, value r d ≤ value r e →
          argumentValue r e ≤ argumentValue r d :=
        fun e he hde => harg e he (hcd.trans_le hde)
      have hdnew := selected_value_in_prefix_support r root d hr hf hd hm hdb hbararg
      have hargnew : ∀ e ∈ support (prefixNode r root), value r c < value r e →
          argumentValue r e ≤ argumentValue r d := by
        intro e he hce
        rcases prefix_support_cases r root e hr hf.1 he with h | h
        · rw [h]; exact hbararg
        · exact harg e h hce
      obtain ⟨rest, hpath, hsub⟩ := ih (by simpa only [endpoint] using hend) hdb
      refine ⟨d :: rest, ValuePath.next c d rest hc hcd hdnew hargnew hpath, ?_⟩
      rw [stripLast_cons_cons]
      exact hsub.cons_cons c

theorem first_localization_prefix (r root : Nat) (hr : Node r root) (hf : FirstCase r root) :
    ((stripLast (nativePath r root)).map (emit r)).Sublist (Localization.word r (prefixNode r root)) := by
  have hi := (Localization.inputCheck_exact r root).mpr hr
  have hb := prefix_node r root hr hf.1
  have hbi := (Localization.inputCheck_exact r _).mpr hb
  obtain ⟨tail, hhead⟩ := nativePath_head r root
  have hp := nativePath_source r root hi
  have hend := nativePath_end r root hi
  have hstart : value r (baseRaw r) ≤ value r (prefixNode r root) := baseRaw_le r _ hb
  rw [hhead] at hp hend ⊢
  obtain ⟨rest, hnew, hsub⟩ := first_prefix_valuePath r root (baseRaw r) tail hr hf hp hend hstart
  obtain ⟨btail, hbhead⟩ := nativePath_head r (prefixNode r root)
  have hbp := nativePath_source r _ hbi
  rw [hbhead] at hbp
  have hv := hnew.values_unique (fun e he => support_node r _ e hb he)
    (baseRaw r) btail (sourcePath_valuePath hbp) rfl
  have he := emit_map_eq_of_values_eq r _ _ hnew.nodes hbp.nodes hv
  have hs := hsub.map (emit r)
  rw [he] at hs
  simpa only [Localization.word, hbhead] using hs

private theorem last_two (xs : List Nat) (h : 2 ≤ xs.length) : ∃ pre a b, xs = pre ++ [a, b] := by
  cases he : xs.reverse with
  | nil => have hl := congrArg List.length he; simp at hl; omega
  | cons b bs =>
    cases hs : bs with
    | nil => have hl := congrArg List.length he; simp only [List.length_reverse, hs,
        List.length_cons, List.length_nil] at hl; omega
    | cons a pre =>
      refine ⟨pre.reverse, a, b, ?_⟩
      have hr := congrArg List.reverse he
      simpa only [List.reverse_reverse, hs, List.reverse_cons, List.reverse_nil,
        List.append_assoc, List.singleton_append] using hr

theorem fallback_localization_prefix (r root : Nat) (hr : Node r root)
    (hproper : finiteBase r < value r root) :
    (stripLast (nativePath r root)).map (emit r) = Localization.word r (fallback r root) := by
  have hi := (Localization.inputCheck_exact r root).mpr hr
  obtain ⟨pre, a, b, he⟩ := last_two _ (localization_length r root hr hproper)
  have hf : fallback r root = a := by simp only [fallback, penultimate, he,
    List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
  have hp := word_prefix r root hi pre a [b] (by simpa only [List.singleton_append] using he)
  rw [he, hf]
  have hsplit : pre ++ [a, b] = (pre ++ [a]) ++ [b] := by
    simp only [List.append_assoc, List.singleton_append]
  rw [hsplit, stripLast_append_one]
  exact hp

/-- The real one-step dependency needed by source Lemma 2.39. -/
theorem predecessor_localization_prefix (r root : Nat)
    (hi : FinePredecessor.inputCheck r root = true) :
    ((stripLast (nativePath r root)).map (emit r)).Sublist
      (Localization.word r (predecessorCode r root)) := by
  have hr := (FinePredecessor.inputCheck_exact r root).mp hi
  rcases predecessor_branches r root hi with ⟨hf, he⟩ | ⟨hf, he⟩
  · rw [he]; exact first_localization_prefix r root hr.1 hf
  · rw [he, ← fallback_localization_prefix r root hr.1 hr.2]
    exact List.Sublist.refl _

theorem localization_word_split (r c : Nat) (hc : Node r c) :
    Localization.word r c = (stripLast (nativePath r c)).map (emit r) ++ [emit r c] := by
  have hi := (Localization.inputCheck_exact r c).mpr hc
  obtain ⟨tail, hh⟩ := nativePath_head r c
  obtain ⟨pre, he⟩ := endpoint_decomposition (baseRaw r) tail
  have hs : nativePath r c = pre ++ [endpoint (nativePath r c)] := by rw [hh]; exact he
  have hn := (nativePath_source r c hi).end_max.1
  have hv := nativePath_end r c hi
  have hem := emit_eq_of_value_eq r _ c hn hc hv
  rw [Localization.word, hs, stripLast_append_one, List.map_append,
    List.map_cons, List.map_nil, hem]

theorem base_localization_word (r c : Nat) (hc : Node r c) (hv : value r c = finiteBase r) :
    Localization.word r c = [emit r c] := by
  have hi := (Localization.inputCheck_exact r c).mpr hc
  obtain ⟨tail, hh⟩ := nativePath_head r c
  have hp := nativePath_source r c hi
  rw [hh] at hp
  have hs : SourcePath r (support c) [baseRaw r] := SourcePath.stop _ (baseRaw_node r)
    (fun e he => by rw [baseRaw_value]; exact (support_bound r c e hc he).trans_eq hv)
  have he := (sourcePath_valuePath hp).values_unique (fun e he => support_node r c e hc he)
    (baseRaw r) [] (sourcePath_valuePath hs) rfl
  have hem := emit_map_eq_of_values_eq r _ _ hp.nodes hs.nodes he
  have hbc := emit_eq_of_value_eq r _ c (baseRaw_node r) hc (by rw [baseRaw_value, hv])
  simpa only [Localization.word, hh, List.map_cons, List.map_nil, hbc] using hem

/-- Literal source 2.39 at actual canonical emission, for every original
weak-normal public FinePath. No global primitive-recursive length is assumed. -/
theorem FinePath.localization_sublist {r c : Nat} {path : List Nat}
    (hp : FinePath r c path) : (Localization.word r c).Sublist (path.map (emit r)) := by
  induction hp with
  | base c hc hv =>
    rw [base_localization_word r c hc hv]
    exact List.Sublist.refl _
  | next c hc path hp ih =>
    have hn := (FinePredecessor.inputCheck_exact r c).mp hc |>.1
    rw [localization_word_split r c hn, List.map_append, List.map_cons, List.map_nil]
    exact List.Sublist.append ((predecessor_localization_prefix r c hc).trans ih)
      (List.Sublist.refl [emit r c])

private theorem emit_values (r : Nat) (xs : List Nat) (hx : ∀ c ∈ xs, Node r c) :
    (xs.map (emit r)).map unionInterpretation = xs.map (value r) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro c hc
  exact (emit_spec r c (hx c hc)).2

/-- The same source subsequence on the actual ordinal values. -/
theorem FinePath.localization_values_sublist {r c : Nat} {path : List Nat}
    (hp : FinePath r c path) :
    ((nativePath r c).map (value r)).Sublist (path.map (value r)) := by
  have hc := hp.nodes c (by obtain ⟨pre, he⟩ := hp.end; rw [he]; simp)
  have hi := (Localization.inputCheck_exact r c).mpr hc
  have hs := (FinePath.localization_sublist hp).map unionInterpretation
  simpa only [Localization.word, emit_values r _ (nativePath_nodes r c hi),
    emit_values r _ hp.nodes] using hs

theorem fineLocalization_localization_sublist (r c output : Nat)
    (ho : output ∈ fineLocalization r c) :
    ∃ n, output = Encodable.encode (FineLocalization.word r c n) ∧
      (Localization.word r c).Sublist ((FineLocalization.word r c n).map (emit r)) := by
  obtain ⟨hc, n, hn, he, hp⟩ := fineLocalization_source r c output ho
  exact ⟨n, he, FinePath.localization_sublist hp⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.FineLocalization.Refinements
