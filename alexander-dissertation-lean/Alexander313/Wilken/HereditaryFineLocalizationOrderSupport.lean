import Mathlib.Data.List.Lex
import Alexander313.Wilken.HereditaryFineLocalizationInvariance
import Alexander313.Wilken.HereditaryFineLocalizationRefinements

/-!
# Actual fine-predecessor gaps and fallback interval retention

Both computed predecessor branches give a genuine two-node SourcePath in the
original root support. This derives the argument and divided-high-part bounds
for every admitted intermediate theta-zero node. In the ordinary-fallback
branch the selected arguments strictly descend, recovering the predecessor
value in the intermediate root's ordinary path and then its real FinePath.
The resulting value prefix and strict lex orientation inside that fallback
gap use proved predecessor determinacy, not native spelling or support equality.

The first/prefix-removal branch does not have the descending-argument bound
used by that interval-prefix proof. Its mixed interval retention, and the
full strict fine lexicographic equivalence of source 2.40, remain unproved.
All statements retain the original weak-normal public domains. These are
uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.FineLocalization.OrderSupport

open Localization Localization.Refinements FinePredecessor

private theorem last_two (xs : List Nat) (h : 2 ≤ xs.length) :
    ∃ pre a b, xs = pre ++ [a, b] := by
  cases he : xs.reverse with
  | nil => have hl := congrArg List.length he; simp at hl; omega
  | cons b bs =>
    cases hs : bs with
    | nil => have hl := congrArg List.length he
              simp only [List.length_reverse, hs, List.length_cons, List.length_nil] at hl
              omega
    | cons a pre =>
      refine ⟨pre.reverse, a, b, ?_⟩
      have hr := congrArg List.reverse he
      simpa only [List.reverse_reverse, hs, List.reverse_cons, List.reverse_nil,
        List.append_assoc, List.singleton_append] using hr

private theorem endpoint_append_last (xs : List Nat) (b : Nat) :
    endpoint (xs ++ [b]) = b := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases xs with
    | nil => rfl
    | cons c xs => simpa only [List.cons_append, endpoint] using ih

private theorem fallback_last (r root a b : Nat) (pre : List Nat)
    (he : nativePath r root = pre ++ [a, b]) : fallback r root = a := by
  simp only [fallback, penultimate, he, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append, List.getElem?_cons_succ,
    List.getElem?_cons_zero, Option.getD_some]

private theorem last_value (r root : Nat) (hr : Node r root) (pre : List Nat) (a b : Nat)
    (he : nativePath r root = pre ++ [a, b]) : value r b = value r root := by
  have hi := (Localization.inputCheck_exact r root).mpr hr
  have hend := nativePath_end r root hi
  have hs : pre ++ [a, b] = (pre ++ [a]) ++ [b] := by
    simp only [List.append_assoc, List.singleton_append]
  simpa only [he, hs, endpoint_append_last] using hend

/-- The first branch itself satisfies the actual ordinary selection rule
when started at its constructed predecessor. -/
theorem first_gap_sourcePath (r root : Nat) (hr : Node r root) (hf : FirstCase r root) :
    SourcePath r (support root) [prefixNode r root, root] := by
  have hb := prefix_node r root hr hf.1
  have hbr := prefix_strict r root hr hf.1
  refine SourcePath.next _ _ [] hb hbr (support_root r root hr) ?_
    (SourcePath.stop root hr (fun e he => support_bound r root e hr he))
  intro e he hbe
  have hen := support_node r root e hr he
  have her := support_bound r root e hr he
  have hev : value r e = value r root := by
    apply le_antisymm her
    apply le_of_not_gt
    intro helt
    exact hbe.not_ge (Refinements.first_support_below_root r root e hr hf he helt)
  exact ((node_value_eq_iff_argument_eq r e root hen hr).mp hev).le

/-- The real final two ordinary selections, with the endpoint replaced only
by its equal-value original root, give the fallback gap path. -/
theorem fallback_gap_sourcePath (r root : Nat) (hr : Node r root)
    (hproper : finiteBase r < value r root) :
    SourcePath r (support root) [fallback r root, root] := by
  have hi := (Localization.inputCheck_exact r root).mpr hr
  obtain ⟨pre, a, b, he⟩ := last_two _ (localization_length r root hr hproper)
  have hf := fallback_last r root a b pre he
  have hb := last_value r root hr pre a b he
  have hs := sourcePath_suffix (nativePath_source r root hi) pre a [b]
    (by simpa only [List.singleton_append] using he)
  have hbn := hs.nodes b (by simp)
  have hba := (node_value_eq_iff_argument_eq r b root hbn hr).mp hb
  rw [hf]
  cases hs with
  | next a b tail ha hab hbs harg hrest =>
    refine SourcePath.next a root [] ha (hab.trans_eq hb) (support_root r root hr) ?_
      (SourcePath.stop root hr (fun e he => support_bound r root e hr he))
    intro e he hae
    exact (harg e he hae).trans_eq hba

/-- Both genuine computed branches expose the same real gap-selection law. -/
theorem predecessor_gap_sourcePath (r root : Nat)
    (hi : FinePredecessor.inputCheck r root = true) :
    SourcePath r (support root) [predecessorCode r root, root] := by
  have hr := (FinePredecessor.inputCheck_exact r root).mp hi
  rcases predecessor_branches r root hi with ⟨hf, he⟩ | ⟨hf, he⟩
  · rw [he]; exact first_gap_sourcePath r root hr.1 hf
  · rw [he]; exact fallback_gap_sourcePath r root hr.1 hr.2

/-- No admission, argument, or localization-level comparison is supplied
for the intermediate node beyond its original Node domain and actual gap. -/
theorem predecessor_gap_argument_lt (r root intermediate : Nat)
    (hi : FinePredecessor.inputCheck r root = true) (hm : Node r intermediate)
    (hlo : value r (predecessorCode r root) < value r intermediate)
    (hhi : value r intermediate < value r root) :
    argumentValue r intermediate < argumentValue r root :=
  sourcePath_interval_argument_lt ((FinePredecessor.inputCheck_exact r root).mp hi).1
    (predecessor_gap_sourcePath r root hi) intermediate hm hlo hhi

theorem predecessor_gap_level_le (r root intermediate : Nat)
    (hi : FinePredecessor.inputCheck r root = true) (hm : Node r intermediate)
    (hlo : value r (predecessorCode r root) < value r intermediate)
    (hhi : value r intermediate < value r root) :
    SourceHighPartComparison.localizationLevel r intermediate ≤
      SourceHighPartComparison.localizationLevel r root :=
  SourceHighPartComparison.highPart_mono (omegaSequence (finiteBase r) 1)
    (predecessor_gap_argument_lt r root intermediate hi hm hlo hhi).le

/-- A proper fallback is a genuinely selected node, so its argument strictly
exceeds the root argument; the initial base is explicitly excluded. -/
theorem fallback_argument_gt (r root : Nat) (hr : Node r root)
    (hproper : finiteBase r < value r root)
    (hb : finiteBase r < value r (fallback r root)) :
    argumentValue r root < argumentValue r (fallback r root) := by
  have hi := (Localization.inputCheck_exact r root).mpr hr
  obtain ⟨pre, a, b, he⟩ := last_two _ (localization_length r root hr hproper)
  have hf := fallback_last r root a b pre he
  have hv := last_value r root hr pre a b he
  have hn := nativePath_nodes r root hi
  have hbn := hn b (by rw [he]; exact List.mem_append.mpr (Or.inr (by simp)))
  have hba := (node_value_eq_iff_argument_eq r b root hbn hr).mp hv
  cases pre with
  | nil =>
    obtain ⟨tail, hh⟩ := nativePath_head r root
    have hc : baseRaw r :: tail = [a, b] := hh.symm.trans (by simpa only [List.nil_append] using he)
    have ha := (List.cons.inj hc).1
    have hbase : value r (fallback r root) = finiteBase r := by rw [hf, ← ha, baseRaw_value]
    exact False.elim ((ne_of_gt hb) hbase)
  | cons p pre =>
    have hp := nativePath_source r root hi
    have hpath : nativePath r root = p :: (pre ++ [a, b]) := by simpa only [List.cons_append] using he
    rw [hpath] at hp
    have hdesc := sourcePath_arguments_descending hp
    rw [List.map_append] at hdesc
    have hpair := (List.pairwise_append.mp hdesc).2.1
    have hlt : argumentValue r b < argumentValue r a :=
      (List.pairwise_cons.mp hpair).1 _ (by simp)
    simpa only [hf, hba] using hlt

/-- A candidate's actual maximal argument forces its value to be reached
by the ordinary recurrence. Membership is recovered from real support. -/
theorem sourcePath_contains_max_value {r root a head : Nat} {tail : List Nat}
    (hr : Node r root) (ha : Node r a)
    (hw : ∃ e ∈ support root, value r e = value r a)
    (hmax : ∀ e ∈ support root, value r a ≤ value r e →
      argumentValue r e ≤ argumentValue r a)
    (hp : SourcePath r (support root) (head :: tail))
    (hstart : value r head ≤ value r a)
    (hend : value r a ≤ value r (endpoint (head :: tail))) :
    ∃ e ∈ head :: tail, value r e = value r a := by
  revert hstart hend
  induction hp with
  | stop c hc hstop =>
    intro hstart hend
    exact ⟨c, List.mem_cons_self, le_antisymm hstart (by simpa only [endpoint] using hend)⟩
  | next c d tail hc hcd hds harg hrest ih =>
    intro hstart hend
    by_cases he : value r c = value r a
    · exact ⟨c, List.mem_cons_self, he⟩
    · have hca := lt_of_le_of_ne hstart he
      obtain ⟨e, hes, hev⟩ := hw
      have hen := support_node r root e hr hes
      have hea := (node_value_eq_iff_argument_eq r e a hen ha).mp hev
      have had : argumentValue r a ≤ argumentValue r d := by
        rw [← hea]
        exact harg e hes (by rw [hev]; exact hca)
      have hdn := hrest.nodes d List.mem_cons_self
      have hda : value r d ≤ value r a := by
        apply le_of_not_gt
        intro hadValue
        have hargEq := le_antisymm (hmax d hds hadValue.le) had
        have hv := (node_value_eq_iff_argument_eq r d a hdn ha).mpr hargEq
        exact hv.not_gt hadValue
      obtain ⟨f, hfs, hfv⟩ := ih hda (by simpa only [endpoint] using hend)
      exact ⟨f, List.mem_cons_of_mem _ hfs, hfv⟩

/-- A node already reached by an actual FinePath has exactly that path as
a value prefix. This follows from the proved recurrence determinacy. -/
theorem FinePath.value_prefix_of_mem {r a root : Nat} {path other : List Nat}
    (hp : FinePath r a path) (hq : FinePath r root other)
    (hm : ∃ e ∈ other, value r e = value r a) :
    ∃ rest : List Ordinal.{0}, other.map (value r) = path.map (value r) ++ rest := by
  revert hm
  induction hq with
  | base c hc hb =>
    intro hm
    obtain ⟨e, he, hev⟩ := hm
    have hec := List.mem_singleton.mp he
    subst e
    have hv := Invariance.FinePath.values_eq hp c [c] (.base c hc hb) hev.symm
    exact ⟨[], by simpa only [List.append_nil] using hv.symm⟩
  | next c hc other hq ih =>
    intro hm
    obtain ⟨e, he, hev⟩ := hm
    rcases List.mem_append.mp he with he | he
    · obtain ⟨rest, hrest⟩ := ih ⟨e, he, hev⟩
      refine ⟨rest ++ [value r c], ?_⟩
      simp only [List.map_append, List.map_cons, List.map_nil, hrest, List.append_assoc]
    · have hec := List.mem_singleton.mp he
      subst e
      have hv := Invariance.FinePath.values_eq hp c (other ++ [c]) (.next c hc other hq) hev.symm
      exact ⟨[], by simpa only [List.append_nil] using hv.symm⟩

/-- The advertised fallback branch is obtained from the original computed
Boolean test, rather than an externally chosen predecessor. -/
theorem predecessor_eq_fallback (r root : Nat)
    (hi : FinePredecessor.inputCheck r root = true)
    (hf : firstBranch r root = false) : predecessorCode r root = fallback r root := by
  have hr := (FinePredecessor.inputCheck_exact r root).mp hi
  rcases predecessor_branches r root hi with ⟨hc, he⟩ | ⟨hc, he⟩
  · have ht := (firstBranch_exact r root hr.1).mpr hc
    simp only [hf, Bool.false_eq_true] at ht
  · exact he

/-- In a genuine proper-fallback gap, its argument is maximal on every
intermediate root's actual support. All support bounds are derived internally. -/
theorem fallback_gap_maximal (r root intermediate : Nat)
    (hi : FinePredecessor.inputCheck r root = true)
    (hf : firstBranch r root = false) (hm : Node r intermediate)
    (hb : finiteBase r < value r (predecessorCode r root))
    (hlo : value r (predecessorCode r root) < value r intermediate)
    (hhi : value r intermediate < value r root) :
    ∀ e ∈ support intermediate, value r (predecessorCode r root) ≤ value r e →
      argumentValue r e ≤ argumentValue r (predecessorCode r root) := by
  have hr := (FinePredecessor.inputCheck_exact r root).mp hi
  have hp := (predecessor_spec r root hi).1
  have he := predecessor_eq_fallback r root hi hf
  have harg : argumentValue r root < argumentValue r (predecessorCode r root) := by
    rw [he] at hb ⊢
    exact fallback_argument_gt r root hr.1 hr.2 hb
  intro e hes hpe
  have hen := support_node r intermediate e hm hes
  by_cases heq : value r e = value r (predecessorCode r root)
  · exact ((node_value_eq_iff_argument_eq r e _ hen hp).mp heq).le
  · have helt : value r (predecessorCode r root) < value r e :=
      lt_of_le_of_ne hpe heq.symm
    have her : value r e < value r root := (support_bound r intermediate e hm hes).trans_lt hhi
    exact (predecessor_gap_argument_lt r root e hi hen helt her).le.trans harg.le

/-- The proper fallback value is genuinely reached in the intermediate
ordinary localization, without assuming literal support or path equality. -/
theorem fallback_gap_in_ordinary_path (r root intermediate : Nat)
    (hi : FinePredecessor.inputCheck r root = true)
    (hf : firstBranch r root = false) (hm : Node r intermediate)
    (hb : finiteBase r < value r (predecessorCode r root))
    (hlo : value r (predecessorCode r root) < value r intermediate)
    (hhi : value r intermediate < value r root) :
    ∃ e ∈ nativePath r intermediate, value r e = value r (predecessorCode r root) := by
  have hp := predecessor_spec r root hi
  have hmax := fallback_gap_maximal r root intermediate hi hf hm hb hlo hhi
  have hw := selected_value_in_support r intermediate (predecessorCode r root) hm hp.1 hmax
    intermediate (support_root r intermediate hm) hlo.le
  have hmi := (Localization.inputCheck_exact r intermediate).mpr hm
  obtain ⟨tail, hh⟩ := nativePath_head r intermediate
  have hpath := nativePath_source r intermediate hmi
  have hend := nativePath_end r intermediate hmi
  rw [hh] at hpath hend ⊢
  exact sourcePath_contains_max_value hm hp.1 hw hmax hpath
    (by simpa only [baseRaw_value] using hp.2.1) (hlo.le.trans_eq hend.symm)

/-- Genuine open-gap prefix retention for the original computed FALLBACK
branch. The base predecessor is handled by its value; no proper-predecessor,
support-witness, interval-selection, or spelling premise is supplied. -/
theorem fallback_interval_value_prefix (r root intermediate : Nat)
    (hi : FinePredecessor.inputCheck r root = true)
    (hf : firstBranch r root = false) (hm : Node r intermediate)
    (hlo : value r (predecessorCode r root) < value r intermediate)
    (hhi : value r intermediate < value r root)
    {«prefix» path : List Nat}
    (hp : FinePath r (predecessorCode r root) «prefix»)
    (hq : FinePath r intermediate path) :
    ∃ rest : List Ordinal.{0}, path.map (value r) = «prefix».map (value r) ++ rest := by
  apply FinePath.value_prefix_of_mem hp hq
  by_cases hb : finiteBase r < value r (predecessorCode r root)
  · obtain ⟨e, hes, hev⟩ := fallback_gap_in_ordinary_path r root intermediate hi hf hm hb hlo hhi
    have hv : value r (predecessorCode r root) ∈ (nativePath r intermediate).map (value r) :=
      List.mem_map.mpr ⟨e, hes, hev⟩
    have hs := Refinements.FinePath.localization_values_sublist hq
    exact List.mem_map.mp (hs.subset hv)
  · have hbase : value r (predecessorCode r root) = finiteBase r :=
      le_antisymm (le_of_not_gt hb) (predecessor_spec r root hi).2.1
    obtain ⟨b, tail, he, hv⟩ := hq.start
    exact ⟨b, by rw [he]; exact List.mem_cons_self, hv.trans hbase.symm⟩

/-- Strict cross-root orientation is derived inside the genuine computed
fallback gap. This is a restricted consequence of the constructed interval
law, not the full source 2.40 equivalence or its missing first-branch case. -/
theorem fallback_gap_values_lex (r root intermediate : Nat)
    (hi : FinePredecessor.inputCheck r root = true)
    (hf : firstBranch r root = false) (hm : Node r intermediate)
    (hlo : value r (predecessorCode r root) < value r intermediate)
    (hhi : value r intermediate < value r root)
    {path other : List Nat} (hp : FinePath r intermediate path) (hq : FinePath r root other) :
    List.Lex (· < ·) (path.map (value r)) (other.map (value r)) := by
  cases hq with
  | base root hr hb =>
    exact False.elim ((ne_of_gt ((FinePredecessor.inputCheck_exact r root).mp hi).2) hb)
  | next root hir «prefix» hprefix =>
    obtain ⟨rest, he⟩ := fallback_interval_value_prefix r root intermediate hi hf hm hlo hhi hprefix hp
    cases rest with
    | nil =>
      obtain ⟨pre, hend⟩ := hp.end
      have hmem : value r intermediate ∈ path.map (value r) :=
        List.mem_map.mpr ⟨intermediate, by rw [hend]; simp, rfl⟩
      rw [he, List.append_nil] at hmem
      obtain ⟨e, hes, hev⟩ := List.mem_map.mp hmem
      have hbound : value r intermediate ≤ value r (predecessorCode r root) := by
        rw [← hev]; exact hprefix.bound e hes
      exact False.elim (hlo.not_ge hbound)
    | cons b rest =>
      have hmem : b ∈ path.map (value r) := by
        rw [he]; exact List.mem_append.mpr (Or.inr List.mem_cons_self)
      obtain ⟨e, hes, hev⟩ := List.mem_map.mp hmem
      have hbr : b < value r root := by
        rw [← hev]; exact (hp.bound e hes).trans_lt hhi
      rw [List.map_append, List.map_cons, List.map_nil, he]
      exact List.Lex.append_left (· < ·) (List.Lex.rel hbr) («prefix».map (value r))

/-- The finite actual fine paths used above always exist, including the
base singleton. Their existence follows from the already constructed search. -/
theorem finePath_exists (r root : Nat) (hr : Node r root) :
    ∃ path, FinePath r root path := by
  obtain ⟨n, hn⟩ := Part.dom_iff_mem.mp (search_domain r root hr)
  exact ⟨FineLocalization.word r root n,
    run_path r root n hr (search_halt r root n hn) (search_before r root n hn)⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.FineLocalization.OrderSupport
