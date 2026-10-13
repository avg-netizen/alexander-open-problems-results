import Alexander313.Wilken.HereditaryFineLocalizationOrderSupport

/-!
# Actual first-branch interval dependencies

Finite ANF head comparison and principal closure recover the literal ordinal
prefix inside an open final-principal block. The original fine predecessor,
ordinary fallback, genuine argument gaps and real residual-image supremum
supply the interval laws below. No support, path or comparison equality is an
input. All domains retain original public admission and weak normality.
These are uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.FineLocalization.FirstBranchSupport

open Localization Localization.Refinements FinePredecessor
open FineLocalization.Refinements FineLocalization.OrderSupport

private theorem stripLast_map {A B : Type} (f : A → B) (xs : List A) :
    stripLast (xs.map f) = (stripLast xs).map f := by
  simp only [stripLast, ← List.map_reverse, ← List.map_tail]

private theorem stripLast_append_last {A : Type} (xs : List A) (a : A) :
    stripLast (xs ++ [a]) = xs := by
  simp only [stripLast, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append, List.tail_cons, List.reverse_reverse]

private theorem stripLast_append {A : Type} (xs ys : List A) (hy : ys ≠ []) :
    stripLast (xs ++ ys) = xs ++ stripLast ys := by
  obtain ⟨a, he, _⟩ := stripLast_split ys hy
  rw [he, ← List.append_assoc, stripLast_append_last, stripLast_append_last]

/-- Between an actual ANF prefix and its next principal summand, every real
ANF word extends that prefix. This is derived from principal closure and
left cancellation, not supplied as an ANF-prefix oracle. -/
theorem anf_open_block_prefix (xs ys : List Ordinal.{0}) (p : Ordinal.{0})
    (hn : IsAdditiveNormalForm (xs ++ [p])) (hy : IsAdditiveNormalForm ys)
    (hlo : principalSum xs < principalSum ys)
    (hhi : principalSum ys < principalSum xs + p) :
    ∃ rest, rest ≠ [] ∧ ys = xs ++ rest := by
  revert ys hn
  induction xs with
  | nil =>
    intro ys hn hy hlo hhi
    refine ⟨ys, ?_, rfl⟩
    intro he
    subst ys
    exact (lt_irrefl (0 : Ordinal.{0})) hlo
  | cons a xs ih =>
    intro ys hn hy hlo hhi
    cases ys with
    | nil => exact False.elim (not_lt_zero hlo)
    | cons b ys =>
      have ha := hn.1 a List.mem_cons_self
      have hb := hy.1 b List.mem_cons_self
      have he : a = b := by
        rcases lt_trichotomy a b with hab | hab | hba
        · have hs : principalSum ((a :: xs) ++ [p]) < b :=
            principalSum_lt hb.1 hb.2 _ (by
              intro e he
              rcases List.mem_cons.mp he with rfl | he
              · exact hab
              · exact (additiveNormalForm_head_ge hn he).trans_lt hab)
          have hupper : principalSum ((a :: xs) ++ [p]) = principalSum (a :: xs) + p := by
            rw [principalSum_append]; simp only [principalSum, add_zero]
          exact False.elim ((hs.trans_le le_self_add).not_ge (by rw [hupper]; exact hhi.le))
        · exact hab
        · have hs : principalSum (b :: ys) < a :=
            principalSum_lt ha.1 ha.2 _ (by
              intro e he
              rcases List.mem_cons.mp he with rfl | he
              · exact hba
              · exact (additiveNormalForm_head_ge hy he).trans_lt hba)
          exact False.elim ((hlo.trans hs).not_ge le_self_add)
      subst b
      have hl : principalSum xs < principalSum ys :=
        (add_lt_add_iff_left a).mp hlo
      have hh : principalSum ys < principalSum xs + p := by
        apply (add_lt_add_iff_left a).mp
        simpa only [principalSum, add_assoc] using hhi
      obtain ⟨rest, hr, he⟩ := ih ys (additiveNormalForm_tail hn) (additiveNormalForm_tail hy) hl hh
      exact ⟨rest, hr, by rw [he]; rfl⟩

theorem anf_open_block_stripLast_le (xs ys : List Ordinal.{0}) (p : Ordinal.{0})
    (hn : IsAdditiveNormalForm (xs ++ [p])) (hy : IsAdditiveNormalForm ys)
    (hlo : principalSum xs < principalSum ys)
    (hhi : principalSum ys < principalSum xs + p) :
    principalSum xs ≤ principalSum (stripLast ys) := by
  obtain ⟨rest, hr, he⟩ := anf_open_block_prefix xs ys p hn hy hlo hhi
  rw [he, stripLast_append xs rest hr, principalSum_append]
  exact le_self_add

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

private theorem fallback_mem (r root : Nat) (hr : Node r root)
    (hb : finiteBase r < value r root) : fallback r root ∈ nativePath r root := by
  obtain ⟨pre, a, b, he⟩ := last_two _ (localization_length r root hr hb)
  have hf : fallback r root = a := by
    simp only [fallback, penultimate, he, List.reverse_append, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.cons_append, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.getD_some]
  rw [hf, he]
  simp

/-- The ordinary fallback never exceeds the actual fine predecessor. The
bound follows from the constructed ordinary/fine subsequence and real path
bounds, including alternate base spellings. -/
theorem fallback_le_predecessor (r root : Nat)
    (hi : FinePredecessor.inputCheck r root = true) :
    value r (fallback r root) ≤ value r (predecessorCode r root) := by
  have hr := (FinePredecessor.inputCheck_exact r root).mp hi
  have hf := fallback_spec r root hr.1 hr.2
  obtain ⟨path, hp⟩ := finePath_exists r root hr.1
  have hmem : value r (fallback r root) ∈ path.map (value r) :=
    (FineLocalization.Refinements.FinePath.localization_values_sublist hp).subset
      (List.mem_map.mpr ⟨fallback r root, fallback_mem r root hr.1 hr.2, rfl⟩)
  cases hp with
  | base root hn hb => exact False.elim ((ne_of_gt hr.2) hb)
  | next root hir path hpath =>
    rw [List.map_append] at hmem
    rcases List.mem_append.mp hmem with hm | hm
    · obtain ⟨e, he, hev⟩ := List.mem_map.mp hm
      rw [← hev]; exact hpath.bound e he
    · have he : value r (fallback r root) = value r root := by
        simpa only [List.map_cons, List.map_nil, List.mem_singleton] using hm
      exact False.elim (he.not_lt hf.2.2)

/-- A genuinely larger node with no larger argument cannot have its ordinary
fallback below the given node: the true ordinary gap law excludes that jump. -/
theorem argument_le_predecessor_bound (r lower upper : Nat)
    (hl : Node r lower) (hu : Node r upper) (hv : value r lower < value r upper)
    (ha : argumentValue r upper ≤ argumentValue r lower) :
    value r lower ≤ value r (predecessorCode r upper) := by
  have hb : finiteBase r < value r upper :=
    (by simpa only [baseRaw_value] using baseRaw_le r lower hl).trans_lt hv
  have hi := (FinePredecessor.inputCheck_exact r upper).mpr ⟨hu, hb⟩
  have hfall : value r lower ≤ value r (fallback r upper) := by
    apply le_of_not_gt
    intro hfl
    have harg := sourcePath_interval_argument_lt hu
      (fallback_gap_sourcePath r upper hu hb) lower hl hfl hv
    exact harg.not_ge ha
  exact hfall.trans (fallback_le_predecessor r upper hi)

/-- The unit first branch has an actual successor ARG, not an assumed
immediate-next-code property. -/
theorem unit_argument_succ (r root : Nat) (hr : Node r root)
    (hn : lowWord r root ≠ []) (hu : denote r (lastAtom r root) = 1) :
    argumentValue r root = argumentValue r (prefixNode r root) + 1 := by
  have hs := low_split r root hr hn
  have hp : argumentValue r (prefixNode r root) = delta r root + prefixResidual r root := by
    simpa only [argumentValue, prefixNode, argumentCode_theta, prefixCode] using prefixCode_value r root
  rw [← (argument_parts r root hr).1, hs.2.2.2.2.2, hu, hp, add_assoc]

theorem predecessor_eq_prefix (r root : Nat)
    (hi : FinePredecessor.inputCheck r root = true) (hf : firstBranch r root = true) :
    predecessorCode r root = prefixNode r root := by
  have hr := (FinePredecessor.inputCheck_exact r root).mp hi
  rcases predecessor_branches r root hi with ⟨hc, he⟩ | ⟨hc, he⟩
  · exact he
  · exact False.elim (hc ((firstBranch_exact r root hr.1).mp hf))

private theorem prefix_argument_value (r root : Nat) :
    argumentValue r (prefixNode r root) = delta r root + prefixResidual r root := by
  simpa only [argumentValue, prefixNode, argumentCode_theta, prefixCode] using prefixCode_value r root

private theorem node_principal (r c : Nat) (hc : Node r c) :
    0 < value r c ∧ Ordinal.IsPrincipal (· + ·) (value r c) := by
  obtain ⟨a, rfl, ha, hn⟩ := hc
  let n := SourceOne.PublicCodes.fragment (.theta 0 a)
  have ht := Theta.checked_admissible r n (.theta 0 a) ha (SourceOne.PublicCodes.height_le_fragment _)
  have hp := Theta.theta_pos_principal r n 0 a ht
  rw [← denote_eq_finite r n (.theta 0 a) ht.2] at hp
  simpa only [value, interpretation_code] using hp

private theorem delta_level (r c : Nat) (hc : Node r c) :
    delta r c = SourceHighPartComparison.localizationLevel r c := by
  simpa only [delta, SourceHighPartComparison.localizationLevel, SourceHighPartComparison.highPart,
    argumentValue] using (SourceDecomposition.parts_code_value r 0 _ (argument_accepted r c hc)).1

private theorem low_sum (r c : Nat) :
    principalSum ((lowWord r c).map (denote r)) = residual r c := by
  simp only [residual, SourceDecomposition.lowCode, interpretation_code,
    SourceDecomposition.lowPartTerm, Theta.Normalization.buildAtoms_denote, lowWord]

/-- The actual final atom lies below the nonzero retained ANF prefix. -/
theorem last_le_nonzero_prefix (r root : Nat) (hr : Node r root)
    (hn : lowWord r root ≠ []) (hp : 0 < prefixResidual r root) :
    denote r (lastAtom r root) ≤ prefixResidual r root := by
  have hs := low_split r root hr hn
  have hnorm := (SourceDecomposition.words_normal r 0 _ (argument_accepted r root hr)).2
  change IsAdditiveNormalForm ((lowWord r root).map (denote r)) at hnorm
  rw [hs.1, List.map_append, List.map_cons, List.map_nil] at hnorm
  cases he : stripLast (lowWord r root) with
  | nil =>
    have hz : prefixResidual r root = 0 := by simp only [prefixResidual, he, List.map_nil, principalSum]
    exact False.elim ((ne_of_gt hp) hz)
  | cons a as =>
    have hhead : denote r (lastAtom r root) ≤ denote r a := by
      rw [he, List.map_cons] at hnorm
      exact additiveNormalForm_head_ge hnorm (List.mem_append_right _ List.mem_cons_self)
    exact hhead.trans (by
      change denote r a ≤ principalSum ((stripLast (lowWord r root)).map (denote r))
      rw [he, List.map_cons]; exact le_self_add)

/-- STRICT makes the retained prefix nonzero; actual principal closure then
puts the whole root residual below the constructed predecessor value. -/
theorem strict_residual_lt_prefix_node (r root : Nat) (hr : Node r root)
    (hn : lowWord r root ≠ [])
    (hs : prefixResidual r root < SourceFixedPointLimits.globalResidualImageSup
      (finiteBase r) 0 (delta r root) (prefixResidual r root)) :
    residual r root < value r (prefixNode r root) := by
  have hp : 0 < prefixResidual r root := by
    apply pos_iff_ne_zero.mpr
    intro hz
    rw [hz] at hs
    simp only [SourceFixedPointLimits.globalResidualImageSup, Ordinal.bsup_zero,
      lt_self_iff_false] at hs
  have htail := prefix_residual_lt_node r root hr hn
  have hlast := (last_le_nonzero_prefix r root hr hn hp).trans_lt htail
  have hprincipal := (node_principal r _ (prefix_node r root hr hn)).2
  rw [(low_split r root hr hn).2.2.2.2.2]
  exact hprincipal htail hlast

/-- An intermediate argument above the removed-prefix argument is genuinely
in the same divided high part, and in the actual open residual ANF block. -/
theorem first_interval_parts (r root intermediate : Nat)
    (hi : FinePredecessor.inputCheck r root = true) (hf : firstBranch r root = true)
    (hm : Node r intermediate)
    (hlo : value r (predecessorCode r root) < value r intermediate)
    (hhi : value r intermediate < value r root)
    (ha : argumentValue r (prefixNode r root) < argumentValue r intermediate) :
    delta r intermediate = delta r root ∧
      prefixResidual r root < residual r intermediate ∧ residual r intermediate < residual r root := by
  have hr := (FinePredecessor.inputCheck_exact r root).mp hi
  have hc := (firstBranch_exact r root hr.1).mp hf
  have hag := predecessor_gap_argument_lt r root intermediate hi hm hlo hhi
  have hl := SourceHighPartComparison.highPart_mono (omegaSequence (finiteBase r) 1) ha.le
  have hh := SourceHighPartComparison.highPart_mono (omegaSequence (finiteBase r) 1) hag.le
  change SourceHighPartComparison.localizationLevel r (prefixNode r root) ≤
    SourceHighPartComparison.localizationLevel r intermediate at hl
  change SourceHighPartComparison.localizationLevel r intermediate ≤
    SourceHighPartComparison.localizationLevel r root at hh
  rw [prefix_level_eq r root hr.1 hc.1] at hl
  have heLevel := le_antisymm hh hl
  have hd : delta r intermediate = delta r root :=
    (delta_level r intermediate hm).trans (heLevel.trans (delta_level r root hr.1).symm)
  refine ⟨hd, ?_, ?_⟩
  · apply (add_lt_add_iff_left (delta r root)).mp
    simpa only [prefix_argument_value, ← (argument_parts r intermediate hm).1, hd] using ha
  · apply (add_lt_add_iff_left (delta r root)).mp
    simpa only [← (argument_parts r intermediate hm).1, ← (argument_parts r root hr.1).1, hd] using hag

/-- The genuine finite ANF prefix theorem applied to the actual source low
words; no normal-form decomposition is supplied for the intermediate node. -/
theorem first_interval_prefix_residual_le (r root intermediate : Nat)
    (hr : Node r root) (hm : Node r intermediate) (hn : lowWord r root ≠ [])
    (hlo : prefixResidual r root < residual r intermediate)
    (hhi : residual r intermediate < residual r root) :
    prefixResidual r root ≤ prefixResidual r intermediate := by
  have hs := low_split r root hr hn
  have hnorm := (SourceDecomposition.words_normal r 0 _ (argument_accepted r root hr)).2
  change IsAdditiveNormalForm ((lowWord r root).map (denote r)) at hnorm
  rw [hs.1, List.map_append, List.map_cons, List.map_nil] at hnorm
  have hmnorm := (SourceDecomposition.words_normal r 0 _ (argument_accepted r intermediate hm)).2
  change IsAdditiveNormalForm ((lowWord r intermediate).map (denote r)) at hmnorm
  have h := anf_open_block_stripLast_le
    ((stripLast (lowWord r root)).map (denote r)) ((lowWord r intermediate).map (denote r))
    (denote r (lastAtom r root)) hnorm hmnorm
    (by simpa only [low_sum, prefixResidual] using hlo)
    (by simpa only [low_sum, prefixResidual, ← hs.2.2.2.2.2] using hhi)
  simpa only [stripLast_map, prefixResidual] using h

private theorem prefix_value_collapse (r root : Nat) :
    value r (prefixNode r root) = globalCollapse (finiteBase r) 0
      (delta r root + prefixResidual r root) := by
  simpa only [value, prefixNode, interpretation_code, denote, eval, prefixCode] using
    congrArg (globalCollapse (finiteBase r) 0) (prefixCode_value r root)

/-- The repaired ordinary STRICT supremum condition is inherited by every
actual stripped residual in the open first-branch ANF block. -/
theorem strict_interval_firstCase (r root intermediate : Nat)
    (hr : Node r root) (hm : Node r intermediate) (hn : lowWord r root ≠ [])
    (hs : prefixResidual r root < SourceFixedPointLimits.globalResidualImageSup
      (finiteBase r) 0 (delta r root) (prefixResidual r root))
    (hd : delta r intermediate = delta r root)
    (hlo : prefixResidual r root < residual r intermediate)
    (hhi : residual r intermediate < residual r root) : FirstCase r intermediate := by
  have hmnonempty : lowWord r intermediate ≠ [] := by
    intro he
    have hz : residual r intermediate = 0 := by
      rw [← low_sum r intermediate, he]; rfl
    exact not_lt_zero (hlo.trans_eq hz)
  have hprefix := first_interval_prefix_residual_le r root intermediate hr hm hn hlo hhi
  have hbound : prefixResidual r intermediate < value r (prefixNode r root) :=
    (prefix_residual_lt r intermediate hm hmnonempty).trans
      (hhi.trans (strict_residual_lt_prefix_node r root hr hn hs))
  refine ⟨hmnonempty, Or.inr ?_⟩
  rw [hd]
  by_cases he : prefixResidual r intermediate = prefixResidual r root
  · simpa only [he] using hs
  · have hlt : prefixResidual r root < prefixResidual r intermediate :=
      lt_of_le_of_ne hprefix he.symm
    have hsup : value r (prefixNode r root) ≤ SourceFixedPointLimits.globalResidualImageSup
        (finiteBase r) 0 (delta r root) (prefixResidual r intermediate) := by
      rw [prefix_value_collapse, SourceFixedPointLimits.globalResidualImageSup]
      exact Ordinal.le_bsup _ (prefixResidual r root) hlt
    exact hbound.trans_le hsup

/-- True source high-part comparison turns the constructed retained residual
inequality into a theta-value inequality in the same real high part. -/
theorem same_delta_prefix_node_le (r left right : Nat) (hl : Node r left) (hr : Node r right)
    (hln : lowWord r left ≠ []) (hrn : lowWord r right ≠ [])
    (hd : delta r left = delta r right)
    (hp : prefixResidual r left ≤ prefixResidual r right) :
    value r (prefixNode r left) ≤ value r (prefixNode r right) := by
  have hleft := prefix_node r left hl hln
  have hright := prefix_node r right hr hrn
  have ha : argumentValue r (prefixNode r left) ≤ argumentValue r (prefixNode r right) := by
    rw [prefix_argument_value, prefix_argument_value, hd]
    exact add_le_add_right hp _
  have he : SourceHighPartComparison.localizationLevel r (prefixNode r left) =
      SourceHighPartComparison.localizationLevel r (prefixNode r right) := by
    rw [prefix_level_eq r left hl hln, prefix_level_eq r right hr hrn,
      ← delta_level r left hl, ← delta_level r right hr, hd]
  apply le_of_not_gt
  intro hreverse
  have h := SourceHighPartComparison.node_level_lt r (prefixNode r right) (prefixNode r left)
    hright hleft hreverse ha
  rw [he] at h
  exact lt_irrefl _ h

/-- The complete computed FIRST branch cannot jump below its predecessor
on an originally admitted intermediate root. The low-argument case uses the
real ordinary gap, the unit case its genuine successor ARG, and the STRICT
case the constructed ANF prefix plus an actual supremum witness. -/
theorem first_gap_predecessor_bound (r root intermediate : Nat)
    (hi : FinePredecessor.inputCheck r root = true) (hf : firstBranch r root = true)
    (hm : Node r intermediate)
    (hlo : value r (predecessorCode r root) < value r intermediate)
    (hhi : value r intermediate < value r root) :
    value r (predecessorCode r root) ≤ value r (predecessorCode r intermediate) := by
  have hr := (FinePredecessor.inputCheck_exact r root).mp hi
  have hc := (firstBranch_exact r root hr.1).mp hf
  have he := predecessor_eq_prefix r root hi hf
  have hpnode := prefix_node r root hr.1 hc.1
  have hproper : finiteBase r < value r intermediate := (predecessor_spec r root hi).2.1.trans_lt hlo
  have hmi := (FinePredecessor.inputCheck_exact r intermediate).mpr ⟨hm, hproper⟩
  by_cases ha : argumentValue r intermediate ≤ argumentValue r (prefixNode r root)
  · rw [he] at hlo ⊢
    exact argument_le_predecessor_bound r _ intermediate hpnode hm hlo ha
  · have hag : argumentValue r (prefixNode r root) < argumentValue r intermediate := lt_of_not_ge ha
    have hparts := first_interval_parts r root intermediate hi hf hm hlo hhi hag
    rcases hc.2 with hu | hs
    · have harg := predecessor_gap_argument_lt r root intermediate hi hm hlo hhi
      rw [unit_argument_succ r root hr.1 hc.1 hu] at harg
      exact False.elim (hag.not_ge (_root_.Order.lt_add_one_iff.mp harg))
    · have hmc := strict_interval_firstCase r root intermediate hr.1 hm hc.1 hs hparts.1 hparts.2.1 hparts.2.2
      have hmf := (firstBranch_exact r intermediate hm).mpr hmc
      have hme := predecessor_eq_prefix r intermediate hmi hmf
      rw [he, hme]
      exact same_delta_prefix_node_le r root intermediate hr.1 hm hc.1 hmc.1 hparts.1.symm
        (first_interval_prefix_residual_le r root intermediate hr.1 hm hc.1 hparts.2.1 hparts.2.2)

/-- Actual fine recurrence, together with the derived no-jump law, reaches
the original first-branch predecessor value on every intermediate path. -/
theorem first_interval_mem (r root : Nat)
    (hi : FinePredecessor.inputCheck r root = true) (hf : firstBranch r root = true)
    {intermediate : Nat} {path : List Nat} (hp : FinePath r intermediate path)
    (hlo : value r (predecessorCode r root) < value r intermediate)
    (hhi : value r intermediate < value r root) :
    ∃ e ∈ path, value r e = value r (predecessorCode r root) := by
  revert hlo hhi
  induction hp with
  | base c hc hb =>
    intro hlo hhi
    have hl := (predecessor_spec r root hi).2.1.trans_lt hlo
    exact False.elim ((ne_of_gt hl) hb)
  | next c hc path hp ih =>
    intro hlo hhi
    have hn := ((FinePredecessor.inputCheck_exact r c).mp hc).1
    have hbound := first_gap_predecessor_bound r root c hi hf hn hlo hhi
    by_cases he : value r (predecessorCode r c) = value r (predecessorCode r root)
    · obtain ⟨pre, hend⟩ := hp.end
      exact ⟨predecessorCode r c, List.mem_append.mpr (Or.inl (by rw [hend]; simp)), he⟩
    · obtain ⟨e, hes, hev⟩ := ih (lt_of_le_of_ne hbound he.symm)
        ((predecessor_spec r c hc).2.2.trans hhi)
      exact ⟨e, List.mem_append.mpr (Or.inl hes), hev⟩

/-- Complete FIRST-branch value-prefix retention with only original guards,
the actual computed Boolean branch, the true interval and genuine FinePaths. -/
theorem first_interval_value_prefix (r root intermediate : Nat)
    (hi : FinePredecessor.inputCheck r root = true) (hf : firstBranch r root = true)
    (hm : Node r intermediate)
    (hlo : value r (predecessorCode r root) < value r intermediate)
    (hhi : value r intermediate < value r root)
    {«prefix» path : List Nat} (hp : FinePath r (predecessorCode r root) «prefix»)
    (hq : FinePath r intermediate path) :
    ∃ rest : List Ordinal.{0}, path.map (value r) = «prefix».map (value r) ++ rest :=
  FineLocalization.OrderSupport.FinePath.value_prefix_of_mem hp hq
    (first_interval_mem r root hi hf hq hlo hhi)

/-- Both branches now yield genuine interval retention. No branch alignment,
normal-form, support maximality or path invariance premise is supplied. -/
theorem predecessor_interval_value_prefix (r root intermediate : Nat)
    (hi : FinePredecessor.inputCheck r root = true) (hm : Node r intermediate)
    (hlo : value r (predecessorCode r root) < value r intermediate)
    (hhi : value r intermediate < value r root)
    {«prefix» path : List Nat} (hp : FinePath r (predecessorCode r root) «prefix»)
    (hq : FinePath r intermediate path) :
    ∃ rest : List Ordinal.{0}, path.map (value r) = «prefix».map (value r) ++ rest := by
  cases hf : firstBranch r root with
  | false => exact fallback_interval_value_prefix r root intermediate hi hf hm hlo hhi hp hq
  | true => exact first_interval_value_prefix r root intermediate hi hf hm hlo hhi hp hq

/-- Strict cross-root orientation throughout the complete actual predecessor
gap, now derived for both source branches. Full arbitrary-root order is a
separate theorem; this statement has the genuine open-gap hypothesis. -/
theorem predecessor_gap_values_lex (r root intermediate : Nat)
    (hi : FinePredecessor.inputCheck r root = true) (hm : Node r intermediate)
    (hlo : value r (predecessorCode r root) < value r intermediate)
    (hhi : value r intermediate < value r root)
    {path other : List Nat} (hp : FinePath r intermediate path) (hq : FinePath r root other) :
    List.Lex (· < ·) (path.map (value r)) (other.map (value r)) := by
  cases hq with
  | base root hr hb =>
    exact False.elim ((ne_of_gt ((FinePredecessor.inputCheck_exact r root).mp hi).2) hb)
  | next root hir «prefix» hprefix =>
    obtain ⟨rest, he⟩ := predecessor_interval_value_prefix r root intermediate hi hm hlo hhi hprefix hp
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

end Alexander313.Wilken.RelativeTerm.Hereditary.FineLocalization.FirstBranchSupport
