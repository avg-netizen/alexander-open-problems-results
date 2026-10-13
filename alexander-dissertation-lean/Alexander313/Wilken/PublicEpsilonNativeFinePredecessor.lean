import Alexander313.Wilken.PublicEpsilonNativeFinePredecessorSupport

/-!
# Actual BOTH-branch fine predecessor and interval gap at every coded epsilon

Every prefix caller is derived from the original weak Normal ANF. Real
full support bounds and the actual unit/STRICT branch give its gap; the
penultimate genuine computed source path gives the fallback gap. The
resulting finite predecessor and its interval argument comparison retain
the literal original native-q source, without a recoder or supplied gap.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceFinePredecessor

open ThetaCourse SourceLocalization
open Normalization (buildRev buildAtoms zeroTree)
open Hereditary.FinePredecessor (stripLast stripLast_split stripLast_mem stripLast_primrec)

theorem atoms_principal_support (m : Nat) (t s : RelativeTerm Nat) :
    s ∈ RelativeTerm.PrincipalSupport.principalList m t ↔
      ∃ a ∈ Comparison.atoms t, s ∈ RelativeTerm.PrincipalSupport.principalList m a := by
  induction t with
  | parameter p =>
    simp only [RelativeTerm.PrincipalSupport.principalList, List.not_mem_nil]
    constructor
    · intro h; exact False.elim h
    · rintro ⟨a, ha, hs⟩
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact List.not_mem_nil hs
  | sum a b iha ihb =>
    simp only [RelativeTerm.PrincipalSupport.principalList, Comparison.atoms, List.mem_append]
    constructor
    · rintro (h | h)
      · obtain ⟨a, ha, hs⟩ := iha.mp h; exact ⟨a, Or.inl ha, hs⟩
      · obtain ⟨a, ha, hs⟩ := ihb.mp h; exact ⟨a, Or.inr ha, hs⟩
    · rintro ⟨a, ha | ha, hs⟩
      · exact Or.inl (iha.mpr ⟨a, ha, hs⟩)
      · exact Or.inr (ihb.mpr ⟨a, ha, hs⟩)
  | theta k a => simp only [Comparison.atoms, List.mem_singleton, exists_eq_left]

private theorem buildRev_principal_support (m : Nat) (as : List (RelativeTerm Nat))
    (s : RelativeTerm Nat) :
    s ∈ RelativeTerm.PrincipalSupport.principalList m (buildRev as) ↔
      ∃ a ∈ as, s ∈ RelativeTerm.PrincipalSupport.principalList m a := by
  induction as with
  | nil =>
    simp only [buildRev, zeroTree, RelativeTerm.PrincipalSupport.principalList,
      List.not_mem_nil, false_and, exists_false]
  | cons a as ih =>
    simp only [buildRev, RelativeTerm.PrincipalSupport.principalList, List.mem_append, ih,
      List.mem_cons]
    constructor
    · rintro (⟨b, hb, hs⟩ | hs)
      · exact ⟨b, Or.inr hb, hs⟩
      · exact ⟨a, Or.inl rfl, hs⟩
    · rintro ⟨b, rfl | hb, hs⟩
      · exact Or.inr hs
      · exact Or.inl ⟨b, hb, hs⟩

theorem buildAtoms_principal_support (m : Nat) (as : List (RelativeTerm Nat))
    (s : RelativeTerm Nat) :
    s ∈ RelativeTerm.PrincipalSupport.principalList m (buildAtoms as) ↔
      ∃ a ∈ as, s ∈ RelativeTerm.PrincipalSupport.principalList m a := by
  simpa only [buildAtoms, List.mem_reverse] using buildRev_principal_support m as.reverse s

theorem prefix_argument_support_subset (q c : Nat) (hc : Node q c) (s : RelativeTerm Nat)
    (hs : s ∈ RelativeTerm.PrincipalSupport.principalList 0 (prefixArgument q c)) :
    s ∈ RelativeTerm.PrincipalSupport.principalList 0 (ThetaCourse.rawTree (argumentCode c)) := by
  obtain ⟨a, ha, hs⟩ := (buildAtoms_principal_support 0 (prefixWord q c) s).mp hs
  have haw : a ∈ Decomposition.word (argumentCode c) := by
    rcases List.mem_append.mp ha with ha | ha
    · exact ((Decomposition.highWord_mem 0 _ a).mp ha).1
    · exact ((Decomposition.lowWord_mem 0 _ a).mp (stripLast_mem _ _ ha)).1
  exact (atoms_principal_support 0 _ s).mpr ⟨a, haw, hs⟩

theorem argument_support_split (q c : Nat) (hc : Node q c) (he : lowWord q c ≠ [])
    (s : RelativeTerm Nat) :
    s ∈ RelativeTerm.PrincipalSupport.principalList 0 (ThetaCourse.rawTree (argumentCode c)) ↔
      s ∈ RelativeTerm.PrincipalSupport.principalList 0 (prefixArgument q c) ∨
      s ∈ RelativeTerm.PrincipalSupport.principalList 0 (lastAtom q c) := by
  have hw : Decomposition.word (argumentCode c) = prefixWord q c ++ [lastAtom q c] := by
    rw [Decomposition.word_partition q 0 _ (argument_accepted q c hc)]
    change highWord q c ++ lowWord q c = _
    rw [(low_split q c hc he).1, ← List.append_assoc]
    rfl
  rw [atoms_principal_support 0, ← Decomposition.word, hw,
    buildAtoms_principal_support]
  constructor
  · rintro ⟨a, ha, hs⟩
    rcases List.mem_append.mp ha with ha | ha
    · exact Or.inl ⟨a, ha, hs⟩
    · rw [List.mem_singleton.mp ha] at hs
      exact Or.inr hs
  · rintro (⟨a, ha, hs⟩ | hs)
    · exact ⟨a, List.mem_append_left _ ha, hs⟩
    · exact ⟨lastAtom q c, List.mem_append_right _ List.mem_cons_self, hs⟩

theorem prefix_argument_lt (q c : Nat) (hc : Node q c) (he : lowWord q c ≠ []) :
    argumentValue q (prefixNode q c) < argumentValue q c := by
  have h := add_lt_add_right (prefix_residual_lt q c hc he) (delta q c)
  rw [← prefixCode_value q c, (argument_parts q c hc).1] at h
  simpa only [prefixNode, argumentValue, argumentCode_theta, prefixCode] using h

theorem prefix_residual_lt_node (q c : Nat) (hc : Node q c) (he : lowWord q c ≠ []) :
    prefixResidual q c < value q (prefixNode q c) := by
  have ha := argument_accepted q c hc
  have hdcheck := (Decomposition.parts_checked q 0 _ ha).1
  let d := FixedPoint.sourceOrdinal q 0 (Decomposition.highPartTerm 0 (argumentCode c)) hdcheck
  have hdv : d.val = delta q c := by
    simp only [d, FixedPoint.sourceOrdinal, delta, Decomposition.highCode, interpretation_code]
  have hd : d.val < omegaSequence (base q) 2 := by
    rw [hdv]
    apply (Decomposition.parts_le q 0 _ ha).1.trans_lt
    obtain ⟨a, heq, hcheck, _⟩ := hc
    simpa only [heq, argumentValue, argumentCode_theta, interpretation_code] using
      FixedPoint.checked_theta_sort q 0 a hcheck
  have ht := RelativeZeta.Support.global_tail_lt_collapse (base q)
    (base_pos q (node_baseCheck q c hc)) d.val d.property hd
    (by simpa only [hdv] using (argument_parts q c hc).2.2) (prefixResidual q c)
    ((prefix_residual_lt q c hc he).trans (argument_parts q c hc).2.1)
  rw [hdv, ← prefixCode_value q c] at ht
  simpa only [prefixNode, value, interpretation_code, denote, eval, prefixCode,
    interpretation_code] using ht

theorem last_support_le (q c : Nat) (hc : Node q c) (he : lowWord q c ≠ [])
    (s : RelativeTerm Nat) (hs : s ∈ RelativeTerm.PrincipalSupport.principalList 0 (lastAtom q c)) :
    denote q s ≤ denote q (lastAtom q c) := by
  have hsplit := low_split q c hc he
  have ham : lastAtom q c ∈ lowWord q c := by rw [hsplit.1]; simp
  have haw := (Decomposition.lowWord_mem 0 _ _).mp ham
  have hsort : (lastAtom q c).outerSort ≤ 1 := by
    have hl := (Decomposition.below_exact q 0 _ hsplit.2.1).mp haw.2
    exact (denote_lt_iff_outerSort_le q _ hsplit.2.1 1 (by omega)).mp hl
  exact Iota.Inverse.fullList_value_le_low q _ _ hsplit.2.1 hsplit.2.2.1 hsort hs

theorem first_last_le_node (q c : Nat) (hc : Node q c) (hf : FirstCase q c) :
    denote q (lastAtom q c) ≤ value q (prefixNode q c) := by
  have hn := (Decomposition.words_normal q 0 _ (argument_accepted q c hc)).2
  have hs := low_split q c hc hf.1
  change IsAdditiveNormalForm ((lowWord q c).map (denote q)) at hn
  rw [hs.1, List.map_append, List.map_cons, List.map_nil] at hn
  cases hp : stripLast (lowWord q c) with
  | nil =>
    have hz : prefixResidual q c = 0 := by simp only [prefixResidual, hp, List.map_nil, principalSum]
    have hu : denote q (lastAtom q c) = 1 := by
      rcases hf.2 with h | h
      · exact h
      · rw [hz] at h
        simp only [SourceFixedPointLimits.globalResidualImageSup, Ordinal.bsup_zero,
          lt_self_iff_false] at h
    rw [hu]
    exact (Order.one_le_iff_pos.mpr (base_pos q (node_baseCheck q c hc))).trans
      (by simpa only [baseRaw_value q (node_baseCheck q c hc)] using baseRaw_le q _ (prefix_node q c hc hf.1))
  | cons a as =>
    have ham : denote q a ∈ (stripLast (lowWord q c)).map (denote q) := by
      rw [hp]; exact List.mem_cons_self
    have hlast : denote q (lastAtom q c) ≤ denote q a := by
      rw [hp, List.map_cons] at hn
      exact additiveNormalForm_head_ge hn (List.mem_append_right _ List.mem_cons_self)
    exact (hlast.trans (principalSum_mem_le ham)).trans
      (prefix_residual_lt_node q c hc hf.1).le

/-- Every genuinely written old argument support lies below the first
branch predecessor. The bound includes its hidden zero-level arguments. -/
theorem first_argument_support_bound (q c : Nat) (hc : Node q c) (hf : FirstCase q c)
    (s : RelativeTerm Nat)
    (hs : s ∈ RelativeTerm.PrincipalSupport.principalList 0 (rawTree (argumentCode c))) :
    denote q s ≤ value q (prefixNode q c) := by
  rcases (argument_support_split q c hc hf.1 s).mp hs with hs | hs
  · have hn := prefix_node q c hc hf.1
    have hnodecheck : check q (.theta 0 (prefixArgument q c)) = true := by
      simpa only [prefixNode, checkCode_code] using
        ((Comparison.acceptedCode_exact q _).mp (node_accepted q _ hn)).1
    simpa only [prefixNode, value, interpretation_code] using
      Iota.Inverse.fullList_value_le_low q (.theta 0 (prefixArgument q c)) s hnodecheck
        (prefix_normal q c hc) (by simp only [RelativeTerm.outerSort]; omega)
        (RelativeTerm.PrincipalSupport.principalList_nested 0 (prefixArgument q c) s hs)
  · exact (last_support_le q c hc hf.1 s hs).trans (first_last_le_node q c hc hf)

theorem first_support_below_root (q c d : Nat) (hc : Node q c) (hf : FirstCase q c)
    (hd : d ∈ support c) (hlt : value q d < value q c) :
    value q d ≤ value q (prefixNode q c) := by
  obtain ⟨a, heq, ha, hn⟩ := hc
  rw [heq, support, PrincipalSupport.listCode_code,
    RelativeTerm.PrincipalSupport.principalList_theta_same] at hd
  obtain ⟨s, hs, hsd⟩ := List.mem_map.mp hd
  rcases List.mem_cons.mp hs with hs | hs
  · have hdc : d = c := by rw [← hsd, hs, heq]
    exact False.elim (by simpa only [hdc, lt_self_iff_false] using hlt)
  · have hsa : s ∈ RelativeTerm.PrincipalSupport.principalList 0
        (ThetaCourse.rawTree (argumentCode c)) := by
      simpa only [heq, argumentCode_theta, ThetaCourse.rawTree_code] using hs
    simpa only [← hsd, value, interpretation_code] using
      first_argument_support_bound q c ⟨a, heq, ha, hn⟩ hf s hsa

def nativeCode (q c : Nat) : Nat := cond (firstBranch q c) (prefixNode q c) (fallback q c)

def predecessorCode (q c : Nat) : Nat := cond (inputCheck q c) (nativeCode q c) 0

theorem predecessor_spec (q c : Nat) (hc : inputCheck q c = true) :
    SourceLocalization.Node q (predecessorCode q c) ∧
      base q ≤ SourceLocalization.value q (predecessorCode q c) ∧
      SourceLocalization.value q (predecessorCode q c) < SourceLocalization.value q c := by
  obtain ⟨hn, hb⟩ := (inputCheck_exact q c).mp hc
  simp only [predecessorCode, hc, Bool.cond_true, nativeCode]
  cases hbcase : firstBranch q c with
  | false => exact fallback_spec q c hn hb
  | true =>
    have he := ((firstBranch_exact q c hn).mp hbcase).1
    have hp := prefix_node q c hn he
    exact ⟨hp, by simpa only [SourceLocalization.baseRaw_value q (node_baseCheck q c hn)] using SourceLocalization.baseRaw_le q _ hp,
      prefix_strict q c hn he⟩

theorem predecessor_branches (q c : Nat) (hc : inputCheck q c = true) :
    (FirstCase q c ∧ predecessorCode q c = prefixNode q c) ∨
      (¬FirstCase q c ∧ predecessorCode q c = fallback q c) := by
  have hn := ((inputCheck_exact q c).mp hc).1
  cases h : firstBranch q c with
  | false =>
    refine Or.inr ⟨?_, by simp only [predecessorCode, hc, nativeCode, h, Bool.cond_true, Bool.cond_false]⟩
    intro hf
    have ht := (firstBranch_exact q c hn).mpr hf
    simp only [h, Bool.false_eq_true] at ht
  | true => exact Or.inl ⟨(firstBranch_exact q c hn).mp h,
      by simp only [predecessorCode, hc, nativeCode, h, Bool.cond_true]⟩

theorem lowWord_primrec : Primrec₂ lowWord :=
  (Decomposition.lowWord_primrec.comp (Primrec.const 0)
    (argumentCode_primrec.comp Primrec.snd)).to₂

theorem highWord_primrec : Primrec₂ highWord :=
  (Decomposition.highWord_primrec.comp (Primrec.const 0)
    (argumentCode_primrec.comp Primrec.snd)).to₂

theorem prefixWord_primrec : Primrec₂ prefixWord :=
  (Primrec.list_append.comp highWord_primrec (stripLast_primrec.comp lowWord_primrec)).to₂

theorem prefixArgument_primrec : Primrec₂ prefixArgument :=
  (Primrec.comp Normalization.Effective.buildAtoms_primrec prefixWord_primrec).to₂

theorem prefixCode_primrec : Primrec₂ prefixCode := code_primrec.comp₂ prefixArgument_primrec

theorem prefixNode_primrec : Primrec₂ prefixNode :=
  (code_primrec.comp (theta_primrec.comp (Primrec.const 0) prefixArgument_primrec)).to₂

theorem lastAtom_primrec : Primrec₂ lastAtom :=
  (Primrec.option_getD.comp (Primrec.list_head?.comp (Primrec.list_reverse.comp lowWord_primrec))
    (Primrec.const Normalization.zeroTree)).to₂

theorem fallback_primrec : Primrec₂ fallback := penultimate_primrec.comp₂ nativePath_primrec

theorem inputCheck_primrec : Primrec₂ inputCheck :=
  (Primrec.and.comp SourceLocalization.inputCheck_primrec
    (Normalization.Effective.lessRawCode_primrec.comp
      (Primrec.fst.pair ((baseRaw_primrec.comp Primrec.fst).pair Primrec.snd)))).to₂

theorem firstBranch_primrec : Primrec₂ firstBranch := by
  have hempty := Primrec.beq.comp (Primrec.list_length.comp lowWord_primrec) (Primrec.const 0)
  have hunit := Normalization.Effective.equalRawCode_primrec.comp
    (Primrec.fst.pair ((code_primrec.comp lastAtom_primrec).pair (unitCode_primrec.comp Primrec.fst)))
  have hstrict := FixedPoint.strictRawCode_primrec.comp
    (Primrec.fst.pair ((Primrec.const 0).pair prefixCode_primrec))
  have hnonempty : Primrec (fun p : Nat × Nat => !(lowWord p.1 p.2).isEmpty) :=
    (Primrec.not.comp hempty).of_eq (fun p => by cases lowWord p.1 p.2 <;> simp)
  exact (Primrec.and.comp hnonempty (Primrec.or.comp hunit hstrict)).to₂

theorem nativeCode_primrec : Primrec₂ nativeCode :=
  (firstBranch_primrec.cond prefixNode_primrec fallback_primrec).to₂

theorem predecessorCode_primrec : Primrec₂ predecessorCode :=
  (inputCheck_primrec.cond nativeCode_primrec (Primrec.const 0)).to₂

def predecessor (q c : Nat) : Part Nat := cond (inputCheck q c) (Part.some (predecessorCode q c)) Part.none

theorem predecessor_partrec : Partrec₂ predecessor :=
  (Partrec.cond inputCheck_primrec.to_comp predecessorCode_primrec.to_comp.partrec Partrec.none).to₂

theorem predecessor_domain (q c : Nat) : (predecessor q c).Dom ↔
    SourceLocalization.Node q c ∧ base q < SourceLocalization.value q c := by
  cases h : inputCheck q c <;> simp [predecessor, h, ← inputCheck_exact]

theorem predecessor_graph (q c d : Nat) : d ∈ predecessor q c ↔
    inputCheck q c = true ∧ d = predecessorCode q c := by
  cases h : inputCheck q c <;> simp [predecessor, h]

theorem predecessor_unique (q c : Nat) (hc : inputCheck q c = true) :
    ∃! d, d ∈ predecessor q c := by
  refine ⟨predecessorCode q c, (predecessor_graph q c _).mpr ⟨hc, rfl⟩, ?_⟩
  intro d hd
  exact ((predecessor_graph q c d).mp hd).2

def graphCheck (q c d : Nat) : Bool := inputCheck q c && (d == predecessorCode q c)

theorem graphCheck_primrec : Primrec (fun p : (Nat × Nat) × Nat => graphCheck p.1.1 p.1.2 p.2) :=
  Primrec.and.comp (inputCheck_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst))
    (Primrec.beq.comp Primrec.snd (predecessorCode_primrec.comp
      (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)))

theorem graphCheck_exact (q c d : Nat) : graphCheck q c d = true ↔ d ∈ predecessor q c := by
  simp only [graphCheck, Bool.and_eq_true, beq_iff_eq, predecessor_graph]

theorem sourcePath_suffix {q : Nat} {source path : List Nat}
    (hp : SourcePath q source path) («prefix» : List Nat) (c : Nat) (tail : List Nat)
    (he : path = «prefix» ++ c :: tail) : SourcePath q source (c :: tail) := by
  revert path
  induction «prefix» with
  | nil => intro path hp he; simpa only [List.nil_append, he] using hp
  | cons a «prefix» ih =>
    intro path hp he
    cases hp with
    | stop d hd hmax =>
      have hlen := congrArg List.length he
      simp only [List.length_singleton, List.length_append, List.length_cons] at hlen
      omega
    | next d e rest hd hde hes harg hrest =>
      have hcons : d :: e :: rest = a :: («prefix» ++ c :: tail) := by
        simpa only [List.cons_append] using he
      exact ih (path := e :: rest) hrest (List.cons.inj hcons).2


private theorem main_last_two (xs : List Nat) (h : 2 ≤ xs.length) :
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

private theorem main_endpoint_append_last (xs : List Nat) (b : Nat) :
    endpoint (xs ++ [b]) = b := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases xs with
    | nil => rfl
    | cons c xs => simpa only [List.cons_append, endpoint] using ih

private theorem fallback_last (q root a b : Nat) (pre : List Nat)
    (he : nativePath q root = pre ++ [a, b]) : fallback q root = a := by
  simp only [fallback, penultimate, he, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append, List.getElem?_cons_succ,
    List.getElem?_cons_zero, Option.getD_some]

private theorem last_value (q root : Nat) (hr : Node q root) (pre : List Nat) (a b : Nat)
    (he : nativePath q root = pre ++ [a, b]) : value q b = value q root := by
  have hi := (SourceLocalization.inputCheck_exact q root).mpr hr
  have hend := nativePath_end q root hi
  have hs : pre ++ [a, b] = (pre ++ [a]) ++ [b] := by
    simp only [List.append_assoc, List.singleton_append]
  simpa only [he, hs, main_endpoint_append_last] using hend

/-- The first branch itself satisfies the actual ordinary selection rule
when started at its constructed predecessor. -/
theorem first_gap_sourcePath (q root : Nat) (hr : Node q root) (hf : FirstCase q root) :
    SourcePath q (support root) [prefixNode q root, root] := by
  have hb := prefix_node q root hr hf.1
  have hbr := prefix_strict q root hr hf.1
  refine SourcePath.next _ _ [] hb hbr (support_root q root hr) ?_
    (SourcePath.stop root hr (fun e he => support_bound q root e hr he))
  intro e he hbe
  have hen := support_node q root e hr he
  have her := support_bound q root e hr he
  have hev : value q e = value q root := by
    apply le_antisymm her
    apply le_of_not_gt
    intro helt
    exact hbe.not_ge (first_support_below_root q root e hr hf he helt)
  exact ((node_value_eq_iff_argument_eq q e root hen hr).mp hev).le

/-- The real final two ordinary selections, with the endpoint replaced only
by its equal-value original root, give the fallback gap path. -/
theorem fallback_gap_sourcePath (q root : Nat) (hr : Node q root)
    (hproper : base q < value q root) :
    SourcePath q (support root) [fallback q root, root] := by
  have hi := (SourceLocalization.inputCheck_exact q root).mpr hr
  obtain ⟨pre, a, b, he⟩ := main_last_two _ (localization_length q root hr hproper)
  have hf := fallback_last q root a b pre he
  have hb := last_value q root hr pre a b he
  have hs := sourcePath_suffix (nativePath_source q root hi) pre a [b]
    (by simpa only [List.singleton_append] using he)
  have hbn := hs.nodes b (by simp)
  have hba := (node_value_eq_iff_argument_eq q b root hbn hr).mp hb
  rw [hf]
  cases hs with
  | next a b tail ha hab hbs harg hrest =>
    refine SourcePath.next a root [] ha (hab.trans_eq hb) (support_root q root hr) ?_
      (SourcePath.stop root hr (fun e he => support_bound q root e hr he))
    intro e he hae
    exact (harg e he hae).trans_eq hba

/-- Both genuine computed branches expose the same real gap-selection law. -/
theorem predecessor_gap_sourcePath (q root : Nat)
    (hi : SourceFinePredecessor.inputCheck q root = true) :
    SourcePath q (support root) [predecessorCode q root, root] := by
  have hr := (SourceFinePredecessor.inputCheck_exact q root).mp hi
  rcases predecessor_branches q root hi with ⟨hf, he⟩ | ⟨hf, he⟩
  · rw [he]; exact first_gap_sourcePath q root hr.1 hf
  · rw [he]; exact fallback_gap_sourcePath q root hr.1 hr.2

/-- No admission, argument, or localization-level comparison is supplied
for the intermediate node beyond its original Node domain and actual gap. -/
theorem predecessor_gap_argument_lt (q root intermediate : Nat)
    (hi : SourceFinePredecessor.inputCheck q root = true) (hm : Node q intermediate)
    (hlo : value q (predecessorCode q root) < value q intermediate)
    (hhi : value q intermediate < value q root) :
    argumentValue q intermediate < argumentValue q root :=
  sourcePath_interval_argument_lt ((SourceFinePredecessor.inputCheck_exact q root).mp hi).1
    (predecessor_gap_sourcePath q root hi) intermediate hm hlo hhi

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceFinePredecessor
