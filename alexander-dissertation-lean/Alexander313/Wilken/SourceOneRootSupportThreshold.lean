import Alexander313.Wilken.SourceOneRootSupportThresholdSupport
import Alexander313.Wilken.SourceCollapseSuccessors

/-!
# Executing original source-one support threshold

The original full written support is filtered by its divided heads.
The genuine source localization maximum is applied to theta-zero wrappers;
their arguments are the original node values, so its actual argument maximum
selects the required VALUE maximum. Original admission supplies every wrapper
caller. No arbitrary ordinal evaluation, maximum or cutoff oracle. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.RootSupportThreshold

open ThetaCourse RootScalar

def argumentHeadCode (c : Nat) : Nat := SourceDecomposition.highCode 0 0 c
def nodeHeadCode (d : Nat) : Nat := argumentHeadCode (Localization.argumentCode d)
noncomputable def nodeHead (d : Nat) : Ordinal.{0} :=
  SourceHighPartComparison.highPart (omegaSequence 1 1)
    (interpretation 0 (Localization.argumentCode d))
def fullCodes (b : Nat) : List Nat := PrincipalSupport.listCode 0 b

theorem argumentHeadCode_primrec : Primrec argumentHeadCode :=
  SourceDecomposition.highCode_primrec.comp ((Primrec.const 0).pair ((Primrec.const 0).pair Primrec.id))
theorem nodeHeadCode_primrec : Primrec nodeHeadCode :=
  argumentHeadCode_primrec.comp Localization.argumentCode_primrec
theorem fullCodes_primrec : Primrec fullCodes :=
  PrincipalSupport.listCode_primrec.comp (Primrec.const 0) Primrec.id

theorem nodeHead_theta (a : RelativeTerm Nat) : nodeHead (.theta 0 a).code = head a := by
  simp only [nodeHead, Localization.argumentCode_theta, interpretation_code, head]

theorem argumentHeadCode_spec (c : Nat) (hc : argumentCheck c = true) :
    argumentCheck (argumentHeadCode c) = true ∧
      interpretation 0 (argumentHeadCode c) =
        SourceHighPartComparison.highPart (omegaSequence 1 1) (interpretation 0 c) :=
  ⟨(SourceDecomposition.parts_accepted 0 0 c hc).1,
    by simpa only [finiteBase_zero] using (SourceDecomposition.parts_code_value 0 0 c hc).1⟩

theorem fullCodes_mem (b d : Nat) (hb : rootCheck b = true) :
    d ∈ fullCodes b ↔ ∃ s ∈ fullList (rawTree b), d = s.code := by
  obtain ⟨a, he, ha, hna, hh⟩ := (rootCheck_exact b).mp hb
  simp only [fullCodes, he, PrincipalSupport.listCode_code, rawTree_code, fullList, List.mem_map]
  constructor
  · rintro ⟨s, hs, he⟩; exact ⟨s, hs, he.symm⟩
  · rintro ⟨s, hs, he⟩; exact ⟨s, hs, he.symm⟩

theorem fullCodes_node (b d : Nat) (hb : rootCheck b = true) (hd : d ∈ fullCodes b) :
    Localization.Node 0 d := by
  obtain ⟨s, hs, rfl⟩ := (fullCodes_mem b d hb).mp hd
  obtain ⟨a, rfl⟩ := RelativeTerm.PrincipalSupport.principalList_shape 0 (rawTree b) s hs
  have ht := SourceDecomposition.input_tree 0 b (root_accepted b hb)
  have hn := PrincipalSupport.principalList_node ht.1 ht.2 hs
  exact ⟨a, rfl, hn.1, hn.2⟩

theorem node_accepted (d : Nat) (hd : Localization.Node 0 d) :
    argumentCheck d = true ∧ argumentCheck (Localization.argumentCode d) = true := by
  obtain ⟨a, rfl, ha, hna⟩ := hd
  exact ⟨(Theta.acceptedCode_iff 0 _).mpr
    ⟨by simpa only [checkCode_code] using ha, by simpa only [rawTree_code] using hna⟩,
    (Theta.acceptedCode_iff 0 _).mpr (Localization.node_argument 0 _ ⟨a, rfl, ha, hna⟩)⟩

def eligible (c d : Nat) : Bool :=
  !Theta.Normalization.lessRawCode 0 (nodeHeadCode d) (argumentHeadCode c)

theorem eligible_primrec : Primrec₂ eligible :=
  (Primrec.not.comp (Theta.Normalization.Effective.lessRawCode_primrec.comp
    ((Primrec.const 0).pair ((nodeHeadCode_primrec.comp Primrec.snd).pair
      (argumentHeadCode_primrec.comp Primrec.fst))))).to₂

theorem eligible_exact (c d : Nat) (hc : argumentCheck c = true)
    (hd : Localization.Node 0 d) : eligible c d = true ↔
    SourceHighPartComparison.highPart (omegaSequence 1 1) (interpretation 0 c) ≤ nodeHead d := by
  have ht := argumentHeadCode_spec c hc
  have hs := argumentHeadCode_spec _ (node_accepted d hd).2
  have he : Theta.Normalization.lessRawCode 0 (nodeHeadCode d) (argumentHeadCode c) = true ↔
      nodeHead d < SourceHighPartComparison.highPart (omegaSequence 1 1) (interpretation 0 c) := by
    simpa only [nodeHeadCode, nodeHead, hs.2, ht.2] using
      Theta.Normalization.lessRawCode_correct 0 (nodeHeadCode d) (argumentHeadCode c)
        ((SourceDecomposition.inputCheck_exact 0 _).mp hs.1).1
        ((SourceDecomposition.inputCheck_exact 0 _).mp ht.1).1
  simp only [eligible, Bool.not_eq_true']
  constructor
  · intro h
    exact le_of_not_gt (fun hv => by
      have hh := he.mpr hv; simp only [h, Bool.false_eq_true] at hh)
  · intro h
    exact Bool.eq_false_of_not_eq_true (fun hv => h.not_gt (he.mp hv))

def select (c : Nat) : List Nat → List Nat
  | [] => []
  | d :: ds => cond (eligible c d) (d :: select c ds) (select c ds)

theorem select_primrec : Primrec₂ select := by
  have hs : Primrec₂ (fun p : Nat × List Nat => fun s : Nat × List Nat =>
      cond (eligible p.1 s.1) (s.1 :: s.2) s.2) :=
    ((eligible_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)).cond
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  have he : (fun p : Nat × List Nat => p.2.foldr
      (fun d ds => cond (eligible p.1 d) (d :: ds) ds) []) = fun p => select p.1 p.2 := by
    funext p
    induction p.2 with
    | nil => rfl
    | cons d ds ih => simp only [List.foldr_cons, select, ih]
  have h := Primrec.list_foldr Primrec.snd (Primrec.const []) hs
  rw [he] at h
  exact h.to₂

theorem select_mem (c d : Nat) (ds : List Nat) :
    d ∈ select c ds ↔ d ∈ ds ∧ eligible c d = true := by
  induction ds with
  | nil => simp only [select, List.not_mem_nil, false_and]
  | cons a ds ih =>
    cases he : eligible c a with
    | false =>
      simp only [select, he, Bool.cond_false, ih, List.mem_cons]
      constructor
      · intro h; exact ⟨Or.inr h.1, h.2⟩
      · rintro ⟨h | h, hd⟩
        · subst d; simp only [he, Bool.false_eq_true] at hd
        · exact ⟨h, hd⟩
    | true =>
      simp only [select, he, Bool.cond_true, List.mem_cons, ih]
      constructor
      · rintro (h | h)
        · subst d; exact ⟨Or.inl rfl, he⟩
        · exact ⟨Or.inr h.1, h.2⟩
      · rintro ⟨h | h, hd⟩
        · exact Or.inl h
        · exact Or.inr ⟨h, hd⟩

def candidates (b c : Nat) : List Nat := select c (fullCodes b)
def wrapperCode (d : Nat) : Nat := nodeCode 0 d
def wrappers (b c : Nat) : List Nat := (candidates b c).map wrapperCode
def selected (b c : Nat) : Option Nat := (Localization.best 0 (wrappers b c)).map Localization.argumentCode

theorem candidates_primrec : Primrec₂ candidates :=
  (select_primrec.comp Primrec.snd (fullCodes_primrec.comp Primrec.fst)).to₂
theorem wrapperCode_primrec : Primrec wrapperCode :=
  BoundedPublicReturn.nodeCode_primrec.comp (Primrec.const 0) Primrec.id
theorem wrappers_primrec : Primrec₂ wrappers :=
  (Primrec.list_map candidates_primrec (wrapperCode_primrec.comp Primrec.snd).to₂).to₂
theorem selected_primrec : Primrec₂ selected :=
  ((Primrec.option_map₁ Localization.argumentCode_primrec).comp
    (Localization.best_primrec.comp (Primrec.const 0) wrappers_primrec)).to₂

theorem wrapper_argument (d : Nat) (hd : argumentCheck d = true) :
    Localization.argumentCode (wrapperCode d) = d := by
  simp only [wrapperCode, nodeCode, BoundedPublicReturn.nodeCode,
    Localization.argumentCode_theta, raw_code d hd]

theorem wrapper_node (d : Nat) (hd : Localization.Node 0 d) : Localization.Node 0 (wrapperCode d) := by
  have ha := (node_accepted d hd).1
  have hl := Localization.node_low 0 d hd
  obtain ⟨t, ht, hlt⟩ := (lowCheckCode_iff 0 d).mp hl
  have hsort : (rawTree d).outerSort ≤ 2 := by
    have hs : t.outerSort ≤ 1 := of_decide_eq_true (Bool.and_eq_true.mp hlt).2
    simpa only [← ht, rawTree_code] using hs.trans (by omega : 1 ≤ 2)
  have hc := (SourceDecomposition.inputCheck_exact 0 _).mp (nodeCode_sorted_spec 0 d ha hsort).1
  exact ⟨rawTree d, rfl, by simpa only [wrapperCode, nodeCode, BoundedPublicReturn.nodeCode,
    checkCode_code] using hc.1,
    by simpa only [wrapperCode, nodeCode, BoundedPublicReturn.nodeCode, rawTree_code] using hc.2⟩

def sortedCheck (c : Nat) : Bool := argumentCheck c && decide ((rawTree c).outerSort ≤ 2)
def inputCheck (b c : Nat) : Bool := rootCheck b &&
  (sortedCheck c && !Theta.Normalization.lessRawCode 0 b (nodeCode 0 c))

theorem sortedCheck_primrec : Primrec sortedCheck := Primrec.and.comp argumentCheck_primrec
  ((Primrec.nat_le.comp (outerSort_primrec.comp rawTree_primrec) (Primrec.const 2)).decide)
theorem sortedCheck_exact (c : Nat) : sortedCheck c = true ↔
    argumentCheck c = true ∧ (rawTree c).outerSort ≤ 2 := by
  simp only [sortedCheck, Bool.and_eq_true, decide_eq_true_eq]
theorem inputCheck_primrec : Primrec₂ inputCheck :=
  (Primrec.and.comp (rootCheck_primrec.comp Primrec.fst)
    (Primrec.and.comp (sortedCheck_primrec.comp Primrec.snd)
      (Primrec.not.comp (Theta.Normalization.Effective.lessRawCode_primrec.comp
        ((Primrec.const 0).pair (Primrec.fst.pair
          (BoundedPublicReturn.nodeCode_primrec.comp (Primrec.const 0) Primrec.snd))))))).to₂

theorem inputCheck_exact (b c : Nat) : inputCheck b c = true ↔
    rootCheck b = true ∧ sortedCheck c = true ∧ interpretation 0 (nodeCode 0 c) ≤ interpretation 0 b := by
  by_cases hb : rootCheck b = true
  · by_cases hc : sortedCheck c = true
    · have harg := (sortedCheck_exact c).mp hc
      have hnode := nodeCode_sorted_spec 0 c harg.1 (by simpa only [Nat.zero_add] using harg.2)
      have he := Theta.Normalization.lessRawCode_correct 0 b (nodeCode 0 c)
        (root_original b hb) ((SourceDecomposition.inputCheck_exact 0 _).mp hnode.1).1
      simp only [inputCheck, hb, hc, Bool.true_and, Bool.not_eq_true', true_and]
      constructor
      · intro h
        exact le_of_not_gt (fun hv => by
          have hh := he.mpr hv; simp only [h, Bool.false_eq_true] at hh)
      · intro h
        exact Bool.eq_false_of_not_eq_true (fun hv => h.not_gt (he.mp hv))
    · simp only [inputCheck, Bool.eq_false_of_not_eq_true hc, Bool.false_and,
        Bool.and_false, Bool.false_eq_true, false_and, and_false]
  · simp only [inputCheck, Bool.eq_false_of_not_eq_true hb, Bool.false_and,
      Bool.false_eq_true, false_and]

theorem requested_theta (c : Nat) (hc : sortedCheck c = true) :
    check 0 (.theta 0 (rawTree c)) = true ∧ Theta.Normal 0 (rawTree c) := by
  have h := (sortedCheck_exact c).mp hc
  have ht := SourceDecomposition.input_tree 0 c h.1
  exact ⟨OmegaQuotient.theta_checked 0 _ ht.1 (by simpa only [Nat.zero_add] using h.2), ht.2⟩

theorem candidates_witness (b c : Nat) (hi : inputCheck b c = true) :
    ∃ d ∈ candidates b c, interpretation 0 (nodeCode 0 c) ≤ interpretation 0 d := by
  have h := (inputCheck_exact b c).mp hi
  obtain ⟨a, he, ha, hna, hh⟩ := (rootCheck_exact b).mp h.1
  have ht := requested_theta c h.2.1
  obtain ⟨v, hv, hvalue, hhead⟩ := support_carries_head a (rawTree c) ha ht.1
    ((Theta.normal_theta 0 0 a).mp hna) ht.2
    (by simpa only [he, nodeCode, BoundedPublicReturn.nodeCode, interpretation_code] using h.2.2)
  have hfull : (.theta 0 v).code ∈ fullCodes b := (fullCodes_mem b _ h.1).mpr
    ⟨.theta 0 v, by simpa only [he, rawTree_code] using hv, rfl⟩
  have hel := (eligible_exact c _ ((sortedCheck_exact c).mp h.2.1).1
    (fullCodes_node b _ h.1 hfull)).mpr (by
      rw [nodeHead_theta, ← raw_value c ((sortedCheck_exact c).mp h.2.1).1]
      exact hhead)
  exact ⟨(.theta 0 v).code, (select_mem c _ (fullCodes b)).mpr ⟨hfull, hel⟩,
    by simpa only [nodeCode, BoundedPublicReturn.nodeCode, interpretation_code] using hvalue⟩

theorem selected_exists (b c : Nat) (hi : inputCheck b c = true) : ∃ d, selected b c = some d := by
  obtain ⟨e, he, hvalue⟩ := candidates_witness b c hi
  cases hs : Localization.best 0 (wrappers b c) with
  | none =>
    have hn := (Localization.best_none 0 (wrappers b c)).mp hs
    have hm : wrapperCode e ∈ wrappers b c := List.mem_map.mpr ⟨e, he, rfl⟩
    rw [hn] at hm
    exact False.elim (List.not_mem_nil hm)
  | some w => exact ⟨Localization.argumentCode w, by simp only [selected, hs, Option.map_some]⟩

theorem selected_spec (b c d : Nat) (hi : inputCheck b c = true) (hs : selected b c = some d) :
    d ∈ fullCodes b ∧ Localization.Node 0 d ∧
      SourceHighPartComparison.highPart (omegaSequence 1 1) (interpretation 0 c) ≤ nodeHead d ∧
      interpretation 0 (nodeCode 0 c) ≤ interpretation 0 d ∧
      (∀ e ∈ fullCodes b, eligible c e = true → interpretation 0 e ≤ interpretation 0 d) := by
  have h := (inputCheck_exact b c).mp hi
  obtain ⟨w, hw, hwd⟩ : ∃ w, Localization.best 0 (wrappers b c) = some w ∧ Localization.argumentCode w = d := by
    cases hh : Localization.best 0 (wrappers b c) with
    | none => simp only [selected, hh, Option.map_none, Option.none_ne_some] at hs
    | some w => exact ⟨w, hh, by simpa only [selected, hh, Option.map_some, Option.some.injEq] using hs⟩
  obtain ⟨e, hem, he⟩ := List.mem_map.mp (Localization.best_mem 0 _ w hw)
  have hefull := ((select_mem c e (fullCodes b)).mp hem).1
  have hen := fullCodes_node b e h.1 hefull
  have hed : e = d := (wrapper_argument e (node_accepted e hen).1).symm.trans
    ((congrArg Localization.argumentCode he).trans hwd)
  subst e
  have hd := (select_mem c d (fullCodes b)).mp hem
  have hnodes : ∀ v ∈ wrappers b c, Localization.Node 0 v := by
    intro v hv
    obtain ⟨e, hem, rfl⟩ := List.mem_map.mp hv
    exact wrapper_node e (fullCodes_node b e h.1 ((select_mem c e (fullCodes b)).mp hem).1)
  have hmax : ∀ e ∈ fullCodes b, eligible c e = true → interpretation 0 e ≤ interpretation 0 d := by
    intro e hef hel
    have hen := fullCodes_node b e h.1 hef
    have hew : wrapperCode e ∈ wrappers b c :=
      List.mem_map.mpr ⟨e, (select_mem c e (fullCodes b)).mpr ⟨hef, hel⟩, rfl⟩
    have hm := Localization.best_maximal 0 _ hnodes w hw (wrapperCode e) hew
    simpa only [Localization.argumentValue, wrapper_argument e (node_accepted e hen).1, hwd] using hm
  obtain ⟨e, hem, hbound⟩ := candidates_witness b c hi
  have hefull := (select_mem c e (fullCodes b)).mp hem
  exact ⟨hd.1, hen, (eligible_exact c d ((sortedCheck_exact c).mp h.2.1).1 hen).mp hd.2,
    hbound.trans (hmax e hefull.1 hefull.2), hmax⟩

theorem selected_value_le_root (b c d : Nat) (hi : inputCheck b c = true)
    (hs : selected b c = some d) : interpretation 0 d ≤ interpretation 0 b := by
  have hb := (inputCheck_exact b c).mp hi
  obtain ⟨s, hmem, hcode⟩ := (fullCodes_mem b d hb.1).mp (selected_spec b c d hi hs).1
  obtain ⟨a, he, ha, hna, hh⟩ := (rootCheck_exact b).mp hb.1
  rw [hcode, interpretation_code, he, interpretation_code]
  apply PrincipalSupport.principalList_theta_value_le 0 a s ha hna
  simpa only [he, rawTree_code] using hmem

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.RootSupportThreshold
