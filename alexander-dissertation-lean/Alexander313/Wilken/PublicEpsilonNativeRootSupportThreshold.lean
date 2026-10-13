import Alexander313.Wilken.PublicEpsilonNativeRootSupportThresholdSupport

/-!
# A finite maximal original support threshold

The actual original high root and checked Normal requested theta argument
derive a nonempty list of its written zero-index support nodes carrying at
least the requested divided head. A primitive-recursive comparison fold
selects a greatest VALUE, using the real native comparator. Its successor
argument lies strictly above the original root: otherwise genuine support
descent would produce a larger eligible written node. The endpoint is a
derived original successor interval, not an assumed localization cutoff.
No relative-collapse identity or full HIGH return fold is claimed here.
Source-only, uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RootSupportThreshold

open ThetaCourse

def argumentHeadCode (c : Nat) : Nat := Decomposition.highCode 0 c

theorem argumentHeadCode_primrec : Primrec argumentHeadCode :=
  Decomposition.highCode_primrec.comp (Primrec.const 0) Primrec.id

def nodeHeadCode (d : Nat) : Nat := argumentHeadCode (Localization.argumentCode d)

theorem nodeHeadCode_primrec : Primrec nodeHeadCode :=
  argumentHeadCode_primrec.comp Localization.argumentCode_primrec

noncomputable def nodeHead (q d : Nat) : Ordinal.{0} :=
  SourceHighPartComparison.highPart (omegaSequence (base q) 1)
    (interpretation q (Localization.argumentCode d))

theorem nodeHead_theta (q : Nat) (a : RelativeTerm Nat) :
    nodeHead q (.theta 0 a).code = head q a := by
  simp only [nodeHead, Localization.argumentCode_theta, interpretation_code, head]

theorem argumentHeadCode_spec (q c : Nat) (hc : Comparison.acceptedCode q c = true) :
    Comparison.acceptedCode q (argumentHeadCode c) = true ∧
      interpretation q (argumentHeadCode c) =
        SourceHighPartComparison.highPart (omegaSequence (base q) 1) (interpretation q c) :=
  ⟨(Decomposition.parts_accepted q 0 c hc).1, (Decomposition.parts_code_value q 0 c hc).1⟩

def fullCodes (b : Nat) : List Nat := PrincipalSupport.listCode 0 b

theorem fullCodes_primrec : Primrec fullCodes :=
  PrincipalSupport.listCode_primrec.comp (Primrec.const 0) Primrec.id

theorem fullCodes_mem (q b d : Nat) (hb : RootLowCollapse.rootCheck q b = true) :
    d ∈ fullCodes b ↔ ∃ s ∈ Iota.fullList (rawTree b), d = s.code := by
  obtain ⟨a, he, ha, hna, hh⟩ := (RootLowCollapse.rootCheck_exact q b).mp hb
  simp only [fullCodes, he, PrincipalSupport.listCode_code, rawTree_code, List.mem_map]
  constructor
  · rintro ⟨s, hs, hsCode⟩; exact ⟨s, hs, hsCode.symm⟩
  · rintro ⟨s, hs, hsCode⟩; exact ⟨s, hs, hsCode.symm⟩

/-- Every retained code has its actual original theta shape, checker and
weak Normality, including every hidden zero-index argument. -/
theorem fullCodes_node (q b d : Nat) (hb : RootLowCollapse.rootCheck q b = true)
    (hd : d ∈ fullCodes b) :
    ∃ a : RelativeTerm Nat, d = (.theta 0 a).code ∧
      check q (.theta 0 a) = true ∧ Comparison.Normal q a := by
  obtain ⟨s, hs, rfl⟩ := (fullCodes_mem q b d hb).mp hd
  obtain ⟨a, rfl⟩ := RelativeTerm.PrincipalSupport.principalList_shape 0 (rawTree b) s hs
  have hroot := (RootLowCollapse.rootCheck_exact q b).mp hb
  have ht : check q (rawTree b) = true := by
    obtain ⟨a, he, ha, hna, hh⟩ := hroot
    simpa only [he, rawTree_code] using ha
  have hn : Comparison.Normal q (rawTree b) := by
    obtain ⟨a, he, ha, hna, hh⟩ := hroot
    simpa only [he, rawTree_code, Comparison.Normal] using hna
  exact ⟨a, rfl, Iota.checked_full_node q _ _ ht hs, normal_full_node q _ _ hn hs⟩

theorem node_accepted (q d : Nat)
    (hd : ∃ a : RelativeTerm Nat, d = (.theta 0 a).code ∧
      check q (.theta 0 a) = true ∧ Comparison.Normal q a) :
    Comparison.acceptedCode q d = true ∧
      Comparison.acceptedCode q (Localization.argumentCode d) = true := by
  obtain ⟨a, rfl, ha, hna⟩ := hd
  constructor
  · exact (Comparison.acceptedCode_exact q _).mpr
      ⟨by simpa only [checkCode_code] using ha,
        by simpa only [rawTree_code, Comparison.Normal] using hna⟩
  · exact DirectZeta.argument_input q _
      ((DirectZeta.inputCheck_exact q _).mpr ⟨a, rfl, ha, hna⟩)

def eligible (q c d : Nat) : Bool :=
  !Normalization.lessRawCode q (nodeHeadCode d) (argumentHeadCode c)

theorem eligible_primrec : Primrec (fun p : Nat × (Nat × Nat) => eligible p.1 p.2.1 p.2.2) :=
  Primrec.not.comp (Normalization.Effective.lessRawCode_primrec.comp
    (Primrec.fst.pair ((nodeHeadCode_primrec.comp (Primrec.snd.comp Primrec.snd)).pair
      (argumentHeadCode_primrec.comp (Primrec.fst.comp Primrec.snd)))))

theorem eligible_exact (q c d : Nat) (hc : Comparison.acceptedCode q c = true)
    (hd : ∃ a : RelativeTerm Nat, d = (.theta 0 a).code ∧
      check q (.theta 0 a) = true ∧ Comparison.Normal q a) :
    eligible q c d = true ↔
      SourceHighPartComparison.highPart (omegaSequence (base q) 1) (interpretation q c) ≤ nodeHead q d := by
  have ht := argumentHeadCode_spec q c hc
  have hs := argumentHeadCode_spec q _ (node_accepted q d hd).2
  have he : Normalization.lessRawCode q (nodeHeadCode d) (argumentHeadCode c) = true ↔
      nodeHead q d < SourceHighPartComparison.highPart (omegaSequence (base q) 1) (interpretation q c) := by
    simpa only [nodeHeadCode, nodeHead, ((Comparison.acceptedCode_exact q _).mp hs.1).1,
      ((Comparison.acceptedCode_exact q _).mp ht.1).1, hs.2, ht.2, true_and] using
      Normalization.lessRawCode_exact q (nodeHeadCode d) (argumentHeadCode c)
  simp only [eligible, Bool.not_eq_true']
  constructor
  · intro h
    exact le_of_not_gt (fun hv => by
      have hh := he.mpr hv
      simp only [h, Bool.false_eq_true] at hh)
  · intro h
    exact Bool.eq_false_of_not_eq_true (fun hv => h.not_gt (he.mp hv))

def select (q c : Nat) : List Nat → List Nat
  | [] => []
  | d :: ds => cond (eligible q c d) (d :: select q c ds) (select q c ds)

theorem select_primrec : Primrec (fun p : Nat × (Nat × List Nat) => select p.1 p.2.1 p.2.2) := by
  have hq := Primrec.fst.comp Primrec.fst
  have hc := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hd := Primrec.fst.comp Primrec.snd
  have htail := Primrec.snd.comp Primrec.snd
  have ht := eligible_primrec.comp (hq.pair (hc.pair hd))
  have hstep : Primrec₂ (fun (p : Nat × (Nat × List Nat)) (s : Nat × List Nat) =>
      cond (eligible p.1 p.2.1 s.1) (s.1 :: s.2) s.2) :=
    (Primrec.cond ht (Primrec.list_cons.comp hd htail) htail).to₂
  have h := Primrec.list_foldr (Primrec.snd.comp Primrec.snd) (Primrec.const []) hstep
  have he : (fun p : Nat × (Nat × List Nat) =>
      p.2.2.foldr (fun d ds => cond (eligible p.1 p.2.1 d) (d :: ds) ds) []) =
      fun p => select p.1 p.2.1 p.2.2 := by
    funext p
    induction p.2.2 with
    | nil => rfl
    | cons d ds ih => simp only [List.foldr_cons, select, ih]
  rw [he] at h
  exact h

theorem select_mem (q c d : Nat) (ds : List Nat) :
    d ∈ select q c ds ↔ d ∈ ds ∧ eligible q c d = true := by
  induction ds with
  | nil => simp only [select, List.not_mem_nil, false_and]
  | cons a ds ih =>
    cases he : eligible q c a with
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

def candidates (q b c : Nat) : List Nat := select q c (fullCodes b)

theorem candidates_primrec : Primrec (fun p : Nat × (Nat × Nat) => candidates p.1 p.2.1 p.2.2) :=
  select_primrec.comp (Primrec.fst.pair ((Primrec.snd.comp Primrec.snd).pair
    (fullCodes_primrec.comp (Primrec.fst.comp Primrec.snd))))

def choose (q d : Nat) (tail : Option Nat) : Option Nat :=
  match tail with
  | none => some d
  | some e => some (cond (Normalization.lessRawCode q e d) d e)

theorem choose_primrec : Primrec (fun p : Nat × (Nat × Option Nat) => choose p.1 p.2.1 p.2.2) := by
  have ho := Primrec.snd.comp Primrec.snd
  have hd := Primrec.fst.comp Primrec.snd
  have hq := Primrec.fst.comp Primrec.fst
  have hcan := hd.comp Primrec.fst
  have ht := Normalization.Effective.lessRawCode_primrec.comp (hq.pair (Primrec.snd.pair hcan))
  exact Primrec.option_casesOn ho (Primrec.option_some.comp hd)
    (Primrec.option_some.comp (Primrec.cond ht hcan Primrec.snd)).to₂

def best (q : Nat) : List Nat → Option Nat
  | [] => none
  | d :: ds => choose q d (best q ds)

theorem best_primrec : Primrec₂ best := by
  have hs : Primrec₂ (fun (p : Nat × List Nat) (s : Nat × Option Nat) => choose p.1 s.1 s.2) :=
    (choose_primrec.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂
  have h := Primrec.list_foldr Primrec.snd (Primrec.const none) hs
  have he : (fun p : Nat × List Nat => p.2.foldr (fun d o => choose p.1 d o) none) =
      fun p => best p.1 p.2 := by
    funext p
    induction p.2 with
    | nil => rfl
    | cons d ds ih => simp only [List.foldr_cons, best, ih]
  rw [he] at h
  exact h.to₂

theorem best_none (q : Nat) (ds : List Nat) : best q ds = none ↔ ds = [] := by
  cases ds with
  | nil => simp only [best]
  | cons d ds => cases best q ds <;>
      simp only [best, choose, Option.some_ne_none, List.cons_ne_nil]

theorem best_mem (q : Nat) (ds : List Nat) (d : Nat) (hd : best q ds = some d) : d ∈ ds := by
  induction ds with
  | nil => simp only [best, Option.none_ne_some] at hd
  | cons a ds ih =>
    cases ht : best q ds with
    | none =>
      have he : a = d := by simpa only [best, ht, choose, Option.some.injEq] using hd
      rw [← he]; exact List.mem_cons_self
    | some e =>
      cases hl : Normalization.lessRawCode q e a with
      | false =>
        have he : e = d := by simpa only [best, ht, choose, hl, Bool.cond_false, Option.some.injEq] using hd
        rw [← he]; exact List.mem_cons_of_mem _ (ih ht)
      | true =>
        have he : a = d := by simpa only [best, ht, choose, hl, Bool.cond_true, Option.some.injEq] using hd
        rw [← he]; exact List.mem_cons_self

theorem best_maximal (q : Nat) (ds : List Nat) (hs : ∀ e ∈ ds, checkCode q e = true)
    (d : Nat) (hd : best q ds = some d) : ∀ e ∈ ds, interpretation q e ≤ interpretation q d := by
  revert hs d hd
  induction ds with
  | nil => intro hs d hd; simp only [best, Option.none_ne_some] at hd
  | cons a ds ih =>
    intro hs d hd
    have ha := hs a List.mem_cons_self
    have htail := fun e he => hs e (List.mem_cons_of_mem _ he)
    cases ht : best q ds with
    | none =>
      have hnil := (best_none q ds).mp ht
      subst ds
      have he : a = d := by simpa only [best, choose, Option.some.injEq] using hd
      subst d
      intro e he
      rw [List.mem_singleton.mp he]
    | some f =>
      have hf := htail f (best_mem q ds f ht)
      have hm := ih htail f ht
      cases hl : Normalization.lessRawCode q f a with
      | false =>
        have he : f = d := by simpa only [best, ht, choose, hl, Bool.cond_false, Option.some.injEq] using hd
        subst d
        have hab : interpretation q a ≤ interpretation q f := le_of_not_gt (fun hv => by
          have hh := (Normalization.lessRawCode_exact q f a).mpr ⟨hf, ha, hv⟩
          simp only [hl, Bool.false_eq_true] at hh)
        intro e he
        rcases List.mem_cons.mp he with rfl | he
        · exact hab
        · exact hm e he
      | true =>
        have he : a = d := by simpa only [best, ht, choose, hl, Bool.cond_true, Option.some.injEq] using hd
        subst d
        have hfa := ((Normalization.lessRawCode_exact q f a).mp hl).2.2
        intro e he
        rcases List.mem_cons.mp he with rfl | he
        · exact le_rfl
        · exact (hm e he).trans hfa.le

def selected (q b c : Nat) : Option Nat := best q (candidates q b c)

theorem selected_primrec : Primrec (fun p : Nat × (Nat × Nat) => selected p.1 p.2.1 p.2.2) :=
  best_primrec.comp Primrec.fst candidates_primrec

def inputCheck (q b c : Nat) : Bool := RootLowCollapse.rootCheck q b &&
  (RootAboveHeadCollapse.argumentCheck q c &&
    !Normalization.lessRawCode q b (OmegaPowers.thetaCode c))

theorem inputCheck_primrec : Primrec (fun p : Nat × (Nat × Nat) => inputCheck p.1 p.2.1 p.2.2) :=
  Primrec.and.comp (RootLowCollapse.rootCheck_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
    (Primrec.and.comp
      (RootAboveHeadCollapse.argumentCheck_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd))
      (Primrec.not.comp (Normalization.Effective.lessRawCode_primrec.comp
        (Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair
          (OmegaPowers.thetaCode_primrec.comp (Primrec.snd.comp Primrec.snd)))))))

theorem requested_theta (q c : Nat) (hc : RootAboveHeadCollapse.argumentCheck q c = true) :
    check q (.theta 0 (rawTree c)) = true ∧ Comparison.Normal q (rawTree c) := by
  have ha := (RootAboveHeadCollapse.argumentCheck_exact q c).mp hc
  have ht := (Comparison.acceptedCode_exact q c).mp ha.1
  exact ⟨SourceChi.Powers.checked_theta_zero q _ (Arithmetic.raw_checked q c ht.1)
    (by rw [Arithmetic.raw_value q c ht.1]; exact RootAboveHeadCollapse.argument_sorted q c hc), ht.2⟩

theorem inputCheck_exact (q b c : Nat) : inputCheck q b c = true ↔
    RootLowCollapse.rootCheck q b = true ∧ RootAboveHeadCollapse.argumentCheck q c = true ∧
      interpretation q (OmegaPowers.thetaCode c) ≤ interpretation q b := by
  by_cases hb : RootLowCollapse.rootCheck q b = true
  · by_cases hc : RootAboveHeadCollapse.argumentCheck q c = true
    · have hroot := (RootLowCollapse.rootCheck_exact q b).mp hb
      have hqb : checkCode q b = true := by
        obtain ⟨a, he, ha, hna, hh⟩ := hroot
        simpa only [he, checkCode_code] using ha
      have ht := RootEndpointCollapse.thetaCode_sorted_spec q c
        ((RootAboveHeadCollapse.argumentCheck_exact q c).mp hc).1
        (RootAboveHeadCollapse.argument_sorted q c hc)
      have hqt := ((Comparison.acceptedCode_exact q _).mp ht.2.1).1
      have he : Normalization.lessRawCode q b (OmegaPowers.thetaCode c) = true ↔
          interpretation q b < interpretation q (OmegaPowers.thetaCode c) := by
        simpa only [hqb, hqt, true_and] using Normalization.lessRawCode_exact q b (OmegaPowers.thetaCode c)
      simp only [inputCheck, hb, hc, Bool.true_and, Bool.not_eq_true', true_and]
      constructor
      · intro h
        exact le_of_not_gt (fun hv => by
          have hh := he.mpr hv
          simp only [h, Bool.false_eq_true] at hh)
      · intro h
        exact Bool.eq_false_of_not_eq_true (fun hv => h.not_gt (he.mp hv))
    · have hfalse := Bool.eq_false_of_not_eq_true hc
      simp only [inputCheck, hfalse, Bool.false_and, Bool.and_false, Bool.false_eq_true,
        false_and]
  · have hfalse := Bool.eq_false_of_not_eq_true hb
    simp only [inputCheck, hfalse, Bool.false_and, Bool.false_eq_true, false_and]

/-- Real support descent produces an eligible original code above the
requested collapse; the finite list is consequently nonempty. -/
theorem candidates_witness (q b c : Nat) (hi : inputCheck q b c = true) :
    ∃ d ∈ candidates q b c, interpretation q (OmegaPowers.thetaCode c) ≤ interpretation q d := by
  have h := (inputCheck_exact q b c).mp hi
  obtain ⟨a, he, ha, hna, hh⟩ := (RootLowCollapse.rootCheck_exact q b).mp h.1
  have ht := requested_theta q c h.2.1
  obtain ⟨v, hv, hvalue, hhead⟩ := support_carries_head q a (rawTree c) ha ht.1 hna ht.2
    (by simpa only [he, OmegaPowers.thetaCode, interpretation_code] using h.2.2)
  have hfull : (.theta 0 v).code ∈ fullCodes b := (fullCodes_mem q b _ h.1).mpr
    ⟨.theta 0 v, by simpa only [he, rawTree_code] using hv, rfl⟩
  have hn := fullCodes_node q b _ h.1 hfull
  have hel : eligible q c (.theta 0 v).code = true :=
    (eligible_exact q c _ ((RootAboveHeadCollapse.argumentCheck_exact q c).mp h.2.1).1 hn).mpr (by
      rw [nodeHead_theta, ← Arithmetic.raw_value q c
        ((Comparison.acceptedCode_exact q c).mp
          ((RootAboveHeadCollapse.argumentCheck_exact q c).mp h.2.1).1).1]
      exact hhead)
  exact ⟨(.theta 0 v).code, (select_mem q c _ (fullCodes b)).mpr ⟨hfull, hel⟩,
    by simpa only [OmegaPowers.thetaCode, interpretation_code] using hvalue⟩

theorem selected_exists (q b c : Nat) (hi : inputCheck q b c = true) :
    ∃ d, selected q b c = some d := by
  obtain ⟨e, he, hbound⟩ := candidates_witness q b c hi
  cases hs : selected q b c with
  | none =>
    have hnil := (best_none q (candidates q b c)).mp hs
    rw [hnil] at he
    exact False.elim (List.not_mem_nil he)
  | some d => exact ⟨d, rfl⟩

theorem selected_spec (q b c d : Nat) (hi : inputCheck q b c = true)
    (hs : selected q b c = some d) :
    d ∈ fullCodes b ∧
      (∃ a : RelativeTerm Nat, d = (.theta 0 a).code ∧
        check q (.theta 0 a) = true ∧ Comparison.Normal q a) ∧
      SourceHighPartComparison.highPart (omegaSequence (base q) 1) (interpretation q c) ≤ nodeHead q d ∧
      interpretation q (OmegaPowers.thetaCode c) ≤ interpretation q d ∧
      (∀ e ∈ fullCodes b, eligible q c e = true → interpretation q e ≤ interpretation q d) := by
  have h := (inputCheck_exact q b c).mp hi
  have hmem := best_mem q (candidates q b c) d hs
  have hd := (select_mem q c d (fullCodes b)).mp hmem
  have hnodes : ∀ e ∈ candidates q b c, checkCode q e = true := by
    intro e he
    have hfull := ((select_mem q c e (fullCodes b)).mp he).1
    exact ((Comparison.acceptedCode_exact q e).mp
      (node_accepted q e (fullCodes_node q b e h.1 hfull)).1).1
  have hmax := best_maximal q (candidates q b c) hnodes d hs
  have hdn := fullCodes_node q b d h.1 hd.1
  obtain ⟨e, he, hv⟩ := candidates_witness q b c hi
  exact ⟨hd.1, hdn,
    (eligible_exact q c d ((RootAboveHeadCollapse.argumentCheck_exact q c).mp h.2.1).1 hdn).mp hd.2,
    hv.trans (hmax e he), fun e he hel => hmax e
      ((select_mem q c e (fullCodes b)).mpr ⟨he, hel⟩)⟩

def successorCode (q d : Nat) : Nat := OmegaPowers.thetaCode
  (Arithmetic.addCode q (Localization.argumentCode d) (OmegaPowerHeight.numeralCode 1))

theorem successorCode_primrec : Primrec₂ successorCode :=
  (OmegaPowers.thetaCode_primrec.comp (Arithmetic.addCode_primrec.comp
    (Primrec.fst.pair ((Localization.argumentCode_primrec.comp Primrec.snd).pair
      (Primrec.const (OmegaPowerHeight.numeralCode 1)))))).to₂

/-- An actual original successor-argument term is constructed and checked.
Its divided head is unchanged and its real collapse value strictly grows. -/
theorem successorCode_spec (q d : Nat)
    (hd : ∃ a : RelativeTerm Nat, d = (.theta 0 a).code ∧
      check q (.theta 0 a) = true ∧ Comparison.Normal q a) :
    lowCheckCode q (successorCode q d) = true ∧
      (∃ a : RelativeTerm Nat, successorCode q d = (.theta 0 a).code ∧
        check q (.theta 0 a) = true ∧ Comparison.Normal q a) ∧
      nodeHead q (successorCode q d) = nodeHead q d ∧
      interpretation q d < interpretation q (successorCode q d) := by
  have han := (node_accepted q d hd).2
  have hac := ((Comparison.acceptedCode_exact q _).mp han).1
  obtain ⟨a, rfl, ha, hna⟩ := hd
  have hq := (Bool.and_eq_true.mp ha).1
  have hab := FixedPoint.checked_theta_sort q 0 a ha
  have hu := OmegaPowerHeight.numeralCode_spec q 1 hq
  have hs := Arithmetic.addCode_spec q _ _ hac
    ((Comparison.acceptedCode_exact q _).mp hu.2.1).1
  let r := Arithmetic.addCode q (Localization.argumentCode (.theta 0 a).code) (OmegaPowerHeight.numeralCode 1)
  have hr : interpretation q r = denote q a + 1 := by
    simpa only [r, Localization.argumentCode_theta, interpretation_code, hu.2.2.1, Nat.cast_one] using hs.2.1
  have hsorted : interpretation q r < omegaSequence (base q) 2 := by
    rw [hr]; exact (omegaSequence_isSuccLimit (base q) 1).add_one_lt hab
  have ht := RootEndpointCollapse.thetaCode_sorted_spec q r hs.1 hsorted
  have hrc := ((Comparison.acceptedCode_exact q r).mp hs.1).1
  have htheta := SourceChi.Powers.checked_theta_zero q (rawTree r)
    (Arithmetic.raw_checked q r hrc) (by rw [Arithmetic.raw_value q r hrc]; exact hsorted)
  have hhead : nodeHead q (OmegaPowers.thetaCode r) = nodeHead q (.theta 0 a).code := by
    simp only [nodeHead, OmegaPowers.thetaCode, Localization.argumentCode_theta, interpretation_code]
    rw [Arithmetic.raw_value q r hrc, hr]
    exact highPart_successor q (denote q a)
  have hg := SourceCollapseSuccessors.global_collapse_lt_successor (base q) (base_pos q hq) 0
    ⟨denote q a, FixedPoint.checked_notation_at q a (FixedPoint.checked_theta_argument q 0 a ha) 1⟩ hab
  refine ⟨ht.1, ⟨rawTree r, rfl, htheta, ((Comparison.acceptedCode_exact q r).mp hs.1).2⟩,
    hhead, ?_⟩
  change denote q (.theta 0 a) < interpretation q (OmegaPowers.thetaCode r)
  rw [ht.2.2, hr]
  exact hg

/-- The real finite maximum encloses the ORIGINAL root in its genuine
successor-argument interval. No support cutoff is supplied as a premise. -/
theorem selected_interval (q b c d : Nat) (hi : inputCheck q b c = true)
    (hs : selected q b c = some d) :
    d ∈ fullCodes b ∧ lowCheckCode q d = true ∧ Comparison.acceptedCode q d = true ∧
      SourceHighPartComparison.highPart (omegaSequence (base q) 1) (interpretation q c) ≤ nodeHead q d ∧
      interpretation q (OmegaPowers.thetaCode c) ≤ interpretation q d ∧
      interpretation q d ≤ interpretation q b ∧ interpretation q b < interpretation q (successorCode q d) := by
  have h := (inputCheck_exact q b c).mp hi
  have hd := selected_spec q b c d hi hs
  have had := (node_accepted q d hd.2.1).1
  have hlow : lowCheckCode q d = true := by
    obtain ⟨v, he, hv, hnv⟩ := hd.2.1
    simp only [he, lowCheckCode_code, lowCheck, hv, RelativeTerm.outerSort, decide_true, Bool.true_and]
  obtain ⟨a, he, ha, hna, hh⟩ := (RootLowCollapse.rootCheck_exact q b).mp h.1
  have hdle : interpretation q d ≤ interpretation q b := by
    obtain ⟨s, hmem, hcode⟩ := (fullCodes_mem q b d h.1).mp hd.1
    rw [hcode, interpretation_code, he, interpretation_code]
    apply Iota.Inverse.fullList_value_le_low q (.theta 0 a) s ha hna (by simp only [RelativeTerm.outerSort]; omega)
    simpa only [he, rawTree_code] using hmem
  have hsuccessor := successorCode_spec q d hd.2.1
  have hupper : interpretation q b < interpretation q (successorCode q d) := by
    by_contra hn
    have hle : interpretation q (successorCode q d) ≤ interpretation q b := le_of_not_gt hn
    obtain ⟨u, heu, hu, hnu⟩ := hsuccessor.2.1
    obtain ⟨v, hv, hvalue, hhead⟩ := support_carries_head q a u ha hu hna hnu
      (by simpa only [heu, he, interpretation_code] using hle)
    have hfull : (.theta 0 v).code ∈ fullCodes b := (fullCodes_mem q b _ h.1).mpr
      ⟨.theta 0 v, by simpa only [he, rawTree_code] using hv, rfl⟩
    have hel : eligible q c (.theta 0 v).code = true :=
      (eligible_exact q c _ ((RootAboveHeadCollapse.argumentCheck_exact q c).mp h.2.1).1
        (fullCodes_node q b _ h.1 hfull)).mpr (by
        have huu : head q u = nodeHead q d := by
          rw [← nodeHead_theta q u, ← heu]; exact hsuccessor.2.2.1
        rw [nodeHead_theta]
        exact hd.2.2.1.trans (huu ▸ hhead))
    have hmax := hd.2.2.2.2 (.theta 0 v).code hfull hel
    have hvs : interpretation q (successorCode q d) ≤ interpretation q (.theta 0 v).code := by
      simpa only [heu, interpretation_code] using hvalue
    exact hsuccessor.2.2.2.not_ge (hvs.trans hmax)
  exact ⟨hd.1, hlow, had, hd.2.2.1, hd.2.2.2.1, hdle, hupper⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RootSupportThreshold
