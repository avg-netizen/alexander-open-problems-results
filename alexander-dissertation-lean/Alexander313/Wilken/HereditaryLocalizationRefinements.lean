import Alexander313.Wilken.HereditaryLocalization

/-!
# Argument descent and hereditary localization prefixes

These refinements use the already executing full-depth localization. Equal
theta-zero values determine equal actual arguments by the genuine theta
comparison and argument-star bound. Maximal selection then makes the selected
arguments strictly decrease. Finite descent through literal theta arguments
recovers each earlier selected value inside every later selected node.

Native spellings are allowed to differ: prefix statements compare actual
values and the emitted canonical codes. Semantic source P correspondence
continues to require the stronger SourceNormal convention of the support
module. No fixed-point-level or fine-localization theorem is assumed here.
All proof terms remain uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.Localization.Refinements

open Theta

/-- A real increasing-argument call cannot have an equal or larger predecessor
value. The finite star bound supplies the first comparison branch. -/
theorem theta_strict_of_argument_lt_of_value_le (r : Nat) (a b : RelativeTerm Nat)
    (ha : check r (.theta 0 a) = true) (hb : check r (.theta 0 b) = true)
    (hna : Theta.Normal r (.theta 0 a)) (hnb : Theta.Normal r (.theta 0 b))
    (hab : denote r a < denote r b)
    (hv : denote r (.theta 0 a) ≤ denote r (.theta 0 b)) :
    denote r (.theta 0 a) < denote r (.theta 0 b) := by
  let n := max (.theta 0 a : RelativeTerm Nat).height (.theta 0 b : RelativeTerm Nat).height
  have hat := checked_admissible r n (.theta 0 a) ha (Nat.le_max_left _ _)
  have hbt := checked_admissible r n (.theta 0 b) hb (Nat.le_max_right _ _)
  apply (theta_global_lt_iff_exposed r n 0 a b hat hbt
    ((normal_theta r 0 a).mp hna) ((normal_theta r 0 b).mp hnb)).mpr
  refine Or.inl ⟨hab, ?_⟩
  intro s hs
  exact (PrincipalSupport.principalList_argument_lt r 0 a s ha
    ((normal_theta r 0 a).mp hna)
    (RelativeTerm.PrincipalSupport.exposed_mem_principalList 0 a s hs)).trans_le hv

/-- Same-base admitted theta-zero values have exactly the same actual argument
when their values agree. This does not assert literal syntax uniqueness. -/
theorem node_value_eq_iff_argument_eq (r c d : Nat) (hc : Node r c) (hd : Node r d) :
    value r c = value r d ↔ argumentValue r c = argumentValue r d := by
  obtain ⟨a, rfl, ha, hna⟩ := hc
  obtain ⟨b, rfl, hb, hnb⟩ := hd
  simp only [value, argumentValue, argumentCode_theta, interpretation_code]
  constructor
  · intro he
    rcases lt_trichotomy (denote r a) (denote r b) with hab | hab | hba
    · exact False.elim (he.not_lt
        (theta_strict_of_argument_lt_of_value_le r a b ha hb hna hnb hab he.le))
    · exact hab
    · exact False.elim (he.symm.not_lt
        (theta_strict_of_argument_lt_of_value_le r b a hb ha hnb hna hba he.symm.le))
  · intro he
    change globalCollapse (finiteBase r) 0 (denote r a) =
      globalCollapse (finiteBase r) 0 (denote r b)
    exact congrArg (globalCollapse (finiteBase r) 0) he

theorem sourcePath_tail_mem {r : Nat} {source : List Nat} {c : Nat} {tail : List Nat}
    (hp : SourcePath r source (c :: tail)) : ∀ d ∈ tail, d ∈ source := by
  induction tail generalizing c with
  | nil => intro d hd; exact False.elim (List.not_mem_nil hd)
  | cons d tail ih =>
    cases hp with
    | next c d tail hc hcd hd harg hrest =>
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact hd
      · exact ih hrest e he

theorem sourcePath_head_lt_tail {r : Nat} {source : List Nat} {c : Nat} {tail : List Nat}
    (hp : SourcePath r source (c :: tail)) : ∀ d ∈ tail, value r c < value r d := by
  have hs := List.pairwise_cons.mp hp.strict
  intro d hd
  exact hs.1 _ (List.mem_map.mpr ⟨d, hd, rfl⟩)

/-- The initial base is excluded: every pair of genuinely selected arguments
is in strict reverse order. -/
theorem sourcePath_arguments_descending {r : Nat} {source : List Nat} {c : Nat} {tail : List Nat}
    (hp : SourcePath r source (c :: tail)) :
    (tail.map (argumentValue r)).Pairwise (fun a b => b < a) := by
  induction tail generalizing c with
  | nil => exact List.Pairwise.nil
  | cons d tail ih =>
    cases hp with
    | next c d tail hc hcd hd harg hrest =>
      apply List.pairwise_cons.mpr
      refine ⟨?_, ih hrest⟩
      intro x hx
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
      have hde := sourcePath_head_lt_tail hrest e he
      have heNode := hrest.nodes e (List.mem_cons_of_mem _ he)
      have hdNode := hrest.nodes d List.mem_cons_self
      have hle := harg e (sourcePath_tail_mem hrest e he) (hcd.trans hde)
      apply lt_of_le_of_ne hle
      intro heq
      have hvalue := (node_value_eq_iff_argument_eq r e d heNode hdNode).mpr heq
      exact hvalue.symm.not_lt hde

theorem nativePath_arguments_descending (r c : Nat) (hc : inputCheck r c = true) :
    ((nativePath r c).tail.map (argumentValue r)).Pairwise (fun a b => b < a) := by
  obtain ⟨tail, he⟩ := nativePath_head r c
  have hp := nativePath_source r c hc
  rw [he] at hp ⊢
  simpa only [List.tail_cons] using sourcePath_arguments_descending hp

/-- Full-depth support is hereditary as literal syntax, without a value or
normality hypothesis. -/
theorem principalList_trans {Parameter : Type} (m : Nat) (t s q : RelativeTerm Parameter)
    (hs : s ∈ RelativeTerm.PrincipalSupport.principalList m t)
    (hq : q ∈ RelativeTerm.PrincipalSupport.principalList m s) :
    q ∈ RelativeTerm.PrincipalSupport.principalList m t := by
  revert hs hq
  induction t with
  | parameter p =>
    intro hs hq
    simp only [RelativeTerm.PrincipalSupport.principalList, List.not_mem_nil] at hs
  | sum a b iha ihb =>
    intro hs hq
    rw [RelativeTerm.PrincipalSupport.principalList] at hs ⊢
    rcases List.mem_append.mp hs with hs | hs
    · exact List.mem_append.mpr (Or.inl (iha hs hq))
    · exact List.mem_append.mpr (Or.inr (ihb hs hq))
  | theta k a ih =>
    intro hs hq
    by_cases hmk : m ≤ k
    · by_cases hkm : k = m
      · rw [RelativeTerm.PrincipalSupport.principalList, if_pos hmk, if_pos hkm] at hs ⊢
        rcases List.mem_cons.mp hs with rfl | hs
        · simpa only [RelativeTerm.PrincipalSupport.principalList, if_pos hmk, if_pos hkm] using hq
        · exact List.mem_cons_of_mem _ (ih hs hq)
      · rw [RelativeTerm.PrincipalSupport.principalList, if_pos hmk, if_neg hkm] at hs ⊢
        exact ih hs hq
    · simp only [RelativeTerm.PrincipalSupport.principalList, if_neg hmk, List.not_mem_nil] at hs

theorem support_trans (r c d e : Nat) (hc : Node r c)
    (hd : d ∈ support c) (he : e ∈ support d) : e ∈ support c := by
  obtain ⟨a, rfl, ha, hna⟩ := hc
  rw [support, PrincipalSupport.listCode_code] at hd
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hd
  rw [support, PrincipalSupport.listCode_code] at he ⊢
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp he
  exact List.mem_map.mpr ⟨q, principalList_trans 0 (.theta 0 a) s q hs hq, rfl⟩

/-- Reverse argument order in an increasing pair forces a genuine exposed
node inside the larger value's argument. -/
theorem reversed_argument_witness (r c d : Nat) (hc : Node r c) (hd : Node r d)
    (hv : value r c < value r d) (ha : argumentValue r d ≤ argumentValue r c) :
    ∃ s : RelativeTerm Nat,
      s ∈ PrincipalSupport.principalList 0 (ThetaCourse.rawTree (argumentCode d)) ∧
      value r c ≤ denote r s := by
  obtain ⟨a, rfl, hca, hna⟩ := hc
  obtain ⟨b, rfl, hdb, hnb⟩ := hd
  let n := max (.theta 0 a : RelativeTerm Nat).height (.theta 0 b : RelativeTerm Nat).height
  have hat := checked_admissible r n (.theta 0 a) hca (Nat.le_max_left _ _)
  have hbt := checked_admissible r n (.theta 0 b) hdb (Nat.le_max_right _ _)
  have hcmp := (theta_global_lt_iff_exposed r n 0 a b hat hbt
    ((normal_theta r 0 a).mp hna) ((normal_theta r 0 b).mp hnb)).mp
      (by simpa only [value, interpretation_code] using hv)
  have harg : denote r b ≤ denote r a := by
    simpa only [argumentValue, argumentCode_theta, interpretation_code] using ha
  rcases hcmp with hcmp | ⟨s, hs, hval⟩
  · exact False.elim (harg.not_gt hcmp.1)
  · refine ⟨s, ?_, ?_⟩
    · simpa only [argumentCode_theta, ThetaCourse.rawTree_code] using
        RelativeTerm.PrincipalSupport.exposed_mem_principalList 0 b s hs
    · simpa only [value, interpretation_code] using hval

theorem nested_support_size (r d : Nat) (hd : Node r d) (s : RelativeTerm Nat)
    (hs : s ∈ PrincipalSupport.principalList 0 (ThetaCourse.rawTree (argumentCode d))) :
    s.code ∈ support d ∧ (ThetaCourse.rawTree s.code).size < (ThetaCourse.rawTree d).size := by
  obtain ⟨b, rfl, hb, hnb⟩ := hd
  have hsb : s ∈ PrincipalSupport.principalList 0 b := by
    simpa only [argumentCode_theta, ThetaCourse.rawTree_code] using hs
  constructor
  · rw [support, PrincipalSupport.listCode_code]
    exact List.mem_map.mpr ⟨s, RelativeTerm.PrincipalSupport.principalList_nested 0 b s hsb, rfl⟩
  · simpa only [ThetaCourse.rawTree_code] using
      RelativeTerm.PrincipalSupport.principalList_argument_size_lt 0 0 b s hsb

/-- Finite syntax descent, using only the genuine comparison witness and
maximal actual arguments, recovers the selected value in every larger node.
The output need not retain the selected node's literal spelling. -/
theorem selected_value_in_support (r root c : Nat) (hroot : Node r root) (hc : Node r c)
    (hmax : ∀ d ∈ support root, value r c ≤ value r d → argumentValue r d ≤ argumentValue r c)
    (d : Nat) (hd : d ∈ support root) (hcd : value r c ≤ value r d) :
    ∃ e ∈ support d, value r e = value r c := by
  have hall : ∀ n : Nat, ∀ d : Nat, (ThetaCourse.rawTree d).size = n →
      d ∈ support root → value r c ≤ value r d → ∃ e ∈ support d, value r e = value r c := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro d hsize hd hcd
      have hdn := support_node r root d hroot hd
      by_cases heq : value r c = value r d
      · exact ⟨d, support_root r d hdn, heq.symm⟩
      · have hlt : value r c < value r d := lt_of_le_of_ne hcd heq
        obtain ⟨s, hs, hcs⟩ := reversed_argument_witness r c d hc hdn hlt (hmax d hd hcd)
        have hnest := nested_support_size r d hdn s hs
        have hsr := support_trans r root d s.code hroot hd hnest.1
        have hcsCode : value r c ≤ value r s.code := by
          simpa only [value, interpretation_code] using hcs
        have hsmall : (ThetaCourse.rawTree s.code).size < n := hnest.2.trans_eq hsize
        obtain ⟨e, he, hval⟩ := ih _ hsmall s.code rfl hsr hcsCode
        exact ⟨e, support_trans r d s.code e hdn hnest.1 he, hval⟩
  exact hall _ d rfl hd hcd

/-- Hereditary support for each genuinely selected localization node. -/
theorem sourcePath_selected_support {r root previous c : Nat} {tail : List Nat}
    (hroot : Node r root) (hp : SourcePath r (support root) (previous :: c :: tail)) :
    ∀ d ∈ c :: tail, ∃ e ∈ support d, value r e = value r c := by
  cases hp with
  | next previous c tail hn hpc hcs harg hrest =>
    have hc := hrest.nodes c List.mem_cons_self
    have hmax : ∀ d ∈ support root, value r c ≤ value r d → argumentValue r d ≤ argumentValue r c :=
      fun d hd hcd => harg d hd (hpc.trans_le hcd)
    intro d hd
    have hds : d ∈ support root := by
      rcases List.mem_cons.mp hd with rfl | hd
      · exact hcs
      · exact sourcePath_tail_mem hrest d hd
    exact selected_value_in_support r root c hroot hc hmax d hds (hrest.head_le d hd)

/-- The actual interval clause of source Lemma 2.33(a). The intermediate
theta node may be absent from the original literal support. -/
theorem sourcePath_interval_argument_lt {r root previous d : Nat} {tail : List Nat}
    (hroot : Node r root) (hp : SourcePath r (support root) (previous :: d :: tail))
    (b : Nat) (hb : Node r b) (hpb : value r previous < value r b)
    (hbd : value r b < value r d) : argumentValue r b < argumentValue r d := by
  cases hp with
  | next previous d tail hn hpd hds harg hrest =>
    have hd := hrest.nodes d List.mem_cons_self
    by_contra hnot
    have hdb : argumentValue r d ≤ argumentValue r b := le_of_not_gt hnot
    have hmax : ∀ e ∈ support root, value r b ≤ value r e → argumentValue r e ≤ argumentValue r b :=
      fun e he hbe => (harg e he (hpb.trans_le hbe)).trans hdb
    obtain ⟨e, hed, heb⟩ := selected_value_in_support r root b hroot hb hmax d hds hbd.le
    have hes := support_trans r root d e hroot hds hed
    have hen := support_node r d e hd hed
    have hargument := (node_value_eq_iff_argument_eq r e b hen hb).mp heb
    have hbe : argumentValue r b ≤ argumentValue r d := by
      rw [← hargument]
      apply harg e hes
      rw [heb]
      exact hpb
    have hvalue := (node_value_eq_iff_argument_eq r b d hb hd).mpr (le_antisymm hbe hdb)
    exact hvalue.not_lt hbd

theorem sourcePath_suffix {r : Nat} {source path : List Nat}
    (hp : SourcePath r source path) («prefix» : List Nat) (c : Nat) (tail : List Nat)
    (he : path = «prefix» ++ c :: tail) : SourcePath r source (c :: tail) := by
  revert path
  induction «prefix» with
  | nil => intro path hp he; simpa only [List.nil_append, he] using hp
  | cons a «prefix» ih =>
    intro path hp he
    cases hp with
    | stop d hd hmax =>
      have hlen := congrArg List.length he
      simp only [List.cons_append, List.length_append, List.length_cons, List.length_nil] at hlen
      omega
    | next d e rest hd hde hes harg hrest =>
      have hcons : d :: e :: rest = a :: («prefix» ++ c :: tail) := by
        simpa only [List.cons_append] using he
      exact ih (path := e :: rest) hrest (List.cons.inj hcons).2

theorem nativePath_interval_argument_lt (r root : Nat) (hroot : inputCheck r root = true)
    («prefix» : List Nat) (previous d : Nat) (tail : List Nat)
    (he : nativePath r root = «prefix» ++ previous :: d :: tail)
    (b : Nat) (hb : Node r b) (hpb : value r previous < value r b)
    (hbd : value r b < value r d) : argumentValue r b < argumentValue r d :=
  sourcePath_interval_argument_lt ((inputCheck_exact r root).mp hroot)
    (sourcePath_suffix (nativePath_source r root hroot) «prefix» previous (d :: tail) he) b hb hpb hbd

/-- The source recurrence with membership by actual value. This permits the
genuine support witness to have another native spelling. -/
inductive ValuePath (r : Nat) (source : List Nat) : List Nat → Prop
  | stop (c : Nat) (hc : Node r c) (hmax : ∀ d ∈ source, value r d ≤ value r c) :
      ValuePath r source [c]
  | next (c d : Nat) (tail : List Nat) (hc : Node r c) (hcd : value r c < value r d)
      (hd : ∃ e ∈ source, value r e = value r d)
      (harg : ∀ e ∈ source, value r c < value r e → argumentValue r e ≤ argumentValue r d)
      (hrest : ValuePath r source (d :: tail)) : ValuePath r source (c :: d :: tail)

theorem sourcePath_valuePath {r : Nat} {source path : List Nat}
    (hp : SourcePath r source path) : ValuePath r source path := by
  induction hp with
  | stop c hc hmax => exact ValuePath.stop c hc hmax
  | next c d tail hc hcd hd harg hp ih =>
    exact ValuePath.next c d tail hc hcd ⟨d, hd, rfl⟩ harg ih

theorem ValuePath.nodes {r : Nat} {source path : List Nat} (hp : ValuePath r source path) :
    ∀ c ∈ path, Node r c := by
  induction hp with
  | stop c hc hmax => intro d hd; rw [List.mem_singleton.mp hd]; exact hc
  | next c d tail hc hcd hd harg hp ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact hc
    · exact ih e he

/-- Maximal actual argument determines the entire value path, independently
of ties between native spellings. -/
theorem ValuePath.values_unique {r : Nat} {source : List Nat} {c : Nat} {tail : List Nat}
    (hp : ValuePath r source (c :: tail)) (hs : ∀ e ∈ source, Node r e)
    (d : Nat) (rest : List Nat) (hq : ValuePath r source (d :: rest))
    (he : value r c = value r d) :
    ((c :: tail).map (value r)) = ((d :: rest).map (value r)) := by
  revert d rest
  induction tail generalizing c with
  | nil =>
    cases hp with
    | stop c hc hmax =>
      intro d rest hq he
      cases hq with
      | stop d hd hstop => simp only [List.map_cons, List.map_nil, he]
      | next d f rest hd hdf hf harg hrest =>
        obtain ⟨e, hes, hef⟩ := hf
        have hbound : value r f ≤ value r c := by rw [← hef]; exact hmax e hes
        exact False.elim ((he.trans_lt hdf).not_ge hbound)
  | cons e tail ih =>
    cases hp with
    | next c e tail hc hce heSource harg hrest =>
      intro d rest hq he
      have hen := hrest.nodes e List.mem_cons_self
      cases hq with
      | stop d hd hstop =>
        obtain ⟨a, has, hae⟩ := heSource
        have hbound : value r e ≤ value r d := by rw [← hae]; exact hstop a has
        exact False.elim ((he.symm.trans_lt hce).not_ge hbound)
      | next d f rest hd hdf hfSource hfarg hfrest =>
        have hfn := hfrest.nodes f List.mem_cons_self
        obtain ⟨a, has, hae⟩ := heSource
        obtain ⟨b, hbs, hbf⟩ := hfSource
        have haa := (node_value_eq_iff_argument_eq r a e (hs a has) hen).mp hae
        have hbb := (node_value_eq_iff_argument_eq r b f (hs b hbs) hfn).mp hbf
        have hfe : argumentValue r f ≤ argumentValue r e := by
          rw [← hbb]
          apply harg b hbs
          rw [hbf]
          exact he.trans_lt hdf
        have hef : argumentValue r e ≤ argumentValue r f := by
          rw [← haa]
          apply hfarg a has
          rw [hae]
          exact he.symm.trans_lt hce
        have heValue := (node_value_eq_iff_argument_eq r e f hen hfn).mpr (le_antisymm hef hfe)
        have htail := ih hrest f rest hfrest heValue
        simp only [List.map_cons, he, htail]

/-- Each prefix is the actual source recurrence over its own endpoint's full
support, with membership by value where an earlier spelling differs. -/
theorem sourcePath_prefix_valuePath {r root : Nat} {path : List Nat}
    (hroot : Node r root) (hp : SourcePath r (support root) path)
    («prefix» : List Nat) (d : Nat) (suffix : List Nat) (he : path = «prefix» ++ d :: suffix) :
    ValuePath r (support d) («prefix» ++ [d]) := by
  revert path
  induction «prefix» with
  | nil =>
    intro path hp he
    simp only [List.nil_append] at he ⊢
    rw [he] at hp
    have hd := hp.nodes d List.mem_cons_self
    exact ValuePath.stop d hd (fun e he => support_bound r d e hd he)
  | cons a «prefix» ih =>
    intro path hp he
    cases hp with
    | stop c hc hmax =>
      have hlen := congrArg List.length he
      simp only [List.cons_append, List.length_append, List.length_cons, List.length_nil] at hlen
      omega
    | next c e tail hc hce hes harg hrest =>
      have hcons : c :: e :: tail = a :: («prefix» ++ d :: suffix) := by
        simpa only [List.cons_append] using he
      have hca := (List.cons.inj hcons).1
      subst a
      have htail := (List.cons.inj hcons).2
      have hdTail : d ∈ e :: tail := by
        rw [htail]
        exact List.mem_append.mpr (Or.inr List.mem_cons_self)
      have hdSource := sourcePath_tail_mem
        (SourcePath.next c e tail hc hce hes harg hrest) d hdTail
      have hwitness := sourcePath_selected_support hroot
        (SourcePath.next c e tail hc hce hes harg hrest) d hdTail
      have hprefix := ih (path := e :: tail) hrest htail
      have hhead : ∃ rest : List Nat, «prefix» ++ [d] = e :: rest := by
        cases «prefix» with
        | nil =>
          have hed : e = d := (List.cons.inj htail).1
          rw [← hed]
          exact ⟨[], rfl⟩
        | cons b «prefix» =>
          have heb : e = b := (List.cons.inj htail).1
          rw [← heb]
          exact ⟨«prefix» ++ [d], rfl⟩
      obtain ⟨rest, hhead⟩ := hhead
      rw [hhead] at hprefix
      have hrestricted : ∀ b ∈ support d, value r c < value r b →
          argumentValue r b ≤ argumentValue r e := fun b hb hcb =>
        harg b (support_trans r root d b hroot hdSource hb) hcb
      simpa only [List.cons_append, hhead] using
        ValuePath.next c e rest hc hce hwitness hrestricted hprefix

theorem emit_eq_of_value_eq (r c d : Nat) (hc : Node r c) (hd : Node r d)
    (he : value r c = value r d) : emit r c = emit r d := by
  have hs := emit_spec r c hc
  have ht := emit_spec r d hd
  exact Canonical.check_value_injective _ _ hs.1 ht.1 (hs.2.trans (he.trans ht.2.symm))

theorem emit_map_eq_of_values_eq (r : Nat) (xs ys : List Nat)
    (hx : ∀ c ∈ xs, Node r c) (hy : ∀ c ∈ ys, Node r c)
    (he : xs.map (value r) = ys.map (value r)) : xs.map (emit r) = ys.map (emit r) := by
  revert hx ys
  induction xs with
  | nil =>
    intro ys hx hy he
    cases ys with
    | nil => rfl
    | cons d ys => simp only [List.map_nil, List.map_cons, reduceCtorEq] at he
  | cons c xs ih =>
    intro ys hx hy he
    cases ys with
    | nil => simp only [List.map_nil, List.map_cons, List.cons_ne_nil] at he
    | cons d ys =>
      have hcons := List.cons.inj he
      have hcd := emit_eq_of_value_eq r c d (hx c List.mem_cons_self) (hy d List.mem_cons_self) hcons.1
      have htail := ih ys (fun e he => hx e (List.mem_cons_of_mem _ he))
        (fun e he => hy e (List.mem_cons_of_mem _ he)) hcons.2
      simp only [List.map_cons, hcd, htail]

/-- Source Lemma 2.33(c), for the actual canonical emission of the constructed
localization. The prefix endpoint need not have the root's native spelling. -/
theorem word_prefix (r root : Nat) (hroot : inputCheck r root = true)
    («prefix» : List Nat) (d : Nat) (suffix : List Nat)
    (he : nativePath r root = «prefix» ++ d :: suffix) :
    («prefix» ++ [d]).map (emit r) = word r d := by
  have hrootNode := (inputCheck_exact r root).mp hroot
  have hp := nativePath_source r root hroot
  have hprefix := sourcePath_prefix_valuePath hrootNode hp «prefix» d suffix he
  have hdPath : d ∈ nativePath r root := by
    rw [he]
    exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  have hd := hp.nodes d hdPath
  have hdp := nativePath_source r d ((inputCheck_exact r d).mpr hd)
  obtain ⟨rootTail, hrootHead⟩ := nativePath_head r root
  have hprefixHead : ∃ tail : List Nat, «prefix» ++ [d] = baseRaw r :: tail := by
    cases «prefix» with
    | nil =>
      have hsame : baseRaw r :: rootTail = d :: suffix := by
        simpa only [List.nil_append] using hrootHead.symm.trans he
      rw [← (List.cons.inj hsame).1]
      exact ⟨[], rfl⟩
    | cons c «prefix» =>
      have hsame : baseRaw r :: rootTail = c :: («prefix» ++ d :: suffix) := by
        simpa only [List.cons_append] using hrootHead.symm.trans he
      rw [← (List.cons.inj hsame).1]
      exact ⟨«prefix» ++ [d], rfl⟩
  obtain ⟨prefixTail, hprefixHead⟩ := hprefixHead
  obtain ⟨dTail, hdHead⟩ := nativePath_head r d
  have hvalues : («prefix» ++ [d]).map (value r) = (nativePath r d).map (value r) := by
    rw [hprefixHead] at hprefix
    rw [hdHead] at hdp
    rw [hprefixHead, hdHead]
    exact hprefix.values_unique (fun e he => support_node r d e hd he) _ _
      (sourcePath_valuePath hdp) rfl
  exact emit_map_eq_of_values_eq r _ _ hprefix.nodes hdp.nodes hvalues

theorem endpoint_decomposition (c : Nat) (tail : List Nat) :
    ∃ «prefix» : List Nat, c :: tail = «prefix» ++ [endpoint (c :: tail)] := by
  induction tail generalizing c with
  | nil => exact ⟨[], rfl⟩
  | cons d tail ih =>
    obtain ⟨«prefix», he⟩ := ih d
    exact ⟨c :: «prefix», by simpa only [endpoint, List.cons_append] using congrArg (List.cons c) he⟩

/-- Re-localizing the actual endpoint spelling preserves the whole canonical
word. This particular spelling invariance is derived from the prefix theorem. -/
theorem word_endpoint (r root : Nat) (hroot : inputCheck r root = true) :
    word r (endpoint (nativePath r root)) = word r root := by
  obtain ⟨tail, hhead⟩ := nativePath_head r root
  obtain ⟨«prefix», he⟩ := endpoint_decomposition (baseRaw r) tail
  have hdecomp : nativePath r root = «prefix» ++ [endpoint (nativePath r root)] := by
    rw [hhead]
    exact he
  have hp := word_prefix r root hroot «prefix» (endpoint (nativePath r root)) [] hdecomp
  rw [← hdecomp] at hp
  exact hp.symm

end Alexander313.Wilken.RelativeTerm.Hereditary.Localization.Refinements
