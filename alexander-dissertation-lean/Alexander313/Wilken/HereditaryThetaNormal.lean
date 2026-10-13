import Alexander313.Wilken.HereditaryThetaPrimitive

/-! # Executing recognition of the full hereditary normal domain

Earlier payload normality is checked recursively, and every written sum uses
the source's final-principal convention on the actually opened atoms. The
literal comparator is now genuinely primitive recursive. The resulting test
is exact for recursively normal trees in the unchanged old grammar. It does
not normalize arbitrary admitted trees or assert canonical code uniqueness.
Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.Theta

open ThetaCourse
open Effective
open SourceOne.Comparison.Effective (listAll_primrec)

private theorem normal_list_zero_iff {α : Type} (value : α → Ordinal.{0}) (as : List α)
    (has : IsAdditiveNormalForm (as.map value)) :
    principalSum (as.map value) = 0 ↔ as = [] := by
  cases as with
  | nil => simp [principalSum]
  | cons a as =>
    have ha : 0 < value a := (has.1 _ (List.mem_cons_self)).1
    have hsum : 0 < principalSum ((a :: as).map value) := ha.trans_le le_self_add
    constructor
    · intro hz
      exact False.elim ((ne_of_gt hsum) hz)
    · intro h
      cases h

private theorem list_singleton_of_map_length {α : Type} (as : List α) (h : as.length = 1) :
    ∃ a, as = [a] := by
  cases as with
  | nil => simp at h
  | cons a as =>
    cases as with
    | nil => exact ⟨a, rfl⟩
    | cons b bs => simp at h

private theorem normalSum_iff_lists {α : Type} (value : α → Ordinal.{0}) (as bs : List α)
    (has : IsAdditiveNormalForm (as.map value)) (hbs : IsAdditiveNormalForm (bs.map value)) :
    SourceNormalSum (principalSum (as.map value) + principalSum (bs.map value))
      (principalSum (as.map value)) (principalSum (bs.map value)) ↔
      (as = [] ∧ bs = []) ∨ ∃ b, bs = [b] ∧ ∀ a ∈ as, value b ≤ value a := by
  constructor
  · intro h
    rcases h with hzero | ⟨xs, hxs, hα, hξ⟩
    · exact Or.inl ⟨(normal_list_zero_iff value as has).mp hzero.2.1,
        (normal_list_zero_iff value bs hbs).mp hzero.2.2⟩
    · have hlast := hxs.1 _ (List.mem_append_right _ (List.mem_singleton_self _))
      have heq : bs.map value = [principalSum (bs.map value)] := by
        exact (canonicalANF_eq_of_normal hbs rfl).symm.trans
          (canonicalANF_principal hlast.1 hlast.2)
      have hlength : bs.length = 1 := by
        have h := congrArg List.length heq
        simpa only [List.length_map, List.length_singleton] using h
      obtain ⟨b, hb⟩ := list_singleton_of_map_length bs hlength
      subst bs
      have hsum : SourceNormalSum
          (principalSum (as.map value) + principalSum ([b].map value))
          (principalSum (as.map value)) (principalSum ([b].map value)) :=
        Or.inr ⟨xs, hxs, hα, hξ⟩
      have hconcat := sourceNormalSum_canonical_concat hsum
      rw [canonicalANF_eq_of_normal has rfl, canonicalANF_eq_of_normal hbs rfl] at hconcat
      apply Or.inr
      refine ⟨b, rfl, ?_⟩
      intro a ha
      exact (List.pairwise_append.mp hconcat.2).2.2 _
        (List.mem_map.mpr ⟨a, ha, rfl⟩) _ (by simp)
  · rintro (⟨rfl, rfl⟩ | ⟨b, rfl, hcross⟩)
    · exact Or.inl ⟨by simp [principalSum], rfl, rfl⟩
    · have hconcat : IsAdditiveNormalForm ((as.map value) ++ [value b]) := by
        refine ⟨?_, ?_⟩
        · intro p hp
          rcases List.mem_append.mp hp with hp | hp
          · exact has.1 p hp
          · have he : p = value b := List.mem_singleton.mp hp
            subst p
            exact hbs.1 _ (by simp)
        · apply List.pairwise_append.mpr
          refine ⟨has.2, by simp, ?_⟩
          intro p hp q hq
          obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
          have he : q = value b := List.mem_singleton.mp hq
          subst q
          exact hcross a ha
      refine Or.inr ⟨as.map value, ?_, rfl, ?_⟩
      · simpa only [List.map_cons, List.map_nil, principalSum, add_zero] using hconcat
      · rw [principalSum_append]
        simp [principalSum]

def normalAppend (r : Nat) (as bs : List (RelativeTerm Nat)) : Bool :=
  match bs with
  | [] => as.isEmpty
  | [b] => as.all (fun a => !less r a b)
  | _ => false

private theorem normalAppend_correct (r : Nat) (a b : RelativeTerm Nat)
    (ha : check r a = true) (hb : check r b = true) (hna : Normal r a) (hnb : Normal r b) :
    normalAppend r (atoms r a) (atoms r b) = true ↔
      SourceNormalSum (denote r (.sum a b)) (denote r a) (denote r b) := by
  let n := max (SourceOne.PublicCodes.fragment a) (SourceOne.PublicCodes.fragment b)
  have had := checked_admissible r n a ha
    ((SourceOne.PublicCodes.height_le_fragment a).trans (le_max_left _ _))
  have hbd := checked_admissible r n b hb
    ((SourceOne.PublicCodes.height_le_fragment b).trans (le_max_right _ _))
  have has := atoms_denote_normal r n a had hna
  have hbs := atoms_denote_normal r n b hbd hnb
  have he := normalSum_iff_lists (denote r) (atoms r a) (atoms r b) has hbs
  rw [atoms_denote_sum r n a had hna, atoms_denote_sum r n b hbd hnb] at he
  change normalAppend r (atoms r a) (atoms r b) = true ↔
    SourceNormalSum (denote r a + denote r b) (denote r a) (denote r b)
  rw [he]
  generalize hlist : atoms r b = bs
  cases bs with
  | nil => simp [normalAppend]
  | cons q qs =>
    cases qs with
    | cons p ps => simp [normalAppend]
    | nil =>
      have hq : q ∈ atoms r b := by rw [hlist]; simp
      have hqs := (atoms_spec r n b hbd hnb).1 q hq
      simp only [normalAppend, List.all_eq_true, List.cons_ne_nil,
        false_and, and_false, false_or, List.cons.injEq, and_true,
        exists_eq_left, exists_eq_right, exists_eq_left']
      apply forall_congr'
      intro p
      apply imp_congr_right
      intro hp
      have hps := (atoms_spec r n a had hna).1 p hp
      have hc := less_correct r p q (admitted_checked hps.1) (admitted_checked hqs.1) hps.2 hqs.2
      cases hcmp : less r p q with
      | false =>
        have hnlt : ¬denote r p < denote r q := by
          intro h
          have ht := hc.mpr h
          simp only [hcmp, Bool.false_eq_true] at ht
        simp [hcmp, not_lt.mp hnlt]
      | true =>
        have hlt := hc.mp hcmp
        simp [hcmp, not_le_of_gt hlt]

theorem normal_sum (r : Nat) (a b : RelativeTerm Nat) :
    Normal r (.sum a b) ↔ Normal r a ∧ Normal r b ∧
      SourceNormalSum (denote r (.sum a b)) (denote r a) (denote r b) := by
  cases r with
  | zero => rfl
  | succ r =>
    simp only [Normal, GlobalNormalSums, RelativeTerm.parameters, Finset.mem_union,
      or_imp, forall_and]
    tauto

def normalCheck : Nat → RelativeTerm Nat → Bool
  | 0, .parameter _ => true
  | r + 1, .parameter p => normalCheck r (rawTree p)
  | r, .sum a b => (normalCheck r a && normalCheck r b) && normalAppend r (atoms r a) (atoms r b)
  | r, .theta _ a => normalCheck r a
termination_by r t => expandedSize r t.code
decreasing_by
  · exact parameter_payload_size_lt _ _
  · exact ThetaCourse.sum_left_size_lt _ _ _
  · exact ThetaCourse.sum_right_size_lt _ _ _
  · exact theta_argument_size_lt _ _ _

@[simp] theorem normalCheck_default (r : Nat) : normalCheck r (.parameter 0) = true := by
  induction r with
  | zero => simp only [normalCheck]
  | succ r ih => simpa [normalCheck, rawTree, decode] using ih

theorem normalCheck_correct (r : Nat) (t : RelativeTerm Nat) (ht : check r t = true) :
    normalCheck r t = true ↔ Normal r t := by
  induction r generalizing t with
  | zero =>
    revert ht
    induction t with
    | parameter p => intro ht; simp [normalCheck, Normal, GlobalNormalSums]
    | theta k a ih =>
      intro ht
      have ha := admitted_checked (admitted_theta_argument
        (checked_admissible 0 (SourceOne.PublicCodes.fragment (.theta k a)) _ ht
          (SourceOne.PublicCodes.height_le_fragment _)))
      simpa only [normalCheck, normal_theta] using ih ha
    | sum a b iha ihb =>
      intro ht
      have hs : check 0 a = true ∧ check 0 b = true := by
        simpa only [Uniform.check_sum, Bool.and_eq_true] using ht
      rw [normal_sum]
      constructor
      · intro hc
        have hc' : normalCheck 0 a = true ∧ normalCheck 0 b = true ∧
            normalAppend 0 (atoms 0 a) (atoms 0 b) = true := by
          simpa only [normalCheck, Bool.and_eq_true, and_assoc] using hc
        have hna := (iha hs.1).mp hc'.1
        have hnb := (ihb hs.2).mp hc'.2.1
        exact ⟨hna, hnb, (normalAppend_correct 0 a b hs.1 hs.2 hna hnb).mp hc'.2.2⟩
      · rintro ⟨hna, hnb, hsum⟩
        simp only [normalCheck, (iha hs.1).mpr hna, (ihb hs.2).mpr hnb,
          (normalAppend_correct 0 a b hs.1 hs.2 hna hnb).mpr hsum, Bool.true_and]
  | succ r ihr =>
    revert ht
    induction t with
    | parameter p =>
      intro ht
      simpa only [normalCheck, normal_parameter_succ, rawTree] using
        ihr (rawTree p) (checked_parameter_payload r p ht)
    | theta k a ih =>
      intro ht
      have ha := admitted_checked (admitted_theta_argument
        (checked_admissible (r + 1) (SourceOne.PublicCodes.fragment (.theta k a)) _ ht
          (SourceOne.PublicCodes.height_le_fragment _)))
      simpa only [normalCheck, normal_theta] using ih ha
    | sum a b iha ihb =>
      intro ht
      have hs : check (r + 1) a = true ∧ check (r + 1) b = true := by
        simpa only [Uniform.check_sum, Bool.and_eq_true] using ht
      rw [normal_sum]
      constructor
      · intro hc
        have hc' : normalCheck (r + 1) a = true ∧ normalCheck (r + 1) b = true ∧
            normalAppend (r + 1) (atoms (r + 1) a) (atoms (r + 1) b) = true := by
          simpa only [normalCheck, Bool.and_eq_true, and_assoc] using hc
        have hna := (iha hs.1).mp hc'.1
        have hnb := (ihb hs.2).mp hc'.2.1
        exact ⟨hna, hnb,
          (normalAppend_correct (r + 1) a b hs.1 hs.2 hna hnb).mp hc'.2.2⟩
      · rintro ⟨hna, hnb, hsum⟩
        simp only [normalCheck, (iha hs.1).mpr hna, (ihb hs.2).mpr hnb,
          (normalAppend_correct (r + 1) a b hs.1 hs.2 hna hnb).mpr hsum, Bool.true_and]

namespace Effective

private def appendNumeric (r : Nat) (as bs : List (RelativeTerm Nat)) : Bool :=
  cond (bs.length == 0) (as.length == 0)
    (cond (bs.length == 1) (as.all (fun a => !less r a (bs[0]?.getD (.parameter 0)))) false)

theorem normalAppend_primrec : Primrec
    (fun p : Nat × (List (RelativeTerm Nat) × List (RelativeTerm Nat)) =>
      normalAppend p.1 p.2.1 p.2.2) := by
  have hlen : Primrec (fun p : Nat × (List (RelativeTerm Nat) × List (RelativeTerm Nat)) =>
      p.2.2.length) := Primrec.list_length.comp (Primrec.snd.comp Primrec.snd)
  have hhead : Primrec (fun p : Nat × (List (RelativeTerm Nat) × List (RelativeTerm Nat)) =>
      p.2.2[0]?.getD (.parameter 0)) := Primrec.option_getD.comp
    (Primrec.list_getElem?.comp (Primrec.snd.comp Primrec.snd) (Primrec.const 0))
    (Primrec.const (RelativeTerm.parameter 0 : RelativeTerm Nat))
  have hall : Primrec (fun p : Nat × (List (RelativeTerm Nat) × List (RelativeTerm Nat)) =>
      p.2.1.all (fun a => !less p.1 a (p.2.2[0]?.getD (.parameter 0)))) := by
    have htest : Primrec₂
        (fun p : Nat × (List (RelativeTerm Nat) × List (RelativeTerm Nat)) =>
          fun a : RelativeTerm Nat => !less p.1 a (p.2.2[0]?.getD (.parameter 0))) :=
      (Primrec.not.comp (less_primrec.comp ((Primrec.fst.comp Primrec.fst).pair
        (Primrec.snd.pair (hhead.comp Primrec.fst))))).to₂
    exact (listAll_primrec _ htest).comp Primrec.id (Primrec.fst.comp Primrec.snd)
  have h := (Primrec.beq.comp hlen (Primrec.const 0)).cond
    (Primrec.beq.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd)) (Primrec.const 0))
    ((Primrec.beq.comp hlen (Primrec.const 1)).cond hall (Primrec.const false))
  have heq : (fun p : Nat × (List (RelativeTerm Nat) × List (RelativeTerm Nat)) =>
      appendNumeric p.1 p.2.1 p.2.2) =
      (fun p : Nat × (List (RelativeTerm Nat) × List (RelativeTerm Nat)) =>
        normalAppend p.1 p.2.1 p.2.2) := by
    funext p
    cases p.2.2 with
    | nil => cases p.2.1 <;> rfl
    | cons b bs => cases bs <;> simp [appendNumeric, normalAppend]
  change Primrec (fun p : Nat × (List (RelativeTerm Nat) × List (RelativeTerm Nat)) =>
    appendNumeric p.1 p.2.1 p.2.2) at h
  rw [heq] at h
  exact h

private def normalCourseParameter (_ : Nat × Nat) (p : Nat) (previous : Bool) : Bool :=
  cond (isCode p) previous true

private def sumOp (q : Nat × Nat) (a b : Bool) : Bool :=
  let p := (q.2 - 1).unpair.2
  (a && b) && normalAppend q.1 (atomsCode q.1 p.unpair.1) (atomsCode q.1 p.unpair.2)

private def normalCourseFold : Nat → Nat → Bool :=
  run (fun _ => true) (fun _ _ => true) normalCourseParameter sumOp (fun _ _ a => a)

private theorem normalCourseFold_primrec : Primrec₂ normalCourseFold := by
  have hp : Primrec (fun p : (Nat × Nat) × (Nat × Bool) => normalCourseParameter p.1 p.2.1 p.2.2) :=
    (isCode_primrec.comp (Primrec.fst.comp Primrec.snd)).cond
      (Primrec.snd.comp Primrec.snd) (Primrec.const true)
  have hs : Primrec (fun p : (Nat × Nat) × (Bool × Bool) => sumOp p.1 p.2.1 p.2.2) := by
    have hr : Primrec (fun p : (Nat × Nat) × (Bool × Bool) => p.1.1) :=
      Primrec.fst.comp Primrec.fst
    have hc : Primrec (fun p : (Nat × Nat) × (Bool × Bool) => p.1.2) :=
      Primrec.snd.comp Primrec.fst
    have hpay := Primrec.snd.comp (Primrec.unpair.comp
      (Primrec.nat_sub.comp hc (Primrec.const 1)))
    have hl := atomsCode_primrec.comp hr (Primrec.fst.comp (Primrec.unpair.comp hpay))
    have hh := atomsCode_primrec.comp hr (Primrec.snd.comp (Primrec.unpair.comp hpay))
    exact Primrec.and.comp
      (Primrec.and.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
      (normalAppend_primrec.comp (hr.pair (hl.pair hh)))
  have ht : Primrec (fun p : (Nat × Nat) × (Nat × Bool) => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  exact run_primrec _ _ _ _ _ (Primrec.const true) (Primrec.const true).to₂ hp hs ht

private theorem normalCourseFold_code (r : Nat) (t : RelativeTerm Nat) :
    normalCourseFold r t.code = normalCheck r t := by
  induction r generalizing t with
  | zero =>
    induction t <;>
      simp_all [normalCourseFold, run, code, Nat.unpair_pair, normalCheck, sumOp]
  | succ r ihr =>
    induction t with
    | parameter p =>
      cases hd : decode p with
      | none =>
        have hs := (decode_eq_none_iff p).mp hd
        simp [normalCourseFold, run, code, Nat.unpair_pair, normalCourseParameter, hs, normalCheck, rawTree, hd]
      | some u =>
        have hu := decode_sound p u hd
        have hprevious := ihr u
        simp only [normalCourseFold] at hprevious
        rw [← hu]
        simp [normalCourseFold, run, code, Nat.unpair_pair, normalCourseParameter, normalCheck, rawTree, hprevious]
    | sum a b iha ihb =>
      simp only [normalCourseFold] at iha ihb
      simp [normalCourseFold, run, code, Nat.unpair_pair, iha, ihb, normalCheck, sumOp]
    | theta k a ih =>
      simp only [normalCourseFold] at ih
      simp [normalCourseFold, run, code, Nat.unpair_pair, ih, normalCheck]

theorem normalCheck_primrec : Primrec₂ normalCheck := by
  have h := normalCourseFold_primrec.comp Primrec.fst (code_primrec.comp Primrec.snd)
  simpa only [normalCourseFold_code] using h.to₂

end Effective

def acceptedCode (r c : Nat) : Bool := checkCode r c && normalCheck r (rawTree c)

def acceptedLowCode (r c : Nat) : Bool := lowCheckCode r c && normalCheck r (rawTree c)

theorem acceptedCode_iff (r c : Nat) : acceptedCode r c = true ↔
    checkCode r c = true ∧ Normal r (rawTree c) := by
  simp only [acceptedCode, Bool.and_eq_true]
  constructor
  · rintro ⟨hc, hn⟩
    obtain ⟨t, ht, hcheck⟩ := (checkCode_iff r c).mp hc
    exact ⟨hc, by simpa only [← ht, rawTree_code] using
      (normalCheck_correct r t hcheck).mp (by simpa only [← ht, rawTree_code] using hn)⟩
  · rintro ⟨hc, hn⟩
    obtain ⟨t, ht, hcheck⟩ := (checkCode_iff r c).mp hc
    exact ⟨hc, by simpa only [← ht, rawTree_code] using
      (normalCheck_correct r t hcheck).mpr (by simpa only [← ht, rawTree_code] using hn)⟩

theorem acceptedLowCode_iff (r c : Nat) : acceptedLowCode r c = true ↔
    lowCheckCode r c = true ∧ Normal r (rawTree c) := by
  have hcheck : lowCheckCode r c = true → checkCode r c = true := by
    intro h
    exact (Bool.and_eq_true_iff.mp (by simpa only [lowCheckCode_eq] using h)).1
  simp only [acceptedLowCode, Bool.and_eq_true]
  constructor
  · rintro ⟨hc, hn⟩
    exact ⟨hc, ((acceptedCode_iff r c).mp (Bool.and_eq_true_iff.mpr ⟨hcheck hc, hn⟩)).2⟩
  · rintro ⟨hc, hn⟩
    exact ⟨hc, (Bool.and_eq_true_iff.mp ((acceptedCode_iff r c).mpr ⟨hcheck hc, hn⟩)).2⟩

namespace Effective

theorem acceptedCode_primrec : Primrec₂ acceptedCode :=
  (Primrec.and.comp Uniform.hereditaryCheckCode_primrec
    (normalCheck_primrec.comp Primrec.fst (rawTree_primrec.comp Primrec.snd))).to₂

theorem acceptedLowCode_primrec : Primrec₂ acceptedLowCode :=
  (Primrec.and.comp Uniform.hereditaryLowCheckCode_primrec
    (normalCheck_primrec.comp Primrec.fst (rawTree_primrec.comp Primrec.snd))).to₂

theorem normalCheck_computable : Computable₂ normalCheck := normalCheck_primrec.to_comp

end Effective
end Alexander313.Wilken.RelativeTerm.Hereditary.Theta
