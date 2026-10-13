import Alexander313.Wilken.SourceOneComparison

/-!
# An executing normal-sum recognizer and exact accepted-code comparison

The actual tree comparator checks the ordering of the final principal atom
against the preceding atoms. A zero final summand is allowed only in the
source's all-zero exceptional sum. Recursive checks enforce this literal
source convention at every sum node. Admission still uses the existing
executing source checker. The resulting accepted numerical domain has exact
actual global-denotation equality/order tests; no semantic normality oracle
is supplied to their correctness theorems.

These are total executable Lean functions. Uniform Primrec/Program proofs,
normalization, canonical uniqueness and coverage by normal codes remain
unfinished and are not inferred from this recognizer.
-/

namespace Alexander313.Wilken.RelativeTerm.SourceOne.Comparison

private theorem normal_list_zero_iff {α : Type} (value : α → Ordinal.{0}) (as : List α)
    (has : IsAdditiveNormalForm (as.map value)) :
    principalSum (as.map value) = 0 ↔ as = [] := by
  cases as with
  | nil => simp [principalSum]
  | cons a as =>
    have ha : 0 < value a := (has.1 _ (List.mem_cons_self)).1
    have hsum : 0 < principalSum ((a :: as).map value) := ha.trans_le le_self_add
    have hsum' : 0 < principalSum (value a :: as.map value) := hsum
    simp [ne_of_gt hsum']

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

def normalAppend (as bs : List (RelativeTerm Nat)) : Bool :=
  match bs with
  | [] => as.isEmpty
  | [b] => as.all (fun a => !less a b)
  | _ => false

private theorem normalAppend_correct (n : Nat) (a b : RelativeTerm Nat)
    (ha : admissible n a) (hb : admissible n b) (hna : Normal n a) (hnb : Normal n b) :
    normalAppend (thetaAtoms a) (thetaAtoms b) = true ↔
      SourceNormalSum (denote n (.sum a b)) (denote n a) (denote n b) := by
  have has := thetaAtoms_denote_normal n a ha hna
  have hbs := thetaAtoms_denote_normal n b hb hnb
  have he := normalSum_iff_lists (denote n) (thetaAtoms a) (thetaAtoms b) has hbs
  rw [thetaAtoms_denote_sum n a ha hna, thetaAtoms_denote_sum n b hb hnb] at he
  change normalAppend (thetaAtoms a) (thetaAtoms b) = true ↔
    SourceNormalSum (denote n a + denote n b) (denote n a) (denote n b)
  rw [he]
  generalize hlist : thetaAtoms b = bs
  cases bs with
  | nil => simp [normalAppend]
  | cons q qs =>
    cases qs with
    | cons r rs => simp [normalAppend]
    | nil =>
      have hq : q ∈ thetaAtoms b := by rw [hlist]; simp
      have hqad := hb.thetaAtoms hq
      have hqn := NormalSums.thetaAtoms hnb hq
      simp only [normalAppend, List.all_eq_true, List.cons_ne_nil,
        false_and, and_false, false_or, List.cons.injEq, and_true,
        exists_eq_left, exists_eq_left', exists_eq_right]
      apply forall_congr'
      intro p
      apply imp_congr_right
      intro hp
      have hc := less_correct n p q (ha.thetaAtoms hp) hqad (NormalSums.thetaAtoms hna hp) hqn
      cases hcmp : less p q with
      | false =>
        have hnlt : ¬denote n p < denote n q := by
          intro h
          have ht := hc.mpr h
          simp only [hcmp, Bool.false_eq_true] at ht
        simp [hcmp, not_lt.mp hnlt]
      | true =>
        have hlt := hc.mp hcmp
        simp [hcmp, not_le_of_gt hlt]

def normalCheck : RelativeTerm Nat → Bool
  | .parameter _ => true
  | .theta _ a => normalCheck a
  | .sum a b => (normalCheck a && normalCheck b) && normalAppend (thetaAtoms a) (thetaAtoms b)

theorem normalCheck_correct (n : Nat) (t : RelativeTerm Nat) (ht : admissible n t) :
    normalCheck t = true ↔ Normal n t := by
  induction ht with
  | parameter hp => simp [normalCheck, Normal, NormalSums]
  | @theta k a h0k hkn hsort ha ih =>
    simpa only [normalCheck, Normal, NormalSums] using ih
  | @sum a b ha hb iha ihb =>
    constructor
    · intro hc
      have hs : normalCheck a = true ∧ normalCheck b = true ∧
          normalAppend (thetaAtoms a) (thetaAtoms b) = true := by
        simpa only [normalCheck, Bool.and_eq_true, and_assoc] using hc
      have hna := iha.mp hs.1
      have hnb := ihb.mp hs.2.1
      exact ⟨hna, hnb, (normalAppend_correct n a b ha hb hna hnb).mp hs.2.2⟩
    · intro hn
      have hc := (normalAppend_correct n a b ha hb hn.1 hn.2.1).mpr hn.2.2
      simp only [normalCheck, iha.mpr hn.1, ihb.mpr hn.2.1, hc, Bool.true_and]

theorem normal_transfer (n n' : Nat) (t : RelativeTerm Nat)
    (ht : admissible n t) (ht' : admissible n' t) (hn : Normal n t) : Normal n' t := by
  have value_eq (s : RelativeTerm Nat) (hs : admissible n s) (hs' : admissible n' s) :
      denote n s = denote n' s :=
    (PublicCodes.denote_eq_finite n s hs).symm.trans (PublicCodes.denote_eq_finite n' s hs')
  revert ht' hn
  induction ht with
  | parameter hp => intro _ _; trivial
  | @theta k a h0k hkn hsort ha ih =>
    intro ht' hn
    cases ht' with
    | theta h0k' hkn' hsort' ha' => exact ih ha' hn
  | @sum a b ha hb iha ihb =>
    intro ht' hn
    cases ht' with
    | sum ha' hb' =>
      refine ⟨iha ha' hn.1, ihb hb' hn.2.1, ?_⟩
      have hsum : SourceNormalSum (denote n (.sum a b)) (denote n a) (denote n b) := hn.2.2
      rw [value_eq (.sum a b) (.sum ha hb) (.sum ha' hb'),
        value_eq a ha ha', value_eq b hb hb'] at hsum
      exact hsum

def acceptedCode (c : Nat) : Bool :=
  PublicCodes.checkCode c && normalCheck ((RelativeTerm.decode c).getD (.parameter 0))

@[simp] theorem acceptedCode_code (t : RelativeTerm Nat) :
    acceptedCode t.code = (PublicCodes.check t && normalCheck t) := by
  simp only [acceptedCode, PublicCodes.checkCode_code, RelativeTerm.decode_code, Option.getD_some]

theorem acceptedCode_iff (c : Nat) : acceptedCode c = true ↔
    ∃ t : RelativeTerm Nat, t.code = c ∧ PublicCodes.check t = true ∧ Normal (PublicCodes.fragment t) t := by
  constructor
  · intro hc
    have hs := Bool.and_eq_true_iff.mp hc
    obtain ⟨t, ht, ha⟩ := (PublicCodes.checkCode_iff c).mp hs.1
    refine ⟨t, ht, ha, ?_⟩
    have hnormal : normalCheck t = true := by
      simpa only [← ht, RelativeTerm.decode_code, Option.getD_some] using hs.2
    exact (normalCheck_correct _ t ((check_iff _ t).mp ha)).mp hnormal
  · rintro ⟨t, rfl, ha, hn⟩
    rw [acceptedCode_code, Bool.and_eq_true]
    exact ⟨ha, (normalCheck_correct _ t ((check_iff _ t).mp ha)).mpr hn⟩

private theorem accepted_pair (c d : Nat) (hc : acceptedCode c = true) (hd : acceptedCode d = true) :
    ∃ (n : Nat) (t u : RelativeTerm Nat), t.code = c ∧ u.code = d ∧ admissible n t ∧ admissible n u ∧
      Normal n t ∧ Normal n u := by
  obtain ⟨t, htc, ht, hnt⟩ := (acceptedCode_iff c).mp hc
  obtain ⟨u, hud, hu, hnu⟩ := (acceptedCode_iff d).mp hd
  let n := max (PublicCodes.fragment t) (PublicCodes.fragment u)
  have htold := (check_iff (PublicCodes.fragment t) t).mp ht
  have huold := (check_iff (PublicCodes.fragment u) u).mp hu
  have htnew : admissible n t := (check_iff n t).mp
    (PublicCodes.check_transfer (PublicCodes.fragment t) t ht n
      ((PublicCodes.height_le_fragment t).trans (le_max_left _ _)))
  have hunew : admissible n u := (check_iff n u).mp
    (PublicCodes.check_transfer (PublicCodes.fragment u) u hu n
      ((PublicCodes.height_le_fragment u).trans (le_max_right _ _)))
  exact ⟨n, t, u, htc, hud, htnew, hunew,
    normal_transfer _ n t htold htnew hnt, normal_transfer _ n u huold hunew hnu⟩

theorem lessCode_correct (c d : Nat) (hc : acceptedCode c = true) (hd : acceptedCode d = true) :
    lessCode c d = true ↔ PublicCodes.interpretation c < PublicCodes.interpretation d := by
  obtain ⟨n, t, u, rfl, rfl, ht, hu, hnt, hnu⟩ := accepted_pair c d hc hd
  rw [lessCode_code, PublicCodes.interpretation_code, PublicCodes.interpretation_code]
  exact less_global_correct n t u ht hu hnt hnu

theorem equalCode_correct (c d : Nat) (hc : acceptedCode c = true) (hd : acceptedCode d = true) :
    equalCode c d = true ↔ PublicCodes.interpretation c = PublicCodes.interpretation d := by
  obtain ⟨n, t, u, rfl, rfl, ht, hu, hnt, hnu⟩ := accepted_pair c d hc hd
  rw [equalCode_code, PublicCodes.interpretation_code, PublicCodes.interpretation_code]
  exact equal_global_correct n t u ht hu hnt hnu

end Alexander313.Wilken.RelativeTerm.SourceOne.Comparison
