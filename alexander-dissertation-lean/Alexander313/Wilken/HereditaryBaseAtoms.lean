import Alexander313.Wilken.TerminalPrincipalArithmetic
import Alexander313.Wilken.SourceOneNormalizationPrimitive

/-! # Concrete principal words across finite hereditary bases

A bottom atom is an actual positive principal from the old checked base-one
grammar. Every higher atom is the actual finite base itself. Their ranges are
disjoint and ordered by level. Thus literal token comparison combines the
constructed base-one comparator with actual finite-base separation. Finite
suffix absorption and lexicographic comparison preserve genuine ordinal
denotation. These words do not represent arbitrary later-base theta terms.
No epsilon membership or semantic comparison oracle is an input. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.BaseAtoms

abbrev Atom := Nat × Nat
abbrev Word := List Atom

noncomputable def value (a : Atom) : Ordinal.{0} :=
  if a.1 = 0 then SourceOne.PublicCodes.interpretation a.2 else finiteBase a.1

def Good (a : Atom) : Prop :=
  if a.1 = 0 then SourceOne.PublicCodes.checkCode a.2 = true ∧
    0 < value a ∧ Ordinal.IsPrincipal (· + ·) (value a) ∧ value a < finiteBase 1
  else a.2 = 0

def GoodWord (as : Word) : Prop := ∀ a ∈ as, Good a

theorem bases_strictMono : StrictMono finiteBase := strictMono_nat_of_lt_succ finiteBase_step

theorem good_pos {a : Atom} (ha : Good a) : 0 < value a := by
  by_cases h : a.1 = 0
  · have hh : SourceOne.PublicCodes.checkCode a.2 = true ∧
        0 < value a ∧ Ordinal.IsPrincipal (· + ·) (value a) ∧ value a < finiteBase 1 := by
      simpa only [Good, if_pos h] using ha
    exact hh.2.1
  · simpa only [value, if_neg h] using finiteBase_pos a.1

theorem good_principal {a : Atom} (ha : Good a) : Ordinal.IsPrincipal (· + ·) (value a) := by
  by_cases h : a.1 = 0
  · have hh : SourceOne.PublicCodes.checkCode a.2 = true ∧
        0 < value a ∧ Ordinal.IsPrincipal (· + ·) (value a) ∧ value a < finiteBase 1 := by
      simpa only [Good, if_pos h] using ha
    exact hh.2.2.1
  · simpa only [value, if_neg h] using finiteBase_add_closed a.1

theorem good_lt_next {a : Atom} (ha : Good a) : value a < finiteBase (a.1 + 1) := by
  by_cases h : a.1 = 0
  · have hh : SourceOne.PublicCodes.checkCode a.2 = true ∧
        0 < value a ∧ Ordinal.IsPrincipal (· + ·) (value a) ∧ value a < finiteBase 1 := by
      simpa only [Good, if_pos h] using ha
    simpa only [h, zero_add] using hh.2.2.2
  · simpa only [value, if_neg h] using finiteBase_step a.1

theorem value_lt_of_level_lt {a b : Atom} (ha : Good a) (h : a.1 < b.1) : value a < value b := by
  have hb0 : b.1 ≠ 0 := by omega
  have hbv : value b = finiteBase b.1 := by simp only [value, if_neg hb0]
  rw [hbv]
  exact (good_lt_next ha).trans_le (bases_strictMono.monotone (Nat.succ_le_of_lt h))

def less (a b : Atom) : Bool :=
  cond ((a.1 == 0) && (b.1 == 0))
    (SourceOne.Normalization.lessRawCode a.2 b.2) (decide (a.1 < b.1))

theorem less_primrec : Primrec₂ less := by
  have ha : Primrec (fun p : Atom × Atom => p.1.1) := Primrec.fst.comp Primrec.fst
  have hb : Primrec (fun p : Atom × Atom => p.2.1) := Primrec.fst.comp Primrec.snd
  have hzero := Primrec.and.comp (Primrec.beq.comp ha (Primrec.const 0))
    (Primrec.beq.comp hb (Primrec.const 0))
  exact (hzero.cond (SourceOne.Normalization.Effective.lessRawCode_primrec.comp
    (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
    (Primrec.nat_lt.comp ha hb).decide).to₂

theorem less_correct (a b : Atom) (ha : Good a) (hb : Good b) :
    less a b = true ↔ value a < value b := by
  by_cases ha0 : a.1 = 0
  · by_cases hb0 : b.1 = 0
    · have hac : SourceOne.PublicCodes.checkCode a.2 = true := by
        have hh : SourceOne.PublicCodes.checkCode a.2 = true ∧
            0 < value a ∧ Ordinal.IsPrincipal (· + ·) (value a) ∧ value a < finiteBase 1 := by
          simpa only [Good, if_pos ha0] using ha
        exact hh.1
      have hbc : SourceOne.PublicCodes.checkCode b.2 = true := by
        have hh : SourceOne.PublicCodes.checkCode b.2 = true ∧
            0 < value b ∧ Ordinal.IsPrincipal (· + ·) (value b) ∧ value b < finiteBase 1 := by
          simpa only [Good, if_pos hb0] using hb
        exact hh.1
      simpa [less, value, ha0, hb0] using SourceOne.Normalization.lessRawCode_correct a.2 b.2 hac hbc
    · have hl : a.1 < b.1 := by omega
      simp [less, ha0, hb0, hl, value_lt_of_level_lt ha hl]
      omega
  · by_cases hb0 : b.1 = 0
    · have hl : b.1 < a.1 := by omega
      simp [less, ha0, hb0, not_lt_of_gt hl, not_lt_of_gt (value_lt_of_level_lt hb hl)]
    · simp only [less, value, if_neg ha0, if_neg hb0]
      simp only [show (a.1 == 0) = false from by simp [ha0], Bool.false_and,
        Bool.cond_false, decide_eq_true_eq]
      constructor
      · exact fun h => bases_strictMono h
      · intro h
        by_contra hn
        exact h.not_ge (bases_strictMono.monotone (le_of_not_gt hn))

def prepend (a : Atom) : Word → Word
  | [] => [a]
  | b :: bs => cond (less a b) (b :: bs) (a :: b :: bs)

def normalize : Word → Word
  | [] => []
  | a :: as => prepend a (normalize as)

theorem prepend_mem (a p : Atom) (as : Word) (hp : p ∈ prepend a as) : p = a ∨ p ∈ as := by
  cases as with
  | nil => simpa [prepend] using hp
  | cons b bs =>
    cases h : less a b
    · simpa [prepend, h] using hp
    · exact Or.inr (by simpa [prepend, h] using hp)

theorem normalize_mem (p : Atom) (as : Word) (hp : p ∈ normalize as) : p ∈ as := by
  revert hp
  induction as with
  | nil => simp [normalize]
  | cons a as ih =>
    intro hp
    rcases prepend_mem a p _ hp with rfl | hp
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih hp)

theorem GoodWord.append {as bs : Word} (ha : GoodWord as) (hb : GoodWord bs) : GoodWord (as ++ bs) := by
  intro a h
  rcases List.mem_append.mp h with h | h
  · exact ha a h
  · exact hb a h

theorem GoodWord.normalize {as : Word} (ha : GoodWord as) : GoodWord (normalize as) :=
  fun a h => ha a (normalize_mem a as h)

private theorem prepend_map (a : Atom) (as : Word) (ha : Good a) (has : GoodWord as) :
    (prepend a as).map value = prependPrincipal (value a) (as.map value) := by
  cases as with
  | nil => rfl
  | cons b bs =>
    have hb := has b (List.mem_cons_self)
    have hc := less_correct a b ha hb
    cases h : less a b with
    | false =>
      have hn : ¬value a < value b := by
        intro hlt
        have ht := hc.mpr hlt
        simp only [h, Bool.false_eq_true] at ht
      simp [prepend, prependPrincipal, h, hn]
    | true => simp [prepend, prependPrincipal, h, hc.mp h]

theorem normalize_map (as : Word) (ha : GoodWord as) :
    (normalize as).map value = normalizePrincipal (as.map value) := by
  revert ha
  induction as with
  | nil => intro ha; rfl
  | cons a as ih =>
    intro ha
    have hhead := ha a (List.mem_cons_self)
    have htail : GoodWord as := fun b hb => ha b (List.mem_cons_of_mem _ hb)
    rw [normalize, prepend_map a _ hhead htail.normalize, ih htail]
    rfl

theorem normalize_normal (as : Word) (ha : GoodWord as) :
    IsAdditiveNormalForm ((normalize as).map value) := by
  rw [normalize_map as ha]
  apply normalizePrincipal_normal
  intro ξ hξ
  obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hξ
  exact ⟨good_pos (ha a ha'), good_principal (ha a ha')⟩

theorem normalize_value (as : Word) (ha : GoodWord as) :
    principalSum ((normalize as).map value) = principalSum (as.map value) := by
  rw [normalize_map as ha]
  apply principalSum_normalizePrincipal
  intro ξ hξ
  obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hξ
  exact ⟨good_pos (ha a ha'), good_principal (ha a ha')⟩

private def prependNumeric (a : Atom) (as : Word) : Word :=
  cond (as.length == 0) [a] (cond (less a (as[0]?.getD (0, 0))) as (a :: as))

theorem prepend_primrec : Primrec₂ prepend := by
  have hh : Primrec (fun p : Atom × Word => p.2[0]?.getD (0, 0)) := Primrec.option_getD.comp
    (Primrec.list_getElem?.comp Primrec.snd (Primrec.const 0)) (Primrec.const (0, 0))
  have h : Primrec (fun p : Atom × Word => prependNumeric p.1 p.2) := (Primrec.beq.comp (Primrec.list_length.comp Primrec.snd) (Primrec.const 0)).cond
    (Primrec.list_cons.comp Primrec.fst (Primrec.const []))
    ((less_primrec.comp Primrec.fst hh).cond Primrec.snd
      (Primrec.list_cons.comp Primrec.fst Primrec.snd))
  have heq : (fun p : Atom × Word => prependNumeric p.1 p.2) =
      (fun p : Atom × Word => prepend p.1 p.2) := by
    funext p
    cases p.2 <;> simp [prependNumeric, prepend]
  change Primrec (fun p : Atom × Word => prependNumeric p.1 p.2) at h
  rw [heq] at h
  exact h.to₂

theorem normalize_primrec : Primrec normalize := by
  have hs : Primrec₂ (fun (_ : Word) => fun p : Atom × Word => prepend p.1 p.2) :=
    (prepend_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  have h := Primrec.list_foldr Primrec.id (Primrec.const []) hs
  have heq : (fun as : Word => as.foldr prepend []) = normalize := by
    funext as
    induction as <;> simp_all [normalize]
  exact h.of_eq (fun a => congrFun heq a)

private theorem add_lt_add_left_iff (a b c : Ordinal.{0}) : a + b < a + c ↔ b < c := by
  constructor
  · intro h
    by_contra hn
    exact h.not_ge (add_le_add_right (le_of_not_gt hn) a)
  · intro h
    exact lt_of_le_of_ne (add_le_add_right h.le a) (fun he => h.ne (add_left_cancel he))

private theorem bool_not_true (b : Bool) : ((!b) = true) ↔ ¬ (b = true) := by
  cases b <;> decide

theorem lex_correct (as bs : Word) (ha : GoodWord as) (hb : GoodWord bs)
    (hna : IsAdditiveNormalForm (as.map value)) (hnb : IsAdditiveNormalForm (bs.map value)) :
    SourceOne.Comparison.lexLT less as bs = true ↔
      principalSum (as.map value) < principalSum (bs.map value) := by
  revert bs ha hb hna hnb
  induction as with
  | nil =>
    intro bs ha hb hna hnb
    cases bs with
    | nil => simp [SourceOne.Comparison.lexLT, principalSum]
    | cons b bs =>
      have hpos : 0 < principalSum ((b :: bs).map value) :=
        (good_pos (hb b (List.mem_cons_self))).trans_le le_self_add
      simpa [SourceOne.Comparison.lexLT, principalSum] using hpos
  | cons a as ih =>
    intro bs ha hb hna hnb
    cases bs with
    | nil => simp [SourceOne.Comparison.lexLT, principalSum]
    | cons b bs =>
      have hhead := less_correct a b (ha a (List.mem_cons_self)) (hb b (List.mem_cons_self))
      have hreverse := less_correct b a (hb b (List.mem_cons_self)) (ha a (List.mem_cons_self))
      have htail := ih bs (fun x hx => ha x (List.mem_cons_of_mem _ hx))
        (fun y hy => hb y (List.mem_cons_of_mem _ hy))
        (additiveNormalForm_tail hna) (additiveNormalForm_tail hnb)
      simp only [SourceOne.Comparison.lexLT, Bool.or_eq_true, Bool.and_eq_true,
        bool_not_true, hhead, hreverse, htail]
      rcases lt_trichotomy (value a) (value b) with hab | hab | hba
      · have hless : principalSum ((a :: as).map value) < value b := by
          apply principalSum_lt (good_pos (hb b (List.mem_cons_self)))
            (good_principal (hb b (List.mem_cons_self)))
          intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · exact hab
          · exact (additiveNormalForm_head_ge hna hp).trans_lt hab
        have hsum := hless.trans_le (le_self_add : value b ≤ principalSum ((b :: bs).map value))
        simp only [List.map_cons, principalSum] at hsum
        simp only [hab, true_or, true_iff]
        exact hsum
      · simp only [hab, lt_self_iff_false, not_false_eq_true, false_or, true_and,
          List.map_cons, principalSum]
        exact (add_lt_add_left_iff (value b) (principalSum (as.map value))
          (principalSum (bs.map value))).symm
      · have hless : principalSum ((b :: bs).map value) < value a := by
          apply principalSum_lt (good_pos (ha a (List.mem_cons_self)))
            (good_principal (ha a (List.mem_cons_self)))
          intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · exact hba
          · exact (additiveNormalForm_head_ge hnb hp).trans_lt hba
        have hsum := hless.trans_le (le_self_add : value a ≤ principalSum ((a :: as).map value))
        have hn := not_lt_of_gt hsum
        simp only [List.map_cons, principalSum] at hn
        simp [hba, not_lt_of_gt hba, List.map_cons, principalSum, hn]

def wordLess (as bs : Word) : Bool :=
  SourceOne.Comparison.lexLT less (normalize as) (normalize bs)

theorem wordLess_primrec : Primrec₂ wordLess := by
  have h := SourceOne.Comparison.Effective.lexLT_primrec (0, 0) (fun (_ : Unit) => less)
    (less_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
  exact (h.comp ((Primrec.const ()).pair
    ((normalize_primrec.comp Primrec.fst).pair (normalize_primrec.comp Primrec.snd)))).to₂

theorem wordLess_correct (as bs : Word) (ha : GoodWord as) (hb : GoodWord bs) :
    wordLess as bs = true ↔ principalSum (as.map value) < principalSum (bs.map value) := by
  have h := lex_correct (normalize as) (normalize bs) ha.normalize hb.normalize
    (normalize_normal as ha) (normalize_normal bs hb)
  simpa only [wordLess, normalize_value as ha, normalize_value bs hb] using h

def baseTree (c : Nat) : RelativeTerm Nat :=
  SourceOne.Normalization.normalize ((decode c).getD (.parameter 0))

def baseWord (c : Nat) : Word := (thetaAtoms (baseTree c)).map (fun t => (0, t.code))

theorem baseWord_primrec : Primrec baseWord := by
  have ht := SourceOne.Normalization.Effective.normalize_primrec.comp
    (Primrec.option_getD.comp decode_primrec (Primrec.const (.parameter 0)))
  have hlist := SourceOne.Comparison.Effective.thetaAtoms_primrec.comp ht
  have he : Primrec₂ (fun (_ : Nat) => fun t : RelativeTerm Nat => (0, t.code)) :=
    ((Primrec.const 0).pair (code_primrec.comp Primrec.snd)).to₂
  exact Primrec.list_map hlist he

/-- Bottom-level words are constructed from the actual normalizer and old
    exact source admission. All their atoms have real principal denotations. -/
theorem baseWord_spec (c : Nat) (hc : SourceOne.PublicCodes.lowCheckCode c = true) :
    GoodWord (baseWord c) ∧ principalSum ((baseWord c).map value) = interpretation 0 c := by
  obtain ⟨t, rfl, ht⟩ := (SourceOne.PublicCodes.lowCheckCode_iff c).mp hc
  let n := SourceOne.PublicCodes.fragment t
  have ha : SourceOne.admissible n t := (SourceOne.check_iff n t).mp (Bool.and_eq_true_iff.mp ht).1
  have hn := SourceOne.Normalization.normalize_spec n t ha
  have hmap : (baseWord t.code).map value =
      (thetaAtoms (SourceOne.Normalization.normalize t)).map (SourceOne.denote n) := by
    simp only [baseWord, baseTree, decode_code, Option.getD_some, List.map_map]
    apply List.map_congr_left
    intro a ha'
    simp only [Function.comp_apply, value, if_pos rfl, SourceOne.PublicCodes.interpretation_code]
    exact SourceOne.PublicCodes.denote_eq_finite n a (hn.1.thetaAtoms ha')
  have hsum : principalSum ((baseWord t.code).map value) = interpretation 0 t.code := by
    rw [hmap, SourceOne.thetaAtoms_denote_sum n _ hn.1 hn.2.1,
      interpretation_code, denote_zero]
    exact hn.2.2.trans (SourceOne.PublicCodes.denote_eq_finite n t ha).symm
  have hlow : interpretation 0 t.code < finiteBase 1 := by
    rw [interpretation_zero]
    exact (SourceOne.PublicCodes.lt_boundary_iff_code _).mpr ⟨t.code, hc, rfl⟩
  refine ⟨?_, hsum⟩
  intro a ha'
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ha'
  have hu' : u ∈ thetaAtoms (SourceOne.Normalization.normalize t) := by
    simpa only [baseTree, decode_code, Option.getD_some] using hu
  have hnormal := SourceOne.thetaAtoms_denote_normal n _ hn.1 hn.2.1
  have hp := hnormal.1 _ (List.mem_map.mpr ⟨u, hu', rfl⟩)
  have hf := SourceOne.PublicCodes.denote_eq_finite n u (hn.1.thetaAtoms hu')
  have hucheck : SourceOne.PublicCodes.checkCode u.code = true := by
    rw [SourceOne.PublicCodes.checkCode_code]
    exact (SourceOne.PublicCodes.check_iff_finite_admissible u).mpr ⟨n, hn.1.thetaAtoms hu'⟩
  have hm : value (0, u.code) ∈ (baseWord t.code).map value :=
    List.mem_map.mpr ⟨(0, u.code), ha', rfl⟩
  have hwhole : principalSum ((baseWord t.code).map value) < finiteBase 1 := by
    rw [hsum]
    exact hlow
  have hbound := (principalSum_mem_le hm).trans_lt hwhole
  simp only [Good, value, ↓reduceIte, SourceOne.PublicCodes.interpretation_code] at hbound ⊢
  exact ⟨hucheck, hf.symm ▸ hp.1, hf.symm ▸ hp.2, hbound⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.BaseAtoms
