import Alexander313.Wilken.HereditaryNativeArithmetic
import Alexander313.Wilken.HereditaryNativeSourceChi

/-!
# The genuine addition clause for the native source indicator

The finite native normalizer retains the final atom of a written sum. On
original admitted weak-normal terms, a joint induction preserves chi and
the Boolean labels of every high-part word. It uses the real ANF identity
on an already decreasing word and the actual fixed-point/last-exponent
tests. It does not assume chi is invariant under arbitrary equal values.

These statements apply to every originally checked coded epsilon context,
including full-sort left inputs. The source Lemma 3.5(a) wrapper retains a
low left input and a proper literal theta-zero right input. The other
arithmetic and lambda/iota clauses of Lemma 3.5 are not claimed.
All proof terms are uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceChi.Arithmetic

open Comparison (Normal atoms)

theorem normalizeAtoms_eq_of_normal (q n : Nat) (hq : baseCheck q = true)
    (as : List (RelativeTerm Nat)) (hg : Normalization.GoodAtoms q n as)
    (hn : IsAdditiveNormalForm (as.map (denote q))) :
    Normalization.normalizeAtoms q as = as := by
  revert hg hn
  induction as with
  | nil => intros; rfl
  | cons a as ih =>
    intro hg hn
    have ha := hg a List.mem_cons_self
    have ht : Normalization.GoodAtoms q n as :=
      fun b hb => hg b (List.mem_cons_of_mem _ hb)
    have htail : IsAdditiveNormalForm (as.map (denote q)) :=
      additiveNormalForm_tail hn
    rw [Normalization.normalizeAtoms, ih ht htail]
    cases as with
    | nil => rfl
    | cons b bs =>
      have hb := ht b List.mem_cons_self
      have hba : denote q b ≤ denote q a :=
        (List.pairwise_cons.mp hn.2).1 _ List.mem_cons_self
      have hc : Comparison.less q a b = false := by
        cases he : Comparison.less q a b with
        | false => rfl
        | true =>
          have hv := (Comparison.less_correct q a b
            (Comparison.admitted_checked q n hq a ha.1)
            (Comparison.admitted_checked q n hq b hb.1) ha.2.1 hb.2.1).mp he
          exact False.elim (hv.not_ge hba)
      simp only [Normalization.prependAtom, hc, Bool.cond_false]

/-- Suffix absorption never removes the final literal atom. -/
theorem normalizeAtoms_append_last (q : Nat) (as : List (RelativeTerm Nat))
    (a : RelativeTerm Nat) :
    ∃ ps, Normalization.normalizeAtoms q (as ++ [a]) = ps ++ [a] := by
  induction as with
  | nil => exact ⟨[], rfl⟩
  | cons b bs ih =>
    obtain ⟨ps, hp⟩ := ih
    rw [List.cons_append, Normalization.normalizeAtoms, hp]
    cases ps with
    | nil =>
      cases hc : Comparison.less q b a with
      | false => exact ⟨[b], by simp [Normalization.prependAtom, hc]⟩
      | true => exact ⟨[], by simp [Normalization.prependAtom, hc]⟩
    | cons c cs =>
      cases hc : Comparison.less q b c with
      | false => exact ⟨b :: c :: cs, by simp [Normalization.prependAtom, hc]⟩
      | true => exact ⟨c :: cs, by simp [Normalization.prependAtom, hc]⟩

private theorem lastIndicator_append (as bs : List Entry) (hb : bs ≠ []) :
    lastIndicator (as ++ bs) = lastIndicator bs := by
  unfold lastIndicator
  rw [List.reverse_append]
  cases hr : bs.reverse with
  | nil =>
    have he : bs = [] := by simpa using congrArg List.reverse hr
    exact False.elim (hb he)
  | cons b cs => rfl

private theorem lastIndicator_bools (as : List Entry) :
    lastIndicator as = (as.map Prod.snd).reverse.head?.getD false := by
  unfold lastIndicator
  rw [← List.map_reverse]
  cases as.reverse <;> rfl

private theorem lastIndicator_parameters (q : Nat) (ps : List Nat) :
    lastIndicator ((ps.map RelativeTerm.parameter).map (fun a => (a, indicator q a))) = false := by
  unfold lastIndicator
  rw [← List.map_reverse, ← List.map_reverse]
  cases ps.reverse <;> rfl

/-- The actual last principal representative carries the source sum label. -/
theorem indicator_atoms (q : Nat) (t : RelativeTerm Nat)
    (ht : check q t = true) (hn : Normal q t) :
    indicator q t = lastIndicator ((atoms t).map (fun a => (a, indicator q a))) := by
  revert ht hn
  induction t with
  | parameter p =>
    intro _ _
    exact (lastIndicator_parameters q (CanonicalCoefficients.word p)).symm
  | theta m a ih => intro _ _; rfl
  | sum a b iha ihb =>
    intro ht hn
    have hs := sum_children q a b ht hn
    have hq := (Bool.and_eq_true.mp ht).1
    rw [indicator_sum, atoms, List.map_append]
    by_cases hb : atoms b = []
    · have hv : denote q b = 0 := by
        have hval := Comparison.atoms_value q _ hq b
          (NativeContext.checked_admissible q b hs.2.2.1) hs.2.2.2.1
        simpa only [hb, List.map_nil, principalSum] using hval.symm
      have ha : denote q a = 0 := by
        rcases hs.2.2.2.2 with hz | ⟨xs, hxs, _, _⟩
        · exact hz.2.1
        · have hp := (hxs.1 _ (List.mem_append_right _ List.mem_cons_self)).1
          exact False.elim ((ne_of_gt hp) hv)
      have hea : atoms a = [] := by
        apply List.map_eq_nil_iff.mp
        rw [Comparison.atoms_anf q _ hq a
          (NativeContext.checked_admissible q a hs.1) hs.2.1, ha, canonicalANF_zero]
      rw [hb, hea]
      exact indicator_below_base q b hs.2.2.1 hs.2.2.2.1
        (by rw [hv]; exact base_pos q hq)
    · rw [lastIndicator_append _ _ (by simpa only [List.map_eq_nil_iff] using hb)]
      exact ihb hs.2.2.1 hs.2.2.2.1

/-- Only the genuine high atom labels are used here; native public payloads
remain atomic and contribute no high labels at any index. -/
def highBits (q m : Nat) (t : RelativeTerm Nat) : List Bool :=
    (highLabels m (state q t).2.2).map Prod.snd

private theorem highLabels_append (m : Nat) (as bs : List Entry) :
    highLabels m (as ++ bs) = highLabels m as ++ highLabels m bs := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    cases hc : Decomposition.above m a.1 <;>
      simp only [List.cons_append, highLabels, hc, Bool.cond_false,
        Bool.cond_true, ih]

theorem highBits_parameter (q m p : Nat) : highBits q m (.parameter p) = [] := by
  unfold highBits
  change (highLabels m (((CanonicalCoefficients.word p).map RelativeTerm.parameter).map
    (fun a => (a, false)))).map Prod.snd = []
  induction CanonicalCoefficients.word p with
  | nil => rfl
  | cons a as ih =>
    simpa only [List.map_cons, highLabels, Decomposition.above, RelativeTerm.outerSort,
      Nat.not_lt_zero, decide_false, Bool.cond_false] using ih

theorem highBits_sum (q m : Nat) (a b : RelativeTerm Nat) :
    highBits q m (.sum a b) = highBits q m a ++ highBits q m b := by
  change (highLabels m ((state q a).2.2 ++ (state q b).2.2)).map Prod.snd = _
  rw [highLabels_append, List.map_append]
  rfl

theorem highBits_theta (q m k : Nat) (a : RelativeTerm Nat) :
    highBits q m (.theta k a) = cond (Decomposition.above m (.theta k a))
      [indicator q (.theta k a)] [] := by
  unfold highBits
  rw [state_labels]
  cases hc : Decomposition.above m (.theta k a) <;>
    simp only [atoms, List.map_cons, List.map_nil, highLabels, hc,
      Bool.cond_false, Bool.cond_true]

private theorem highBits_parameter_word (q m : Nat) (ps : List Nat) :
    (ps.map RelativeTerm.parameter).flatMap (highBits q m) = [] := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [List.map_cons, List.flatMap_cons, highBits_parameter,
      List.nil_append, ih]

theorem highBits_atoms (q m : Nat) (t : RelativeTerm Nat) :
    (atoms t).flatMap (highBits q m) = highBits q m t := by
  induction t with
  | parameter p => rw [highBits_parameter]; exact highBits_parameter_word q m _
  | sum a b iha ihb => rw [atoms, List.flatMap_append, iha, ihb, highBits_sum]
  | theta k a ih => simp only [atoms, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem highBits_buildAtoms (q m : Nat) (as : List (RelativeTerm Nat)) :
    highBits q m (Normalization.buildAtoms as) = as.flatMap (highBits q m) := by
  have h : ∀ bs : List (RelativeTerm Nat), highBits q m (Normalization.buildRev bs) =
      bs.reverse.flatMap (highBits q m) := by
    intro bs
    induction bs with
    | nil => exact highBits_parameter q m _
    | cons b bs ih =>
      rw [Normalization.buildRev, highBits_sum, ih, List.reverse_cons, List.flatMap_append]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  simpa only [Normalization.buildAtoms, List.reverse_reverse] using h as.reverse

private theorem indicator_theta_bits (q m : Nat) (a : RelativeTerm Nat) :
    indicator q (.theta m a) = cond (baseCase q m a.code) true
      (cond (chooseHigh q m a.code) ((highBits q m a).reverse.head?.getD false)
        (indicator q a)) := by
  change cond (baseCase q m (state q a).1.code) true
    (cond (chooseHigh q m (state q a).1.code)
      (lastIndicator (highLabels m (state q a).2.2)) (indicator q a)) = _
  rw [state_tree, lastIndicator_bools]
  rfl

private theorem bool_eq_of_true_iff {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

/-- The branch tests agree by their actual source denotations, not by an
assumed invariance of chi or of the reconstructed spellings. -/
theorem theta_branch_agreement (q m : Nat) (a b : RelativeTerm Nat)
    (ha : check q (.theta m a) = true) (hb : check q (.theta m b) = true)
    (hna : Normal q (.theta m a)) (hnb : Normal q (.theta m b))
    (hv : denote q a = denote q b) :
    baseCase q m a.code = baseCase q m b.code ∧
      chooseHigh q m a.code = chooseHigh q m b.code := by
  have hpa := theta_argument_parts q m a ha hna
  have hpb := theta_argument_parts q m b hb hnb
  constructor
  · apply bool_eq_of_true_iff
    simp only [baseCase, Bool.and_eq_true, beq_iff_eq,
      FixedPoint.zeroCheck_exact q a.code hpa.1,
      FixedPoint.zeroCheck_exact q b.code hpb.1, interpretation_code, hv]
  · apply bool_eq_of_true_iff
    rw [chooseHigh_correct q m a ha hna, chooseHigh_correct q m b hb hnb]
    have hva := Decomposition.parts_code_value q m a.code hpa.1
    have hvb := Decomposition.parts_code_value q m b.code hpb.1
    simp only [FixedPoint.SourceFixed, FixedPoint.delta, FixedPoint.residual,
      hva.2, hvb.2, interpretation_code, hv]

/-- Joint source-fold invariance under the actual normalizer on ORIGINAL
admitted weak-normal inputs. Arbitrary equal-value spellings are not inputs
to this theorem. -/
theorem normalize_indicator_highBits (q : Nat) (t : RelativeTerm Nat)
    (ht : check q t = true) (hn : Normal q t) :
    indicator q (Normalization.normalize q t) = indicator q t ∧
      ∀ m, highBits q m (Normalization.normalize q t) = highBits q m t := by
  revert ht hn
  induction t with
  | parameter p => intro _ _; exact ⟨rfl, fun _ => rfl⟩
  | theta k a ih =>
    intro ht hn
    have ha := FixedPoint.checked_theta_argument q k a ht
    have hi := ih ha hn
    have ho := Normalization.normalize_checked q (.theta k a) ht
    have hav := Normalization.normalize_checked q a ha
    have hc := theta_branch_agreement q k (Normalization.normalize q a) a
      ho.1 ht ho.2.1 hn hav.2.2
    have hchi : indicator q (Normalization.normalize q (.theta k a)) =
        indicator q (.theta k a) := by
      change indicator q (.theta k (Normalization.normalize q a)) = _
      rw [indicator_theta_bits, indicator_theta_bits, hc.1, hc.2, hi.1, hi.2 k]
    refine ⟨hchi, ?_⟩
    intro m
    change highBits q m (.theta k (Normalization.normalize q a)) = _
    rw [highBits_theta, highBits_theta]
    change cond (decide (m + 1 < k + 1)) [indicator q (Normalization.normalize q (.theta k a))] [] =
      cond (decide (m + 1 < k + 1)) [indicator q (.theta k a)] []
    rw [hchi]
  | sum a b iha ihb =>
    intro ht hn
    have hs := sum_children q a b ht hn
    have hia := iha hs.1 hs.2.1
    have hib := ihb hs.2.2.1 hs.2.2.2.1
    have hq := (Bool.and_eq_true.mp ht).1
    have had := NativeContext.checked_admissible q (.sum a b) ht
    cases had.2 with
    | sum haa hbb =>
      have hpa := Normalization.normalize_spec q _ hq a ⟨had.1.1, haa⟩
      have hpb := Normalization.normalize_spec q _ hq b ⟨had.1.2, hbb⟩
      let na := Normalization.normalize q a
      let nb := Normalization.normalize q b
      let word := atoms na ++ atoms nb
      have hg : Normalization.GoodAtoms q _ word :=
        (Normalization.GoodAtoms.atoms q _ hq na hpa.1 hpa.2.1).append
          (Normalization.GoodAtoms.atoms q _ hq nb hpb.1 hpb.2.1)
      have hw : IsAdditiveNormalForm (word.map (denote q)) := by
        change IsAdditiveNormalForm ((atoms na ++ atoms nb).map (denote q))
        rw [List.map_append, Comparison.atoms_anf q _ hq na hpa.1 hpa.2.1,
          Comparison.atoms_anf q _ hq nb hpb.1 hpb.2.1, hpa.2.2, hpb.2.2]
        exact sourceNormalSum_canonical_concat hs.2.2.2.2
      have he := normalizeAtoms_eq_of_normal q _ hq word hg hw
      have hsn : Normal q (.sum na nb) := by
        refine ⟨hpa.2.1, hpb.2.1, ?_⟩
        change SourceNormalSum (denote q na + denote q nb) (denote q na) (denote q nb)
        rw [hpa.2.2, hpb.2.2]
        exact hs.2.2.2.2
      have hsc : check q (.sum na nb) = true :=
        Comparison.admitted_checked q _ hq _
          ⟨⟨hpa.1.1, hpb.1.1⟩, .sum hpa.1.2 hpb.1.2⟩
      have hchi : indicator q (Normalization.normalize q (.sum a b)) =
          indicator q (.sum a b) := by
        change indicator q (Normalization.buildAtoms (Normalization.normalizeAtoms q word)) = _
        rw [he, indicator_buildAtoms]
        change lastIndicator ((atoms (.sum na nb)).map (fun p => (p, indicator q p))) = _
        rw [← indicator_atoms q (.sum na nb) hsc hsn, indicator_sum, indicator_sum]
        exact hib.1
      refine ⟨hchi, ?_⟩
      intro m
      change highBits q m (Normalization.buildAtoms (Normalization.normalizeAtoms q word)) = _
      rw [he, highBits_buildAtoms]
      change (atoms na ++ atoms nb).flatMap (highBits q m) = _
      rw [List.flatMap_append, highBits_atoms, highBits_atoms, hia.2 m, hib.2 m, highBits_sum]

theorem indicator_normalize (q : Nat) (t : RelativeTerm Nat)
    (ht : check q t = true) (hn : Normal q t) :
    indicator q (Normalization.normalize q t) = indicator q t :=
  (normalize_indicator_highBits q t ht hn).1

theorem highBits_normalize (q m : Nat) (t : RelativeTerm Nat)
    (ht : check q t = true) (hn : Normal q t) :
    highBits q m (Normalization.normalize q t) = highBits q m t :=
  (normalize_indicator_highBits q t ht hn).2 m

theorem chiCode_normalize (q c : Nat) (hc : SourceChi.inputCheck q c = true) :
    chiCode q (Normalization.normalizeCode q c) = chiCode q c := by
  obtain ⟨ht, hn⟩ := (SourceChi.inputCheck_exact q c).mp hc
  obtain ⟨t, rfl, hct⟩ := (checkCode_exact q c).mp ht
  have hnt : Normal q t := by simpa only [ThetaCourse.rawTree_code] using hn
  have ho := Normalization.normalize_checked q t hct
  simp only [Normalization.normalizeCode, checkCode_code, hct, Bool.cond_true,
    ThetaCourse.rawTree_code]
  rw [chiCode_correct q _ ho.1 ho.2.1, chiCode_correct q t hct hnt]
  exact indicator_normalize q t hct hnt

theorem rawChiCode_eq_chiCode (q c : Nat) (hc : SourceChi.inputCheck q c = true) :
    rawChiCode q c = chiCode q c := by
  rw [rawChiCode, chiCode_normalize q c hc]
  simp only [rawInputCheck, ((SourceChi.inputCheck_exact q c).mp hc).1, Bool.true_and]

private theorem indicator_buildAtoms_append (q : Nat) (ps : List (RelativeTerm Nat))
    (a : RelativeTerm Nat) : indicator q (Normalization.buildAtoms (ps ++ [a])) = indicator q a := by
  rw [indicator_buildAtoms]
  simp only [lastIndicator, List.map_append, List.map_cons, List.map_nil,
    List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, List.head?_cons, Option.getD_some]

/-- This literal final-atom statement is unconditional finite computation. -/
theorem indicator_normalized_sum_theta (q k : Nat) (b a : RelativeTerm Nat) :
    indicator q (Normalization.normalize q (.sum b (.theta k a))) =
      indicator q (Normalization.normalize q (.theta k a)) := by
  change indicator q (Normalization.buildAtoms (Normalization.normalizeAtoms q
    (atoms (Normalization.normalize q b) ++ [.theta k (Normalization.normalize q a)]))) = _
  obtain ⟨ps, he⟩ := normalizeAtoms_append_last q (atoms (Normalization.normalize q b))
    (.theta k (Normalization.normalize q a))
  rw [he, indicator_buildAtoms_append]
  rfl

theorem indicator_addTerm_theta (q c k : Nat) (a : RelativeTerm Nat)
    (ha : check q (.theta k a) = true) (hna : Normal q (.theta k a)) :
    indicator q (NativeContext.Arithmetic.addTerm q c (.theta k a : RelativeTerm Nat).code) =
      indicator q (.theta k a) := by
  unfold NativeContext.Arithmetic.addTerm
  rw [ThetaCourse.rawTree_code, indicator_normalized_sum_theta]
  exact indicator_normalize q (.theta k a) ha hna

/-- Actual checked addition preserves chi of an original normal literal
theta right input. The left input is any originally admitted full-sort code. -/
theorem chiCode_addCode_theta (q c k : Nat) (a : RelativeTerm Nat)
    (hc : checkCode q c = true) (ha : check q (.theta k a) = true)
    (hna : Normal q (.theta k a)) :
    chiCode q (NativeContext.Arithmetic.addCode q c (.theta k a : RelativeTerm Nat).code) =
      chiCode q (.theta k a : RelativeTerm Nat).code := by
  have had : checkCode q (.theta k a : RelativeTerm Nat).code = true :=
    by simpa only [checkCode_code] using ha
  have hi := (NativeContext.Arithmetic.inputCheck_exact q c _).mpr ⟨hc, had⟩
  have ho := NativeContext.Arithmetic.addTerm_spec q c _ hc had
  have hq := (Bool.and_eq_true.mp ha).1
  have hcheck := Comparison.admitted_checked q _ hq _ ho.1
  rw [NativeContext.Arithmetic.addCode, hi]
  simp only [Bool.cond_true]
  rw [chiCode_correct q _ hcheck ho.2.1, chiCode_correct q _ ha hna]
  exact indicator_addTerm_theta q c k a ha hna

/-- The genuine addition subclaim of source Lemma 3.5(a), with its literal
proper theta-zero right input and original beta < tau-infinity domain. -/
theorem source_lemma_3_5_a_add (q c : Nat) (a : RelativeTerm Nat)
    (hc : lowCheckCode q c = true) (ha : check q (.theta 0 a) = true)
    (hna : Normal q (.theta 0 a)) (hproper : base q < denote q (.theta 0 a)) :
    chiCode q (NativeContext.Arithmetic.addCode q c (.theta 0 a : RelativeTerm Nat).code) =
      chiCode q (.theta 0 a : RelativeTerm Nat).code := by
  have hct := (Bool.and_eq_true.mp hc).1
  exact chiCode_addCode_theta q c 0 a hct ha hna

/-- The genuine proper-domain condition is a nonzero actual argument. -/
theorem proper_theta_zero_iff (q : Nat) (a : RelativeTerm Nat)
    (ha : check q (.theta 0 a) = true) (hna : Normal q (.theta 0 a)) :
    base q < denote q (.theta 0 a) ↔ denote q a ≠ 0 := by
  have hq := (Bool.and_eq_true.mp ha).1
  have hr : base q ≤ denote q (.theta 0 a) := by
    simpa only [omegaSequence_zero] using (FixedPoint.checked_theta_range q 0 a ha).1
  constructor
  · intro hp hz
    have he : denote q (.theta 0 a) = base q := by
      change globalCollapse (base q) 0 (denote q a) = base q
      rw [hz, globalCollapse_zero (base q) (base_pos q hq) (base_add_closed q hq) 0,
        omegaSequence_zero]
    exact (ne_of_lt hp) he.symm
  · intro hnz
    apply lt_of_le_of_ne hr
    intro he
    exact hnz (theta_base_argument_zero q 0 a ha he.symm).2

def rightCode (a : Nat) : Nat := (.theta 0 (ThetaCourse.rawTree a) : RelativeTerm Nat).code

theorem rightCode_primrec : Primrec rightCode :=
  code_primrec.comp (theta_primrec.comp (Primrec.const 0) ThetaCourse.rawTree_primrec)

/-- Source beta is original low, and the constructed right source node
retains the ORIGINAL argument check, weak normality, theta call and proviso. -/
def sourceInput (q c a : Nat) : Bool := lowCheckCode q c &&
    (SourceChi.inputCheck q a && (checkCode q (rightCode a) && !FixedPoint.zeroCheck a))

theorem sourceInput_primrec : Primrec
    (fun p : Nat × (Nat × Nat) => sourceInput p.1 p.2.1 p.2.2) := by
  have hq := Primrec.fst
  have hc := Primrec.fst.comp Primrec.snd
  have ha := Primrec.snd.comp Primrec.snd
  exact Primrec.and.comp (lowCheckCode_primrec.comp hq hc)
    (Primrec.and.comp (SourceChi.inputCheck_primrec.comp hq ha)
      (Primrec.and.comp (checkCode_primrec.comp hq (rightCode_primrec.comp ha))
        (Primrec.not.comp (FixedPoint.zeroCheck_primrec.comp ha))))

theorem sourceInput_exact (q c a : Nat) : sourceInput q c a = true ↔
    lowCheckCode q c = true ∧ SourceChi.inputCheck q a = true ∧
      checkCode q (rightCode a) = true ∧ interpretation q a ≠ 0 := by
  simp only [sourceInput, Bool.and_eq_true, Bool.not_eq_true']
  constructor
  · rintro ⟨hc, ha, ht, hz⟩
    refine ⟨hc, ha, ht, ?_⟩
    intro hv
    have he := (FixedPoint.zeroCheck_exact q a ha).mpr hv
    simp only [hz, Bool.false_eq_true] at he
  · rintro ⟨hc, ha, ht, hv⟩
    refine ⟨hc, ha, ht, ?_⟩
    cases hz : FixedPoint.zeroCheck a with
    | false => rfl
    | true => exact False.elim (hv ((FixedPoint.zeroCheck_exact q a ha).mp hz))

theorem sourceInput_literal (q c a : Nat) : sourceInput q c a = true ↔
    lowCheckCode q c = true ∧ checkCode q a = true ∧ Normal q (ThetaCourse.rawTree a) ∧
      check q (.theta 0 (ThetaCourse.rawTree a)) = true ∧
        base q < denote q (.theta 0 (ThetaCourse.rawTree a)) := by
  rw [sourceInput_exact]
  constructor
  · rintro ⟨hc, ha, ht, hz⟩
    have han := (SourceChi.inputCheck_exact q a).mp ha
    have htheta : check q (.theta 0 (ThetaCourse.rawTree a)) = true := by
      simpa only [rightCode, checkCode_code] using ht
    have hav := NativeContext.Arithmetic.raw_value q a han.1
    refine ⟨hc, han.1, han.2, htheta, ?_⟩
    exact (proper_theta_zero_iff q _ htheta han.2).mpr (by rw [hav]; exact hz)
  · rintro ⟨hc, ha, hn, ht, hp⟩
    refine ⟨hc, (SourceChi.inputCheck_exact q a).mpr ⟨ha, hn⟩,
      by simpa only [rightCode, checkCode_code] using ht, ?_⟩
    have hnz := (proper_theta_zero_iff q _ ht hn).mp hp
    rw [← NativeContext.Arithmetic.raw_value q a ha]
    exact hnz

def additionChi (q c a : Nat) : Bool := sourceInput q c a &&
  chiCode q (NativeContext.Arithmetic.addCode q c (rightCode a))

theorem additionChi_primrec : Primrec
    (fun p : Nat × (Nat × Nat) => additionChi p.1 p.2.1 p.2.2) := by
  have hq := Primrec.fst
  have hc := Primrec.fst.comp Primrec.snd
  have ha := Primrec.snd.comp Primrec.snd
  have hs := NativeContext.Arithmetic.addCode_primrec.comp
    (hq.pair (hc.pair (rightCode_primrec.comp ha)))
  exact Primrec.and.comp sourceInput_primrec (chiCode_primrec.comp hq hs)

/-- The executing guarded kernel computes the ORIGINAL normal right-hand
indicator, by real addition and the derived terminal-normalization law. -/
theorem additionChi_correct (q c a : Nat) (h : sourceInput q c a = true) :
    additionChi q c a = chiCode q (rightCode a) := by
  have hs := (sourceInput_literal q c a).mp h
  rw [additionChi, h, Bool.true_and]
  exact source_lemma_3_5_a_add q c (ThetaCourse.rawTree a) hs.1 hs.2.2.2.1 hs.2.2.1 hs.2.2.2.2

theorem additionChi_spec (q c a : Nat) (h : sourceInput q c a = true) :
    Comparison.acceptedCode q (NativeContext.Arithmetic.addCode q c (rightCode a)) = true ∧
    interpretation q (NativeContext.Arithmetic.addCode q c (rightCode a)) =
      interpretation q c + interpretation q (rightCode a) ∧
    additionChi q c a = indicator q (.theta 0 (ThetaCourse.rawTree a)) := by
  have hs := (sourceInput_exact q c a).mp h
  have hc := (Bool.and_eq_true.mp hs.1).1
  have ho := NativeContext.Arithmetic.addCode_spec q c (rightCode a) hc hs.2.2.1
  have hl := (sourceInput_literal q c a).mp h
  exact ⟨ho.1, ho.2.1, (additionChi_correct q c a h).trans
    (chiCode_correct q _ hl.2.2.2.1 hl.2.2.1)⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceChi.Arithmetic
