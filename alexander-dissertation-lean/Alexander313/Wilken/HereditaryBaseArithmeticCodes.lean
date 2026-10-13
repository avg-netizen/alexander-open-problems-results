import Alexander313.Wilken.HereditaryBaseAtoms
import Alexander313.Wilken.HereditaryUniformRecognition

/-! # Actual hereditary parameter and fresh-base arithmetic

This is an explicit subclass of the unchanged hereditary low grammar. Level
zero includes the whole actual low base-one grammar. At a positive level,
parameters contain real earlier-fragment codes, sums are literal ordinal sums,
and the fresh theta term is exactly theta0(zeroTree level). The checker and
principal-word output are uniform primitive recursive code-course computations.
The old hereditary admission and genuine finite/global interpretations are
retained. Arbitrary later-base theta arguments are outside this subclass.
Uncompiled; no epsilon or hereditary comparison oracle is used.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.BaseArithmetic

open BaseAtoms

abbrev State := Bool × Word

def zeroCode : Nat → Nat
  | 0 => (.parameter 0 : RelativeTerm Nat).code
  | r + 1 => (.parameter (zeroCode r) : RelativeTerm Nat).code

@[simp] theorem zeroCode_eq (r : Nat) : zeroCode r = (zeroTree r).code := by
  induction r <;> simp_all [zeroCode, zeroTree]

theorem zeroCode_primrec : Primrec zeroCode := by
  have hp : Primrec (fun p : Nat => (.parameter p : RelativeTerm Nat).code) :=
    code_primrec.comp parameter_primrec
  have h : Primrec₂ (fun (_ : Unit) r => Nat.rec (motive := fun _ => Nat)
      ((.parameter 0 : RelativeTerm Nat).code)
      (fun _ p => (.parameter p : RelativeTerm Nat).code) r) :=
    Primrec.nat_rec (Primrec.const ((.parameter 0 : RelativeTerm Nat).code))
      ((hp.comp (Primrec.snd.comp Primrec.snd)).to₂)
  exact (h.comp (Primrec.const ()) Primrec.id).of_eq (by
    intro r
    induction r <;> simp_all [zeroCode])

def state : Nat → Nat → State
  | 0, c => (SourceOne.PublicCodes.lowCheckCode c, baseWord c)
  | r + 1, 0 => (false, [])
  | r + 1, c + 1 =>
      let tag := c.unpair.1
      let p := c.unpair.2
      if tag = 0 then state r p
      else if tag = 1 then
        let a := state (r + 1) p.unpair.1
        let b := state (r + 1) p.unpair.2
        (a.1 && b.1, a.2 ++ b.2)
      else if tag = 2 then
        (p.unpair.1 == 0 && p.unpair.2 == zeroCode (r + 1), [(r + 1, 0)])
      else (false, [])
termination_by _ c => c
decreasing_by
  all_goals
    have hp := Nat.unpair_right_le c
    have hl := Nat.unpair_left_le c.unpair.2
    have hr := Nat.unpair_right_le c.unpair.2
    omega

@[simp] theorem state_zero (c : Nat) :
    state 0 c = (SourceOne.PublicCodes.lowCheckCode c, baseWord c) := by
  simp only [state]

@[simp] theorem state_parameter (r p : Nat) :
    state (r + 1) (.parameter p : RelativeTerm Nat).code = state r p := by
  simp [state, code, Nat.unpair_pair]

@[simp] theorem state_sum (r : Nat) (a b : RelativeTerm Nat) :
    state (r + 1) (.sum a b : RelativeTerm Nat).code =
      ((state (r + 1) a.code).1 && (state (r + 1) b.code).1,
        (state (r + 1) a.code).2 ++ (state (r + 1) b.code).2) := by
  simp [state, code, Nat.unpair_pair]

@[simp] theorem state_theta (r k : Nat) (a : RelativeTerm Nat) :
    state (r + 1) (.theta k a : RelativeTerm Nat).code =
      (k == 0 && a.code == zeroCode (r + 1), [(r + 1, 0)]) := by
  simp [state, code, Nat.unpair_pair]

inductive Grammar : Nat → RelativeTerm Nat → Prop
  | base (t : RelativeTerm Nat) (h : SourceOne.PublicCodes.lowCheck t = true) : Grammar 0 t
  | parameter (r : Nat) (u : RelativeTerm Nat) (h : Grammar r u) : Grammar (r + 1) (.parameter u.code)
  | sum (r : Nat) (a b : RelativeTerm Nat) (ha : Grammar (r + 1) a) (hb : Grammar (r + 1) b) :
      Grammar (r + 1) (.sum a b)
  | fresh (r : Nat) : Grammar (r + 1) (.theta 0 (zeroTree (r + 1)))

theorem grammar_state {r : Nat} {t : RelativeTerm Nat} (ht : Grammar r t) :
    (state r t.code).1 = true := by
  induction ht with
  | base t h => simpa only [state_zero, SourceOne.PublicCodes.lowCheckCode_code] using h
  | parameter r u h ih => simpa only [state_parameter] using ih
  | sum r a b ha hb iha ihb => simp only [state_sum, iha, ihb, Bool.true_and]
  | fresh r => simp only [state_theta, zeroCode_eq, beq_self_eq_true, Bool.true_and]

private theorem state_sound (r c : Nat) (hc : (state r c).1 = true) :
    ∃ t : RelativeTerm Nat, t.code = c ∧ Grammar r t := by
  induction c using Nat.strong_induction_on generalizing r with
  | h c ih =>
    cases r with
    | zero =>
      obtain ⟨t, ht, hg⟩ := (SourceOne.PublicCodes.lowCheckCode_iff c).mp
        (by simpa only [state_zero] using hc)
      exact ⟨t, ht, .base t hg⟩
    | succ r =>
      cases c with
      | zero => simp [state] at hc
      | succ c =>
        let tag := c.unpair.1
        let p := c.unpair.2
        have hp : p < c + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le c)
        have hl : p.unpair.1 < c + 1 := (Nat.unpair_left_le p).trans_lt hp
        have hr : p.unpair.2 < c + 1 := (Nat.unpair_right_le p).trans_lt hp
        have hk : c = Nat.pair tag p := (Nat.pair_unpair c).symm
        by_cases h0 : tag = 0
        · have hs : (state r p).1 = true := by simpa [state, tag, p, h0] using hc
          obtain ⟨u, hu, hg⟩ := ih p hp r hs
          refine ⟨.parameter u.code, ?_, .parameter r u hg⟩
          simp only [code_parameter, hu, hk, h0]
        by_cases h1 : tag = 1
        · have hs : (state (r + 1) p.unpair.1).1 = true ∧
              (state (r + 1) p.unpair.2).1 = true := by
            simpa [state, tag, p, h0, h1, Bool.and_eq_true] using hc
          obtain ⟨a, ha, hga⟩ := ih _ hl (r + 1) hs.1
          obtain ⟨b, hb, hgb⟩ := ih _ hr (r + 1) hs.2
          refine ⟨.sum a b, ?_, .sum r a b hga hgb⟩
          simp only [code_sum, ha, hb, Nat.pair_unpair, hk, h1]
        by_cases h2 : tag = 2
        · have hs : p.unpair.1 = 0 ∧ p.unpair.2 = zeroCode (r + 1) := by
            simpa [state, tag, p, h0, h1, h2, Bool.and_eq_true] using hc
          refine ⟨.theta 0 (zeroTree (r + 1)), ?_, .fresh r⟩
          have hpay : Nat.pair 0 (zeroTree (r + 1)).code = p := by
            rw [← zeroCode_eq, ← hs.1, ← hs.2, Nat.pair_unpair]
          simp only [code_theta, hpay, hk, h2]
        · simp [state, tag, p, h0, h1, h2] at hc

theorem state_exact (r c : Nat) : (state r c).1 = true ↔
    ∃ t : RelativeTerm Nat, t.code = c ∧ Grammar r t :=
  ⟨state_sound r c, fun ⟨t, ht, hg⟩ => ht ▸ grammar_state hg⟩

@[simp] theorem zeroTree_height (r : Nat) : (zeroTree r).height = 0 := by
  cases r <;> rfl

@[simp] theorem zeroTree_outerSort (r : Nat) : (zeroTree r).outerSort = 0 := by
  cases r <;> rfl

private theorem fresh_low (r : Nat) : lowCheck r (.theta 0 (zeroTree r)) = true := by
  have hz : finiteCheck r 2 (zeroTree r) = true :=
    finiteCheck_transfer r _ _ (Bool.and_eq_true_iff.mp (zeroTree_lowCheck r)).1 2 (by simp)
  simp [lowCheck, check, SourceOne.PublicCodes.fragment, height, outerSort, hz]

/-- Actual old hereditary admission, not a replacement public-domain target. -/
theorem grammar_low {r : Nat} {t : RelativeTerm Nat} (ht : Grammar r t) : lowCheck r t = true := by
  induction ht with
  | base t h => exact h
  | parameter r u h ih =>
    change (lowCheckCode r u.code && decide ((0 : Nat) ≤ 1)) = true
    rw [lowCheckCode_code, ih]
    rfl
  | sum r a b ha hb iha ihb =>
    have hca : check (r + 1) a = true := (Bool.and_eq_true_iff.mp iha).1
    have hcb : check (r + 1) b = true := (Bool.and_eq_true_iff.mp ihb).1
    have hsa : a.outerSort ≤ 1 := of_decide_eq_true (Bool.and_eq_true_iff.mp iha).2
    have hsb : b.outerSort ≤ 1 := of_decide_eq_true (Bool.and_eq_true_iff.mp ihb).2
    let n := SourceOne.PublicCodes.fragment (.sum a b)
    have hn : (.sum a b : RelativeTerm Nat).height ≤ n :=
      SourceOne.PublicCodes.height_le_fragment _
    have hfa := finiteCheck_transfer (r + 1) _ a hca n ((le_max_left _ _).trans hn)
    have hfb := finiteCheck_transfer (r + 1) _ b hcb n ((le_max_right _ _).trans hn)
    change (finiteCheck (r + 1) n (.sum a b) && decide (max a.outerSort b.outerSort ≤ 1)) = true
    simp only [finiteCheck_sum, hfa, hfb, max_le hsa hsb, decide_true, Bool.true_and]
  | fresh r => exact fresh_low (r + 1)

theorem grammar_word {r : Nat} {t : RelativeTerm Nat} (ht : Grammar r t) :
    GoodWord (state r t.code).2 ∧
      principalSum ((state r t.code).2.map value) = denote r t := by
  induction ht with
  | base t h =>
    have hs := baseWord_spec t.code (by simpa only [SourceOne.PublicCodes.lowCheckCode_code] using h)
    simpa only [state_zero, interpretation_code] using hs
  | parameter r u h ih =>
    simpa only [state_parameter, denote, eval, parameters_succ, interpretation_code] using ih
  | sum r a b ha hb iha ihb =>
    rw [state_sum]
    refine ⟨iha.1.append ihb.1, ?_⟩
    rw [List.map_append, principalSum_append, iha.2, ihb.2]
    rfl
  | fresh r =>
    simp only [state_theta, zeroCode_eq, beq_self_eq_true, Bool.true_and, Prod.snd]
    refine ⟨?_, ?_⟩
    · intro a ha
      have he : a = (r + 1, 0) := List.mem_singleton.mp ha
      subst a
      simp [Good]
    · change value (r + 1, 0) + 0 = globalCollapse (finiteBase (r + 1)) 0 (denote (r + 1) (zeroTree (r + 1)))
      rw [zeroTree_denote, finiteBase_collapse_zero_base]
      simp [value]

def checkCode (r c : Nat) : Bool := (state r c).1

def words (r c : Nat) : Word := (state r c).2

theorem checkCode_old (r c : Nat) (hc : checkCode r c = true) : lowCheckCode r c = true := by
  obtain ⟨t, ht, hg⟩ := (state_exact r c).mp hc
  rw [← ht, lowCheckCode_code]
  exact grammar_low hg

theorem words_spec (r c : Nat) (hc : checkCode r c = true) :
    GoodWord (words r c) ∧ principalSum ((words r c).map value) = interpretation r c := by
  obtain ⟨t, ht, hg⟩ := (state_exact r c).mp hc
  rw [← ht, interpretation_code]
  exact grammar_word hg

private def row (R c : Nat) : List State :=
  (List.range (R + 1)).map (fun r => state r c)

private theorem row_get (R c r : Nat) (hr : r ≤ R) :
    (row R c)[r]?.getD (false, []) = state r c := by
  simp [row, List.getElem?_range (Nat.lt_succ_of_le hr)]

private def fetch (history : List (List State)) (c r : Nat) : State :=
  ((history[c]?.getD [])[r]?).getD (false, [])

private def combine (a b : State) : State := (a.1 && b.1, a.2 ++ b.2)

private def entry (history : List (List State)) (r : Nat) : State :=
  let c := history.length
  let k := c - 1
  let tag := k.unpair.1
  let p := k.unpair.2
  cond (r == 0) (SourceOne.PublicCodes.lowCheckCode c, baseWord c)
    (cond (c == 0) (false, [])
      (cond (tag == 0) (fetch history p (r - 1))
        (cond (tag == 1) (combine (fetch history p.unpair.1 r) (fetch history p.unpair.2 r))
          (cond (tag == 2)
            (p.unpair.1 == 0 && p.unpair.2 == zeroCode r, [(r, 0)]) (false, [])))))

private theorem fetch_primrec : Primrec (fun p : List (List State) × (Nat × Nat) =>
    fetch p.1 p.2.1 p.2.2) := by
  have hr : Primrec (fun p : List (List State) × (Nat × Nat) =>
      p.1[p.2.1]?.getD []) := Primrec.option_getD.comp
    (Primrec.list_getElem?.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
    (Primrec.const ([] : List State))
  exact Primrec.option_getD.comp (Primrec.list_getElem?.comp hr (Primrec.snd.comp Primrec.snd))
    (Primrec.const (false, []))

private theorem combine_primrec : Primrec₂ combine :=
  ((Primrec.and.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)).pair
    (Primrec.list_append.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))).to₂

private theorem entry_primrec : Primrec₂ entry := by
  have hc : Primrec (fun p : List (List State) × Nat => p.1.length) :=
    Primrec.list_length.comp Primrec.fst
  have hk := Primrec.nat_sub.comp hc (Primrec.const 1)
  have htag := Primrec.fst.comp (Primrec.unpair.comp hk)
  have hp := Primrec.snd.comp (Primrec.unpair.comp hk)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hp)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hp)
  have get (f g : List (List State) × Nat → Nat) (hf : Primrec f) (hg : Primrec g) :
      Primrec (fun p : List (List State) × Nat => fetch p.1 (f p) (g p)) :=
    fetch_primrec.comp (Primrec.fst.pair (hf.pair hg))
  have tag (i : Nat) := Primrec.beq.comp htag (Primrec.const i)
  have htheta := (Primrec.and.comp (Primrec.beq.comp hl (Primrec.const 0))
    (Primrec.beq.comp hr (zeroCode_primrec.comp Primrec.snd))).pair
    (Primrec.list_cons.comp (Primrec.snd.pair (Primrec.const 0)) (Primrec.const []))
  exact ((Primrec.beq.comp Primrec.snd (Primrec.const 0)).cond
    ((SourceOne.PublicCodes.lowCheckCode_primrec.comp hc).pair (baseWord_primrec.comp hc))
    ((Primrec.beq.comp hc (Primrec.const 0)).cond (Primrec.const (false, []))
      ((tag 0).cond (get _ _ hp (Primrec.nat_sub.comp Primrec.snd (Primrec.const 1)))
        ((tag 1).cond (combine_primrec.comp (get _ _ hl Primrec.snd) (get _ _ hr Primrec.snd))
          ((tag 2).cond htheta (Primrec.const (false, []))))))).to₂

private def rowStep (R : Nat) (history : List (List State)) : List State :=
  (List.range (R + 1)).map (entry history)

private theorem rowStep_primrec : Primrec₂ rowStep := by
  have hr : Primrec (fun p : Nat × List (List State) => List.range (p.1 + 1)) :=
    Primrec.list_range.comp (Primrec.succ.comp Primrec.fst)
  have he : Primrec₂ (fun p : Nat × List (List State) => entry p.2) :=
    (entry_primrec.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
  exact (Primrec.list_map hr he).to₂

private theorem entry_correct (R c r : Nat) (hr : r ≤ R) :
    entry ((List.range c).map (row R)) r = state r c := by
  cases r with
  | zero => simp [entry, state]
  | succ r =>
    cases c with
    | zero => simp [entry, state]
    | succ c =>
      have hp : c.unpair.2 < c + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le c)
      have hl : c.unpair.2.unpair.1 < c + 1 := (Nat.unpair_left_le _).trans_lt hp
      have hh : c.unpair.2.unpair.2 < c + 1 := (Nat.unpair_right_le _).trans_lt hp
      have hprev : r ≤ R := (Nat.le_succ r).trans hr
      simp [entry, state, fetch, combine, List.getElem?_range hp, List.getElem?_range hl,
        List.getElem?_range hh, row_get R _ r hprev, row_get R _ (r + 1) hr,
        Bool.beq_eq_decide_eq]
      split_ifs <;> simp_all

private theorem rowStep_correct (R c : Nat) :
    rowStep R ((List.range c).map (row R)) = row R c := by
  unfold rowStep row
  apply List.map_congr_left
  intro r hr
  exact entry_correct R c r (Nat.le_of_lt_succ (List.mem_range.mp hr))

private theorem row_primrec : Primrec₂ row :=
  Primrec.nat_strong_rec row (Primrec.option_some.comp₂ rowStep_primrec) (by
    intro R c
    simpa only [rowStep] using congrArg some (rowStep_correct R c))

/-- Genuine uniform effectivity in both the level and the literal raw code. -/
theorem state_primrec : Primrec₂ state := by
  have h := Primrec.option_getD.comp
    (Primrec.list_getElem?.comp row_primrec Primrec.fst) (Primrec.const (false, []))
  have heq : (fun p : Nat × Nat => (row p.1 p.2)[p.1]?.getD (false, [])) =
      (fun p : Nat × Nat => state p.1 p.2) := by
    funext p
    exact row_get p.1 p.2 p.1 le_rfl
  rw [heq] at h
  exact h.to₂

theorem checkCode_primrec : Primrec₂ checkCode := Primrec.fst.comp₂ state_primrec

theorem words_primrec : Primrec₂ words := Primrec.snd.comp₂ state_primrec

def less (r c s d : Nat) : Bool :=
  (checkCode r c && checkCode s d) && wordLess (words r c) (words s d)

theorem less_primrec : Primrec (fun p : (Nat × Nat) × (Nat × Nat) => less p.1.1 p.1.2 p.2.1 p.2.2) := by
  have hc : Primrec (fun p : (Nat × Nat) × (Nat × Nat) => checkCode p.1.1 p.1.2) :=
    checkCode_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)
  have hd : Primrec (fun p : (Nat × Nat) × (Nat × Nat) => checkCode p.2.1 p.2.2) :=
    checkCode_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  have hw : Primrec (fun p : (Nat × Nat) × (Nat × Nat) => words p.1.1 p.1.2) :=
    words_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)
  have hv : Primrec (fun p : (Nat × Nat) × (Nat × Nat) => words p.2.1 p.2.2) :=
    words_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  exact Primrec.and.comp (Primrec.and.comp hc hd) (wordLess_primrec.comp hw hv)

theorem less_correct (r c s d : Nat) (hc : checkCode r c = true) (hd : checkCode s d = true) :
    less r c s d = true ↔ interpretation r c < interpretation s d := by
  have hs := words_spec r c hc
  have ht := words_spec s d hd
  simpa only [less, hc, hd, Bool.true_and, hs.2, ht.2] using
    wordLess_correct (words r c) (words s d) hs.1 ht.1

def equal (r c s d : Nat) : Bool :=
  (checkCode r c && checkCode s d) && (!less r c s d && !less s d r c)

theorem equal_primrec : Primrec (fun p : (Nat × Nat) × (Nat × Nat) => equal p.1.1 p.1.2 p.2.1 p.2.2) := by
  have hc : Primrec (fun p : (Nat × Nat) × (Nat × Nat) => checkCode p.1.1 p.1.2) :=
    checkCode_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)
  have hd : Primrec (fun p : (Nat × Nat) × (Nat × Nat) => checkCode p.2.1 p.2.2) :=
    checkCode_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  have hr : Primrec (fun p : (Nat × Nat) × (Nat × Nat) => less p.2.1 p.2.2 p.1.1 p.1.2) :=
    less_primrec.comp (Primrec.snd.pair Primrec.fst)
  exact Primrec.and.comp (Primrec.and.comp hc hd)
    (Primrec.and.comp (Primrec.not.comp less_primrec) (Primrec.not.comp hr))

theorem equal_correct (r c s d : Nat) (hc : checkCode r c = true) (hd : checkCode s d = true) :
    equal r c s d = true ↔ interpretation r c = interpretation s d := by
  have hn (b : Bool) : ((!b) = true) ↔ ¬ (b = true) := by cases b <;> decide
  simp only [equal, hc, hd, Bool.true_and, Bool.and_eq_true, hn,
    less_correct r c s d hc hd, less_correct s d r c hd hc, not_lt]
  constructor
  · intro h
    exact le_antisymm h.2 h.1
  · intro h
    exact ⟨h.ge, h.le⟩

theorem less_exact (r c s d : Nat) : less r c s d = true ↔
    checkCode r c = true ∧ checkCode s d = true ∧ interpretation r c < interpretation s d := by
  constructor
  · intro h
    have hg := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1)
    exact ⟨hg.1, hg.2, (less_correct r c s d hg.1 hg.2).mp h⟩
  · rintro ⟨hc, hd, h⟩
    exact (less_correct r c s d hc hd).mpr h

theorem equal_exact (r c s d : Nat) : equal r c s d = true ↔
    checkCode r c = true ∧ checkCode s d = true ∧ interpretation r c = interpretation s d := by
  constructor
  · intro h
    have hg := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1)
    exact ⟨hg.1, hg.2, (equal_correct r c s d hg.1 hg.2).mp h⟩
  · rintro ⟨hc, hd, h⟩
    exact (equal_correct r c s d hc hd).mpr h

def liftCode (c : Nat) : Nat := (.parameter c : RelativeTerm Nat).code

theorem liftCode_primrec : Primrec liftCode := code_primrec.comp parameter_primrec

def embedCode (steps c : Nat) : Nat := Nat.rec c (fun _ previous => liftCode previous) steps

theorem embedCode_primrec : Primrec₂ embedCode := by
  have h : Primrec₂ (fun c steps => embedCode steps c) :=
    Primrec.nat_rec Primrec.id ((liftCode_primrec.comp (Primrec.snd.comp Primrec.snd)).to₂)
  exact (h.comp Primrec.snd Primrec.fst).to₂

theorem embed_state (r steps c : Nat) : state (r + steps) (embedCode steps c) = state r c := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
    change state (r + (steps + 1)) (liftCode (embedCode steps c)) = _
    rw [Nat.add_succ]
    exact (state_parameter (r + steps) (embedCode steps c)).trans ih

theorem embed_checked (r steps c : Nat) (hc : checkCode r c = true) :
    checkCode (r + steps) (embedCode steps c) = true := by
  simpa only [checkCode, embed_state] using hc

theorem embed_value (r steps c : Nat) (hc : checkCode r c = true) :
    interpretation (r + steps) (embedCode steps c) = interpretation r c := by
  have hs := words_spec r c hc
  have ht := words_spec (r + steps) (embedCode steps c) (embed_checked r steps c hc)
  have hw : words (r + steps) (embedCode steps c) = words r c :=
    congrArg Prod.snd (embed_state r steps c)
  rw [hw] at ht
  exact ht.2.symm.trans hs.2

theorem embed_equal (r steps c : Nat) (hc : checkCode r c = true) :
    equal r c (r + steps) (embedCode steps c) = true :=
  (equal_correct _ _ _ _ hc (embed_checked r steps c hc)).mpr (embed_value r steps c hc).symm

theorem parameter_before_base (r c : Nat) (hc : checkCode r c = true) :
    interpretation (r + 1) (liftCode c) < finiteBase (r + 1) := by
  rw [show liftCode c = embedCode 1 c from rfl, embed_value r 1 c hc]
  exact (lt_nextBase_iff_code r _).mpr ⟨c, checkCode_old r c hc, rfl⟩

def freshCode (r : Nat) : Nat := (.theta 0 (zeroTree r) : RelativeTerm Nat).code

theorem freshCode_primrec : Primrec freshCode := by
  have hp := Primrec₂.natPair.comp (Primrec.const 0) zeroCode_primrec
  have h := Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 2) hp)
  exact h.of_eq (fun r => by simp only [freshCode, code_theta, zeroCode_eq])

theorem fresh_checked (r : Nat) : checkCode r (freshCode r) = true := by
  cases r with
  | zero =>
    change (state 0 (freshCode 0)).1 = true
    rw [state_zero]
    change SourceOne.PublicCodes.lowCheckCode (.theta 0 (zeroTree 0) : RelativeTerm Nat).code = true
    rw [SourceOne.PublicCodes.lowCheckCode_code]
    exact fresh_low 0
  | succ r => exact grammar_state (.fresh r)

theorem fresh_value (r : Nat) : interpretation r (freshCode r) = finiteBase r := by
  rw [freshCode, interpretation_code]
  change globalCollapse (finiteBase r) 0 (denote r (zeroTree r)) = finiteBase r
  rw [zeroTree_denote, finiteBase_collapse_zero_base]

theorem parameter_less_fresh (r c : Nat) (hc : checkCode r c = true) :
    less (r + 1) (liftCode c) (r + 1) (freshCode (r + 1)) = true := by
  apply (less_correct _ _ _ _ (embed_checked r 1 c hc) (fresh_checked (r + 1))).mpr
  rw [fresh_value]
  exact parameter_before_base r c hc

theorem fresh_less_fresh (r s : Nat) (h : r < s) : less r (freshCode r) s (freshCode s) = true := by
  apply (less_correct _ _ _ _ (fresh_checked r) (fresh_checked s)).mpr
  rw [fresh_value, fresh_value]
  exact bases_strictMono h

end Alexander313.Wilken.RelativeTerm.Hereditary.BaseArithmetic
