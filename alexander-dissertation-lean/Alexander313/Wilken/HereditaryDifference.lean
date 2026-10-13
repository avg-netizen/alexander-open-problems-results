import Alexander313.Wilken.HereditaryAddition
import Alexander313.Wilken.HereditaryPrincipalClassification

/-!
# Genuine right difference on the original hereditary public domain

Principal words are obtained by the actual normalizer and earlier-payload
opening. Equal initial principal values are removed. At the first unequal
principal, the whole remaining right suffix is retained. On ordered inputs,
principal closure proves absorption of the remaining left suffix. The result
therefore satisfies α + γ = β and is the actual ordinal right subtraction
β - α. A finite list fold implements the literal operation uniformly PR.

All original input admissions and cross-level values are retained. The ordered
operation rejects malformed or reversed inputs with raw zero. Full subtraction
instead gives an admitted zero tree on checked reversed pairs.
No ordinal arithmetic or effectivity oracle is an input. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.Difference

open Theta ThetaCourse

def removeCommon {α : Type} (equal : α → α → Bool) : List α → List α → List α
  | [], bs => bs
  | _ :: _, [] => []
  | a :: as, b :: bs => cond (equal a b) (removeCommon equal as bs) (b :: bs)

theorem removeCommon_mem {α : Type} (equal : α → α → Bool) (as bs : List α) (p : α)
    (hp : p ∈ removeCommon equal as bs) : p ∈ bs := by
  revert bs hp
  induction as with
  | nil => intro bs hp; exact hp
  | cons a as ih =>
    intro bs hp
    cases bs with
    | nil => simp [removeCommon] at hp
    | cons b bs =>
      cases h : equal a b with
      | false => simpa only [removeCommon, h, Bool.cond_false] using hp
      | true => exact List.mem_cons_of_mem _ (ih bs (by simpa only [removeCommon, h, Bool.cond_true] using hp))

theorem removeCommon_normal {α : Type} (equal : α → α → Bool) (value : α → Ordinal.{0})
    (as bs : List α) (hbs : IsAdditiveNormalForm (bs.map value)) :
    IsAdditiveNormalForm ((removeCommon equal as bs).map value) := by
  revert bs hbs
  induction as with
  | nil => intro bs hbs; exact hbs
  | cons a as ih =>
    intro bs hbs
    cases bs with
    | nil => exact additiveNormalForm_nil
    | cons b bs =>
      cases h : equal a b with
      | false => simpa only [removeCommon, h, Bool.cond_false] using hbs
      | true => simpa only [removeCommon, h, Bool.cond_true] using ih bs (additiveNormalForm_tail hbs)

private theorem difference_add_le_left_iff (a b c : Ordinal.{0}) :
    a + b ≤ a + c ↔ b ≤ c := by
  constructor
  · intro h
    apply le_of_not_gt
    intro hcb
    have hstrict : a + c < a + b := lt_of_le_of_ne (add_le_add_right hcb.le a)
      (fun he => hcb.ne (add_left_cancel he))
    exact (not_le_of_gt hstrict) h
  · intro h; exact add_le_add_right h a

/-- This proof uses actual principal closure at the first strict mismatch.
It applies to arbitrary finite ordered principal words, including repetitions. -/
theorem removeCommon_add {α : Type} (equal : α → α → Bool) (value : α → Ordinal.{0})
    (as bs : List α) (has : IsAdditiveNormalForm (as.map value))
    (hbs : IsAdditiveNormalForm (bs.map value))
    (equal_exact : ∀ a ∈ as, ∀ b ∈ bs, equal a b = true ↔ value a = value b)
    (ordered : principalSum (as.map value) ≤ principalSum (bs.map value)) :
    principalSum (as.map value) + principalSum ((removeCommon equal as bs).map value) =
      principalSum (bs.map value) := by
  revert bs has hbs equal_exact ordered
  induction as with
  | nil => intro bs _ _ _ _; simp [removeCommon, principalSum]
  | cons a as ih =>
    intro bs has hbs equal_exact ordered
    cases bs with
    | nil =>
      have hpositive : 0 < principalSum ((a :: as).map value) :=
        (has.1 _ (List.mem_cons_self)).1.trans_le le_self_add
      exact False.elim ((not_le_of_gt hpositive) ordered)
    | cons b bs =>
      have head_exact := equal_exact a List.mem_cons_self b List.mem_cons_self
      cases hcmp : equal a b with
      | true =>
        have he : value a = value b := head_exact.mp hcmp
        have htail : principalSum (as.map value) ≤ principalSum (bs.map value) := by
          apply (difference_add_le_left_iff (value b) _ _).mp
          simpa only [List.map_cons, principalSum, he] using ordered
        have hd := ih bs (additiveNormalForm_tail has) (additiveNormalForm_tail hbs)
          (fun x hx y hy => equal_exact x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)) htail
        simp only [removeCommon, hcmp, Bool.cond_true, List.map_cons, principalSum, he]
        rw [add_assoc, hd]
      | false =>
        have hne : value a ≠ value b := by
          intro he
          have ht := head_exact.mpr he
          simp only [hcmp, Bool.false_eq_true] at ht
        have hhead : value a < value b := by
          apply lt_of_le_of_ne _ hne
          apply le_of_not_gt
          intro hba
          have hsmall : principalSum ((b :: bs).map value) < value a := by
            apply principalSum_lt (has.1 _ List.mem_cons_self).1 (has.1 _ List.mem_cons_self).2
            intro p hp
            rcases List.mem_cons.mp hp with rfl | hp
            · exact hba
            · exact (additiveNormalForm_head_ge hbs hp).trans_lt hba
          have hreverse : principalSum ((b :: bs).map value) < principalSum ((a :: as).map value) :=
            hsmall.trans_le le_self_add
          exact (not_le_of_gt hreverse) ordered
        have hsmall : principalSum ((a :: as).map value) < value b := by
          apply principalSum_lt (hbs.1 _ List.mem_cons_self).1 (hbs.1 _ List.mem_cons_self).2
          intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · exact hhead
          · exact (additiveNormalForm_head_ge has hp).trans_lt hhead
        have absorb := (hbs.1 _ List.mem_cons_self).2.add_eq_right hsmall
        simp only [removeCommon, hcmp, Bool.cond_false]
        change principalSum ((a :: as).map value) + (value b + principalSum (bs.map value)) = _
        rw [← add_assoc, absorb]
        rfl

abbrev State (α : Type) := List α × Bool

def stripStep {α : Type} (equal : α → α → Bool) (a : α) (s : State α) : State α :=
  cond s.2 s (match s.1 with
    | [] => ([], true)
    | b :: bs => cond (equal a b) (bs, false) (b :: bs, true))

def stripRun {α : Type} (equal : α → α → Bool) (as bs : List α) : List α :=
  (as.foldl (fun s a => stripStep equal a s) (bs, false)).1

private theorem difference_strip_absorbed {α : Type} (equal : α → α → Bool) (as bs : List α) :
    as.foldl (fun s a => stripStep equal a s) (bs, true) = (bs, true) := by
  induction as <;> simp_all [stripStep]

theorem stripRun_eq {α : Type} (equal : α → α → Bool) (as bs : List α) :
    stripRun equal as bs = removeCommon equal as bs := by
  induction as generalizing bs with
  | nil => rfl
  | cons a as ih =>
    cases bs with
    | nil =>
      simpa only [stripRun, List.foldl_cons, stripStep, Bool.cond_false, removeCommon] using
        congrArg Prod.fst (difference_strip_absorbed equal as [])
    | cons b bs =>
      cases h : equal a b with
      | false =>
        simpa only [stripRun, List.foldl_cons, stripStep, Bool.cond_false, removeCommon, h] using
          congrArg Prod.fst (difference_strip_absorbed equal as (b :: bs))
      | true =>
        simpa only [stripRun, List.foldl_cons, stripStep, Bool.cond_false, removeCommon, h,
          Bool.cond_true] using ih bs

private def stripNumeric {α : Type} (default : α) (equal : α → α → Bool)
    (a : α) (s : State α) : State α :=
  cond s.2 s (cond (s.1.length == 0) ([], true)
    (cond (equal a (s.1[0]?.getD default)) (s.1.tail, false) (s.1, true)))

private theorem difference_stripNumeric_eq {α : Type} (default : α) (equal : α → α → Bool)
    (a : α) (s : State α) : stripNumeric default equal a s = stripStep equal a s := by
  rcases s with ⟨bs, done⟩
  cases done <;> cases bs <;> simp [stripNumeric, stripStep]

theorem removeCommon_primrec {α Data : Type} [Primcodable α] [Primcodable Data]
    (default : α) (equal : Data → α → α → Bool)
    (he : Primrec (fun p : Data × (α × α) => equal p.1 p.2.1 p.2.2)) :
    Primrec (fun p : Data × (List α × List α) => removeCommon (equal p.1) p.2.1 p.2.2) := by
  have hs : Primrec₂ (fun p : Data × (List α × List α) => fun q : State α × α =>
      stripNumeric default (equal p.1) q.2 q.1) := by
    have hstate : Primrec (fun p : (Data × (List α × List α)) × (State α × α) => p.2.1) := Primrec.fst.comp Primrec.snd
    have hbs := Primrec.fst.comp hstate
    have hdone := Primrec.snd.comp hstate
    have ha : Primrec (fun p : (Data × (List α × List α)) × (State α × α) => p.2.2) :=
      Primrec.snd.comp Primrec.snd
    have hhead := Primrec.option_getD.comp (Primrec.list_getElem?.comp hbs (Primrec.const 0))
      (Primrec.const default)
    have hcmp := he.comp ((Primrec.fst.comp Primrec.fst).pair (ha.pair hhead))
    exact (hdone.cond hstate
      ((Primrec.beq.comp (Primrec.list_length.comp hbs) (Primrec.const 0)).cond
        (Primrec.const ([], true))
        (hcmp.cond ((Primrec.list_tail.comp hbs).pair (Primrec.const false))
          (hbs.pair (Primrec.const true))))).to₂
  have hfold := Primrec.list_foldl (Primrec.fst.comp Primrec.snd)
    ((Primrec.snd.comp Primrec.snd).pair (Primrec.const false)) hs
  have hrun := Primrec.fst.comp hfold
  have heq : (fun p : Data × (List α × List α) =>
      (p.2.1.foldl (fun s a => stripNumeric default (equal p.1) a s) (p.2.2, false)).1) =
      (fun p : Data × (List α × List α) => removeCommon (equal p.1) p.2.1 p.2.2) := by
    funext p
    simp only [difference_stripNumeric_eq]
    exact stripRun_eq _ _ _
  rw [heq] at hrun
  exact hrun

def word (r c d : Nat) : List (RelativeTerm Nat) :=
  removeCommon (Theta.equal r) (Principal.normalizedAtoms r c) (Principal.normalizedAtoms r d)

theorem word_primrec : Primrec
    (fun p : Nat × (Nat × Nat) => word p.1 p.2.1 p.2.2) :=
  (removeCommon_primrec (.parameter 0) Theta.equal Theta.Effective.equal_primrec).comp
    (Primrec.fst.pair
      ((Principal.normalizedAtoms_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd)).pair
        (Principal.normalizedAtoms_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd))))

theorem word_normal (r c d : Nat) (hd : checkCode r d = true) :
    IsAdditiveNormalForm ((word r c d).map (denote r)) := by
  apply removeCommon_normal
  rw [Principal.normalizedAtoms_anf r d hd]
  exact canonicalANF_normal _

theorem word_add (r c d : Nat) (hc : checkCode r c = true) (hd : checkCode r d = true)
    (hle : interpretation r c ≤ interpretation r d) :
    interpretation r c + principalSum ((word r c d).map (denote r)) = interpretation r d := by
  have ha := Principal.normalizedAtoms_anf r c hc
  have hb := Principal.normalizedAtoms_anf r d hd
  have hnormalA : IsAdditiveNormalForm ((Principal.normalizedAtoms r c).map (denote r)) := by
    rw [ha]; exact canonicalANF_normal _
  have hnormalB : IsAdditiveNormalForm ((Principal.normalizedAtoms r d).map (denote r)) := by
    rw [hb]; exact canonicalANF_normal _
  have h := removeCommon_add (Theta.equal r) (denote r)
    (Principal.normalizedAtoms r c) (Principal.normalizedAtoms r d) hnormalA hnormalB
    (by
      intro a ham b hbm
      have hs := Principal.normalizedAtoms_admitted r c hc a ham
      have ht := Principal.normalizedAtoms_admitted r d hd b hbm
      exact Theta.equal_correct r a b
        (by simpa only [checkCode_code] using hs.1)
        (by simpa only [checkCode_code] using ht.1) hs.2.1 ht.2.1)
    (by simpa only [ha, hb, principalSum_canonicalANF] using hle)
  simpa only [ha, hb, principalSum_canonicalANF, word] using h

def tree (r c d : Nat) : RelativeTerm Nat := Normalization.buildAtoms r (word r c d)

theorem tree_primrec : Primrec
    (fun p : Nat × (Nat × Nat) => tree p.1 p.2.1 p.2.2) :=
  Normalization.Effective.buildAtoms_primrec.comp Primrec.fst word_primrec

theorem tree_spec (r c d : Nat) (hc : checkCode r c = true) (hd : checkCode r d = true)
    (hle : interpretation r c ≤ interpretation r d) :
    check r (tree r c d) = true ∧ Normal r (tree r c d) ∧
      interpretation r c + denote r (tree r c d) = interpretation r d ∧
      denote r (tree r c d) = interpretation r d - interpretation r c := by
  let t := Principal.normalizedTree r d
  let n := SourceOne.PublicCodes.fragment t
  have hs := Principal.normalizedTree_spec r d hd
  have ht : admissible r n t := (finiteCheck_iff r n t).mp hs.1
  have good := Normalization.GoodAtoms.atoms r n t ht hs.2.1
  have goodWord : Normalization.GoodAtoms r n (word r c d) := by
    intro a ha
    apply good a
    exact removeCommon_mem _ _ _ _ ha
  have hadm := Normalization.buildAtoms_admissible r n (word r c d) goodWord
  have hnormal := Normalization.buildAtoms_normal r n (word r c d) goodWord (word_normal r c d hd)
  have hsum : interpretation r c + denote r (tree r c d) = interpretation r d := by
    rw [tree, Normalization.buildAtoms_denote]
    exact word_add r c d hc hd hle
  refine ⟨admitted_checked hadm, hnormal, hsum, ?_⟩
  exact add_left_cancel (hsum.trans (Ordinal.add_sub_cancel_of_le hle).symm)

private theorem difference_not_bool_iff (b : Bool) : ((!b) = true) ↔ ¬(b = true) := by
  cases b <;> decide

def guard (r c d : Nat) : Bool :=
  (checkCode r c && checkCode r d) && !Normalization.lessRawCode r d c

theorem guard_primrec : Primrec
    (fun p : Nat × (Nat × Nat) => guard p.1 p.2.1 p.2.2) :=
  Primrec.and.comp
    (Primrec.and.comp
      (Uniform.hereditaryCheckCode_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Uniform.hereditaryCheckCode_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd)))
    (Primrec.not.comp (Normalization.Effective.lessRawCode_primrec.comp
      (Primrec.fst.pair ((Primrec.snd.comp Primrec.snd).pair (Primrec.fst.comp Primrec.snd)))))

theorem guard_exact (r c d : Nat) : guard r c d = true ↔
    checkCode r c = true ∧ checkCode r d = true ∧ interpretation r c ≤ interpretation r d := by
  simp only [guard, Bool.and_eq_true, and_assoc, difference_not_bool_iff]
  constructor
  · rintro ⟨hc, hd, hn⟩
    exact ⟨hc, hd, le_of_not_gt (fun h => hn ((Normalization.lessRawCode_correct r d c hd hc).mpr h))⟩
  · rintro ⟨hc, hd, hle⟩
    exact ⟨hc, hd, fun h => (not_lt_of_ge hle) ((Normalization.lessRawCode_correct r d c hd hc).mp h)⟩

def differenceCode (r c d : Nat) : Nat := cond (guard r c d) (tree r c d).code 0

theorem differenceCode_primrec : Primrec
    (fun p : Nat × (Nat × Nat) => differenceCode p.1 p.2.1 p.2.2) :=
  guard_primrec.cond (code_primrec.comp tree_primrec) (Primrec.const 0)

theorem differenceCode_rejected (r c d : Nat) (h : guard r c d = false) :
    differenceCode r c d = 0 := by simp only [differenceCode, h, Bool.cond_false]

theorem differenceCode_checked (r c d : Nat) (hc : checkCode r c = true) (hd : checkCode r d = true)
    (hle : interpretation r c ≤ interpretation r d) :
    acceptedCode r (differenceCode r c d) = true ∧
      interpretation r c + interpretation r (differenceCode r c d) = interpretation r d ∧
      interpretation r (differenceCode r c d) = interpretation r d - interpretation r c := by
  have hguard := (guard_exact r c d).mpr ⟨hc, hd, hle⟩
  have hs := tree_spec r c d hc hd hle
  simp only [differenceCode, hguard, Bool.cond_true, interpretation_code]
  exact ⟨(acceptedCode_iff _ _).mpr ⟨by simpa only [checkCode_code] using hs.1,
    by simpa only [rawTree_code] using hs.2.1⟩, hs.2.2⟩

private theorem difference_low_of_value (r : Nat) (a : RelativeTerm Nat)
    (ha : check r a = true) (hvalue : denote r a < finiteBase (r + 1)) :
    lowCheck r a = true := by
  have hsort : a.outerSort ≤ 1 :=
    (denote_lt_iff_outerSort_le r a ha 1 (Nat.zero_lt_succ 0)).mp
      (hvalue.trans (finiteBase_lt_cardinal r))
  simp only [lowCheck, ha, hsort, decide_true, Bool.true_and]

theorem differenceCode_lowChecked (r c d : Nat)
    (hc : lowCheckCode r c = true) (hd : lowCheckCode r d = true)
    (hle : interpretation r c ≤ interpretation r d) :
    acceptedLowCode r (differenceCode r c d) = true ∧
      interpretation r c + interpretation r (differenceCode r c d) = interpretation r d ∧
      interpretation r (differenceCode r c d) = interpretation r d - interpretation r c := by
  have hc' := (Bool.and_eq_true_iff.mp (by simpa only [lowCheckCode_eq] using hc)).1
  have hd' := (Bool.and_eq_true_iff.mp (by simpa only [lowCheckCode_eq] using hd)).1
  have hguard := (guard_exact r c d).mpr ⟨hc', hd', hle⟩
  have hs := tree_spec r c d hc' hd' hle
  have hbound : denote r (tree r c d) < finiteBase (r + 1) :=
    (le_add_self.trans_eq hs.2.2.1).trans_lt ((lt_nextBase_iff_code r _).mpr ⟨d, hd, rfl⟩)
  have hlow := difference_low_of_value r (tree r c d) hs.1 hbound
  simp only [differenceCode, hguard, Bool.cond_true, interpretation_code]
  exact ⟨(acceptedLowCode_iff _ _).mpr ⟨by simpa only [lowCheckCode_code] using hlow,
    by simpa only [rawTree_code] using hs.2.1⟩, hs.2.2⟩

def crossGuard (r c s d : Nat) : Bool :=
  (lowCheckCode r c && lowCheckCode s d) && !HereditaryThetaProgram.crossLess s d r c

theorem crossGuard_primrec : Primrec
    (fun p : (Nat × Nat) × (Nat × Nat) => crossGuard p.1.1 p.1.2 p.2.1 p.2.2) :=
  Primrec.and.comp
    (Primrec.and.comp
      (Uniform.hereditaryLowCheckCode_primrec.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.snd.comp Primrec.fst))
      (Uniform.hereditaryLowCheckCode_primrec.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)))
    (Primrec.not.comp (HereditaryThetaProgram.crossLess_primrec.comp (Primrec.snd.pair Primrec.fst)))

theorem crossGuard_exact (r c s d : Nat) : crossGuard r c s d = true ↔
    lowCheckCode r c = true ∧ lowCheckCode s d = true ∧ interpretation r c ≤ interpretation s d := by
  simp only [crossGuard, Bool.and_eq_true, and_assoc, difference_not_bool_iff]
  constructor
  · rintro ⟨hc, hd, hn⟩
    exact ⟨hc, hd, le_of_not_gt (fun h => hn ((HereditaryThetaProgram.crossLess_exact s d r c).mpr
      ⟨hd, hc, h⟩))⟩
  · rintro ⟨hc, hd, hle⟩
    exact ⟨hc, hd, fun h => (not_lt_of_ge hle) ((HereditaryThetaProgram.crossLess_exact s d r c).mp h).2.2⟩

def crossDifference (r c s d : Nat) : Nat :=
  cond (crossGuard r c s d)
    (differenceCode (max r s) (HereditaryThetaProgram.alignCode r s c)
      (HereditaryThetaProgram.alignCode s r d)) 0

theorem crossDifference_primrec : Primrec
    (fun p : (Nat × Nat) × (Nat × Nat) => crossDifference p.1.1 p.1.2 p.2.1 p.2.2) := by
  have hr : Primrec (fun p : (Nat × Nat) × (Nat × Nat) => p.1.1) := Primrec.fst.comp Primrec.fst
  have hs : Primrec (fun p : (Nat × Nat) × (Nat × Nat) => p.2.1) := Primrec.fst.comp Primrec.snd
  have hc : Primrec (fun p : (Nat × Nat) × (Nat × Nat) => p.1.2) := Primrec.snd.comp Primrec.fst
  have hd : Primrec (fun p : (Nat × Nat) × (Nat × Nat) => p.2.2) := Primrec.snd.comp Primrec.snd
  have hl := HereditaryThetaProgram.alignCode_primrec.comp ((hr.pair hs).pair hc)
  have hh := HereditaryThetaProgram.alignCode_primrec.comp ((hs.pair hr).pair hd)
  exact crossGuard_primrec.cond
    (differenceCode_primrec.comp ((Primrec.nat_max.comp hr hs).pair (hl.pair hh))) (Primrec.const 0)

theorem crossDifference_rejected (r c s d : Nat) (h : crossGuard r c s d = false) :
    crossDifference r c s d = 0 := by simp only [crossDifference, h, Bool.cond_false]

theorem crossDifference_checked (r c s d : Nat)
    (hc : lowCheckCode r c = true) (hd : lowCheckCode s d = true)
    (hle : interpretation r c ≤ interpretation s d) :
    acceptedLowCode (max r s) (crossDifference r c s d) = true ∧
      interpretation r c + interpretation (max r s) (crossDifference r c s d) = interpretation s d ∧
      interpretation (max r s) (crossDifference r c s d) = interpretation s d - interpretation r c := by
  have hl := HereditaryThetaProgram.alignCode_checked r s c hc
  have hh : lowCheckCode (max r s) (HereditaryThetaProgram.alignCode s r d) = true := by
    simpa only [max_comm s r] using HereditaryThetaProgram.alignCode_checked s r d hd
  have hlvalue := HereditaryThetaProgram.alignCode_value r s c
  have hhvalue : interpretation (max r s) (HereditaryThetaProgram.alignCode s r d) = interpretation s d := by
    simpa only [max_comm s r] using HereditaryThetaProgram.alignCode_value s r d
  have hs := differenceCode_lowChecked (max r s) _ _ hl hh
    (by simpa only [hlvalue, hhvalue] using hle)
  have hguard := (crossGuard_exact r c s d).mpr ⟨hc, hd, hle⟩
  simpa only [crossDifference, hguard, Bool.cond_true, hlvalue, hhvalue] using hs

def unionGuard (q v : Nat) : Bool :=
  crossGuard q.unpair.1 q.unpair.2 v.unpair.1 v.unpair.2

theorem unionGuard_primrec : Primrec₂ unionGuard :=
  (crossGuard_primrec.comp ((Primrec.unpair.comp Primrec.fst).pair
    (Primrec.unpair.comp Primrec.snd))).to₂

theorem unionGuard_exact (q v : Nat) : unionGuard q v = true ↔
    unionCheck q = true ∧ unionCheck v = true ∧ unionInterpretation q ≤ unionInterpretation v :=
  crossGuard_exact q.unpair.1 q.unpair.2 v.unpair.1 v.unpair.2

def unionDifference (q v : Nat) : Nat :=
  cond (unionGuard q v) (Nat.pair (max q.unpair.1 v.unpair.1)
    (crossDifference q.unpair.1 q.unpair.2 v.unpair.1 v.unpair.2)) 0

theorem unionDifference_primrec : Primrec₂ unionDifference := by
  have hq : Primrec (fun p : Nat × Nat => p.1.unpair) := Primrec.unpair.comp Primrec.fst
  have hv : Primrec (fun p : Nat × Nat => p.2.unpair) := Primrec.unpair.comp Primrec.snd
  exact (unionGuard_primrec.cond
    (Primrec₂.natPair.comp (Primrec.nat_max.comp (Primrec.fst.comp hq) (Primrec.fst.comp hv))
      (crossDifference_primrec.comp (hq.pair hv))) (Primrec.const 0)).to₂

theorem unionDifference_rejected (q v : Nat) (h : unionGuard q v = false) :
    unionDifference q v = 0 := by simp only [unionDifference, h, Bool.cond_false]

theorem unionDifference_checked (q v : Nat) (hq : unionCheck q = true) (hv : unionCheck v = true)
    (hle : unionInterpretation q ≤ unionInterpretation v) :
    unionCheck (unionDifference q v) = true ∧
      Normal (max q.unpair.1 v.unpair.1)
        (rawTree (crossDifference q.unpair.1 q.unpair.2 v.unpair.1 v.unpair.2)) ∧
      unionInterpretation q + unionInterpretation (unionDifference q v) = unionInterpretation v ∧
      unionInterpretation (unionDifference q v) = unionInterpretation v - unionInterpretation q := by
  have hguard := (unionGuard_exact q v).mpr ⟨hq, hv, hle⟩
  have hs := crossDifference_checked q.unpair.1 q.unpair.2 v.unpair.1 v.unpair.2 hq hv hle
  have hn := (acceptedLowCode_iff _ _).mp hs.1
  refine ⟨?_, hn.2, ?_, ?_⟩
  · simpa only [unionDifference, hguard, Bool.cond_true, unionCheck_pair] using hn.1
  · simpa only [unionDifference, hguard, Bool.cond_true, unionInterpretation, Nat.unpair_pair] using hs.2.1
  · simpa only [unionDifference, hguard, Bool.cond_true, unionInterpretation, Nat.unpair_pair] using hs.2.2

theorem unionDifference_below_limit (q v : Nat) (hq : unionCheck q = true) (hv : unionCheck v = true)
    (hle : unionInterpretation q ≤ unionInterpretation v) :
    unionInterpretation v - unionInterpretation q < finiteBaseLimit := by
  have hs := unionDifference_checked q v hq hv hle
  exact (lt_finiteBaseLimit_iff_code _).mpr ⟨unionDifference q v, hs.1, hs.2.2.2⟩

theorem unionDifference_computable : Computable₂ unionDifference := unionDifference_primrec.to_comp

private theorem difference_sub_eq_zero {α β : Ordinal.{0}} (h : β ≤ α) : β - α = 0 := by
  have hz : β - α ≤ 0 := Ordinal.sub_le.2 (by simpa only [add_zero] using h)
  exact le_antisymm hz (zero_le)

/-- Full actual subtraction retains the ordered difference operation and
returns a genuinely admitted zero tree on checked reversed inputs. -/
def fullSubtraction (r c d : Nat) : Nat :=
  cond (checkCode r c && checkCode r d)
    (cond (guard r c d) (differenceCode r c d) (zeroTree r).code) 0

theorem fullSubtraction_primrec : Primrec
    (fun p : Nat × (Nat × Nat) => fullSubtraction p.1 p.2.1 p.2.2) :=
  (Primrec.and.comp
    (Uniform.hereditaryCheckCode_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
    (Uniform.hereditaryCheckCode_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd))).cond
      (guard_primrec.cond differenceCode_primrec
        (code_primrec.comp (Normalization.Effective.zeroTree_primrec.comp Primrec.fst))) (Primrec.const 0)

theorem fullSubtraction_rejected (r c d : Nat) (h : (checkCode r c && checkCode r d) = false) :
    fullSubtraction r c d = 0 := by simp only [fullSubtraction, h, Bool.cond_false]

theorem fullSubtraction_checked (r c d : Nat) (hc : checkCode r c = true) (hd : checkCode r d = true) :
    acceptedCode r (fullSubtraction r c d) = true ∧
      interpretation r (fullSubtraction r c d) = interpretation r d - interpretation r c := by
  by_cases hle : interpretation r c ≤ interpretation r d
  · have hg := (guard_exact r c d).mpr ⟨hc, hd, hle⟩
    have hs := differenceCode_checked r c d hc hd hle
    simpa only [fullSubtraction, hc, hd, Bool.true_and, Bool.cond_true, hg] using And.intro hs.1 hs.2.2
  · have hg : guard r c d = false := by
      cases h : guard r c d with
      | false => rfl
      | true => exact False.elim (hle ((guard_exact r c d).mp h).2.2)
    have hz := difference_sub_eq_zero (lt_of_not_ge hle).le
    have hzero : acceptedCode r (zeroTree r).code = true :=
      (acceptedCode_iff _ _).mpr ⟨by simpa only [checkCode_code] using (Bool.and_eq_true_iff.mp (zeroTree_lowCheck r)).1,
        by simpa only [rawTree_code] using Normalization.zeroTree_normal r⟩
    simpa only [fullSubtraction, hc, hd, Bool.true_and, Bool.cond_true, hg, Bool.cond_false,
      interpretation_code, zeroTree_denote, hz] using And.intro hzero (Eq.refl (0 : Ordinal.{0}))

theorem fullSubtraction_lowChecked (r c d : Nat)
    (hc : lowCheckCode r c = true) (hd : lowCheckCode r d = true) :
    acceptedLowCode r (fullSubtraction r c d) = true ∧
      interpretation r (fullSubtraction r c d) = interpretation r d - interpretation r c := by
  have hc' := (Bool.and_eq_true_iff.mp (by simpa only [lowCheckCode_eq] using hc)).1
  have hd' := (Bool.and_eq_true_iff.mp (by simpa only [lowCheckCode_eq] using hd)).1
  by_cases hle : interpretation r c ≤ interpretation r d
  · have hg := (guard_exact r c d).mpr ⟨hc', hd', hle⟩
    have hs := differenceCode_lowChecked r c d hc hd hle
    simpa only [fullSubtraction, hc', hd', Bool.true_and, Bool.cond_true, hg] using And.intro hs.1 hs.2.2
  · have hg : guard r c d = false := by
      cases h : guard r c d with
      | false => rfl
      | true => exact False.elim (hle ((guard_exact r c d).mp h).2.2)
    have hz := difference_sub_eq_zero (lt_of_not_ge hle).le
    have hzero : acceptedLowCode r (zeroTree r).code = true :=
      (acceptedLowCode_iff _ _).mpr ⟨by simpa only [lowCheckCode_code] using zeroTree_lowCheck r,
        by simpa only [rawTree_code] using Normalization.zeroTree_normal r⟩
    simpa only [fullSubtraction, hc', hd', Bool.true_and, Bool.cond_true, hg, Bool.cond_false,
      interpretation_code, zeroTree_denote, hz] using And.intro hzero (Eq.refl (0 : Ordinal.{0}))

def crossSubtraction (r c s d : Nat) : Nat :=
  cond (lowCheckCode r c && lowCheckCode s d)
    (fullSubtraction (max r s) (HereditaryThetaProgram.alignCode r s c)
      (HereditaryThetaProgram.alignCode s r d)) 0

theorem crossSubtraction_primrec : Primrec
    (fun p : (Nat × Nat) × (Nat × Nat) => crossSubtraction p.1.1 p.1.2 p.2.1 p.2.2) := by
  have hr : Primrec (fun p : (Nat × Nat) × (Nat × Nat) => p.1.1) := Primrec.fst.comp Primrec.fst
  have hs : Primrec (fun p : (Nat × Nat) × (Nat × Nat) => p.2.1) := Primrec.fst.comp Primrec.snd
  have hc : Primrec (fun p : (Nat × Nat) × (Nat × Nat) => p.1.2) := Primrec.snd.comp Primrec.fst
  have hd : Primrec (fun p : (Nat × Nat) × (Nat × Nat) => p.2.2) := Primrec.snd.comp Primrec.snd
  have hl := HereditaryThetaProgram.alignCode_primrec.comp ((hr.pair hs).pair hc)
  have hh := HereditaryThetaProgram.alignCode_primrec.comp ((hs.pair hr).pair hd)
  exact (Primrec.and.comp (Uniform.hereditaryLowCheckCode_primrec.comp hr hc)
    (Uniform.hereditaryLowCheckCode_primrec.comp hs hd)).cond
      (fullSubtraction_primrec.comp ((Primrec.nat_max.comp hr hs).pair (hl.pair hh))) (Primrec.const 0)

theorem crossSubtraction_rejected (r c s d : Nat) (h : (lowCheckCode r c && lowCheckCode s d) = false) :
    crossSubtraction r c s d = 0 := by simp only [crossSubtraction, h, Bool.cond_false]

theorem crossSubtraction_checked (r c s d : Nat)
    (hc : lowCheckCode r c = true) (hd : lowCheckCode s d = true) :
    acceptedLowCode (max r s) (crossSubtraction r c s d) = true ∧
      interpretation (max r s) (crossSubtraction r c s d) = interpretation s d - interpretation r c := by
  have hl := HereditaryThetaProgram.alignCode_checked r s c hc
  have hh : lowCheckCode (max r s) (HereditaryThetaProgram.alignCode s r d) = true := by
    simpa only [max_comm s r] using HereditaryThetaProgram.alignCode_checked s r d hd
  have hlvalue := HereditaryThetaProgram.alignCode_value r s c
  have hhvalue : interpretation (max r s) (HereditaryThetaProgram.alignCode s r d) = interpretation s d := by
    simpa only [max_comm s r] using HereditaryThetaProgram.alignCode_value s r d
  simpa only [crossSubtraction, hc, hd, Bool.true_and, Bool.cond_true, hlvalue, hhvalue] using
    fullSubtraction_lowChecked (max r s) _ _ hl hh

def unionSubtraction (q v : Nat) : Nat :=
  cond (unionCheck q && unionCheck v) (Nat.pair (max q.unpair.1 v.unpair.1)
    (crossSubtraction q.unpair.1 q.unpair.2 v.unpair.1 v.unpair.2)) 0

theorem unionSubtraction_primrec : Primrec₂ unionSubtraction := by
  have hq : Primrec (fun p : Nat × Nat => p.1.unpair) := Primrec.unpair.comp Primrec.fst
  have hv : Primrec (fun p : Nat × Nat => p.2.unpair) := Primrec.unpair.comp Primrec.snd
  exact ((Primrec.and.comp (Uniform.unionCheck_primrec.comp Primrec.fst)
    (Uniform.unionCheck_primrec.comp Primrec.snd)).cond
      (Primrec₂.natPair.comp (Primrec.nat_max.comp (Primrec.fst.comp hq) (Primrec.fst.comp hv))
        (crossSubtraction_primrec.comp (hq.pair hv))) (Primrec.const 0)).to₂

theorem unionSubtraction_rejected (q v : Nat) (h : (unionCheck q && unionCheck v) = false) :
    unionSubtraction q v = 0 := by simp only [unionSubtraction, h, Bool.cond_false]

theorem unionSubtraction_checked (q v : Nat) (hq : unionCheck q = true) (hv : unionCheck v = true) :
    unionCheck (unionSubtraction q v) = true ∧
      Normal (max q.unpair.1 v.unpair.1)
        (rawTree (crossSubtraction q.unpair.1 q.unpair.2 v.unpair.1 v.unpair.2)) ∧
      unionInterpretation (unionSubtraction q v) = unionInterpretation v - unionInterpretation q := by
  have hs := crossSubtraction_checked q.unpair.1 q.unpair.2 v.unpair.1 v.unpair.2 hq hv
  have hn := (acceptedLowCode_iff _ _).mp hs.1
  refine ⟨?_, hn.2, ?_⟩
  · simpa only [unionSubtraction, hq, hv, Bool.true_and, Bool.cond_true, unionCheck_pair] using hn.1
  · simpa only [unionSubtraction, hq, hv, Bool.true_and, Bool.cond_true,
      unionInterpretation, Nat.unpair_pair] using hs.2

theorem unionSubtraction_below_limit (q v : Nat) (hq : unionCheck q = true) (hv : unionCheck v = true) :
    unionInterpretation v - unionInterpretation q < finiteBaseLimit := by
  have hs := unionSubtraction_checked q v hq hv
  exact (lt_finiteBaseLimit_iff_code _).mpr ⟨unionSubtraction q v, hs.1, hs.2.2⟩

theorem unionSubtraction_computable : Computable₂ unionSubtraction := unionSubtraction_primrec.to_comp

end Alexander313.Wilken.RelativeTerm.Hereditary.Difference
