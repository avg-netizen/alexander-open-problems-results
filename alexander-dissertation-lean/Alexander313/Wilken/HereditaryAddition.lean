import Alexander313.Effective.HereditaryThetaPrograms
import Alexander313.Wilken.GlobalBaseArithmetic

/-! # Actual addition on the full hereditary public domain

Literal source sums are admitted by the unchanged grammar. The constructed
normalizer retains their admission and real ordinal sum. Full earlier-level
parameter embeddings align arbitrary low codes before summing them. All
operations are genuinely uniformly primitive recursive; original input
guards remain explicit. No numerical-code ordering, supplied arithmetic
oracle or printed structural canonical spelling is used. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.Addition

open Theta ThetaCourse

def sumCode (c d : Nat) : Nat :=
  cond (isCode c && isCode d) (RelativeTerm.sum (rawTree c) (rawTree d)).code 0

@[simp] theorem sumCode_code (a b : RelativeTerm Nat) :
    sumCode a.code b.code = (RelativeTerm.sum a b).code := by
  simp [sumCode]

theorem sumCode_primrec : Primrec₂ sumCode :=
  ((Primrec.and.comp (isCode_primrec.comp Primrec.fst)
    (isCode_primrec.comp Primrec.snd)).cond
      (code_primrec.comp (sum_primrec.comp (rawTree_primrec.comp Primrec.fst)
        (rawTree_primrec.comp Primrec.snd))) (Primrec.const 0)).to₂

theorem sumCode_checked (r c d : Nat)
    (hc : checkCode r c = true) (hd : checkCode r d = true) :
    checkCode r (sumCode c d) = true ∧
      interpretation r (sumCode c d) = interpretation r c + interpretation r d := by
  obtain ⟨a, rfl, ha⟩ := (checkCode_iff r c).mp hc
  obtain ⟨b, rfl, hb⟩ := (checkCode_iff r d).mp hd
  simp only [sumCode_code, checkCode_code, interpretation_code]
  refine ⟨?_, rfl⟩
  simp only [Uniform.check_sum, ha, hb, Bool.true_and]

theorem sumCode_lowChecked (r c d : Nat)
    (hc : lowCheckCode r c = true) (hd : lowCheckCode r d = true) :
    lowCheckCode r (sumCode c d) = true ∧
      interpretation r (sumCode c d) = interpretation r c + interpretation r d := by
  obtain ⟨a, rfl, ha⟩ := (lowCheckCode_iff r c).mp hc
  obtain ⟨b, rfl, hb⟩ := (lowCheckCode_iff r d).mp hd
  have has : check r a = true ∧ a.outerSort ≤ 1 := by
    simpa only [lowCheck, Bool.and_eq_true, decide_eq_true_eq] using ha
  have hbs : check r b = true ∧ b.outerSort ≤ 1 := by
    simpa only [lowCheck, Bool.and_eq_true, decide_eq_true_eq] using hb
  simp only [sumCode_code, lowCheckCode_code, interpretation_code]
  refine ⟨?_, rfl⟩
  simp only [lowCheck, Uniform.check_sum, has.1, hbs.1, Bool.true_and,
    outerSort, max_le has.2 hbs.2, decide_true]

def normalizedSumCode (r c d : Nat) : Nat := Normalization.normalizeCode r (sumCode c d)

theorem normalizedSumCode_primrec : Primrec
    (fun p : Nat × (Nat × Nat) => normalizedSumCode p.1 p.2.1 p.2.2) :=
  Normalization.Effective.normalizeCode_primrec.comp Primrec.fst
    (sumCode_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))

theorem normalizedSumCode_checked (r c d : Nat)
    (hc : checkCode r c = true) (hd : checkCode r d = true) :
    acceptedCode r (normalizedSumCode r c d) = true ∧
      interpretation r (normalizedSumCode r c d) = interpretation r c + interpretation r d := by
  have hs := sumCode_checked r c d hc hd
  have hn := Normalization.normalizeCode_accepted r (sumCode c d) hs.1
  exact ⟨hn.1, hn.2.trans hs.2⟩

theorem normalizedSumCode_lowChecked (r c d : Nat)
    (hc : lowCheckCode r c = true) (hd : lowCheckCode r d = true) :
    acceptedLowCode r (normalizedSumCode r c d) = true ∧
      interpretation r (normalizedSumCode r c d) = interpretation r c + interpretation r d := by
  have hs := sumCode_lowChecked r c d hc hd
  have hn := Normalization.normalizeCode_acceptedLow r (sumCode c d) hs.1
  exact ⟨hn.1, hn.2.trans hs.2⟩

def crossSum (r c s d : Nat) : Nat :=
  cond (lowCheckCode r c && lowCheckCode s d)
    (normalizedSumCode (max r s) (HereditaryThetaProgram.alignCode r s c)
      (HereditaryThetaProgram.alignCode s r d)) 0

theorem crossSum_primrec : Primrec
    (fun p : (Nat × Nat) × (Nat × Nat) => crossSum p.1.1 p.1.2 p.2.1 p.2.2) := by
  have hr : Primrec (fun p : (Nat × Nat) × (Nat × Nat) => p.1.1) := Primrec.fst.comp Primrec.fst
  have hs : Primrec (fun p : (Nat × Nat) × (Nat × Nat) => p.2.1) := Primrec.fst.comp Primrec.snd
  have hc : Primrec (fun p : (Nat × Nat) × (Nat × Nat) => p.1.2) := Primrec.snd.comp Primrec.fst
  have hd : Primrec (fun p : (Nat × Nat) × (Nat × Nat) => p.2.2) := Primrec.snd.comp Primrec.snd
  have hguard := Primrec.and.comp (Uniform.hereditaryLowCheckCode_primrec.comp hr hc)
    (Uniform.hereditaryLowCheckCode_primrec.comp hs hd)
  have hleft := HereditaryThetaProgram.alignCode_primrec.comp ((hr.pair hs).pair hc)
  have hright := HereditaryThetaProgram.alignCode_primrec.comp ((hs.pair hr).pair hd)
  exact hguard.cond (normalizedSumCode_primrec.comp
    ((Primrec.nat_max.comp hr hs).pair (hleft.pair hright))) (Primrec.const 0)

theorem crossSum_checked (r c s d : Nat)
    (hc : lowCheckCode r c = true) (hd : lowCheckCode s d = true) :
    acceptedLowCode (max r s) (crossSum r c s d) = true ∧
      interpretation (max r s) (crossSum r c s d) = interpretation r c + interpretation s d := by
  have hl := HereditaryThetaProgram.alignCode_checked r s c hc
  have hr : lowCheckCode (max r s) (HereditaryThetaProgram.alignCode s r d) = true := by
    simpa only [max_comm s r] using HereditaryThetaProgram.alignCode_checked s r d hd
  have h := normalizedSumCode_lowChecked (max r s) _ _ hl hr
  have hv : interpretation (max r s) (HereditaryThetaProgram.alignCode s r d) =
      interpretation s d := by
    simpa only [max_comm s r] using HereditaryThetaProgram.alignCode_value s r d
  simpa [crossSum, hc, hd, HereditaryThetaProgram.alignCode_value r s c, hv] using h

def unionAdd (q v : Nat) : Nat :=
  Nat.pair (max q.unpair.1 v.unpair.1)
    (crossSum q.unpair.1 q.unpair.2 v.unpair.1 v.unpair.2)

theorem unionAdd_primrec : Primrec₂ unionAdd := by
  have hq : Primrec (fun p : Nat × Nat => p.1.unpair) := Primrec.unpair.comp Primrec.fst
  have hv : Primrec (fun p : Nat × Nat => p.2.unpair) := Primrec.unpair.comp Primrec.snd
  exact (Primrec₂.natPair.comp
    (Primrec.nat_max.comp (Primrec.fst.comp hq) (Primrec.fst.comp hv))
    (crossSum_primrec.comp (hq.pair hv))).to₂

theorem unionAdd_checked (q v : Nat) (hq : unionCheck q = true) (hv : unionCheck v = true) :
    unionCheck (unionAdd q v) = true ∧
      Normal (max q.unpair.1 v.unpair.1)
        (rawTree (crossSum q.unpair.1 q.unpair.2 v.unpair.1 v.unpair.2)) ∧
      unionInterpretation (unionAdd q v) = unionInterpretation q + unionInterpretation v := by
  have h := crossSum_checked q.unpair.1 q.unpair.2 v.unpair.1 v.unpair.2 hq hv
  have ha := (acceptedLowCode_iff _ _).mp h.1
  exact ⟨by simpa only [unionAdd, unionCheck_pair] using ha.1, ha.2,
    by simpa only [unionAdd, unionInterpretation, Nat.unpair_pair] using h.2⟩

theorem unionAdd_below_limit (q v : Nat) (hq : unionCheck q = true) (hv : unionCheck v = true) :
    unionInterpretation q + unionInterpretation v < finiteBaseLimit := by
  have h := unionAdd_checked q v hq hv
  exact (lt_finiteBaseLimit_iff_code _).mpr ⟨unionAdd q v, h.1, h.2.2⟩

theorem unionAdd_computable : Computable₂ unionAdd := unionAdd_primrec.to_comp

end Alexander313.Wilken.RelativeTerm.Hereditary.Addition
