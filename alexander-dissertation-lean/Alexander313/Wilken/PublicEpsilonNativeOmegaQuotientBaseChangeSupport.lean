import Alexander313.Wilken.PublicEpsilonNativeOmegaQuotient
import Alexander313.Wilken.PublicEpsilonNativePowerBaseChange

/-!
# Actual Omega-one quotient branches at two epsilon contexts

The literal native quotient operation is the existing atom/ANF producer.
Its LOW theta-one branch uses the proved actual omega-power agreement;
the middle branch uses real native left subtraction. Full target payloads
are constructed from those actual outputs and the original checked atoms.
No quotient naturality, target admission or syntactic cutoff oracle is
supplied. Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonIota.OmegaQuotient.BaseChange

open ThetaCourse
open BoundedContextIota.OmegaQuotient (atomTerm quotientWord quotientTerm limitWord limitTerm finiteOffset)
open NativeContext.OmegaQuotient (baseTerm thresholdTerm baseTerm_spec unitTest selectUnits selectUnits_mem)

theorem subtractTerm_context (q v c d : Nat)
    (hcq : checkCode q c = true) (hdq : checkCode q d = true)
    (hcv : checkCode v c = true) (hdv : checkCode v d = true) :
    Arithmetic.subtractTerm q c d = Arithmetic.subtractTerm v c d := by
  have he : Comparison.equal q = Comparison.equal v :=
    funext fun t => funext fun u => BaseTransformation.equal_context q v t u
  simp only [Arithmetic.subtractTerm, Arithmetic.leCode,
    OmegaPowers.BaseChange.lessRawCode_context q v d c hdq hcq hdv hcv,
    Arithmetic.differenceWord,
    OmegaPowers.BaseChange.normalizedWord_context q v c hcq hcv,
    OmegaPowers.BaseChange.normalizedWord_context q v d hdq hdv, he]

/-- Every actual branch agrees literally on an original atom admitted
at both contexts, including theta-one at the equality threshold. -/
theorem atomTerm_context (q v : Nat) (t : RelativeTerm Nat)
    (htq : check q t = true) (htv : check v t = true) :
    atomTerm q t = atomTerm v t := by
  cases t with
  | parameter p => rfl
  | sum a b => rfl
  | theta k t =>
    have hcq := BaseTransformation.theta_argument_check q k t htq
    have hcv := BaseTransformation.theta_argument_check v k t htv
    have hq := (Bool.and_eq_true.mp htq).1
    have hv := (Bool.and_eq_true.mp htv).1
    have hbq : checkCode q baseTerm.code = true := by
      simpa only [checkCode_code] using (baseTerm_spec q hq).1
    have hbv : checkCode v baseTerm.code = true := by
      simpa only [checkCode_code] using (baseTerm_spec v hv).1
    have htcq : checkCode q t.code = true := by simpa only [checkCode_code] using hcq
    have htcv : checkCode v t.code = true := by simpa only [checkCode_code] using hcv
    by_cases hk : k = 1
    · subst k
      by_cases hl : t.outerSort ≤ 1
      · have hlq : lowCheckCode q t.code = true := by
          simp only [lowCheckCode_code, lowCheck, hcq, hl, decide_true, Bool.true_and]
        have hlv : lowCheckCode v t.code = true := by
          simp only [lowCheckCode_code, lowCheck, hcv, hl, decide_true, Bool.true_and]
        simp only [atomTerm, beq_self_eq_true, hl, decide_true, Bool.cond_true,
          OmegaPowers.BaseChange.powerCode_context q v t.code hlq hlv]
      · simp only [atomTerm, beq_self_eq_true, hl, decide_false, Bool.cond_true, Bool.cond_false,
          BaseTransformation.less_context q v,
          subtractTerm_context q v baseTerm.code t.code hbq htcq hbv htcv]
    · have hkb : (k == 1) = false := Bool.eq_false_of_not_eq_true
        (fun h => hk (beq_iff_eq.mp h))
      simp only [atomTerm, hkb, Bool.cond_false]

/-- The actual quotient atom carries ONLY genuinely checked target
payloads. The small branch uses the real target power output checker and
the middle branch the real target subtraction admissibility theorem. -/
theorem atomTerm_payloads (v : Nat) (t : RelativeTerm Nat) (ht : check v t = true) :
    Payloads v (atomTerm v t) := by
  cases t with
  | parameter p => exact (checked_admissible v _ ht).1
  | sum a b => exact (checked_admissible v _ ht).1
  | theta k t =>
    have hc := BaseTransformation.theta_argument_check v k t ht
    have hv := (Bool.and_eq_true.mp ht).1
    by_cases hk : k = 1
    · subst k
      by_cases hl : t.outerSort ≤ 1
      · have hlow : lowCheckCode v t.code = true := by
          simp only [lowCheckCode_code, lowCheck, hc, hl, decide_true, Bool.true_and]
        have hp := (Bool.and_eq_true.mp (OmegaPowers.powerCode_spec v t.code hlow).1).1
        simpa only [atomTerm, beq_self_eq_true, hl, decide_true, Bool.cond_true] using
          (checked_admissible v _ (Arithmetic.raw_checked v _ hp)).1
      · have hb : checkCode v baseTerm.code = true := by
          simpa only [checkCode_code] using (baseTerm_spec v hv).1
        have htc : checkCode v t.code = true := by simpa only [checkCode_code] using hc
        have hs := (Arithmetic.subtractTerm_spec v baseTerm.code t.code hb htc).1.1
        cases he : Comparison.less v t thresholdTerm <;>
          simp only [atomTerm, beq_self_eq_true, hl, decide_false, he,
            Bool.cond_true, Bool.cond_false, Payloads]
        · exact (checked_admissible v _ hc).1
        · exact hs
    · have hkb : (k == 1) = false := Bool.eq_false_of_not_eq_true
        (fun h => hk (beq_iff_eq.mp h))
      simpa only [atomTerm, hkb, Bool.cond_false] using (checked_admissible v _ ht).1

theorem quotientWord_context (q v c : Nat) (hcq : Decomposition.inputCheck q c = true)
    (hcv : Decomposition.inputCheck v c = true) : quotientWord q c = quotientWord v c := by
  unfold quotientWord
  apply List.map_congr_left
  intro t ht
  have hm := (Decomposition.highWord_mem 0 c t).mp ht
  exact atomTerm_context q v t ((Decomposition.word_spec q c hcq).1 t hm.1).1
    ((Decomposition.word_spec v c hcv).1 t hm.1).1

theorem quotientWord_payloads (v c : Nat) (hc : Decomposition.inputCheck v c = true) :
    ∀ t ∈ quotientWord v c, Payloads v t := by
  intro t ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  have hm := (Decomposition.highWord_mem 0 c u).mp hu
  exact atomTerm_payloads v u ((Decomposition.word_spec v c hc).1 u hm.1).1

theorem selectUnits_context (units : Bool) (q v : Nat) (as : List (RelativeTerm Nat)) :
    selectUnits units q as = selectUnits units v as := by
  induction as with
  | nil => rfl
  | cons t as ih =>
    simp only [selectUnits, unitTest, BaseTransformation.equal_context q v, ih]

theorem limitWord_context (q v c : Nat) (hcq : Decomposition.inputCheck q c = true)
    (hcv : Decomposition.inputCheck v c = true) : limitWord q c = limitWord v c := by
  simp only [limitWord, quotientWord_context q v c hcq hcv, selectUnits_context false q v]

theorem limitTerm_context (q v c : Nat) (hcq : Decomposition.inputCheck q c = true)
    (hcv : Decomposition.inputCheck v c = true) : limitTerm q c = limitTerm v c :=
  congrArg Normalization.buildAtoms (limitWord_context q v c hcq hcv)

theorem finiteOffset_context (q v c : Nat) (hcq : Decomposition.inputCheck q c = true)
    (hcv : Decomposition.inputCheck v c = true) : finiteOffset q c = finiteOffset v c := by
  simp only [finiteOffset, quotientWord_context q v c hcq hcv, selectUnits_context true q v]

private theorem buildRev_payloads (v : Nat) (hv : baseCheck v = true)
    (as : List (RelativeTerm Nat)) (hp : ∀ t ∈ as, Payloads v t) :
    Payloads v (Normalization.buildRev as) := by
  revert hp
  induction as with
  | nil => intro _; exact (checked_admissible v _ (Normalization.zeroTree_checked v hv)).1
  | cons t as ih =>
    intro hp
    exact ⟨ih (fun u hu => hp u (List.mem_cons_of_mem _ hu)), hp t List.mem_cons_self⟩

theorem limitTerm_payloads (v c : Nat) (hc : Decomposition.inputCheck v c = true) :
    Payloads v (limitTerm v c) := by
  have hv := (Bool.and_eq_true.mp (Decomposition.input_tree v c hc).1).1
  apply buildRev_payloads v hv
  intro t ht
  have hm : t ∈ limitWord v c := List.mem_reverse.mp ht
  have hq := (selectUnits_mem false v (quotientWord v c) t).mp hm
  exact quotientWord_payloads v c hc t hq.1

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonIota.OmegaQuotient.BaseChange
