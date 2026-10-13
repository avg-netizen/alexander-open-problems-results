import Alexander313.Wilken.HereditaryDifference

/-!
# Actual Programs for ordered right difference and full subtraction

The total Program computes the proved literal right-difference/subtraction
algorithms. A separate positive Program recognizes the exact unchanged input
domains. Ordered difference requires α ≤ β; full subtraction accepts every
originally admitted pair, giving a genuine normal zero on reversed inputs.
Both cross-level operations align actual low codes and preserve their original
ordinal values. No supplied compiler or ordinal arithmetic contract is used.
Uncompiled.
-/

namespace Alexander313.HereditaryDifferenceProgram

open Wilken.RelativeTerm.Hereditary

def output (tag payload : Nat) : Nat :=
  let r := payload.unpair.1
  let cd := payload.unpair.2.unpair
  let rc := payload.unpair.1.unpair
  let sd := payload.unpair.2.unpair
  let qv := payload.unpair
  cond (tag == 0) (Difference.differenceCode r cd.1 cd.2)
    (cond (tag == 1) (Difference.crossDifference rc.1 rc.2 sd.1 sd.2)
      (cond (tag == 2) (Difference.unionDifference qv.1 qv.2)
        (cond (tag == 3) (Difference.fullSubtraction r cd.1 cd.2)
          (cond (tag == 4) (Difference.crossSubtraction rc.1 rc.2 sd.1 sd.2)
            (cond (tag == 5) (Difference.unionSubtraction qv.1 qv.2) 0)))))

theorem output_primrec : Primrec₂ output := by
  have hp : Primrec (fun p : Nat × Nat => p.2.unpair) := Primrec.unpair.comp Primrec.snd
  have hr := Primrec.fst.comp hp
  have hcd := Primrec.unpair.comp (Primrec.snd.comp hp)
  have hpair := (Primrec.unpair.comp (Primrec.fst.comp hp)).pair hcd
  have tag (i : Nat) : Primrec (fun p : Nat × Nat => p.1 == i) :=
    Primrec.beq.comp Primrec.fst (Primrec.const i)
  exact ((tag 0).cond (Difference.differenceCode_primrec.comp (hr.pair hcd))
    ((tag 1).cond (Difference.crossDifference_primrec.comp hpair)
      ((tag 2).cond (Difference.unionDifference_primrec.comp (Primrec.fst.comp hp) (Primrec.snd.comp hp))
        ((tag 3).cond (Difference.fullSubtraction_primrec.comp (hr.pair hcd))
          ((tag 4).cond (Difference.crossSubtraction_primrec.comp hpair)
            ((tag 5).cond (Difference.unionSubtraction_primrec.comp (Primrec.fst.comp hp)
              (Primrec.snd.comp hp)) (Primrec.const 0))))))).to₂

theorem decisionProgram_exists : ∃ p : Program, ∀ query,
    p.eval query = Part.some (output query.unpair.1 query.unpair.2) := by
  have h : Partrec (fun query : Nat => Part.some (output query.unpair.1 query.unpair.2)) :=
    (output_primrec.comp (Primrec.fst.comp Primrec.unpair)
      (Primrec.snd.comp Primrec.unpair)).to_comp.partrec
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp h)
  exact ⟨p, fun query => congrFun hp query⟩

noncomputable def decisionProgram : Program := Classical.choose decisionProgram_exists

theorem decisionProgram_eval (query : Nat) :
    decisionProgram.eval query = Part.some (output query.unpair.1 query.unpair.2) :=
  Classical.choose_spec decisionProgram_exists query

noncomputable def decisionColumn (tag : Nat) : Program := decisionProgram.column tag

theorem decisionColumn_eval (tag payload : Nat) :
    (decisionColumn tag).eval payload = Part.some (output tag payload) := by
  rw [decisionColumn, Program.column, Nat.Partrec.Code.eval_curry, decisionProgram_eval]
  simp only [Nat.unpair_pair]

theorem difference_eval (r c d : Nat) :
    (decisionColumn 0).eval (Nat.pair r (Nat.pair c d)) = Part.some (Difference.differenceCode r c d) := by
  simpa [output, Nat.unpair_pair] using decisionColumn_eval 0 (Nat.pair r (Nat.pair c d))

theorem cross_difference_eval (r c s d : Nat) :
    (decisionColumn 1).eval (Nat.pair (Nat.pair r c) (Nat.pair s d)) =
      Part.some (Difference.crossDifference r c s d) := by
  simpa [output, Nat.unpair_pair] using decisionColumn_eval 1 (Nat.pair (Nat.pair r c) (Nat.pair s d))

theorem union_difference_eval (q v : Nat) :
    (decisionColumn 2).eval (Nat.pair q v) = Part.some (Difference.unionDifference q v) := by
  simpa [output, Nat.unpair_pair] using decisionColumn_eval 2 (Nat.pair q v)

theorem subtraction_eval (r c d : Nat) :
    (decisionColumn 3).eval (Nat.pair r (Nat.pair c d)) = Part.some (Difference.fullSubtraction r c d) := by
  simpa [output, Nat.unpair_pair] using decisionColumn_eval 3 (Nat.pair r (Nat.pair c d))

theorem cross_subtraction_eval (r c s d : Nat) :
    (decisionColumn 4).eval (Nat.pair (Nat.pair r c) (Nat.pair s d)) =
      Part.some (Difference.crossSubtraction r c s d) := by
  simpa [output, Nat.unpair_pair] using decisionColumn_eval 4 (Nat.pair (Nat.pair r c) (Nat.pair s d))

theorem union_subtraction_eval (q v : Nat) :
    (decisionColumn 5).eval (Nat.pair q v) = Part.some (Difference.unionSubtraction q v) := by
  simpa [output, Nat.unpair_pair] using decisionColumn_eval 5 (Nat.pair q v)

theorem decisionColumn_total (tag payload : Nat) : (decisionColumn tag).domain payload := by
  change ((decisionColumn tag).eval payload).Dom
  rw [decisionColumn_eval]
  trivial

def check (tag payload : Nat) : Bool :=
  let r := payload.unpair.1
  let cd := payload.unpair.2.unpair
  let rc := payload.unpair.1.unpair
  let sd := payload.unpair.2.unpair
  let qv := payload.unpair
  cond (tag == 0) (Difference.guard r cd.1 cd.2)
    (cond (tag == 1) (Difference.crossGuard rc.1 rc.2 sd.1 sd.2)
      (cond (tag == 2) (Difference.unionGuard qv.1 qv.2)
        (cond (tag == 3) (checkCode r cd.1 && checkCode r cd.2)
          (cond (tag == 4) (lowCheckCode rc.1 rc.2 && lowCheckCode sd.1 sd.2)
            (cond (tag == 5) (unionCheck qv.1 && unionCheck qv.2) false)))))

theorem check_primrec : Primrec₂ check := by
  have hp : Primrec (fun p : Nat × Nat => p.2.unpair) := Primrec.unpair.comp Primrec.snd
  have hr := Primrec.fst.comp hp
  have hcd := Primrec.unpair.comp (Primrec.snd.comp hp)
  have hrc := Primrec.unpair.comp (Primrec.fst.comp hp)
  have hpair := hrc.pair hcd
  have tag (i : Nat) : Primrec (fun p : Nat × Nat => p.1 == i) :=
    Primrec.beq.comp Primrec.fst (Primrec.const i)
  have hfull := Primrec.and.comp
    (Uniform.hereditaryCheckCode_primrec.comp hr (Primrec.fst.comp hcd))
    (Uniform.hereditaryCheckCode_primrec.comp hr (Primrec.snd.comp hcd))
  have hcross := Primrec.and.comp
    (Uniform.hereditaryLowCheckCode_primrec.comp (Primrec.fst.comp hrc) (Primrec.snd.comp hrc))
    (Uniform.hereditaryLowCheckCode_primrec.comp (Primrec.fst.comp hcd) (Primrec.snd.comp hcd))
  have hunion := Primrec.and.comp (Uniform.unionCheck_primrec.comp (Primrec.fst.comp hp))
    (Uniform.unionCheck_primrec.comp (Primrec.snd.comp hp))
  exact ((tag 0).cond (Difference.guard_primrec.comp (hr.pair hcd))
    ((tag 1).cond (Difference.crossGuard_primrec.comp hpair)
      ((tag 2).cond (Difference.unionGuard_primrec.comp (Primrec.fst.comp hp) (Primrec.snd.comp hp))
        ((tag 3).cond hfull ((tag 4).cond hcross ((tag 5).cond hunion (Primrec.const false))))))).to₂

private def constantCheck (query : Nat) (_ : Nat) : Bool := check query.unpair.1 query.unpair.2

private theorem difference_constantCheck_primrec : Primrec₂ constantCheck :=
  (check_primrec.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst))
    (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst))).to₂

def evaluation (query : Nat) : Part Nat :=
  Nat.rfind (fun witness => Part.some (constantCheck query witness))

theorem evaluation_partrec : Partrec evaluation :=
  Partrec.rfind difference_constantCheck_primrec.to_comp.partrec.to₂

theorem evaluation_domain (query : Nat) : (evaluation query).Dom ↔
    check query.unpair.1 query.unpair.2 = true := by
  simp only [evaluation, constantCheck, Nat.rfind_dom, Part.mem_some_iff,
    Part.some_dom, implies_true, and_true, Bool.true_eq, exists_const]

theorem recognizer_exists : ∃ p : Program, ∀ query,
    p.domain query ↔ check query.unpair.1 query.unpair.2 = true := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp evaluation_partrec)
  refine ⟨p, fun query => ?_⟩
  simpa only [Program.domain, hp] using evaluation_domain query

noncomputable def recognizer : Program := Classical.choose recognizer_exists

theorem recognizer_domain (query : Nat) : recognizer.domain query ↔
    check query.unpair.1 query.unpair.2 = true := Classical.choose_spec recognizer_exists query

noncomputable def recognizerColumn (tag : Nat) : Program := recognizer.column tag

theorem recognizerColumn_domain (tag payload : Nat) :
    (recognizerColumn tag).domain payload ↔ check tag payload = true := by
  simp only [recognizerColumn, Program.column_domain, recognizer_domain, Nat.unpair_pair]

theorem difference_domain (r c d : Nat) :
    (recognizerColumn 0).domain (Nat.pair r (Nat.pair c d)) ↔
      checkCode r c = true ∧ checkCode r d = true ∧ interpretation r c ≤ interpretation r d := by
  rw [recognizerColumn_domain]
  simpa [check, Nat.unpair_pair] using Difference.guard_exact r c d

theorem cross_difference_domain (r c s d : Nat) :
    (recognizerColumn 1).domain (Nat.pair (Nat.pair r c) (Nat.pair s d)) ↔
      lowCheckCode r c = true ∧ lowCheckCode s d = true ∧ interpretation r c ≤ interpretation s d := by
  rw [recognizerColumn_domain]
  simpa [check, Nat.unpair_pair] using Difference.crossGuard_exact r c s d

theorem union_difference_domain (q v : Nat) :
    (recognizerColumn 2).domain (Nat.pair q v) ↔
      unionCheck q = true ∧ unionCheck v = true ∧ unionInterpretation q ≤ unionInterpretation v := by
  rw [recognizerColumn_domain]
  simpa [check, Nat.unpair_pair] using Difference.unionGuard_exact q v

theorem subtraction_domain (r c d : Nat) :
    (recognizerColumn 3).domain (Nat.pair r (Nat.pair c d)) ↔
      checkCode r c = true ∧ checkCode r d = true := by
  simpa [check, Nat.unpair_pair, Bool.and_eq_true] using recognizerColumn_domain 3 (Nat.pair r (Nat.pair c d))

theorem cross_subtraction_domain (r c s d : Nat) :
    (recognizerColumn 4).domain (Nat.pair (Nat.pair r c) (Nat.pair s d)) ↔
      lowCheckCode r c = true ∧ lowCheckCode s d = true := by
  simpa [check, Nat.unpair_pair, Bool.and_eq_true] using
    recognizerColumn_domain 4 (Nat.pair (Nat.pair r c) (Nat.pair s d))

theorem union_subtraction_domain (q v : Nat) :
    (recognizerColumn 5).domain (Nat.pair q v) ↔ unionCheck q = true ∧ unionCheck v = true := by
  simpa [check, Nat.unpair_pair, Bool.and_eq_true] using recognizerColumn_domain 5 (Nat.pair q v)

theorem union_difference_result (q v : Nat) (hq : unionCheck q = true) (hv : unionCheck v = true)
    (hle : unionInterpretation q ≤ unionInterpretation v) :
    unionCheck (Difference.unionDifference q v) = true ∧
      unionInterpretation q + unionInterpretation (Difference.unionDifference q v) = unionInterpretation v ∧
      unionInterpretation (Difference.unionDifference q v) = unionInterpretation v - unionInterpretation q := by
  have h := Difference.unionDifference_checked q v hq hv hle
  exact ⟨h.1, h.2.2⟩

theorem union_subtraction_result (q v : Nat) (hq : unionCheck q = true) (hv : unionCheck v = true) :
    unionCheck (Difference.unionSubtraction q v) = true ∧
      unionInterpretation (Difference.unionSubtraction q v) = unionInterpretation v - unionInterpretation q := by
  have h := Difference.unionSubtraction_checked q v hq hv
  exact ⟨h.1, h.2.2⟩

end Alexander313.HereditaryDifferenceProgram
