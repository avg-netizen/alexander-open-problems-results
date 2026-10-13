import Alexander313.Wilken.HereditaryNativeBoundedContextMu

/-!
# Actual original-source callers for intermediate-root return

The full finite SAME-value return is executed on the intermediate root and
its genuinely restricted source expressions. Their original hidden calls
are below beta, hence below the original outer alpha-plus. The intermediate
root's high argument forces the actual high branch of the real return.
Its returned original theta-zero root, admission, Normality, high argument
and canonical beta identity are derived. No root, return or translation
oracle is supplied. Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.BoundedContextIota.SourceReturn

open NativePublicBridge (contextCode)

def returnedTerm (s a : Nat) (t : RelativeTerm Nat) : RelativeTerm Nat :=
  ThetaCourse.rawTree (BoundedPublicReturn.sourceTermCode s a t)

def returnedRoot (s a root : Nat) : Nat :=
  BoundedPublicReturn.sourceTermCode s a (ThetaCourse.rawTree root)

theorem returnedTerm_primrec : Primrec₂ (fun ctx : Nat × Nat => returnedTerm ctx.1 ctx.2) :=
  ThetaCourse.rawTree_primrec.comp₂ BoundedPublicReturn.sourceTermCode_primrec

theorem returnedRoot_primrec : Primrec (fun p : Context => returnedRoot p.1.1 p.1.2 p.2) :=
  BoundedPublicReturn.sourceTermCode_primrec.comp Primrec.fst
    (ThetaCourse.rawTree_primrec.comp Primrec.snd)

theorem sourceTermCode_spec (s a root : Nat) (ha : rootCheck s a root = true)
    (t : RelativeTerm Nat) (ht : check (sourceCode s a) t = true)
    (hn : Comparison.Normal (sourceCode s a) t) (hr : Restricted s a root t) :
    Comparison.acceptedCode (contextCode s) (BoundedPublicReturn.sourceTermCode s a t) = true ∧
      interpretation (contextCode s) (BoundedPublicReturn.sourceTermCode s a t) =
        denote (sourceCode s a) t := by
  apply BoundedPublicReturn.sourceTermCode_spec s a (outer_root s a root ha) t ht hn
  intro u hu
  exact (hr u hu).trans_lt ((rootCheck_exact s a root).mp ha).2.2

theorem returnedTerm_spec (s a root : Nat) (ha : rootCheck s a root = true)
    (t : RelativeTerm Nat) (ht : check (sourceCode s a) t = true)
    (hn : Comparison.Normal (sourceCode s a) t) (hr : Restricted s a root t) :
    check (contextCode s) (returnedTerm s a t) = true ∧
      Comparison.Normal (contextCode s) (returnedTerm s a t) ∧
      denote (contextCode s) (returnedTerm s a t) = denote (sourceCode s a) t := by
  have hs := sourceTermCode_spec s a root ha t ht hn hr
  have hc := Decomposition.input_tree (contextCode s) _ hs.1
  exact ⟨hc.1, hc.2, (Decomposition.input_value (contextCode s) _ hs.1).symm.trans hs.2⟩

theorem returnedRoot_spec (s a root : Nat) (ha : rootCheck s a root = true) :
    Comparison.acceptedCode (contextCode s) (returnedRoot s a root) = true ∧
      lowCheckCode (contextCode s) (returnedRoot s a root) = true ∧
      interpretation (contextCode s) (returnedRoot s a root) =
        interpretation (sourceCode s a) root := by
  obtain ⟨houter, ⟨t, he, ht, hn, hh⟩, hb⟩ := (rootCheck_exact s a root).mp ha
  have hbound : denote (sourceCode s a) (.theta 0 t) < Iota.AlphaPlus.sourceValue s a := by
    simpa only [he, interpretation_code] using hb
  have hs := BoundedPublicReturn.sourceTermCode_low_spec s a houter (.theta 0 t)
    ht hn (by decide) hbound
  simpa only [returnedRoot, he, ThetaCourse.rawTree_code, LowArithmetic.lowInput,
    sourceCode, interpretation_code] using hs

theorem returnedRoot_shape (s a root : Nat) (ha : rootCheck s a root = true) :
    ∃ t : RelativeTerm Nat, returnedRoot s a root = (.theta 0 t).code := by
  obtain ⟨houter, ⟨t, he, ht, hn, hh⟩, hb⟩ := (rootCheck_exact s a root).mp ha
  have hac := BaseTransformation.theta_argument_check (sourceCode s a) 0 t ht
  have hr : Restricted s a root t := by
    simpa only [he, Localization.argumentCode_theta, ThetaCourse.rawTree_code] using
      argument_restricted s a root ha
  let c := BoundedPublicReturn.sourceTermCode s a t
  have hc := sourceTermCode_spec s a root ha t hac hn hr
  have hhigh : omegaSequence (base (contextCode s)) 1 ≤ interpretation (contextCode s) c := by
    rw [hc.2, Iota.HeightSupport.root_omegaSequence_succ s a 0 houter]
    apply le_of_not_gt
    intro h
    exact (not_le_of_gt hh) ((denote_lt_iff_outerSort_le (sourceCode s a) t hac 1 (by omega)).mp h)
  have hΩ : 0 < omegaSequence (base (contextCode s)) 1 :=
    (omegaSequence_isSuccLimit (base (contextCode s)) 0).bot_lt
  have hpos : 0 < interpretation (contextCode s) (Decomposition.highCode 0 c) := by
    rw [(Decomposition.parts_code_value (contextCode s) 0 c hc.1).1]
    exact mul_pos hΩ ((Ordinal.div_pos hΩ.ne').mpr hhigh)
  have hzero : FixedPoint.zeroCheck (Decomposition.highCode 0 c) = false := by
    apply Bool.eq_false_of_not_eq_true
    intro hz
    have hez := (FixedPoint.zeroCheck_exact (contextCode s) _
      (Decomposition.parts_accepted (contextCode s) 0 c hc.1).1).mp hz
    exact (ne_of_gt hpos) hez
  have hroot : returnedRoot s a root = BoundedPublicReturn.zeroCode s a c := by
    simpa only [returnedRoot, he, ThetaCourse.rawTree_code, BoundedPublicReturn.sourceTermCode_theta,
      BoundedPublicReturn.thetaCode, beq_self_eq_true, Bool.cond_true]
  rw [hroot]
  simp only [BoundedPublicReturn.zeroCode, hzero, Bool.cond_false]
  cases h : Normalization.lessRawCode (contextCode s) a
      (BoundedPublicReturn.nodeCode 0 (Decomposition.highCode 0 c)) with
  | true => exact ⟨ThetaCourse.rawTree c, rfl⟩
  | false => exact ⟨ThetaCourse.rawTree (BoundedPublicReturn.shiftedArgument s a c), rfl⟩

theorem returnedRoot_iota_caller (s a root : Nat) (ha : rootCheck s a root = true) :
    Iota.rootCheck s (returnedRoot s a root) = true := by
  have hs := returnedRoot_spec s a root ha
  obtain ⟨t, he⟩ := returnedRoot_shape s a root ha
  have hc := (Comparison.acceptedCode_exact _ _).mp hs.1
  have ht : check (contextCode s) (.theta 0 t) = true := by
    simpa only [he, checkCode_code] using hc.1
  have hn : Comparison.Normal (contextCode s) t := by
    simpa only [he, ThetaCourse.rawTree_code, Comparison.Normal] using hc.2
  have hv : denote (contextCode s) (.theta 0 t) = interpretation (sourceCode s a) root := by
    rw [← interpretation_code, ← he]
    exact hs.2.2
  have hb : base (contextCode s) < denote (contextCode s) (.theta 0 t) := by
    rw [hv]
    calc
      base (contextCode s) ≤ interpretation (contextCode s) a :=
        Iota.root_base_le s a (outer_root s a root ha)
      _ = base (sourceCode s a) := (Iota.alpha_base s a (outer_root s a root ha)).symm
      _ < interpretation (sourceCode s a) root := Mu.root_base_lt s a root ha
  have heps : Ordinal.omega0 ^ denote (contextCode s) (.theta 0 t) =
      denote (contextCode s) (.theta 0 t) := by
    rw [hv]
    exact root_epsilon s a root ha
  have hh : omegaSequence (base (contextCode s)) 1 ≤ denote (contextCode s) t := by
    rcases (OmegaPowers.theta_epsilon_iff (contextCode s) t ht).mp heps with hz | hh
    · exact False.elim ((ne_of_gt hb) hz)
    · exact hh
  have hsort : 1 < t.outerSort := by
    apply lt_of_not_ge
    intro hl
    exact hh.not_gt ((denote_lt_iff_outerSort_le (contextCode s) t
      (BaseTransformation.theta_argument_check _ 0 t ht) 1 (by omega)).mpr hl)
  exact (Iota.rootCheck_exact _ _).mpr ⟨t, he, ht, hn, hsort⟩

theorem returnedRoot_alphaCode (s a root : Nat) (ha : rootCheck s a root = true) :
    Iota.alphaCode s (returnedRoot s a root) = betaCode s a root := by
  have hs := Iota.alphaCode_spec s _ (returnedRoot_iota_caller s a root ha)
  have ht := betaCode_spec s a root ha
  exact Canonical.check_value_injective _ _ hs.1 ht.1
    (hs.2.trans ((returnedRoot_spec s a root ha).2.2.trans ht.2.symm))

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.BoundedContextIota.SourceReturn
