import Alexander313.Wilken.SourceCollapseSuccessorIntervals
import Alexander313.Wilken.HereditaryNativeMuBounds

/-!
# Genuine original-source mu successors in the adjacent interval

The actual mu output is additive principal. Genuine original-source LOW
coverage supplies a checked Normal term. If mu is strictly above the original
root alpha, its principal Normal spelling reduces to a genuine theta-zero
representative at the ORIGINAL source base. Actual source argument addition
and the source theta checker then construct its Convention 2.28 successor.
The genuine adjacent-interval comparison proves this successor below alpha+.
The result includes original raw execution and does not supply a source
representation, admission, argument-descent or successor-bound oracle.

The strict mu>alpha hypothesis is explicit. The mu<=alpha cases, source base
one and executing cross-context recoder remain separate; this file does not
claim the whole second endpoint inequality of Lemma 3.7. Uncompiled drafts.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Mu.SuccessorIntervals

open NativePublicBridge (contextCode contextCode_checked)

/-- A checked Normal additive principal value in the genuine interval
[base,Omega1) has an actual source theta-zero representative. Zero prefixes
in weak Normal sums are removed by the real final-principal sum criterion. -/
theorem principal_theta_zero (q : Nat) (t : RelativeTerm Nat)
    (ht : check q t = true) (hn : Comparison.Normal q t)
    (hb : base q ≤ denote q t) (hl : denote q t < omegaSequence (base q) 1)
    (hp : Ordinal.IsPrincipal (· + ·) (denote q t)) :
    ∃ b : RelativeTerm Nat, check q (.theta 0 b) = true ∧ Comparison.Normal q b ∧
      denote q (.theta 0 b) = denote q t := by
  revert ht hn hb hl hp
  induction t with
  | parameter p =>
    intro ht hn hb hl hp
    exact False.elim ((FixedPoint.checked_parameter_lt_base q p ht).not_ge hb)
  | sum a b iha ihb =>
    intro ht hn hb hl hp
    have hc := BaseTransformation.sum_checks q a b ht
    have hz : denote q a = 0 := by
      by_contra h
      exact RelativeTerm.PrincipalSupport.sourceNormalSum_not_principal hn.2.2
        (pos_iff_ne_zero.mpr h) hp
    have he : denote q b = denote q (.sum a b) := by
      change denote q b = denote q a + denote q b
      rw [hz, zero_add]
    obtain ⟨u, hu, hun, hv⟩ := ihb hc.2 hn.2.1 (he.symm ▸ hb) (he.symm ▸ hl) (he.symm ▸ hp)
    exact ⟨u, hu, hun, hv.trans he⟩
  | theta k b ih =>
    intro ht hn hb hl hp
    have hk : k = 0 := by
      by_contra h
      have h1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr h
      have hbad := ((omegaSequence_strictMono (base q)).monotone h1).trans
        (FixedPoint.checked_theta_range q k b ht).1
      exact hl.not_ge hbad
    subst k
    exact ⟨b, ht, hn, rfl⟩

/-- A genuine finite source operation on the actual theta argument. It
normalizes the original argument plus an admitted original unit. -/
def sourceSuccessorTerm (q : Nat) (b : RelativeTerm Nat) : RelativeTerm Nat :=
  .theta 0 (Arithmetic.addTerm q b.code (OmegaPowerHeight.numeralCode 1))

theorem sourceSuccessorTerm_primrec : Primrec₂ sourceSuccessorTerm := by
  have hi : Primrec (fun p : Nat × RelativeTerm Nat =>
      (p.1, (p.2.code, OmegaPowerHeight.numeralCode 1))) :=
    Primrec.fst.pair ((code_primrec.comp Primrec.snd).pair
    (Primrec.const (OmegaPowerHeight.numeralCode 1)))
  exact (theta_primrec.comp (Primrec.const 0) (Arithmetic.addTerm_primrec.comp hi)).to₂

/-- Original source theta admission derives every successor caller. The
output is checked, weak Normal and LOW and has the literal Convention 2.28
value at the SAME base; no target-to-source conversion is performed here. -/
theorem sourceSuccessorTerm_spec (q : Nat) (b : RelativeTerm Nat)
    (ht : check q (.theta 0 b) = true) :
    check q (sourceSuccessorTerm q b) = true ∧
      Comparison.Normal q (sourceSuccessorTerm q b) ∧
      (sourceSuccessorTerm q b).outerSort ≤ 1 ∧
      denote q (sourceSuccessorTerm q b) = globalCollapse (base q) 0 (denote q b + 1) := by
  have hq := (Bool.and_eq_true.mp ht).1
  have hb := FixedPoint.checked_theta_argument q 0 b ht
  have hc : checkCode q b.code = true := by simpa only [checkCode_code] using hb
  have hu := OmegaPowerHeight.numeralCode_spec q 1 hq
  have hus := (Comparison.acceptedCode_exact q _).mp hu.2.1
  have hs := Arithmetic.addTerm_spec q b.code (OmegaPowerHeight.numeralCode 1) hc hus.1
  have harg := Comparison.admitted_checked q _ hq _ hs.1
  have hv : denote q (Arithmetic.addTerm q b.code (OmegaPowerHeight.numeralCode 1)) =
      denote q b + 1 := by
    simpa only [interpretation_code, hu.2.2.1, Nat.cast_one] using hs.2.2
  have hsort : denote q (Arithmetic.addTerm q b.code (OmegaPowerHeight.numeralCode 1)) <
      omegaSequence (base q) 2 := by
    rw [hv]
    exact (omegaSequence_isSuccLimit (base q) 1).add_one_lt
      (FixedPoint.checked_theta_sort q 0 b ht)
  have hout := OmegaQuotient.theta_checked q 0 _ harg
    ((denote_lt_iff_outerSort_le q _ harg 2 (by omega)).mp hsort)
  refine ⟨hout, hs.2.1, by simp only [sourceSuccessorTerm, RelativeTerm.outerSort], ?_⟩
  change globalCollapse (base q) 0
    (denote q (Arithmetic.addTerm q b.code (OmegaPowerHeight.numeralCode 1))) = _
  rw [hv]

/-- Original source argument injectivity makes this successor value
independent of the chosen admitted theta-zero source representation. -/
theorem sourceSuccessorTerm_value_congr (q : Nat) (b c : RelativeTerm Nat)
    (hb : check q (.theta 0 b) = true) (hc : check q (.theta 0 c) = true)
    (he : denote q (.theta 0 b) = denote q (.theta 0 c)) :
    denote q (sourceSuccessorTerm q b) = denote q (sourceSuccessorTerm q c) := by
  have hq := (Bool.and_eq_true.mp hb).1
  have hbarg := FixedPoint.checked_theta_argument q 0 b hb
  have hcarg := FixedPoint.checked_theta_argument q 0 c hc
  have hargs := (globalCollapse_eq_iff (base q) (base_pos q hq) 0
    (FixedPoint.sourceOrdinal q 0 b hbarg) (FixedPoint.sourceOrdinal q 0 c hcarg)
    (FixedPoint.checked_theta_sort q 0 b hb) (FixedPoint.checked_theta_sort q 0 c hc)).mp he
  have hv : denote q b = denote q c := hargs
  rw [(sourceSuccessorTerm_spec q b hb).2.2.2,
    (sourceSuccessorTerm_spec q c hc).2.2.2, hv]

/-- Whole original normal mu execution and the explicit mu>alpha case
derive the actual source theta-zero representative, rather than assuming it. -/
theorem execute_source_theta (s a out : Nat) (ho : out ∈ Mu.execute s a)
    (hgt : interpretation (contextCode s) a < interpretation (Iota.alphaCode s a) out) :
    ∃ b : RelativeTerm Nat, check (contextCode s) (.theta 0 b) = true ∧
      Comparison.Normal (contextCode s) b ∧
      denote (contextCode s) (.theta 0 b) = interpretation (Iota.alphaCode s a) out := by
  have ha := (Mu.execute_spec s a out ho).1
  have hbound := (Mu.Bounds.execute_lt_source_alphaPlus s a out ho).trans
    (Lambda.SourceReturn.alphaPlus_lt_source_boundary s a (Bool.and_eq_true.mp ha).1)
  obtain ⟨t, ht, hn, hlow, hv⟩ := Lambda.SourceReturn.normal_low_representative s _ hbound
  have hb : base (contextCode s) ≤ denote (contextCode s) t := by
    rw [hv]
    exact (Iota.root_base_le s a ha).trans hgt.le
  have hl : denote (contextCode s) t < omegaSequence (base (contextCode s)) 1 := by
    rw [hv]
    exact hbound.trans (globalBoundary_lt_cardinal _ (base_pos _ (contextCode_checked s)) 0)
  have hp : Ordinal.IsPrincipal (· + ·) (denote (contextCode s) t) := by
    rw [hv, (Mu.execute_spec s a out ho).2.2.2, Mu.sourceValue]
    exact Ordinal.isPrincipal_add_omega0_opow _
  obtain ⟨b, hb, hbn, hbv⟩ := principal_theta_zero _ t ht hn hb hl hp
  exact ⟨b, hb, hbn, hbv.trans hv⟩

/-- The actual Convention 2.28 source mu-successor is constructed and
bounded for the explicit adjacent-interval mu>alpha branch. Its source
theta representative and all successor admissions are conclusions. -/
theorem execute_source_successor_lt (s a out : Nat) (ho : out ∈ Mu.execute s a)
    (hgt : interpretation (contextCode s) a < interpretation (Iota.alphaCode s a) out) :
    ∃ b : RelativeTerm Nat, check (contextCode s) (.theta 0 b) = true ∧
      Comparison.Normal (contextCode s) b ∧
      denote (contextCode s) (.theta 0 b) = interpretation (Iota.alphaCode s a) out ∧
      Comparison.acceptedCode (contextCode s) (sourceSuccessorTerm (contextCode s) b).code = true ∧
      interpretation (Iota.alphaCode s a) out < denote (contextCode s) (sourceSuccessorTerm (contextCode s) b) ∧
      denote (contextCode s) (sourceSuccessorTerm (contextCode s) b) < Iota.AlphaPlus.sourceValue s a := by
  have ha := (Mu.execute_spec s a out ho).1
  obtain ⟨b, hb, hbn, hv⟩ := execute_source_theta s a out ho hgt
  obtain ⟨A, he, hA, hAn, hAh⟩ := (Iota.rootCheck_exact s a).mp ha
  let q := contextCode s
  have hq := contextCode_checked s
  have hp := base_pos q hq
  have hac := FixedPoint.checked_theta_argument q 0 A hA
  have hbc := FixedPoint.checked_theta_argument q 0 b hb
  have hAs := FixedPoint.checked_theta_sort q 0 A hA
  have hbs := FixedPoint.checked_theta_sort q 0 b hb
  have hroot : interpretation q a = globalCollapse (base q) 0 (denote q A) := by
    rw [he, interpretation_code]
    rfl
  have hend : Iota.AlphaPlus.sourceValue s a = globalCollapse (base q) 0 (denote q A + 1) := by
    simp only [Iota.AlphaPlus.sourceValue, Lambda.argumentCode, he,
      Localization.argumentCode_theta, interpretation_code]
  have hgt' : globalCollapse (base q) 0 (denote q A) < globalCollapse (base q) 0 (denote q b) := by
    rw [← hroot]
    exact hgt.trans_eq hv.symm
  have hupper : globalCollapse (base q) 0 (denote q b) < globalCollapse (base q) 0 (denote q A + 1) := by
    rw [← hend]
    exact hv.trans_lt (Mu.Bounds.execute_lt_source_alphaPlus s a out ho)
  have hs := sourceSuccessorTerm_spec q b hb
  have hsucc := SourceCollapseSuccessorIntervals.global_adjacent_successor_lt_endpoint
    (base q) hp 0 (FixedPoint.sourceOrdinal q 0 A hac) (FixedPoint.sourceOrdinal q 0 b hbc)
    hAs hbs hgt' hupper
  refine ⟨b, hb, hbn, hv, ?_, ?_, ?_⟩
  · exact (Comparison.acceptedCode_exact q _).mpr
      ⟨by simpa only [checkCode_code] using hs.1,
        by simpa only [ThetaCourse.rawTree_code] using hs.2.1⟩
  · rw [hs.2.2.2, ← hv]
    exact SourceCollapseSuccessors.global_collapse_lt_successor (base q) hp 0
      (FixedPoint.sourceOrdinal q 0 b hbc) hbs
  · rw [hs.2.2.2, hend]
    exact hsucc

/-- Original raw execution inherits the SAME original-source successor
bound. Real normalization supplies the root and endpoint value equalities;
no normalized-domain or invariance hypothesis is supplied. -/
theorem raw_execute_source_successor_lt (s a out : Nat) (ho : out ∈ Mu.Raw.execute s a)
    (hgt : interpretation (contextCode s) a < interpretation (Mu.Raw.outputContext s a) out) :
    ∃ b : RelativeTerm Nat, check (contextCode s) (.theta 0 b) = true ∧
      Comparison.Normal (contextCode s) b ∧
      denote (contextCode s) (.theta 0 b) = interpretation (Mu.Raw.outputContext s a) out ∧
      Comparison.acceptedCode (contextCode s) (sourceSuccessorTerm (contextCode s) b).code = true ∧
      interpretation (Mu.Raw.outputContext s a) out < denote (contextCode s) (sourceSuccessorTerm (contextCode s) b) ∧
      denote (contextCode s) (sourceSuccessorTerm (contextCode s) b) < Iota.AlphaPlus.sourceValue s a := by
  have hr := (Mu.Raw.execute_graph s a out).mp ho
  have hc := Bool.and_eq_true.mp hr.1
  have hn : out ∈ Mu.execute s (Mu.Raw.normalizedRoot s a) :=
    (Mu.execute_graph s _ out).mpr ⟨hc.2, by
      simpa only [Mu.Raw.muCode, hr.1, Bool.cond_true] using hr.2⟩
  have he : interpretation (contextCode s) (Mu.Raw.normalizedRoot s a) =
      interpretation (contextCode s) a :=
    (Iota.alpha_base s _ hc.2).symm.trans (Mu.Raw.outputContext_value s a hr.1)
  have hgn : interpretation (contextCode s) (Mu.Raw.normalizedRoot s a) <
      interpretation (Iota.alphaCode s (Mu.Raw.normalizedRoot s a)) out := by
    simpa only [he, Mu.Raw.outputContext] using hgt
  simpa only [Mu.Raw.outputContext, Lambda.Branches.Raw.normalized_source_alphaPlus s a hc.1] using
    execute_source_successor_lt s (Mu.Raw.normalizedRoot s a) out hn hgn

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Mu.SuccessorIntervals
