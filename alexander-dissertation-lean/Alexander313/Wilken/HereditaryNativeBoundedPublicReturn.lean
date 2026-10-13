import Alexander313.Wilken.HereditaryNativeBoundedPublicReturnSupport

/-!
# Finite same-value return from the genuine bounded alpha grammar

The original source-code producer recurses on the actual target tree.
Positive indices remain unchanged. A zero call splits its already returned
argument at the true source Omega1. A zero head uses the full corrected LOW
collapse formula. A nonzero head uses actual source comparison with the
original root, selecting the two proved high-tail SAME-value rewrites.
All local admission and endpoint bounds follow from the original target
checker, Normality and the derived complete zero-call bound. The LOW caller
derives that bound from its original value below original alpha-plus.
Uncompiled source candidates. No executing return or comparison oracle.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.BoundedPublicReturn

open NativePublicBridge (contextCode contextCode_checked)
open Iota Iota.HeightSupport RelativeHighRewrite

def nodeCode (k c : Nat) : Nat := (.theta k (ThetaCourse.rawTree c) : RelativeTerm Nat).code

theorem nodeCode_primrec : Primrec₂ nodeCode :=
  (code_primrec.comp (theta_primrec.comp Primrec.fst
    (ThetaCourse.rawTree_primrec.comp Primrec.snd))).to₂

theorem nodeCode_spec (q k c : Nat) (hc : Decomposition.inputCheck q c = true)
    (hs : interpretation q c < omegaSequence (base q) (k + 2)) :
    Comparison.acceptedCode q (nodeCode k c) = true ∧
      interpretation q (nodeCode k c) = globalCollapse (base q) k (interpretation q c) := by
  have ht := Decomposition.input_tree q c hc
  have hcc := (Decomposition.inputCheck_exact q c).mp hc
  have hsort : (ThetaCourse.rawTree c).outerSort ≤ k + 2 :=
    (denote_lt_iff_outerSort_le q _ ht.1 (k + 2) (by omega)).mp
      ((Arithmetic.raw_value q c hcc.1).trans_lt hs)
  have hn := Iota.Inverse.checked_theta q k _ ht.1 hsort
  refine ⟨accepted_of_checked_normal q _ hn ht.2, ?_⟩
  simp only [nodeCode, interpretation_code]
  change globalCollapse (base q) k (denote q (ThetaCourse.rawTree c)) = _
  rw [Arithmetic.raw_value q c hcc.1]

def shiftedArgument (s a c : Nat) : Nat := Arithmetic.addCode (contextCode s)
  (Decomposition.highCode 0 c)
  (Arithmetic.addCode (contextCode s) a (Decomposition.lowCode 0 c))

def zeroCode (s a c : Nat) : Nat :=
  cond (FixedPoint.zeroCheck (Decomposition.highCode 0 c))
    (LowArithmetic.returnCode s (ElementaryPublicReturn.collapseCode (alphaCode s a)
      (LowArithmetic.publicCode s c)))
    (cond (Normalization.lessRawCode (contextCode s) a (nodeCode 0 (Decomposition.highCode 0 c)))
      (nodeCode 0 c) (nodeCode 0 (shiftedArgument s a c)))

/-- The actual node producer preserves the target zero-call value. Every
high-head caller is derived from its ORIGINAL endpoint bound. -/
theorem zeroCode_spec (s a c : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (alphaCode s a) (.theta 0 t) = true)
    (hn : Comparison.Normal (alphaCode s a) t)
    (hb : denote (alphaCode s a) (.theta 0 t) < AlphaPlus.sourceValue s a)
    (hc : Decomposition.inputCheck (contextCode s) c = true)
    (hv : interpretation (contextCode s) c = denote (alphaCode s a) t) :
    Comparison.acceptedCode (contextCode s) (zeroCode s a c) = true ∧
      interpretation (contextCode s) (zeroCode s a c) = denote (alphaCode s a) (.theta 0 t) := by
  let q := contextCode s
  let α := interpretation q a
  let Γ := interpretation q (Decomposition.highCode 0 c)
  let ρ := interpretation q (Decomposition.lowCode 0 c)
  have hq := contextCode_checked s
  have hcc := (Decomposition.inputCheck_exact q c).mp hc
  have hqp := base_pos q hq
  have hα := alpha_base s a ha
  have hαlow := root_below_first_cardinal s a ha
  have hle := root_base_le s a ha
  have hd := Decomposition.parts_reconstruct q 0 c hc
  have hlow : ρ < omegaSequence (base q) 1 := Decomposition.lowPart_bound q 0 c hc
  have hΓd : omegaSequence (base q) 1 ∣ Γ := Decomposition.highPart_dvd q 0 c hc
  have hs : interpretation q c < omegaSequence (base q) 2 := by
    rw [hv, root_omegaSequence_succ s a 1 ha]
    exact FixedPoint.checked_theta_sort _ 0 t ht
  have hΓs : Γ < omegaSequence (base q) 2 := (Decomposition.parts_le q 0 c hc).1.trans_lt hs
  have hp := Decomposition.parts_accepted q 0 c hc
  have hpc := (Decomposition.inputCheck_exact q _).mp hp.1
  have hpl := (Decomposition.inputCheck_exact q _).mp hp.2
  have hΓn : GlobalNotation (base q) 1 Γ := by
    simpa only [Γ, Decomposition.highCode, interpretation_code] using
      Decomposition.checked_all_levels q 1 (Decomposition.highPartTerm 0 c)
        (Decomposition.parts_checked q 0 c hc).1
  have hhead := nodeCode_spec q 0 (Decomposition.highCode 0 c) hp.1 hΓs
  have hnode := nodeCode_spec q 0 c hc hs
  have htarget : denote (alphaCode s a) (.theta 0 t) =
      globalCollapse α 0 (Γ + ρ) := by
    change globalCollapse (base (alphaCode s a)) 0 (denote (alphaCode s a) t) = _
    rw [hα, ← hv, ← hd]
  cases hz : FixedPoint.zeroCheck (Decomposition.highCode 0 c) with
  | true =>
    have hΓ0 : Γ = 0 := (FixedPoint.zeroCheck_exact q _ hp.1).mp hz
    have hcs : interpretation q c < omegaSequence (base q) 1 := by
      calc
        interpretation q c = Γ + ρ := hd.symm
        _ = ρ := by rw [hΓ0, zero_add]
        _ < omegaSequence (base q) 1 := hlow
    have htcode := (Decomposition.input_tree q c hc).1
    have hl : (ThetaCourse.rawTree c).outerSort ≤ 1 :=
      (denote_lt_iff_outerSort_le q _ htcode 1 (by omega)).mp
        ((Arithmetic.raw_value q c hcc.1).trans_lt hcs)
    have hli : LowArithmetic.lowInput s c = true := by
      obtain ⟨v, he, hvcheck⟩ := (checkCode_exact q c).mp hcc.1
      have hvl : v.outerSort ≤ 1 := by
        simpa only [← he, ThetaCourse.rawTree_code] using hl
      simpa only [LowArithmetic.lowInput, ← he, lowCheckCode_code, lowCheck,
        hvcheck, hvl, decide_true, Bool.true_and]
    have hpublic := LowArithmetic.publicCode_spec s c hli
    have hcollapse := ElementaryPublicReturn.collapseCode_spec (alphaCode s a)
      (LowArithmetic.publicCode s c) (alphaCode_baseCheck s a ha) hpublic.1 (by
        rw [hpublic.2, ← root_omegaSequence_succ s a 0 ha]
        exact hcs)
    have hvalue : unionInterpretation (ElementaryPublicReturn.collapseCode (alphaCode s a)
        (LowArithmetic.publicCode s c)) = denote (alphaCode s a) (.theta 0 t) := by
      rw [hcollapse.2, hpublic.2, hv]
      rfl
    have hret := LowArithmetic.returnCode_spec s _ hcollapse.1
      (hvalue.trans_lt (hb.trans (sourceValue_lt_public_endpoint s a ha)))
    simp only [zeroCode, hz, Bool.cond_true]
    exact ⟨hret.2.1, hret.2.2.trans hvalue⟩
  | false =>
    have hΓne : Γ ≠ 0 := by
      intro he
      have htrue := (FixedPoint.zeroCheck_exact q _ hp.1).mpr he
      simp only [hz, Bool.false_eq_true] at htrue
    have hΓ0 : 0 < Γ := pos_iff_ne_zero.mpr hΓne
    cases hbigger : Normalization.lessRawCode q a (nodeCode 0 (Decomposition.highCode 0 c)) with
    | true =>
      have hgt := (Normalization.lessRawCode_exact q a _).mp hbigger
      have habove : α < globalCollapse (base q) 0 Γ := by
        simpa only [hhead.2] using hgt.2.2
      have he := global_relative_tail_eq_of_source_head_above (base q) α hqp hle hαlow
        Γ hΓn hΓs hΓd habove ρ hlow
      simp only [zeroCode, hz, Bool.cond_false, hbigger, Bool.cond_true]
      refine ⟨hnode.1, ?_⟩
      rw [hnode.2, ← hd, ← he, ← htarget]
    | false =>
      have hbelow : globalCollapse (base q) 0 Γ ≤ α := by
        apply le_of_not_gt
        intro hgt
        have htrue := (Normalization.lessRawCode_exact q a _).mpr
          ⟨root_original s a ha, ((Comparison.acceptedCode_exact q _).mp hhead.1).1,
            by simpa only [hhead.2] using hgt⟩
        simp only [hbigger, Bool.false_eq_true] at htrue
      have hΓΔ := converted_highPart_lt_delta s a c ha t ht hn hb hc hv
      have hAinput := Lambda.argument_accepted s a ha
      have hroot := (rootCheck_exact s a).mp ha
      obtain ⟨b, hecode, hbcheck, hbn, hhigh⟩ := hroot
      let A := interpretation q (Lambda.argumentCode a)
      have hA : GlobalNotation (base q) 1 A := by
        simpa only [A, Lambda.argumentCode, hecode, Localization.argumentCode_theta,
          interpretation_code] using Decomposition.checked_all_levels q 1 b
            (BaseTransformation.theta_argument_check q 0 b hbcheck)
      have hAs : A < omegaSequence (base q) 2 := by
        simpa only [A, Lambda.argumentCode, hecode, Localization.argumentCode_theta,
          interpretation_code] using FixedPoint.checked_theta_sort q 0 b hbcheck
      have hrootvalue : α = globalCollapse (base q) 0 A := by
        simp only [α, A, hecode, Lambda.argumentCode, Localization.argumentCode_theta,
          interpretation_code]
        rfl
      have he := global_relative_tail_eq_of_source_head_below (base q) hqp A
        (interpretation q (Lambda.deltaCode a))
        (interpretation q (Decomposition.lowCode 0 (Lambda.argumentCode a))) Γ hA hAs
        (Decomposition.highPart_dvd q 0 (Lambda.argumentCode a) hAinput)
        (Decomposition.lowPart_bound q 0 (Lambda.argumentCode a) hAinput)
        (Decomposition.parts_reconstruct q 0 (Lambda.argumentCode a) hAinput).symm
        hΓn hΓd hΓ0 hΓΔ (by simpa only [← hrootvalue] using hbelow) ρ hlow
      have hsum1 := Arithmetic.addCode_spec q a (Decomposition.lowCode 0 c)
        (root_original s a ha) hpl.1
      have hsum2 := Arithmetic.addCode_spec q (Decomposition.highCode 0 c)
        (Arithmetic.addCode q a (Decomposition.lowCode 0 c)) hpc.1
        ((Comparison.acceptedCode_exact q _).mp hsum1.1).1
      have hshiftvalue : interpretation q (shiftedArgument s a c) = Γ + (α + ρ) :=
        hsum2.2.1.trans (by rw [hsum1.2.1])
      have htail : α + ρ < omegaSequence (base q) 1 :=
        (omegaSequence_add_closed (base q) 0) hαlow hlow
      have hshiftsort : interpretation q (shiftedArgument s a c) < omegaSequence (base q) 2 := by
        rw [hshiftvalue]
        exact (omegaSequence_add_closed (base q) 1) hΓs
          (htail.trans ((omegaSequence_strictMono (base q)) (by omega : 1 < 2)))
      have hshift := nodeCode_spec q 0 (shiftedArgument s a c) hsum2.1 hshiftsort
      simp only [zeroCode, hz, Bool.cond_false, hbigger]
      refine ⟨hshift.1, ?_⟩
      rw [hshift.2, hshiftvalue]
      have he' : globalCollapse (base q) 0 (Γ + (α + ρ)) =
          globalCollapse α 0 (Γ + ρ) := by simpa only [← hrootvalue] using he.symm
      exact he'.trans htarget.symm

theorem zeroCode_primrec : Primrec
    (fun p : Nat × (Nat × Nat) => zeroCode p.1 p.2.1 p.2.2) := by
  have hs := Primrec.fst
  have ha := Primrec.fst.comp Primrec.snd
  have hc := Primrec.snd.comp Primrec.snd
  have hq := contextCode_primrec.comp hs
  have hg := Decomposition.highCode_primrec.comp (Primrec.const 0) hc
  have hl := Decomposition.lowCode_primrec.comp (Primrec.const 0) hc
  have hsum1 := Arithmetic.addCode_primrec.comp (hq.pair (ha.pair hl))
  have hsum2 := Arithmetic.addCode_primrec.comp (hq.pair (hg.pair hsum1))
  have hα := alphaCode_primrec.comp hs ha
  have hp := LowArithmetic.publicCode_primrec.comp hs hc
  exact (FixedPoint.zeroCheck_primrec.comp hg).cond
    (LowArithmetic.returnCode_primrec.comp hs
      (ElementaryPublicReturn.collapseCode_primrec.comp hα hp))
    ((Normalization.Effective.lessRawCode_primrec.comp
      (hq.pair (ha.pair (nodeCode_primrec.comp (Primrec.const 0) hg)))).cond
      (nodeCode_primrec.comp (Primrec.const 0) hc)
      (nodeCode_primrec.comp (Primrec.const 0) hsum2))

def thetaCode (s a k c : Nat) : Nat := cond (k == 0) (zeroCode s a c) (nodeCode k c)

theorem thetaCode_primrec : Primrec
    (fun p : (Nat × Nat) × (Nat × Nat) => thetaCode p.1.1 p.1.2 p.2.1 p.2.2) := by
  have hs := Primrec.fst.comp Primrec.fst
  have ha := Primrec.snd.comp Primrec.fst
  have hk := Primrec.fst.comp Primrec.snd
  have hc := Primrec.snd.comp Primrec.snd
  exact (Primrec.beq.comp hk (Primrec.const 0)).cond
    (zeroCode_primrec.comp (hs.pair (ha.pair hc))) (nodeCode_primrec.comp hk hc)

def parameterState (ctx : Nat × Nat) (p : Nat) : Nat × Nat :=
  (ctx.1, Iota.Inverse.atomCode ctx.1 p)

def sumState (x y : Nat × Nat) : Nat × Nat :=
  (x.1, Arithmetic.addCode (contextCode x.1) x.2 y.2)

def thetaState (ctx : Nat × Nat) (k : Nat) (x : Nat × Nat) : Nat × Nat :=
  (ctx.1, thetaCode ctx.1 ctx.2 k x.2)

def stateTerm (s a : Nat) (t : RelativeTerm Nat) : Nat × Nat :=
  ValueFold.term parameterState sumState thetaState (s, a) t

def sourceTermCode (s a : Nat) (t : RelativeTerm Nat) : Nat := (stateTerm s a t).2

theorem stateTerm_context (s a : Nat) (t : RelativeTerm Nat) : (stateTerm s a t).1 = s := by
  induction t with
  | parameter p => rfl
  | sum t u iht ihu => exact iht
  | theta k t ih => rfl

theorem sourceTermCode_parameter (s a p : Nat) :
    sourceTermCode s a (.parameter p) = Iota.Inverse.atomCode s p := rfl

theorem sourceTermCode_sum (s a : Nat) (t u : RelativeTerm Nat) :
    sourceTermCode s a (.sum t u) = Arithmetic.addCode (contextCode s)
      (sourceTermCode s a t) (sourceTermCode s a u) := by
  change Arithmetic.addCode (contextCode (stateTerm s a t).1) _ _ = _
  rw [stateTerm_context]

theorem sourceTermCode_theta (s a k : Nat) (t : RelativeTerm Nat) :
    sourceTermCode s a (.theta k t) = thetaCode s a k (sourceTermCode s a t) := rfl

theorem stateTerm_primrec : Primrec₂ (fun ctx : Nat × Nat => stateTerm ctx.1 ctx.2) := by
  have hp : Primrec₂ parameterState := by
    have hs := Primrec.fst.comp Primrec.fst
    exact (hs.pair (Iota.Inverse.atomCode_primrec.comp hs Primrec.snd)).to₂
  have hadd : Primrec₂ sumState := by
    have hs := Primrec.fst.comp Primrec.fst
    have hc := Primrec.snd.comp Primrec.fst
    have hd := Primrec.snd.comp Primrec.snd
    exact (hs.pair (Arithmetic.addCode_primrec.comp
      ((contextCode_primrec.comp hs).pair (hc.pair hd)))).to₂
  have hθ : Primrec (fun p : (Nat × Nat) × (Nat × (Nat × Nat)) =>
      thetaState p.1 p.2.1 p.2.2) := by
    have hs := Primrec.fst.comp Primrec.fst
    have ha := Primrec.snd.comp Primrec.fst
    have hk := Primrec.fst.comp Primrec.snd
    have hc := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
    exact hs.pair (thetaCode_primrec.comp ((hs.pair ha).pair (hk.pair hc)))
  exact ValueFold.term_primrec parameterState sumState thetaState (0, 0) hp hadd hθ

theorem sourceTermCode_primrec : Primrec₂ (fun ctx : Nat × Nat => sourceTermCode ctx.1 ctx.2) :=
  (Primrec.snd.comp stateTerm_primrec).to₂

/-- Every hidden zero caller is carried through the recursion. For the
original LOW domain this internal induction invariant is derived below. -/
theorem sourceTermCode_spec (s a : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (alphaCode s a) t = true)
    (hn : Comparison.Normal (alphaCode s a) t)
    (hb : ∀ u ∈ fullList t, denote (alphaCode s a) u < AlphaPlus.sourceValue s a) :
    Comparison.acceptedCode (contextCode s) (sourceTermCode s a t) = true ∧
      interpretation (contextCode s) (sourceTermCode s a t) = denote (alphaCode s a) t := by
  revert ht hn hb
  induction t with
  | parameter p =>
    intro ht hn hb
    have hp := (parameterCheck_exact _ p).mp (checked_admissible _ _ ht).1
    have hv := Canonical.canonicalize_value p hp.1
    have hsmall : parameters p < interpretation (contextCode s) a := by
      simpa only [alpha_base s a ha] using hp.2.2
    have hbound : unionInterpretation (Canonical.canonicalize p) < finiteBase ((s + 1) + 1) := by
      rw [hv]
      exact hsmall.trans (LowArithmetic.lowInput_bound s a (root_low s a ha))
    have hs := LowArithmetic.returnCode_spec s (Canonical.canonicalize p)
      (Canonical.canonicalize_check p hp.1) hbound
    rw [sourceTermCode_parameter]
    exact ⟨hs.2.1, hs.2.2.trans hv⟩
  | sum t u iht ihu =>
    intro ht hn hb
    have hc := BaseTransformation.sum_checks _ t u ht
    have hbt : ∀ v ∈ fullList t, denote (alphaCode s a) v < AlphaPlus.sourceValue s a := by
      intro v hv
      exact hb v (List.mem_append.mpr (Or.inl hv))
    have hbu : ∀ v ∈ fullList u, denote (alphaCode s a) v < AlphaPlus.sourceValue s a := by
      intro v hv
      exact hb v (List.mem_append.mpr (Or.inr hv))
    have hst := iht hc.1 hn.1 hbt
    have hsu := ihu hc.2 hn.2.1 hbu
    rw [sourceTermCode_sum]
    have hs := Arithmetic.addCode_spec (contextCode s) _ _
      ((Comparison.acceptedCode_exact _ _).mp hst.1).1
      ((Comparison.acceptedCode_exact _ _).mp hsu.1).1
    exact ⟨hs.1, hs.2.1.trans (by rw [hst.2, hsu.2]; rfl)⟩
  | theta k t ih =>
    intro ht hn hb
    have hc := BaseTransformation.theta_argument_check _ k t ht
    have hbt : ∀ u ∈ fullList t, denote (alphaCode s a) u < AlphaPlus.sourceValue s a := by
      intro u hu
      cases k with
      | zero => exact hb u (RelativeTerm.PrincipalSupport.principalList_nested 0 t u hu)
      | succ k =>
        exact hb u (by simpa only [fullList,
          RelativeTerm.PrincipalSupport.principalList_theta_higher 0 (k + 1) t (Nat.succ_pos k)] using hu)
    have hs := ih hc hn hbt
    rw [sourceTermCode_theta]
    cases k with
    | zero =>
      simp only [thetaCode, beq_self_eq_true, Bool.cond_true]
      exact zeroCode_spec s a _ ha t ht hn
        (hb (.theta 0 t) (RelativeTerm.PrincipalSupport.principalList_root 0 t)) hs.1 hs.2
    | succ k =>
      have hk0 : (k + 1 == 0) = false := by simp
      simp only [thetaCode, hk0, Bool.cond_false]
      have hsort : interpretation (contextCode s) (sourceTermCode s a t) <
          omegaSequence (base (contextCode s)) (k + 1 + 2) := by
        rw [hs.2, root_omegaSequence_succ s a (k + 2) ha]
        exact FixedPoint.checked_theta_sort _ (k + 1) t ht
      have hnode := nodeCode_spec (contextCode s) (k + 1) _ hs.1 hsort
      refine ⟨hnode.1, ?_⟩
      have htarg := Decomposition.input_tree (contextCode s) _ hs.1
      have hcheck := (Comparison.acceptedCode_exact _ _).mp hnode.1
      have hcnode := Arithmetic.raw_checked _ _ hcheck.1
      have hsourcecheck : check (contextCode s)
          (.theta (k + 1) (ThetaCourse.rawTree (sourceTermCode s a t))) = true := by
        simpa only [nodeCode, ThetaCourse.rawTree_code] using hcnode
      have hv : denote (alphaCode s a) t =
          denote (contextCode s) (ThetaCourse.rawTree (sourceTermCode s a t)) :=
        hs.2.symm.trans (Arithmetic.raw_value _ _ ((Comparison.acceptedCode_exact _ _).mp hs.1).1).symm
      have he := root_positive_theta_value s a (k + 1) ha _ t (Nat.succ_pos k)
        hsourcecheck ht hv
      simpa only [nodeCode, interpretation_code] using he.symm

theorem sourceTermCode_low_spec (s a : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (alphaCode s a) t = true)
    (hn : Comparison.Normal (alphaCode s a) t) (hl : t.outerSort ≤ 1)
    (hb : denote (alphaCode s a) t < AlphaPlus.sourceValue s a) :
    Comparison.acceptedCode (contextCode s) (sourceTermCode s a t) = true ∧
      LowArithmetic.lowInput s (sourceTermCode s a t) = true ∧
      interpretation (contextCode s) (sourceTermCode s a t) = denote (alphaCode s a) t := by
  have hs := sourceTermCode_spec s a ha t ht hn (low_zero_calls_bounded s a ha t ht hn hl hb)
  have hc := (Comparison.acceptedCode_exact _ _).mp hs.1
  have hct := Arithmetic.raw_checked _ _ hc.1
  have hlow : (ThetaCourse.rawTree (sourceTermCode s a t)).outerSort ≤ 1 := by
    apply (denote_lt_iff_outerSort_le _ _ hct 1 (by omega)).mp
    rw [Arithmetic.raw_value _ _ hc.1, hs.2, root_omegaSequence_succ s a 0 ha]
    exact (denote_lt_iff_outerSort_le _ _ ht 1 (by omega)).mpr hl
  obtain ⟨u, he, hu⟩ := (checkCode_exact _ _).mp hc.1
  have hul : u.outerSort ≤ 1 := by simpa only [← he, ThetaCourse.rawTree_code] using hlow
  refine ⟨hs.1, ?_, hs.2⟩
  simp only [LowArithmetic.lowInput, ← he, lowCheckCode_code, lowCheck, hu, hul,
    decide_true, Bool.true_and]

def publicTerm (s a : Nat) (t : RelativeTerm Nat) : Nat :=
  Canonical.canonicalize (LowArithmetic.publicCode s (sourceTermCode s a t))

theorem publicTerm_primrec : Primrec₂ (fun ctx : Nat × Nat => publicTerm ctx.1 ctx.2) :=
  (Canonical.Effective.canonicalize_primrec.comp
    (LowArithmetic.publicCode_primrec.comp (Primrec.fst.comp Primrec.fst) sourceTermCode_primrec)).to₂

/-- SAME public value on the whole original checked LOW weak-normal alpha
domain below ORIGINAL source alpha-plus, including all high hidden calls.
There is no extra high-head, payload, height or restriction guard. -/
theorem publicTerm_spec (s a : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (alphaCode s a) t = true)
    (hn : Comparison.Normal (alphaCode s a) t) (hl : t.outerSort ≤ 1)
    (hb : denote (alphaCode s a) t < AlphaPlus.sourceValue s a) :
    Canonical.check (publicTerm s a t) = true ∧
      unionInterpretation (publicTerm s a t) = denote (alphaCode s a) t := by
  have hs := sourceTermCode_low_spec s a ha t ht hn hl hb
  have hp := LowArithmetic.publicCode_spec s _ hs.2.1
  exact ⟨Canonical.canonicalize_check _ hp.1,
    (Canonical.canonicalize_value _ hp.1).trans (hp.2.trans hs.2.2)⟩

/-- The original raw target is normalized before the genuine finite return.
No weak-Normal premise is added to the original raw LOW domain. -/
def rawPublicCode (s a c : Nat) : Nat := publicTerm s a
  (Normalization.normalize (alphaCode s a) (ThetaCourse.rawTree c))

theorem rawPublicCode_primrec : Primrec
    (fun p : (Nat × Nat) × Nat => rawPublicCode p.1.1 p.1.2 p.2) := by
  have hα := alphaCode_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)
  exact publicTerm_primrec.comp Primrec.fst
    (Normalization.Effective.normalize_primrec.comp hα (ThetaCourse.rawTree_primrec.comp Primrec.snd))

theorem rawPublicCode_spec (s a c : Nat) (ha : rootCheck s a = true)
    (hc : lowCheckCode (alphaCode s a) c = true)
    (hb : interpretation (alphaCode s a) c < AlphaPlus.sourceValue s a) :
    Canonical.check (rawPublicCode s a c) = true ∧
      unionInterpretation (rawPublicCode s a c) = interpretation (alphaCode s a) c := by
  obtain ⟨t, he, ht⟩ := (lowCheckCode_exact _ c).mp hc
  have hparts := Bool.and_eq_true.mp ht
  have hl : t.outerSort ≤ 1 := of_decide_eq_true hparts.2
  have hn := Normalization.normalize_checked (alphaCode s a) t hparts.1
  have hnl : (Normalization.normalize (alphaCode s a) t).outerSort ≤ 1 := by
    apply (denote_lt_iff_outerSort_le _ _ hn.1 1 (by omega)).mp
    rw [hn.2.2]
    exact (denote_lt_iff_outerSort_le _ _ hparts.1 1 (by omega)).mpr hl
  have hbound : denote (alphaCode s a) (Normalization.normalize (alphaCode s a) t) <
      AlphaPlus.sourceValue s a := by
    rw [hn.2.2]
    simpa only [← he, interpretation_code] using hb
  have hs := publicTerm_spec s a ha _ hn.1 hn.2.1 hnl hbound
  simpa only [rawPublicCode, ← he, ThetaCourse.rawTree_code, interpretation_code,
    hn.2.2] using hs

theorem rawPublicCode_value_invariant (s a c d : Nat) (ha : rootCheck s a = true)
    (hc : lowCheckCode (alphaCode s a) c = true) (hd : lowCheckCode (alphaCode s a) d = true)
    (hb : interpretation (alphaCode s a) c < AlphaPlus.sourceValue s a)
    (he : interpretation (alphaCode s a) c = interpretation (alphaCode s a) d) :
    rawPublicCode s a c = rawPublicCode s a d := by
  have hs := rawPublicCode_spec s a c ha hc hb
  have hs' := rawPublicCode_spec s a d ha hd (he ▸ hb)
  exact Canonical.check_value_injective _ _ hs.1 hs'.1 (hs.2.trans (he.trans hs'.2.symm))

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.BoundedPublicReturn
