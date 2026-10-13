import Alexander313.Wilken.SourceOneNativeBoundedPublicReturnSupport
import Alexander313.Wilken.HereditaryAddition
import Alexander313.Wilken.HereditarySourceFixedPoint

/-!
# Finite SAME-value return in the ORIGINAL source-one dictionary

Positive theta indices are retained. Zero calls split the already returned
ORIGINAL argument at source Omega-one. Zero head uses the true corrected
LOW collapse formula and bounded return at public level zero. Nonzero
head uses the actual ORIGINAL comparison and both proved high-tail
rewrites. The original raw LOW endpoint supplies every hidden caller.
No native positive-epsilon source parser is used for tau=1. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.BoundedPublicReturn

open OrderSupport HeightSupport
open NativeContext.RelativeHighRewrite

def nodeCode (k c : Nat) : Nat := (.theta k (ThetaCourse.rawTree c) : RelativeTerm Nat).code

theorem nodeCode_primrec : Primrec₂ nodeCode :=
  (code_primrec.comp (theta_primrec.comp Primrec.fst
    (ThetaCourse.rawTree_primrec.comp Primrec.snd))).to₂

theorem nodeCode_spec (k c : Nat) (hc : SourceDecomposition.inputCheck 0 c = true)
    (hs : interpretation 0 c < omegaSequence (finiteBase 0) (k + 2)) :
    Theta.acceptedCode 0 (nodeCode k c) = true ∧
      interpretation 0 (nodeCode k c) = globalCollapse (finiteBase 0) k (interpretation 0 c) := by
  have ht := SourceDecomposition.input_tree 0 c hc
  have hv := SourceDecomposition.input_value 0 c hc
  have hsort : (ThetaCourse.rawTree c).outerSort ≤ k + 2 :=
    (denote_lt_iff_outerSort_le 0 _ ht.1 (k + 2) (by omega)).mp (hv ▸ hs)
  have hn := OmegaQuotient.theta_checked k _ ht.1 hsort
  refine ⟨(Theta.acceptedCode_iff 0 _).mpr ⟨?_, ht.2⟩, ?_⟩
  · simpa only [nodeCode, checkCode_code] using hn
  · simp only [nodeCode, interpretation_code]
    change globalCollapse (finiteBase 0) k (denote 0 (ThetaCourse.rawTree c)) = _
    rw [← hv]

def shiftedArgument (a c : Nat) : Nat := Addition.normalizedSumCode 0
  (SourceDecomposition.highCode 0 0 c)
  (Addition.normalizedSumCode 0 a (SourceDecomposition.lowCode 0 0 c))

def zeroCode (a c : Nat) : Nat :=
  cond (SourceFixedPoint.zeroCheck 0 (SourceDecomposition.highCode 0 0 c))
    (SourceZeta.Transport.returnCode 0 (NativeContext.ElementaryPublicReturn.collapseCode
      (alphaCode a) (Nat.pair 0 c)))
    (cond (Theta.Normalization.lessRawCode 0 a (nodeCode 0 (SourceDecomposition.highCode 0 0 c)))
      (nodeCode 0 c) (nodeCode 0 (shiftedArgument a c)))

theorem zeroCode_spec (a c : Nat) (ha : rootCheck a = true)
    (t : RelativeTerm Nat) (ht : NativeContext.check (alphaCode a) (.theta 0 t) = true)
    (hn : NativeContext.Comparison.Normal (alphaCode a) t)
    (hb : NativeContext.denote (alphaCode a) (.theta 0 t) < Enclosure.sourceAlphaPlus a)
    (hc : SourceDecomposition.inputCheck 0 c = true)
    (hv : interpretation 0 c = NativeContext.denote (alphaCode a) t) :
    Theta.acceptedCode 0 (zeroCode a c) = true ∧
      interpretation 0 (zeroCode a c) = NativeContext.denote (alphaCode a) (.theta 0 t) := by
  let α := interpretation 0 a
  let Γ := interpretation 0 (SourceDecomposition.highCode 0 0 c)
  let ρ := interpretation 0 (SourceDecomposition.lowCode 0 0 c)
  have hcc := (SourceDecomposition.inputCheck_exact 0 c).mp hc
  have hqp := finiteBase_pos 0
  have hα := alpha_base a ha
  have hαlow : α < omegaSequence (finiteBase 0) 1 := by
    simpa only [α, finiteBase_zero] using root_lt_first a ha
  have hle : finiteBase 0 ≤ α := by
    simpa only [α, finiteBase_zero] using (EpsilonOffsets.epsilon_one_lt (root_epsilon a ha)).le
  have hd := SourceDecomposition.parts_reconstruct 0 0 c hc
  have hlow : ρ < omegaSequence (finiteBase 0) 1 := SourceDecomposition.lowPart_bound 0 0 c hc
  have hΓd : omegaSequence (finiteBase 0) 1 ∣ Γ := SourceDecomposition.highPart_dvd 0 0 c hc
  have hs : interpretation 0 c < omegaSequence (finiteBase 0) 2 := by
    rw [hv]
    simpa only [finiteBase_zero, root_omegaSequence_succ a 1 ha] using
      NativeContext.FixedPoint.checked_theta_sort _ 0 t ht
  have hΓs : Γ < omegaSequence (finiteBase 0) 2 := (SourceDecomposition.parts_le 0 0 c hc).1.trans_lt hs
  have hp := SourceDecomposition.parts_accepted 0 0 c hc
  have hpc := (SourceDecomposition.inputCheck_exact 0 _).mp hp.1
  have hpl := (SourceDecomposition.inputCheck_exact 0 _).mp hp.2
  have hΓn : GlobalNotation (finiteBase 0) 1 Γ := by
    simpa only [Γ, SourceDecomposition.highCode, interpretation_code] using
      SourceDecomposition.checked_all_levels 0 1 (SourceDecomposition.highPartTerm 0 0 c)
        (SourceDecomposition.parts_checked 0 0 c hc).1
  have hhead := nodeCode_spec 0 (SourceDecomposition.highCode 0 0 c) hp.1 hΓs
  have hnode := nodeCode_spec 0 c hc hs
  have htarget : NativeContext.denote (alphaCode a) (.theta 0 t) =
      globalCollapse α 0 (Γ + ρ) := by
    change globalCollapse (NativeContext.base (alphaCode a)) 0
      (NativeContext.denote (alphaCode a) t) = _
    rw [hα, ← hv, ← hd]
  cases hz : SourceFixedPoint.zeroCheck 0 (SourceDecomposition.highCode 0 0 c) with
  | true =>
    have hΓ0 : Γ = 0 := (SourceFixedPoint.zeroCheck_exact 0 _ hp.1).mp hz
    have hcs : interpretation 0 c < omegaSequence (finiteBase 0) 1 := by
      calc
        interpretation 0 c = Γ + ρ := hd.symm
        _ = ρ := by rw [hΓ0, zero_add]
        _ < omegaSequence (finiteBase 0) 1 := hlow
    have htcode := (SourceDecomposition.input_tree 0 c hc).1
    have hl : (ThetaCourse.rawTree c).outerSort ≤ 1 :=
      (denote_lt_iff_outerSort_le 0 _ htcode 1 (by omega)).mp
        ((SourceDecomposition.input_value 0 c hc) ▸ hcs)
    have hli : lowCheckCode 0 c = true := by
      obtain ⟨v, he, hvcheck⟩ := (checkCode_iff 0 c).mp hcc.1
      have hvl : v.outerSort ≤ 1 := by simpa only [← he, ThetaCourse.rawTree_code] using hl
      simpa only [← he, lowCheckCode_code, lowCheck, hvcheck, hvl, decide_true, Bool.true_and]
    have hpublic : unionCheck (Nat.pair 0 c) = true := by simpa only [unionCheck_pair] using hli
    have hcollapse := NativeContext.ElementaryPublicReturn.collapseCode_spec (alphaCode a)
      (Nat.pair 0 c) (alphaCode_baseCheck a ha) hpublic (by
        simpa only [unionInterpretation_pair, finiteBase_zero, root_omegaSequence_succ a 0 ha] using hcs)
    have hvalue : unionInterpretation (NativeContext.ElementaryPublicReturn.collapseCode (alphaCode a)
        (Nat.pair 0 c)) = NativeContext.denote (alphaCode a) (.theta 0 t) := by
      rw [hcollapse.2, unionInterpretation_pair, hv]
      rfl
    have hret := SourceZeta.Transport.returnCode_spec 0 _ hcollapse.1
      (hvalue.trans_lt (hb.trans (sourceAlphaPlus_lt_public_endpoint a ha)))
    have hacc : Theta.acceptedCode 0 (SourceZeta.Transport.returnCode 0
        (NativeContext.ElementaryPublicReturn.collapseCode (alphaCode a) (Nat.pair 0 c))) = true := by
      have hx := (Theta.acceptedLowCode_iff 0 _).mp hret.1
      exact (Theta.acceptedCode_iff 0 _).mpr
        ⟨(Bool.and_eq_true.mp (by simpa only [lowCheckCode_eq] using hx.1)).1, hx.2⟩
    simp only [zeroCode, hz, Bool.cond_true]
    exact ⟨hacc, hret.2.trans hvalue⟩
  | false =>
    have hΓne : Γ ≠ 0 := by
      intro he
      have htrue := (SourceFixedPoint.zeroCheck_exact 0 _ hp.1).mpr he
      simp only [hz, Bool.false_eq_true] at htrue
    have hΓ0 : 0 < Γ := pos_iff_ne_zero.mpr hΓne
    cases hbigger : Theta.Normalization.lessRawCode 0 a (nodeCode 0 (SourceDecomposition.highCode 0 0 c)) with
    | true =>
      have hgt := (Theta.Normalization.lessRawCode_correct 0 a _ (root_original a ha)
        ((Theta.acceptedCode_iff 0 _).mp hhead.1).1).mp hbigger
      have habove : α < globalCollapse (finiteBase 0) 0 Γ := by simpa only [hhead.2] using hgt
      have he := global_relative_tail_eq_of_source_head_above (finiteBase 0) α hqp hle hαlow
        Γ hΓn hΓs hΓd habove ρ hlow
      simp only [zeroCode, hz, Bool.cond_false, hbigger, Bool.cond_true]
      refine ⟨hnode.1, ?_⟩
      rw [hnode.2, ← hd, ← he, ← htarget]
    | false =>
      have hbelow : globalCollapse (finiteBase 0) 0 Γ ≤ α := by
        apply le_of_not_gt
        intro hgt
        have htrue := (Theta.Normalization.lessRawCode_correct 0 a _ (root_original a ha)
          ((Theta.acceptedCode_iff 0 _).mp hhead.1).1).mpr (by simpa only [hhead.2] using hgt)
        simp only [hbigger, Bool.false_eq_true] at htrue
      have hΓΔ := converted_highPart_lt_delta a c ha t ht hn hb hc hv
      have hAinput := Lambda.argument_accepted a ha
      obtain ⟨b, hecode, hbcheck, hbn, hhigh⟩ := (rootCheck_exact a).mp ha
      let A := interpretation 0 (Lambda.argumentCode a)
      have hA : GlobalNotation (finiteBase 0) 1 A := by
        simpa only [A, Lambda.argumentCode, OmegaQuotient.argumentCode, hecode,
          Localization.argumentCode_theta, interpretation_code] using
          SourceDecomposition.checked_all_levels 0 1 b (argument_checked 0 b hbcheck)
      have hAs : A < omegaSequence (finiteBase 0) 2 := by
        simpa only [A, Lambda.argumentCode, OmegaQuotient.argumentCode, hecode,
          Localization.argumentCode_theta, interpretation_code] using
          SourceFixedPoint.checked_theta_sort 0 0 b hbcheck
      have hrootvalue : α = globalCollapse (finiteBase 0) 0 A := by
        simp only [α, A, hecode, Lambda.argumentCode, OmegaQuotient.argumentCode,
          Localization.argumentCode_theta, interpretation_code]
        rfl
      have he := global_relative_tail_eq_of_source_head_below (finiteBase 0) hqp A
        (interpretation 0 (Lambda.deltaCode a))
        (interpretation 0 (SourceDecomposition.lowCode 0 0 (Lambda.argumentCode a))) Γ hA hAs
        (SourceDecomposition.highPart_dvd 0 0 (Lambda.argumentCode a) hAinput)
        (SourceDecomposition.lowPart_bound 0 0 (Lambda.argumentCode a) hAinput)
        (SourceDecomposition.parts_reconstruct 0 0 (Lambda.argumentCode a) hAinput).symm
        hΓn hΓd hΓ0 hΓΔ (by simpa only [← hrootvalue] using hbelow) ρ hlow
      have hsum1 := Addition.normalizedSumCode_checked 0 a (SourceDecomposition.lowCode 0 0 c)
        (root_original a ha) hpl.1
      have hsum2 := Addition.normalizedSumCode_checked 0 (SourceDecomposition.highCode 0 0 c)
        (Addition.normalizedSumCode 0 a (SourceDecomposition.lowCode 0 0 c)) hpc.1
        ((Theta.acceptedCode_iff 0 _).mp hsum1.1).1
      have hshiftvalue : interpretation 0 (shiftedArgument a c) = Γ + (α + ρ) :=
        hsum2.2.trans (by rw [hsum1.2])
      have htail : α + ρ < omegaSequence (finiteBase 0) 1 :=
        (omegaSequence_add_closed (finiteBase 0) 0) hαlow hlow
      have hshiftsort : interpretation 0 (shiftedArgument a c) < omegaSequence (finiteBase 0) 2 := by
        rw [hshiftvalue]
        exact (omegaSequence_add_closed (finiteBase 0) 1) hΓs
          (htail.trans ((omegaSequence_strictMono (finiteBase 0)) (by omega : 1 < 2)))
      have hshift := nodeCode_spec 0 (shiftedArgument a c) hsum2.1 hshiftsort
      simp only [zeroCode, hz, Bool.cond_false, hbigger]
      refine ⟨hshift.1, ?_⟩
      rw [hshift.2, hshiftvalue]
      have he' : globalCollapse (finiteBase 0) 0 (Γ + (α + ρ)) =
          globalCollapse α 0 (Γ + ρ) := by simpa only [← hrootvalue] using he.symm
      exact he'.trans htarget.symm

theorem zeroCode_primrec : Primrec₂ zeroCode := by
  have ha := Primrec.fst
  have hc := Primrec.snd
  have hg := SourceDecomposition.highCode_primrec.comp
    ((Primrec.const 0).pair ((Primrec.const 0).pair hc))
  have hl := SourceDecomposition.lowCode_primrec.comp
    ((Primrec.const 0).pair ((Primrec.const 0).pair hc))
  have hsum1 := Addition.normalizedSumCode_primrec.comp ((Primrec.const 0).pair (ha.pair hl))
  have hsum2 := Addition.normalizedSumCode_primrec.comp ((Primrec.const 0).pair (hg.pair hsum1))
  exact ((SourceFixedPoint.zeroCheck_primrec.comp (Primrec.const 0) hg).cond
    (SourceZeta.Transport.returnCode_primrec.comp (Primrec.const 0)
      (NativeContext.ElementaryPublicReturn.collapseCode_primrec.comp (alphaCode_primrec.comp ha)
        (Primrec₂.natPair.comp (Primrec.const 0) hc)))
    ((Theta.Normalization.Effective.lessRawCode_primrec.comp
      ((Primrec.const 0).pair (ha.pair (nodeCode_primrec.comp (Primrec.const 0) hg)))).cond
      (nodeCode_primrec.comp (Primrec.const 0) hc)
      (nodeCode_primrec.comp (Primrec.const 0) hsum2))).to₂

def thetaCode (a k c : Nat) : Nat := cond (k == 0) (zeroCode a c) (nodeCode k c)

theorem thetaCode_primrec : Primrec
    (fun p : Nat × (Nat × Nat) => thetaCode p.1 p.2.1 p.2.2) := by
  have ha := Primrec.fst
  have hk := Primrec.fst.comp Primrec.snd
  have hc := Primrec.snd.comp Primrec.snd
  exact (Primrec.beq.comp hk (Primrec.const 0)).cond
    (zeroCode_primrec.comp ha hc) (nodeCode_primrec.comp hk hc)

def parameterState (a p : Nat) : Nat × Nat := (a, Inverse.atomCode p)

def sumState (x y : Nat × Nat) : Nat × Nat :=
  (x.1, Addition.normalizedSumCode 0 x.2 y.2)

def thetaState (a k : Nat) (x : Nat × Nat) : Nat × Nat := (a, thetaCode a k x.2)

def stateTerm (a : Nat) (t : RelativeTerm Nat) : Nat × Nat :=
  ValueFold.term parameterState sumState thetaState a t

def sourceTermCode (a : Nat) (t : RelativeTerm Nat) : Nat := (stateTerm a t).2

theorem stateTerm_context (a : Nat) (t : RelativeTerm Nat) : (stateTerm a t).1 = a := by
  induction t with
  | parameter p => rfl
  | sum t u iht ihu => exact iht
  | theta k t ih => rfl

theorem sourceTermCode_parameter (a p : Nat) :
    sourceTermCode a (.parameter p) = Inverse.atomCode p := rfl

theorem sourceTermCode_sum (a : Nat) (t u : RelativeTerm Nat) :
    sourceTermCode a (.sum t u) = Addition.normalizedSumCode 0
      (sourceTermCode a t) (sourceTermCode a u) := rfl

theorem sourceTermCode_theta (a k : Nat) (t : RelativeTerm Nat) :
    sourceTermCode a (.theta k t) = thetaCode a k (sourceTermCode a t) := rfl

theorem stateTerm_primrec : Primrec₂ stateTerm := by
  have hp : Primrec₂ parameterState :=
    (Primrec.fst.pair (Inverse.atomCode_primrec.comp Primrec.snd)).to₂
  have hadd : Primrec₂ sumState := by
    have ha := Primrec.fst.comp Primrec.fst
    have hc := Primrec.snd.comp Primrec.fst
    have hd := Primrec.snd.comp Primrec.snd
    exact (ha.pair (Addition.normalizedSumCode_primrec.comp
      ((Primrec.const 0).pair (hc.pair hd)))).to₂
  have hθ : Primrec (fun p : Nat × (Nat × (Nat × Nat)) => thetaState p.1 p.2.1 p.2.2) := by
    have ha := Primrec.fst
    have hk := Primrec.fst.comp Primrec.snd
    have hc := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
    exact ha.pair (thetaCode_primrec.comp (ha.pair (hk.pair hc)))
  exact ValueFold.term_primrec parameterState sumState thetaState (0, 0) hp hadd hθ

theorem sourceTermCode_primrec : Primrec₂ sourceTermCode := (Primrec.snd.comp stateTerm_primrec).to₂

theorem sourceTermCode_spec (a : Nat) (ha : rootCheck a = true)
    (t : RelativeTerm Nat) (ht : NativeContext.check (alphaCode a) t = true)
    (hn : NativeContext.Comparison.Normal (alphaCode a) t)
    (hb : ∀ u ∈ fullList t, NativeContext.denote (alphaCode a) u < Enclosure.sourceAlphaPlus a) :
    Theta.acceptedCode 0 (sourceTermCode a t) = true ∧
      interpretation 0 (sourceTermCode a t) = NativeContext.denote (alphaCode a) t := by
  revert ht hn hb
  induction t with
  | parameter p =>
    intro ht hn hb
    have hp := (NativeContext.parameterCheck_exact _ p).mp (NativeContext.checked_admissible _ _ ht).1
    have hv := Canonical.canonicalize_value p hp.1
    have hsmall : NativeContext.parameters p < interpretation 0 a := by
      simpa only [alpha_base a ha] using hp.2.2
    have hbound : unionInterpretation (Canonical.canonicalize p) < finiteBase (0 + 1) := by
      rw [hv]
      exact hsmall.trans ((lt_nextBase_iff_code 0 _).mpr ⟨a, root_low a ha, rfl⟩)
    have hs := SourceZeta.Transport.returnCode_spec 0 (Canonical.canonicalize p)
      (Canonical.canonicalize_check p hp.1) hbound
    have hx := (Theta.acceptedLowCode_iff 0 _).mp hs.1
    have hacc := (Theta.acceptedCode_iff 0 _).mpr
      ⟨(Bool.and_eq_true.mp (by simpa only [lowCheckCode_eq] using hx.1)).1, hx.2⟩
    rw [sourceTermCode_parameter]
    exact ⟨hacc, hs.2.trans hv⟩
  | sum t u iht ihu =>
    intro ht hn hb
    have hc := NativeContext.BaseTransformation.sum_checks _ t u ht
    have hbt : ∀ v ∈ fullList t, NativeContext.denote (alphaCode a) v < Enclosure.sourceAlphaPlus a := by
      intro v hv; exact hb v (List.mem_append.mpr (Or.inl hv))
    have hbu : ∀ v ∈ fullList u, NativeContext.denote (alphaCode a) v < Enclosure.sourceAlphaPlus a := by
      intro v hv; exact hb v (List.mem_append.mpr (Or.inr hv))
    have hst := iht hc.1 hn.1 hbt
    have hsu := ihu hc.2 hn.2.1 hbu
    rw [sourceTermCode_sum]
    have hs := Addition.normalizedSumCode_checked 0 _ _
      ((Theta.acceptedCode_iff 0 _).mp hst.1).1 ((Theta.acceptedCode_iff 0 _).mp hsu.1).1
    exact ⟨hs.1, hs.2.trans (by rw [hst.2, hsu.2]; rfl)⟩
  | theta k t ih =>
    intro ht hn hb
    have hc := NativeContext.BaseTransformation.theta_argument_check _ k t ht
    have hbt : ∀ u ∈ fullList t, NativeContext.denote (alphaCode a) u < Enclosure.sourceAlphaPlus a := by
      intro u hu
      cases k with
      | zero => exact hb u (RelativeTerm.PrincipalSupport.principalList_nested 0 t u hu)
      | succ k => exact hb u (by simpa only [fullList,
          RelativeTerm.PrincipalSupport.principalList_theta_higher 0 (k + 1) t (Nat.succ_pos k)] using hu)
    have hs := ih hc hn hbt
    rw [sourceTermCode_theta]
    cases k with
    | zero =>
      simp only [thetaCode, beq_self_eq_true, Bool.cond_true]
      exact zeroCode_spec a _ ha t ht hn
        (hb (.theta 0 t) (RelativeTerm.PrincipalSupport.principalList_root 0 t)) hs.1 hs.2
    | succ k =>
      have hk0 : (k + 1 == 0) = false := by simp
      simp only [thetaCode, hk0, Bool.cond_false]
      have hsort : interpretation 0 (sourceTermCode a t) < omegaSequence (finiteBase 0) (k + 1 + 2) := by
        rw [hs.2]
        simpa only [finiteBase_zero, root_omegaSequence_succ a (k + 2) ha] using
          NativeContext.FixedPoint.checked_theta_sort _ (k + 1) t ht
      have hnode := nodeCode_spec (k + 1) _ hs.1 hsort
      refine ⟨hnode.1, ?_⟩
      have htarg := SourceDecomposition.input_tree 0 _ hs.1
      have hsourcecheck := OmegaQuotient.theta_checked (k + 1) _ htarg.1
        ((denote_lt_iff_outerSort_le 0 _ htarg.1 (k + 1 + 2) (by omega)).mp
          ((SourceDecomposition.input_value 0 _ hs.1) ▸ hsort))
      have hv : NativeContext.denote (alphaCode a) t = denote 0 (ThetaCourse.rawTree (sourceTermCode a t)) :=
        hs.2.symm.trans (SourceDecomposition.input_value 0 _ hs.1)
      have he := root_positive_theta_value a (k + 1) ha _ t (Nat.succ_pos k) hsourcecheck ht hv
      simpa only [nodeCode, interpretation_code] using he.symm

theorem sourceTermCode_low_spec (a : Nat) (ha : rootCheck a = true)
    (t : RelativeTerm Nat) (ht : NativeContext.check (alphaCode a) t = true)
    (hn : NativeContext.Comparison.Normal (alphaCode a) t) (hl : t.outerSort ≤ 1)
    (hb : NativeContext.denote (alphaCode a) t < Enclosure.sourceAlphaPlus a) :
    Theta.acceptedLowCode 0 (sourceTermCode a t) = true ∧
      interpretation 0 (sourceTermCode a t) = NativeContext.denote (alphaCode a) t := by
  have hs := sourceTermCode_spec a ha t ht hn (low_zero_calls_bounded a ha t ht hn hl hb)
  have hct := SourceDecomposition.input_tree 0 _ hs.1
  have hlow : (ThetaCourse.rawTree (sourceTermCode a t)).outerSort ≤ 1 := by
    apply (denote_lt_iff_outerSort_le 0 _ hct.1 1 (by omega)).mp
    rw [← SourceDecomposition.input_value 0 _ hs.1, hs.2, finiteBase_zero, root_omegaSequence_succ a 0 ha]
    exact (NativeContext.denote_lt_iff_outerSort_le _ _ ht 1 (by omega)).mpr hl
  refine ⟨(Theta.acceptedLowCode_iff 0 _).mpr ⟨?_, hct.2⟩, hs.2⟩
  obtain ⟨u, he, hu⟩ := (checkCode_iff 0 _).mp ((Theta.acceptedCode_iff 0 _).mp hs.1).1
  have hul : u.outerSort ≤ 1 := by simpa only [← he, ThetaCourse.rawTree_code] using hlow
  simp only [← he, lowCheckCode_code, lowCheck, hu, hul, decide_true, Bool.true_and]

def publicTerm (a : Nat) (t : RelativeTerm Nat) : Nat :=
  Canonical.canonicalize (Nat.pair 0 (sourceTermCode a t))

theorem publicTerm_primrec : Primrec₂ publicTerm :=
  (Canonical.Effective.canonicalize_primrec.comp
    (Primrec₂.natPair.comp (Primrec.const 0) sourceTermCode_primrec)).to₂

theorem publicTerm_spec (a : Nat) (ha : rootCheck a = true)
    (t : RelativeTerm Nat) (ht : NativeContext.check (alphaCode a) t = true)
    (hn : NativeContext.Comparison.Normal (alphaCode a) t) (hl : t.outerSort ≤ 1)
    (hb : NativeContext.denote (alphaCode a) t < Enclosure.sourceAlphaPlus a) :
    Canonical.check (publicTerm a t) = true ∧
      unionInterpretation (publicTerm a t) = NativeContext.denote (alphaCode a) t := by
  have hs := sourceTermCode_low_spec a ha t ht hn hl hb
  have hp : unionCheck (Nat.pair 0 (sourceTermCode a t)) = true := by
    simpa only [unionCheck_pair] using ((Theta.acceptedLowCode_iff 0 _).mp hs.1).1
  exact ⟨Canonical.canonicalize_check _ hp, (Canonical.canonicalize_value _ hp).trans
    (by simpa only [unionInterpretation_pair] using hs.2)⟩

def rawPublicCode (a c : Nat) : Nat := publicTerm a
  (NativeContext.Normalization.normalize (alphaCode a) (ThetaCourse.rawTree c))

theorem rawPublicCode_primrec : Primrec₂ rawPublicCode := by
  exact (publicTerm_primrec.comp Primrec.fst
    (NativeContext.Normalization.Effective.normalize_primrec.comp (alphaCode_primrec.comp Primrec.fst)
      (ThetaCourse.rawTree_primrec.comp Primrec.snd))).to₂

theorem rawPublicCode_spec (a c : Nat) (ha : rootCheck a = true)
    (hc : NativeContext.lowCheckCode (alphaCode a) c = true)
    (hb : NativeContext.interpretation (alphaCode a) c < Enclosure.sourceAlphaPlus a) :
    Canonical.check (rawPublicCode a c) = true ∧
      unionInterpretation (rawPublicCode a c) = NativeContext.interpretation (alphaCode a) c := by
  obtain ⟨t, he, ht⟩ := (NativeContext.lowCheckCode_exact _ c).mp hc
  have hparts := Bool.and_eq_true.mp ht
  have hl : t.outerSort ≤ 1 := of_decide_eq_true hparts.2
  have hn := NativeContext.Normalization.normalize_checked (alphaCode a) t hparts.1
  have hnl : (NativeContext.Normalization.normalize (alphaCode a) t).outerSort ≤ 1 := by
    apply (NativeContext.denote_lt_iff_outerSort_le _ _ hn.1 1 (by omega)).mp
    rw [hn.2.2]
    exact (NativeContext.denote_lt_iff_outerSort_le _ _ hparts.1 1 (by omega)).mpr hl
  have hbound : NativeContext.denote (alphaCode a) (NativeContext.Normalization.normalize (alphaCode a) t) <
      Enclosure.sourceAlphaPlus a := by
    rw [hn.2.2]
    simpa only [← he, NativeContext.interpretation_code] using hb
  have hs := publicTerm_spec a ha _ hn.1 hn.2.1 hnl hbound
  simpa only [rawPublicCode, ← he, ThetaCourse.rawTree_code, NativeContext.interpretation_code, hn.2.2] using hs

theorem rawPublicCode_value_invariant (a c d : Nat) (ha : rootCheck a = true)
    (hc : NativeContext.lowCheckCode (alphaCode a) c = true)
    (hd : NativeContext.lowCheckCode (alphaCode a) d = true)
    (hb : NativeContext.interpretation (alphaCode a) c < Enclosure.sourceAlphaPlus a)
    (he : NativeContext.interpretation (alphaCode a) c = NativeContext.interpretation (alphaCode a) d) :
    rawPublicCode a c = rawPublicCode a d := by
  have hs := rawPublicCode_spec a c ha hc hb
  have hs' := rawPublicCode_spec a d ha hd (he ▸ hb)
  exact Canonical.check_value_injective _ _ hs.1 hs'.1 (hs.2.trans (he.trans hs'.2.symm))

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.BoundedPublicReturn
