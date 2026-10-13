import Alexander313.Wilken.HereditaryNativeBoundedContextLambdaTranslation
import Alexander313.Wilken.HereditaryNativeBoundedContextLambdaLowTranslation

/-!
# Both actual intermediate lambda branches and full positive-source transport

The guard is the ORIGINAL proper Normal theta-zero root in the actual
alpha context, below ORIGINAL source alpha-plus. Properness is recognized
by the genuine nonzero argument test. The real high-root test is equivalent
to the root being epsilon. The actual high lambda producer and direct low
zeta producer therefore execute the two cases of Definition 2.45.

The original-source caller is constructed separately in each actual branch.
The proved high-tail transport and exact low-root logarithm identity give
the full positive-source normal execution assertion of Lemma 2.48(d).
No root, translation, STRICT or equality oracle occurs. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.BoundedContextIota.Lambda.Branches

open NativePublicBridge (contextCode)

def inputCheck (s a c : Nat) : Bool :=
  (BoundedPublicReturn.inputCheck s a c && DirectZeta.inputCheck (sourceCode s a) c) &&
    !FixedPoint.zeroCheck (Localization.argumentCode c)

theorem inputCheck_primrec : Primrec
    (fun p : Context => inputCheck p.1.1 p.1.2 p.2) := by
  have hq := sourceCode_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)
  have hd := DirectZeta.inputCheck_primrec.comp hq Primrec.snd
  have hn := Primrec.not.comp (FixedPoint.zeroCheck_primrec.comp
    (Localization.argumentCode_primrec.comp Primrec.snd))
  exact Primrec.and.comp (Primrec.and.comp BoundedPublicReturn.inputCheck_primrec hd) hn

theorem inputCheck_exact (s a c : Nat) : inputCheck s a c = true ↔
    Iota.rootCheck s a = true ∧ DirectZeta.inputCheck (sourceCode s a) c = true ∧
      base (sourceCode s a) < interpretation (sourceCode s a) c ∧
      interpretation (sourceCode s a) c < Iota.AlphaPlus.sourceValue s a := by
  constructor
  · intro h
    obtain ⟨hc, hz⟩ := Bool.and_eq_true.mp h
    obtain ⟨hb, hd⟩ := Bool.and_eq_true.mp hc
    have hs := (BoundedPublicReturn.inputCheck_exact s a c).mp hb
    obtain ⟨t, he, ht, hn⟩ := (DirectZeta.inputCheck_exact _ c).mp hd
    have hi := DirectZeta.argument_input _ c hd
    have hnz : denote (sourceCode s a) t ≠ 0 := by
      intro hv
      have htrue := (FixedPoint.zeroCheck_exact _ _ hi).mpr (by
        simpa only [DirectZeta.argumentCode, he, Localization.argumentCode_theta,
          interpretation_code] using hv)
      have hfalse : FixedPoint.zeroCheck (Localization.argumentCode c) = false :=
        by simpa only [Bool.not_eq_true'] using hz
      simp only [DirectZeta.argumentCode, hfalse, Bool.false_eq_true] at htrue
    exact ⟨hs.1, hd, by simpa only [he, interpretation_code] using
      (SourceChi.Arithmetic.proper_theta_zero_iff _ t ht hn).mpr hnz, hs.2.2⟩
  · rintro ⟨ha, hd, hp, hb⟩
    obtain ⟨t, he, ht, hn⟩ := (DirectZeta.inputCheck_exact _ c).mp hd
    have hl : lowCheckCode (sourceCode s a) c = true := by
      simp only [he, lowCheckCode_code, lowCheck, ht, RelativeTerm.outerSort,
        decide_true, Bool.true_and]
    have hbound := (BoundedPublicReturn.inputCheck_exact s a c).mpr ⟨ha, hl, hb⟩
    have hi := DirectZeta.argument_input _ c hd
    have hnz := (SourceChi.Arithmetic.proper_theta_zero_iff _ t ht hn).mp
      (by simpa only [he, interpretation_code] using hp)
    refine Bool.and_eq_true.mpr ⟨Bool.and_eq_true.mpr ⟨hbound, hd⟩, ?_⟩
    cases hz : FixedPoint.zeroCheck (Localization.argumentCode c) with
    | false => rfl
    | true =>
      exact False.elim (hnz (by simpa only [DirectZeta.argumentCode, he,
        Localization.argumentCode_theta, interpretation_code] using
          (FixedPoint.zeroCheck_exact _ _ hi).mp hz))

theorem high_input (s a c : Nat) (hc : BoundedContextIota.rootCheck s a c = true) :
    inputCheck s a c = true := by
  have hs := (BoundedContextIota.rootCheck_exact s a c).mp hc
  apply (inputCheck_exact s a c).mpr
  obtain ⟨t, he, ht, hn, hh⟩ := hs.2.1
  exact ⟨hs.1, (DirectZeta.inputCheck_exact _ _).mpr ⟨t, he, ht, hn⟩,
    BoundedContextIota.Mu.root_base_lt s a c hc, hs.2.2⟩

/-- The zero-argument base exception is excluded by ORIGINAL properness. -/
theorem high_iff_epsilon (s a c : Nat) (hc : inputCheck s a c = true) :
    BoundedContextIota.rootCheck s a c = true ↔
      Ordinal.omega0 ^ interpretation (sourceCode s a) c = interpretation (sourceCode s a) c := by
  have hs := (inputCheck_exact s a c).mp hc
  constructor
  · exact BoundedContextIota.root_epsilon s a c
  · intro hε
    obtain ⟨t, he, ht, hn⟩ := (DirectZeta.inputCheck_exact _ c).mp hs.2.1
    have heps : Ordinal.omega0 ^ denote (sourceCode s a) (.theta 0 t) =
        denote (sourceCode s a) (.theta 0 t) := by simpa only [he, interpretation_code] using hε
    have hh : omegaSequence (base (sourceCode s a)) 1 ≤ denote (sourceCode s a) t := by
      rcases (OmegaPowers.theta_epsilon_iff _ t ht).mp heps with hz | hh
      · exact False.elim ((ne_of_gt (by simpa only [he, interpretation_code] using hs.2.2.1)) hz)
      · exact hh
    have hsort : 1 < t.outerSort := by
      apply lt_of_not_ge
      intro hl
      exact hh.not_gt ((denote_lt_iff_outerSort_le _ t
        (BaseTransformation.theta_argument_check _ 0 t ht) 1 (by omega)).mpr hl)
    exact (BoundedContextIota.rootCheck_exact s a c).mpr ⟨hs.1, ⟨t, he, ht, hn, hsort⟩, hs.2.2.2⟩

def outputContext (s a c : Nat) : Nat := cond (BoundedContextIota.rootCheck s a c)
  (betaCode s a c) (sourceCode s a)

theorem outputContext_primrec : Primrec
    (fun p : Context => outputContext p.1.1 p.1.2 p.2) :=
  BoundedContextIota.rootCheck_primrec.cond betaCode_primrec
    (sourceCode_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst))

theorem outputContext_checked (s a c : Nat) (hc : inputCheck s a c = true) :
    baseCheck (outputContext s a c) = true := by
  cases hh : BoundedContextIota.rootCheck s a c with
  | true => simpa only [outputContext, hh, Bool.cond_true] using betaCode_baseCheck s a c hh
  | false =>
    simpa only [outputContext, hh, Bool.cond_false, sourceCode] using
      Iota.alphaCode_baseCheck s a ((inputCheck_exact s a c).mp hc).1

noncomputable def sourceValue (s a c : Nat) : Ordinal.{0} :=
  if BoundedContextIota.rootCheck s a c = true then BoundedContextIota.Lambda.sourceValue s a c
  else DirectZeta.sourceValue (sourceCode s a) c

theorem source_definition_2_45 (s a c : Nat) (hc : inputCheck s a c = true) :
    sourceValue s a c =
      if Ordinal.omega0 ^ interpretation (sourceCode s a) c = interpretation (sourceCode s a) c then
        interpretation (betaCode s a c) (literalDelta s a c) + DirectZeta.sourceValue (sourceCode s a) c
      else DirectZeta.sourceValue (sourceCode s a) c := by
  rw [← high_iff_epsilon s a c hc]
  rfl

def returnedRoot (s a c : Nat) : Nat := cond (BoundedContextIota.rootCheck s a c)
  (SourceReturn.returnedRoot s a c) (LowTranslation.returnedCode s a c)

theorem returnedRoot_primrec : Primrec
    (fun p : Context => returnedRoot p.1.1 p.1.2 p.2) :=
  BoundedContextIota.rootCheck_primrec.cond SourceReturn.returnedRoot_primrec
    (LowTranslation.returnedCode_primrec.comp Primrec.fst Primrec.snd)

theorem returnedRoot_spec (s a c : Nat) (hc : inputCheck s a c = true) :
    NativeContext.Lambda.Branches.inputCheck s (returnedRoot s a c) = true ∧
      interpretation (contextCode s) (returnedRoot s a c) = interpretation (sourceCode s a) c := by
  have hs := (inputCheck_exact s a c).mp hc
  cases hh : BoundedContextIota.rootCheck s a c with
  | true =>
    simpa only [returnedRoot, hh, Bool.cond_true] using
      And.intro (NativeContext.Lambda.Branches.high_input s _
        (SourceReturn.returnedRoot_iota_caller s a c hh)) (SourceReturn.returnedRoot_spec s a c hh).2.2
  | false =>
    simpa only [returnedRoot, hh, Bool.cond_false] using
      LowTranslation.returnedCode_spec s a c hs.1 hs.2.1 hs.2.2.1 hs.2.2.2

def execute (s a c : Nat) : Part Nat := cond (inputCheck s a c)
  (cond (BoundedContextIota.rootCheck s a c) (BoundedContextIota.Lambda.execute s a c)
    (DirectZeta.execute (sourceCode s a) c)) Part.none

theorem execute_partrec : Partrec (fun p : Context => execute p.1.1 p.1.2 p.2) := by
  have hq := sourceCode_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)
  exact Partrec.cond inputCheck_primrec.to_comp
    (Partrec.cond BoundedContextIota.rootCheck_primrec.to_comp BoundedContextIota.Lambda.execute_partrec
      (DirectZeta.execute_partrec.comp hq.to_comp Primrec.snd.to_comp)) Partrec.none

theorem execute_domain (s a c : Nat) : (execute s a c).Dom ↔ inputCheck s a c = true := by
  cases hc : inputCheck s a c with
  | false => simp only [execute, hc, Bool.cond_false, Part.not_none_dom, Bool.false_eq_true]
  | true =>
    cases hh : BoundedContextIota.rootCheck s a c with
    | true => simp only [execute, hc, hh, Bool.cond_true,
        BoundedContextIota.Lambda.execute_domain, BoundedContextIota.Lambda.inputCheck, hh]
    | false =>
      have hd := ((inputCheck_exact s a c).mp hc).2.1
      simp only [execute, hc, hh, Bool.cond_true, Bool.cond_false, DirectZeta.execute_domain, hd]

theorem execute_returns (s a c : Nat) (hc : inputCheck s a c = true) :
    ∃ out, out ∈ execute s a c := Part.dom_iff_mem.mp ((execute_domain s a c).mpr hc)

theorem execute_spec (s a c out : Nat) (ho : out ∈ execute s a c) :
    inputCheck s a c = true ∧ lowCheckCode (outputContext s a c) out = true ∧
      Comparison.acceptedCode (outputContext s a c) out = true ∧
      interpretation (outputContext s a c) out = sourceValue s a c := by
  have hc := (execute_domain s a c).mp (Part.dom_iff_mem.mpr ⟨out, ho⟩)
  cases hh : BoundedContextIota.rootCheck s a c with
  | true =>
    have hm : out ∈ BoundedContextIota.Lambda.execute s a c := by
      simpa only [execute, hc, hh, Bool.cond_true] using ho
    have hs := BoundedContextIota.Lambda.execute_spec s a c out hm
    refine ⟨hc, ?_⟩
    simpa only [outputContext, sourceValue, hh, Bool.cond_true, if_pos rfl] using hs.2
  | false =>
    have hm : out ∈ DirectZeta.execute (sourceCode s a) c := by
      simpa only [execute, hc, hh, Bool.cond_true, Bool.cond_false] using ho
    have hs := DirectZeta.execute_spec _ c out hm
    refine ⟨hc, ?_⟩
    simpa only [outputContext, sourceValue, hh, Bool.cond_false, Bool.false_eq_true, if_false] using hs.2

/-- Full positive-source normal execution transport: both epsilon and
non-epsilon proper roots in the ORIGINAL interval are included. -/
theorem execute_translation (s a c out : Nat) (ho : out ∈ execute s a c) :
    ∃ other, other ∈ NativeContext.Lambda.Branches.execute s (returnedRoot s a c) ∧
      interpretation (NativeContext.Lambda.Branches.outputContext s (returnedRoot s a c)) other =
        interpretation (outputContext s a c) out := by
  have hc := (execute_domain s a c).mp (Part.dom_iff_mem.mpr ⟨out, ho⟩)
  cases hh : BoundedContextIota.rootCheck s a c with
  | true =>
    have hm : out ∈ BoundedContextIota.Lambda.execute s a c := by
      simpa only [execute, hc, hh, Bool.cond_true] using ho
    obtain ⟨other, hold, hbase, hv⟩ := Translation.execute_translation s a c out hm
    have hroot := SourceReturn.returnedRoot_iota_caller s a c hh
    have hb := NativeContext.Lambda.Branches.high_input s _ hroot
    refine ⟨other, ?_, ?_⟩
    · simpa only [returnedRoot, hh, Bool.cond_true, NativeContext.Lambda.Branches.execute,
        hb, hroot] using hold
    · simpa only [returnedRoot, outputContext, hh, Bool.cond_true,
        NativeContext.Lambda.Branches.outputContext, hroot, hbase] using hv
  | false =>
    have hm : out ∈ DirectZeta.execute (sourceCode s a) c := by
      simpa only [execute, hc, hh, Bool.cond_true, Bool.cond_false] using ho
    have hs := (inputCheck_exact s a c).mp hc
    have hε : Ordinal.omega0 ^ interpretation (sourceCode s a) c ≠ interpretation (sourceCode s a) c := by
      intro he
      have ht := (high_iff_epsilon s a c hc).mpr he
      simp only [hh, Bool.false_eq_true] at ht
    obtain ⟨other, hold, hbase, hv⟩ := LowTranslation.execute_translation s a c out hs.1 hm
      hs.2.2.1 hs.2.2.2 hε
    refine ⟨other, by simpa only [returnedRoot, hh, Bool.cond_false] using hold, ?_⟩
    simpa only [returnedRoot, outputContext, hh, Bool.cond_false, hbase] using hv

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.BoundedContextIota.Lambda.Branches
