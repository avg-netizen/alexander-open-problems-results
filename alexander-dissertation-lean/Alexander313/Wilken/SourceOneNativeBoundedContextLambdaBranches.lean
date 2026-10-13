import Alexander313.Wilken.SourceOneNativeBoundedContextLambdaTranslation
import Alexander313.Wilken.SourceOneNativeBoundedContextLambdaLowTranslation

/-!
# Both genuine intermediate lambda branches over the original source one

The original admitted Normal proper theta-zero root lies strictly between
the actual alpha and ORIGINAL source-one alpha-plus endpoint. The genuine
high-root test is exactly epsilon status. The actual intermediate high
lambda and real direct zeta execute Definition2.45 in their respective
true contexts. Each branch constructs its ORIGINAL source-zero caller;
the proved high and low identities give full normal source-one outer
Lemma2.48(d). No Native base-one parser or transport oracle. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.BoundedContextLambda.Branches

def highCheck (a c : Nat) : Bool := NativeContext.PublicEpsilonIota.rootCheck (alphaCode a) c

theorem highCheck_primrec : Primrec₂ highCheck :=
  (NativeContext.PublicEpsilonIota.rootCheck_primrec.comp (alphaCode_primrec.comp Primrec.fst) Primrec.snd).to₂

def inputCheck (a c : Nat) : Bool :=
  (BoundedPublicReturn.inputCheck a c && NativeContext.DirectZeta.inputCheck (alphaCode a) c) &&
    !NativeContext.FixedPoint.zeroCheck (Localization.argumentCode c)

theorem inputCheck_primrec : Primrec₂ inputCheck :=
  (Primrec.and.comp
    (Primrec.and.comp BoundedPublicReturn.inputCheck_primrec
      (NativeContext.DirectZeta.inputCheck_primrec.comp (alphaCode_primrec.comp Primrec.fst) Primrec.snd))
    (Primrec.not.comp (NativeContext.FixedPoint.zeroCheck_primrec.comp
      (Localization.argumentCode_primrec.comp Primrec.snd)))).to₂

theorem inputCheck_exact (a c : Nat) : inputCheck a c = true ↔
    SourceOneIota.rootCheck a = true ∧ NativeContext.DirectZeta.inputCheck (alphaCode a) c = true ∧
      NativeContext.base (alphaCode a) < NativeContext.interpretation (alphaCode a) c ∧
      NativeContext.interpretation (alphaCode a) c < Enclosure.sourceAlphaPlus a := by
  constructor
  · intro h
    obtain ⟨hc, hz⟩ := Bool.and_eq_true.mp h
    obtain ⟨hb, hd⟩ := Bool.and_eq_true.mp hc
    have hs := (BoundedPublicReturn.inputCheck_exact a c).mp hb
    obtain ⟨t, he, ht, hn⟩ := (NativeContext.DirectZeta.inputCheck_exact _ c).mp hd
    have hi := NativeContext.DirectZeta.argument_input _ c hd
    have hnz : NativeContext.denote (alphaCode a) t ≠ 0 := by
      intro hv
      have htrue := (NativeContext.FixedPoint.zeroCheck_exact _ _ hi).mpr (by
        simpa only [NativeContext.DirectZeta.argumentCode, he, Localization.argumentCode_theta,
          NativeContext.interpretation_code] using hv)
      have hfalse : NativeContext.FixedPoint.zeroCheck (Localization.argumentCode c) = false :=
        by simpa only [Bool.not_eq_true'] using hz
      simp only [NativeContext.DirectZeta.argumentCode, hfalse, Bool.false_eq_true] at htrue
    exact ⟨hs.1, hd, by simpa only [he, NativeContext.interpretation_code] using
      (NativeContext.SourceChi.Arithmetic.proper_theta_zero_iff _ t ht hn).mpr hnz, hs.2.2⟩
  · rintro ⟨ha, hd, hp, hb⟩
    obtain ⟨t, he, ht, hn⟩ := (NativeContext.DirectZeta.inputCheck_exact _ c).mp hd
    have hl : NativeContext.lowCheckCode (alphaCode a) c = true := by
      simp only [he, NativeContext.lowCheckCode_code, NativeContext.lowCheck, ht,
        RelativeTerm.outerSort, decide_true, Bool.true_and]
    have hbound := (BoundedPublicReturn.inputCheck_exact a c).mpr ⟨ha, hl, hb⟩
    have hi := NativeContext.DirectZeta.argument_input _ c hd
    have hnz := (NativeContext.SourceChi.Arithmetic.proper_theta_zero_iff _ t ht hn).mp
      (by simpa only [he, NativeContext.interpretation_code] using hp)
    refine Bool.and_eq_true.mpr ⟨Bool.and_eq_true.mpr ⟨hbound, hd⟩, ?_⟩
    cases hz : NativeContext.FixedPoint.zeroCheck (Localization.argumentCode c) with
    | false => rfl
    | true => exact False.elim (hnz (by simpa only [NativeContext.DirectZeta.argumentCode, he,
        Localization.argumentCode_theta, NativeContext.interpretation_code] using
          (NativeContext.FixedPoint.zeroCheck_exact _ _ hi).mp hz))

theorem high_input (a c : Nat) (ha : SourceOneIota.rootCheck a = true)
    (hc : highCheck a c = true) : inputCheck a c = true := by
  obtain ⟨_, ⟨t, he, ht, hn, hh⟩, hb⟩ :=
    (NativeContext.PublicEpsilonIota.rootCheck_exact _ _).mp hc
  exact (inputCheck_exact a c).mpr ⟨ha,
    (NativeContext.DirectZeta.inputCheck_exact _ _).mpr ⟨t, he, ht, hn⟩,
    NativeContext.PublicEpsilonIota.root_base_lt _ _ hc,
    BoundedContextReturn.intermediate_bound a c ha hc⟩

theorem high_iff_epsilon (a c : Nat) (hc : inputCheck a c = true) : highCheck a c = true ↔
    Ordinal.omega0 ^ NativeContext.interpretation (alphaCode a) c = NativeContext.interpretation (alphaCode a) c := by
  have hs := (inputCheck_exact a c).mp hc
  constructor
  · exact NativeContext.PublicEpsilonIota.root_epsilon _ c
  · intro hε
    obtain ⟨t, he, ht, hn⟩ := (NativeContext.DirectZeta.inputCheck_exact _ c).mp hs.2.1
    have heps : Ordinal.omega0 ^ NativeContext.denote (alphaCode a) (.theta 0 t) =
        NativeContext.denote (alphaCode a) (.theta 0 t) := by
      simpa only [he, NativeContext.interpretation_code] using hε
    have hh : omegaSequence (NativeContext.base (alphaCode a)) 1 ≤ NativeContext.denote (alphaCode a) t := by
      rcases (NativeContext.OmegaPowers.theta_epsilon_iff _ t ht).mp heps with hz | hh
      · exact False.elim ((ne_of_gt (by simpa only [he, NativeContext.interpretation_code] using hs.2.2.1)) hz)
      · exact hh
    have hsort : 1 < t.outerSort := by
      apply lt_of_not_ge
      intro hl
      exact hh.not_gt ((NativeContext.denote_lt_iff_outerSort_le _ t
        (NativeContext.BaseTransformation.theta_argument_check _ 0 t ht) 1 (by omega)).mpr hl)
    have hg := BoundedContextReturn.intermediate_root_caller a hs.1 t ht hn hsort
      (by simpa only [he, NativeContext.interpretation_code] using hs.2.2.2)
    simpa only [highCheck, he] using hg

def outputContext (a c : Nat) : Nat := cond (highCheck a c) (betaCode a c) (alphaCode a)

theorem outputContext_primrec : Primrec₂ outputContext :=
  (highCheck_primrec.cond betaCode_primrec (alphaCode_primrec.comp Primrec.fst)).to₂

theorem outputContext_checked (a c : Nat) (hc : inputCheck a c = true) :
    NativeContext.baseCheck (outputContext a c) = true := by
  cases hh : highCheck a c with
  | true => simpa only [outputContext, hh, Bool.cond_true] using
      NativeContext.PublicEpsilonIota.betaCode_baseCheck (alphaCode a) c hh
  | false => simpa only [outputContext, hh, Bool.cond_false] using
      alphaCode_baseCheck a ((inputCheck_exact a c).mp hc).1

noncomputable def sourceValue (a c : Nat) : Ordinal.{0} :=
  if highCheck a c = true then BoundedContextLambda.sourceValue a c
  else NativeContext.DirectZeta.sourceValue (alphaCode a) c

theorem source_definition_2_45 (a c : Nat) (hc : inputCheck a c = true) : sourceValue a c =
    if Ordinal.omega0 ^ NativeContext.interpretation (alphaCode a) c = NativeContext.interpretation (alphaCode a) c then
      NativeContext.interpretation (betaCode a c) (literalDelta a c) + NativeContext.DirectZeta.sourceValue (alphaCode a) c
    else NativeContext.DirectZeta.sourceValue (alphaCode a) c := by
  rw [← high_iff_epsilon a c hc]
  rfl

def returnedRoot (a c : Nat) : Nat := cond (highCheck a c)
  (BoundedContextReturn.returnedRoot a c) (LowTranslation.returnedCode a c)

theorem returnedRoot_primrec : Primrec₂ returnedRoot :=
  (highCheck_primrec.cond BoundedContextReturn.returnedRoot_primrec LowTranslation.returnedCode_primrec).to₂

theorem returnedRoot_spec (a c : Nat) (hc : inputCheck a c = true) :
    Lambda.PublicBranches.inputCheck (returnedRoot a c) = true ∧
      interpretation 0 (returnedRoot a c) = NativeContext.interpretation (alphaCode a) c := by
  have hs := (inputCheck_exact a c).mp hc
  cases hh : highCheck a c with
  | true => simpa only [returnedRoot, hh, Bool.cond_true] using
      And.intro (Lambda.PublicBranches.high_input _ (BoundedContextReturn.returnedRoot_iota_caller a c hs.1 hh))
        (BoundedContextReturn.returnedRoot_spec a c hs.1 hh).2.2
  | false => simpa only [returnedRoot, hh, Bool.cond_false] using
      LowTranslation.returnedCode_spec a c hs.1 hs.2.1 hs.2.2.1 hs.2.2.2

def execute (a c : Nat) : Part Nat := cond (inputCheck a c)
  (cond (highCheck a c) (BoundedContextLambda.execute a c) (NativeContext.DirectZeta.execute (alphaCode a) c)) Part.none

theorem execute_partrec : Partrec₂ execute :=
  (Partrec.cond inputCheck_primrec.to_comp
    (Partrec.cond highCheck_primrec.to_comp BoundedContextLambda.execute_partrec
      (NativeContext.DirectZeta.execute_partrec.comp (alphaCode_primrec.comp Primrec.fst).to_comp Computable.snd))
    Partrec.none).to₂

theorem execute_domain (a c : Nat) : (execute a c).Dom ↔ inputCheck a c = true := by
  cases hc : inputCheck a c with
  | false => simp only [execute, hc, Bool.cond_false, Part.not_none_dom, Bool.false_eq_true]
  | true =>
    have hs := (inputCheck_exact a c).mp hc
    cases hh : highCheck a c with
    | true =>
      have hi : BoundedContextLambda.inputCheck a c = true :=
        (BoundedContextLambda.inputCheck_exact a c).mpr ⟨hs.1, hh⟩
      simp only [execute, hc, hh, Bool.cond_true, BoundedContextLambda.execute_domain, hi]
    | false => simp only [execute, hc, hh, Bool.cond_true, Bool.cond_false,
        NativeContext.DirectZeta.execute_domain, hs.2.1]

theorem execute_returns (a c : Nat) (hc : inputCheck a c = true) : ∃ out, out ∈ execute a c :=
  Part.dom_iff_mem.mp ((execute_domain a c).mpr hc)

theorem execute_spec (a c out : Nat) (ho : out ∈ execute a c) : inputCheck a c = true ∧
    NativeContext.lowCheckCode (outputContext a c) out = true ∧
      NativeContext.Comparison.acceptedCode (outputContext a c) out = true ∧
      NativeContext.interpretation (outputContext a c) out = sourceValue a c := by
  have hc := (execute_domain a c).mp (Part.dom_iff_mem.mpr ⟨out, ho⟩)
  cases hh : highCheck a c with
  | true =>
    have hm : out ∈ BoundedContextLambda.execute a c := by simpa only [execute, hc, hh, Bool.cond_true] using ho
    have hs := BoundedContextLambda.execute_spec a c out hm
    refine ⟨hc, ?_⟩
    simpa only [outputContext, sourceValue, hh, Bool.cond_true, if_pos rfl] using hs.2
  | false =>
    have hm : out ∈ NativeContext.DirectZeta.execute (alphaCode a) c := by
      simpa only [execute, hc, hh, Bool.cond_true, Bool.cond_false] using ho
    have hs := NativeContext.DirectZeta.execute_spec _ c out hm
    refine ⟨hc, ?_⟩
    simpa only [outputContext, sourceValue, hh, Bool.cond_false, Bool.false_eq_true, if_false] using hs.2

/-- Full original source-one outer normal Lemma2.48(d): both intermediate
epsilon and non-epsilon roots have actual original public lambda executions. -/
theorem execute_translation (a c out : Nat) (ho : out ∈ execute a c) :
    ∃ other, other ∈ Lambda.PublicBranches.execute (returnedRoot a c) ∧
      unionInterpretation other = NativeContext.interpretation (outputContext a c) out := by
  have hc := (execute_domain a c).mp (Part.dom_iff_mem.mpr ⟨out, ho⟩)
  have hs := (inputCheck_exact a c).mp hc
  cases hh : highCheck a c with
  | true =>
    have hm : out ∈ BoundedContextLambda.execute a c := by simpa only [execute, hc, hh, Bool.cond_true] using ho
    obtain ⟨nativeOut, hold, hbase, hv⟩ := Translation.execute_translation a c out hm
    have hroot := BoundedContextReturn.returnedRoot_iota_caller a c hs.1 hh
    have hpub := BoundedPublicReturn.lambda_public_spec _ nativeOut hold
    rw [hbase] at hpub
    refine ⟨BoundedPublicReturn.publicCode (BoundedContextReturn.returnedRoot a c) nativeOut, ?_, ?_⟩
    · simp only [returnedRoot, hh, Bool.cond_true, Lambda.PublicBranches.execute_high _ hroot]
      exact (Part.mem_map_iff _).mpr ⟨nativeOut, hold, rfl⟩
    · simpa only [outputContext, hh, Bool.cond_true] using hpub.2.trans hv
  | false =>
    have hm : out ∈ NativeContext.DirectZeta.execute (alphaCode a) c := by
      simpa only [execute, hc, hh, Bool.cond_true, Bool.cond_false] using ho
    have hε : Ordinal.omega0 ^ NativeContext.interpretation (alphaCode a) c ≠ NativeContext.interpretation (alphaCode a) c := by
      intro he
      have ht := (high_iff_epsilon a c hc).mpr he
      simp only [hh, Bool.false_eq_true] at ht
    obtain ⟨other, hold, hv⟩ := LowTranslation.execute_translation a c out hs.1 hm hs.2.2.1 hs.2.2.2 hε
    exact ⟨other, by simpa only [returnedRoot, hh, Bool.cond_false] using hold,
      by simpa only [outputContext, hh, Bool.cond_false] using hv⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.BoundedContextLambda.Branches
