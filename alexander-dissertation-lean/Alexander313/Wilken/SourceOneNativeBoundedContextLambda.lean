import Alexander313.Wilken.SourceOneNativeBoundedContextIotaReturn
import Alexander313.Wilken.PublicEpsilonNativeOmegaQuotient
import Alexander313.Wilken.HereditaryNativeDirectZeta

/-!
# Actual intermediate lambda over an original source-one outer root

The original source-one outer root and the original high intermediate root
supply every iota, zeta, public-return and beta-parameter caller. The real
native addition executes iota(Delta)+zeta in the genuine beta context.
The original source-one checker is retained for the outer root; one is
never passed to the native epsilon parser. Translation is proved separately.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.BoundedContextLambda

abbrev Context := Nat × Nat

def inputCheck (a b : Nat) : Bool := SourceOneIota.rootCheck a &&
  NativeContext.PublicEpsilonIota.rootCheck (alphaCode a) b

theorem inputCheck_primrec : Primrec₂ inputCheck :=
  (Primrec.and.comp (rootCheck_primrec.comp Primrec.fst)
    (NativeContext.PublicEpsilonIota.rootCheck_primrec.comp
      (alphaCode_primrec.comp Primrec.fst) Primrec.snd)).to₂

theorem inputCheck_exact (a b : Nat) : inputCheck a b = true ↔
    SourceOneIota.rootCheck a = true ∧
      NativeContext.PublicEpsilonIota.rootCheck (alphaCode a) b = true :=
  Bool.and_eq_true

def betaCode (a b : Nat) : Nat := NativeContext.PublicEpsilonIota.betaCode (alphaCode a) b

theorem betaCode_primrec : Primrec₂ betaCode :=
  (NativeContext.PublicEpsilonIota.betaCode_primrec.comp
    (alphaCode_primrec.comp Primrec.fst) Primrec.snd).to₂

abbrev deltaCode := NativeContext.PublicEpsilonIota.OmegaQuotient.deltaCode

theorem deltaCode_primrec : Primrec deltaCode :=
  NativeContext.PublicEpsilonIota.OmegaQuotient.deltaCode_primrec

theorem zeta_input (a b : Nat) (hi : inputCheck a b = true) :
    NativeContext.DirectZeta.inputCheck (alphaCode a) b = true := by
  obtain ⟨_, ⟨t, he, ht, hn, hh⟩, _⟩ :=
    (NativeContext.PublicEpsilonIota.rootCheck_exact _ _).mp ((inputCheck_exact a b).mp hi).2
  exact (NativeContext.DirectZeta.inputCheck_exact _ _).mpr ⟨t, he, ht, hn⟩

theorem delta_restricted (a b : Nat) (hi : inputCheck a b = true) :
    NativeContext.PublicEpsilonIota.Restricted (alphaCode a) b
      (NativeContext.Decomposition.highPartTerm 0
        (NativeContext.PublicEpsilonIota.OmegaQuotient.argumentCode b)) := by
  apply NativeContext.PublicEpsilonIota.OmegaQuotient.Support.buildAtoms_restricted
  intro t ht
  exact NativeContext.PublicEpsilonIota.OmegaQuotient.Support.atoms_restricted _ _ _
    (NativeContext.PublicEpsilonIota.argument_restricted _ _ ((inputCheck_exact a b).mp hi).2) t
    ((NativeContext.Decomposition.highWord_mem 0 _ t).mp ht).1

theorem delta_input (a b : Nat) (hi : inputCheck a b = true) :
    NativeContext.PublicEpsilonIota.inputCheck (alphaCode a) b (deltaCode b) = true := by
  have hb := ((inputCheck_exact a b).mp hi).2
  have hc := NativeContext.PublicEpsilonIota.OmegaQuotient.Support.argument_accepted _ _ hb
  have ht := (NativeContext.Decomposition.parts_checked (alphaCode a) 0 _ hc).1
  have hn := (NativeContext.Decomposition.parts_normal (alphaCode a) 0 _ hc).1
  apply (NativeContext.PublicEpsilonIota.inputCheck_exact _ _ _).mpr
  exact ⟨hb, NativeContext.Decomposition.highPartTerm 0
    (NativeContext.PublicEpsilonIota.OmegaQuotient.argumentCode b), rfl, ht, hn,
      (NativeContext.PublicEpsilonIota.restricted_iff_sourceStar _ _ hb _ ht hn).mp
        (delta_restricted a b hi)⟩

def literalDelta (a b : Nat) : Nat :=
  NativeContext.PublicEpsilonIota.literalCode (alphaCode a) b (deltaCode b)

theorem literalDelta_primrec : Primrec₂ literalDelta :=
  (NativeContext.PublicEpsilonIota.literalCode_primrec.comp
    ((alphaCode_primrec.comp Primrec.fst).pair Primrec.snd)
    (deltaCode_primrec.comp Primrec.snd)).to₂

theorem literalDelta_spec (a b : Nat) (hi : inputCheck a b = true) :
    NativeContext.lowCheckCode (betaCode a b) (literalDelta a b) = true ∧
      NativeContext.Comparison.acceptedCode (betaCode a b) (literalDelta a b) = true := by
  have hb := ((inputCheck_exact a b).mp hi).2
  have hc := NativeContext.PublicEpsilonIota.OmegaQuotient.Support.argument_accepted _ _ hb
  let t := NativeContext.Decomposition.highPartTerm 0
    (NativeContext.PublicEpsilonIota.OmegaQuotient.argumentCode b)
  have ht := (NativeContext.Decomposition.parts_checked (alphaCode a) 0 _ hc).1
  have hn := (NativeContext.Decomposition.parts_normal (alphaCode a) 0 _ hc).1
  have hr := delta_restricted a b hi
  have hsort : t.outerSort ≤ 2 :=
    (NativeContext.denote_lt_iff_outerSort_le _ t ht 2 (by omega)).mp (by
      have h := (NativeContext.Decomposition.parts_le (alphaCode a) 0 _ hc).1.trans_lt
        (NativeContext.DirectZeta.argument_sorted _ _ (zeta_input a b hi))
      simpa only [t, NativeContext.Decomposition.highCode, NativeContext.interpretation_code] using h)
  have hchecked := NativeContext.PublicEpsilonIota.transform_checked _ _ hb t ht hr
  have hout : (NativeContext.PublicEpsilonIota.transform (alphaCode a) b t).outerSort ≤ 1 := by
    have h := NativeContext.PublicEpsilonIota.transform_outerSort _ _ hb t ht hr
    omega
  have he : literalDelta a b = (NativeContext.PublicEpsilonIota.transform (alphaCode a) b t).code :=
    NativeContext.PublicEpsilonIota.literalCode_code _ _ hb t ht hn hr
  refine ⟨?_, NativeContext.PublicEpsilonIota.literalCode_accepted _ _ _ (delta_input a b hi)⟩
  rw [he]
  simp only [NativeContext.lowCheckCode_code, NativeContext.lowCheck, hchecked, hout,
    decide_true, Bool.true_and]

def zetaParameterCode (a b d : Nat) : Nat :=
  NativeContext.OmegaPowers.parameterCode (BoundedPublicReturn.publicCode a d)

theorem zetaParameterCode_primrec : Primrec₂ (fun p : Context => zetaParameterCode p.1 p.2) :=
  ((NativeContext.OmegaPowers.parameterCode_primrec.comp
    (BoundedPublicReturn.publicCode_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd))).to₂

theorem zetaParameterCode_spec (a b d : Nat) (hi : inputCheck a b = true)
    (hd : d ∈ NativeContext.DirectZeta.execute (alphaCode a) b) :
    NativeContext.lowCheckCode (betaCode a b) (zetaParameterCode a b d) = true ∧
      NativeContext.Comparison.acceptedCode (betaCode a b) (zetaParameterCode a b d) = true ∧
      NativeContext.interpretation (betaCode a b) (zetaParameterCode a b d) =
        NativeContext.DirectZeta.sourceValue (alphaCode a) b := by
  have hs := NativeContext.DirectZeta.execute_spec _ b d hd
  have hb := NativeContext.DirectZeta.execute_bound _ b d hd
  have hin := (inputCheck_exact a b).mp hi
  have hc := (BoundedPublicReturn.inputCheck_exact a d).mpr
    ⟨hin.1, hs.2.1, hb.trans_lt (BoundedContextReturn.intermediate_bound a b hin.1 hin.2)⟩
  have hp := BoundedPublicReturn.publicCode_spec a d hc
  have hbeta := NativeContext.PublicEpsilonIota.betaCode_baseCheck _ _ hin.2
  have hparam := (NativeContext.parameterCheck_exact (betaCode a b) _).mpr
    ⟨Canonical.check_original hp.1, ((NativeContext.baseCheck_exact _).mp hbeta).1,
      by rw [NativeContext.parameters, hp.2,
        NativeContext.PublicEpsilonIota.beta_base _ _ hin.2]; exact hb⟩
  have hv := NativeContext.OmegaPowers.parameterCode_spec (betaCode a b) _ hparam hbeta
  exact ⟨hv.1, hv.2.1, hv.2.2.trans (hp.2.trans hs.2.2.2)⟩

noncomputable def sourceValue (a b : Nat) : Ordinal.{0} :=
  NativeContext.interpretation (betaCode a b) (literalDelta a b) +
    NativeContext.DirectZeta.sourceValue (alphaCode a) b

def emitCode (a b d : Nat) : Nat := NativeContext.Arithmetic.addCode (betaCode a b)
  (literalDelta a b) (zetaParameterCode a b d)

theorem emitCode_primrec : Primrec₂ (fun p : Context => emitCode p.1 p.2) :=
  (NativeContext.Arithmetic.addCode_primrec.comp ((betaCode_primrec.comp Primrec.fst).pair
    ((literalDelta_primrec.comp Primrec.fst).pair zetaParameterCode_primrec))).to₂

theorem emitCode_spec (a b d : Nat) (hi : inputCheck a b = true)
    (hd : d ∈ NativeContext.DirectZeta.execute (alphaCode a) b) :
    NativeContext.lowCheckCode (betaCode a b) (emitCode a b d) = true ∧
      NativeContext.Comparison.acceptedCode (betaCode a b) (emitCode a b d) = true ∧
      NativeContext.interpretation (betaCode a b) (emitCode a b d) = sourceValue a b := by
  have hl := literalDelta_spec a b hi
  have hz := zetaParameterCode_spec a b d hi hd
  have hs := NativeContext.Arithmetic.addCode_spec _ _ _
    ((NativeContext.Comparison.acceptedCode_exact _ _).mp hl.2).1
    ((NativeContext.Comparison.acceptedCode_exact _ _).mp hz.2.1).1
  exact ⟨(NativeContext.OmegaPowerHeight.addCode_low_height _ _ _ hl.1 hz.1).1, hs.1,
    by simpa only [emitCode, sourceValue, hz.2.2] using hs.2.1⟩

def execute (a b : Nat) : Part Nat := cond (inputCheck a b)
  ((NativeContext.DirectZeta.execute (alphaCode a) b).map (emitCode a b)) Part.none

theorem execute_partrec : Partrec₂ execute :=
  (Partrec.cond inputCheck_primrec.to_comp
    (Partrec.map (NativeContext.DirectZeta.execute_partrec.comp
      (alphaCode_primrec.comp Primrec.fst).to_comp Computable.snd) emitCode_primrec.to_comp)
    Partrec.none).to₂

theorem execute_domain (a b : Nat) : (execute a b).Dom ↔ inputCheck a b = true := by
  cases hi : inputCheck a b with
  | false => simp only [execute, hi, Bool.cond_false, Part.not_none_dom, Bool.false_eq_true]
  | true => simp only [execute, hi, Bool.cond_true, Part.map,
      NativeContext.DirectZeta.execute_domain, zeta_input a b hi]

theorem execute_returns (a b : Nat) (hi : inputCheck a b = true) :
    ∃ out, out ∈ execute a b := Part.dom_iff_mem.mp ((execute_domain a b).mpr hi)

theorem execute_spec (a b out : Nat) (ho : out ∈ execute a b) :
    inputCheck a b = true ∧ NativeContext.lowCheckCode (betaCode a b) out = true ∧
      NativeContext.Comparison.acceptedCode (betaCode a b) out = true ∧
      NativeContext.interpretation (betaCode a b) out = sourceValue a b := by
  have hi := (execute_domain a b).mp (Part.dom_iff_mem.mpr ⟨out, ho⟩)
  have hm : out ∈ (NativeContext.DirectZeta.execute (alphaCode a) b).map (emitCode a b) := by
    simpa only [execute, hi, Bool.cond_true] using ho
  obtain ⟨d, hd, rfl⟩ := (Part.mem_map_iff (emitCode a b)).mp hm
  exact ⟨hi, emitCode_spec a b d hi hd⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.BoundedContextLambda
