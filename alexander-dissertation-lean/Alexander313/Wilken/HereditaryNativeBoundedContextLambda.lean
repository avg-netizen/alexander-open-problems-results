import Alexander313.Wilken.HereditaryNativeDirectZeta
import Alexander313.Wilken.HereditaryNativeBoundedContextOmegaQuotient

/-!
# Actual lambda in the original bounded intermediate epsilon source

The original root supplies its full restricted high part and genuine iota
caller. Direct native zeta is below that same original root. The ORIGINAL
outer bounded public return therefore constructs its actual public payload;
that value is below the computed beta and supplies the real target parameter
caller. Native addition constructs LOW Normal lambda at beta. The actual
iota height shift and original decomposition derive the strict printed
height bound. No return, restriction, output or height oracle is assumed.
Cross-base lambda equality is separate. Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.BoundedContextIota.Lambda

abbrev inputCheck := BoundedContextIota.rootCheck

def deltaCode (root : Nat) : Nat := OmegaQuotient.deltaCode root

theorem deltaCode_primrec : Primrec deltaCode := OmegaQuotient.deltaCode_primrec

theorem zeta_input (s a root : Nat) (ha : inputCheck s a root = true) :
    DirectZeta.inputCheck (sourceCode s a) root = true := by
  obtain ⟨_, ⟨t, he, ht, hn, hh⟩, _⟩ := (rootCheck_exact s a root).mp ha
  exact (DirectZeta.inputCheck_exact _ _).mpr ⟨t, he, ht, hn⟩

theorem delta_restricted (s a root : Nat) (ha : inputCheck s a root = true) :
    Restricted s a root (Decomposition.highPartTerm 0 (OmegaQuotient.argumentCode root)) := by
  apply OmegaQuotient.buildAtoms_restricted
  intro t ht
  exact OmegaQuotient.atoms_restricted s a root _ (argument_restricted s a root ha) t
    ((Decomposition.highWord_mem 0 _ t).mp ht).1

theorem delta_input (s a root : Nat) (ha : inputCheck s a root = true) :
    BoundedContextIota.inputCheck s a root (deltaCode root) = true := by
  have hi := OmegaQuotient.argument_accepted s a root ha
  have hc := (Decomposition.parts_checked (sourceCode s a) 0 _ hi).1
  have hn := (Decomposition.parts_normal (sourceCode s a) 0 _ hi).1
  apply (BoundedContextIota.inputCheck_exact s a root _).mpr
  refine ⟨ha, Decomposition.highPartTerm 0 (OmegaQuotient.argumentCode root), rfl, hc, hn, ?_⟩
  exact (restricted_iff_sourceStar s a root ha _ hc hn).mp (delta_restricted s a root ha)

def literalDelta (s a root : Nat) : Nat := BoundedContextIota.literalCode s a root (deltaCode root)

theorem literalDelta_primrec : Primrec (fun p : Context => literalDelta p.1.1 p.1.2 p.2) :=
  literalCode_primrec.comp Primrec.id (deltaCode_primrec.comp Primrec.snd)

theorem literalDelta_spec (s a root : Nat) (ha : inputCheck s a root = true) :
    lowCheckCode (betaCode s a root) (literalDelta s a root) = true ∧
      Comparison.acceptedCode (betaCode s a root) (literalDelta s a root) = true := by
  have hi := OmegaQuotient.argument_accepted s a root ha
  let t := Decomposition.highPartTerm 0 (OmegaQuotient.argumentCode root)
  have ht := (Decomposition.parts_checked (sourceCode s a) 0 _ hi).1
  have hn := (Decomposition.parts_normal (sourceCode s a) 0 _ hi).1
  have hr := delta_restricted s a root ha
  have hsort : t.outerSort ≤ 2 :=
    (denote_lt_iff_outerSort_le (sourceCode s a) t ht 2 (by omega)).mp (by
      have h := (Decomposition.parts_le (sourceCode s a) 0 _ hi).1.trans_lt
        (DirectZeta.argument_sorted _ _ (zeta_input s a root ha))
      simpa only [deltaCode, OmegaQuotient.deltaCode, Decomposition.highCode, interpretation_code] using h)
  have htransform := transform_checked s a root ha t ht hr
  have houter : (transform s a root t).outerSort ≤ 1 := by
    have h := transform_outerSort s a root ha t ht hr
    omega
  have he : literalDelta s a root = (transform s a root t).code :=
    literalCode_code s a root ha t ht hn hr
  have hac := literalCode_accepted s a root _ (delta_input s a root ha)
  refine ⟨?_, hac⟩
  rw [he]
  simp only [lowCheckCode_code, lowCheck, htransform, houter, decide_true, Bool.true_and]

def zetaParameterCode (s a root d : Nat) : Nat :=
  OmegaPowers.parameterCode (BoundedPublicReturn.publicCode s a d)

theorem zetaParameterCode_primrec : Primrec₂
    (fun p : Context => zetaParameterCode p.1.1 p.1.2 p.2) :=
  ((OmegaPowers.parameterCode_primrec.comp (BoundedPublicReturn.publicCode_primrec.comp
    (((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair Primrec.snd)))).to₂

/-- The original outer endpoint and true zeta<beta supply the actual
canonical public return and target-beta parameter admission. -/
theorem zetaParameterCode_spec (s a root d : Nat) (ha : inputCheck s a root = true)
    (hd : d ∈ DirectZeta.execute (sourceCode s a) root) :
    lowCheckCode (betaCode s a root) (zetaParameterCode s a root d) = true ∧
      Comparison.acceptedCode (betaCode s a root) (zetaParameterCode s a root d) = true ∧
      interpretation (betaCode s a root) (zetaParameterCode s a root d) =
        DirectZeta.sourceValue (sourceCode s a) root := by
  have hs := DirectZeta.execute_spec _ root d hd
  have hb := DirectZeta.execute_bound _ root d hd
  have hc := (BoundedPublicReturn.inputCheck_exact s a d).mpr
    ⟨outer_root s a root ha, hs.2.1, hb.trans_lt ((rootCheck_exact s a root).mp ha).2.2⟩
  have hp := BoundedPublicReturn.publicCode_spec s a d hc
  have hparam := (parameterCheck_exact (betaCode s a root) _).mpr
    ⟨Canonical.check_original hp.1, ((baseCheck_exact _).mp (betaCode_baseCheck s a root ha)).1,
      by rw [parameters, hp.2, beta_base s a root ha]; exact hb⟩
  have hv := OmegaPowers.parameterCode_spec (betaCode s a root) _ hparam
    (betaCode_baseCheck s a root ha)
  exact ⟨hv.1, hv.2.1, hv.2.2.trans (hp.2.trans hs.2.2.2)⟩

noncomputable def sourceValue (s a root : Nat) : Ordinal.{0} :=
  interpretation (betaCode s a root) (literalDelta s a root) +
    DirectZeta.sourceValue (sourceCode s a) root

theorem source_definition_2_45 (s a root : Nat) (ha : inputCheck s a root = true) :
    sourceValue s a root =
      if Ordinal.omega0 ^ interpretation (sourceCode s a) root = interpretation (sourceCode s a) root then
        interpretation (betaCode s a root) (literalDelta s a root) +
          DirectZeta.sourceValue (sourceCode s a) root
      else DirectZeta.sourceValue (sourceCode s a) root := by
  rw [if_pos (root_epsilon s a root ha)]
  rfl

def emitCode (s a root d : Nat) : Nat :=
  Arithmetic.addCode (betaCode s a root) (literalDelta s a root) (zetaParameterCode s a root d)

theorem emitCode_primrec : Primrec₂ (fun p : Context => emitCode p.1.1 p.1.2 p.2) :=
  (Arithmetic.addCode_primrec.comp ((betaCode_primrec.comp Primrec.fst).pair
    ((literalDelta_primrec.comp Primrec.fst).pair zetaParameterCode_primrec))).to₂

theorem emitCode_spec (s a root d : Nat) (ha : inputCheck s a root = true)
    (hd : d ∈ DirectZeta.execute (sourceCode s a) root) :
    lowCheckCode (betaCode s a root) (emitCode s a root d) = true ∧
      Comparison.acceptedCode (betaCode s a root) (emitCode s a root d) = true ∧
      interpretation (betaCode s a root) (emitCode s a root d) = sourceValue s a root := by
  have hl := literalDelta_spec s a root ha
  have hz := zetaParameterCode_spec s a root d ha hd
  have hs := Arithmetic.addCode_spec _ _ _ ((Comparison.acceptedCode_exact _ _).mp hl.2).1
    ((Comparison.acceptedCode_exact _ _).mp hz.2.1).1
  exact ⟨(OmegaPowerHeight.addCode_low_height _ _ _ hl.1 hz.1).1, hs.1,
    by simpa only [emitCode, sourceValue, hz.2.2] using hs.2.1⟩

def execute (s a root : Nat) : Part Nat := cond (inputCheck s a root)
  ((DirectZeta.execute (sourceCode s a) root).map (emitCode s a root)) Part.none

theorem execute_partrec : Partrec (fun p : Context => execute p.1.1 p.1.2 p.2) :=
  Partrec.cond rootCheck_primrec.to_comp
    ((DirectZeta.execute_partrec.comp
      (sourceCode_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)).to_comp
      Computable.snd).map emitCode_primrec.to_comp) Partrec.none

theorem execute_domain (s a root : Nat) : (execute s a root).Dom ↔ inputCheck s a root = true := by
  cases ha : inputCheck s a root with
  | false => simp only [execute, ha, Bool.cond_false, Part.not_none_dom, Bool.false_eq_true]
  | true => simp only [execute, ha, Bool.cond_true, Part.map, DirectZeta.execute_domain,
      zeta_input s a root ha]

theorem execute_spec (s a root out : Nat) (ho : out ∈ execute s a root) :
    inputCheck s a root = true ∧ lowCheckCode (betaCode s a root) out = true ∧
      Comparison.acceptedCode (betaCode s a root) out = true ∧
      interpretation (betaCode s a root) out = sourceValue s a root := by
  have ha := (execute_domain s a root).mp (Part.dom_iff_mem.mpr ⟨out, ho⟩)
  have hm : out ∈ (DirectZeta.execute (sourceCode s a) root).map (emitCode s a root) := by
    simpa only [execute, ha, Bool.cond_true] using ho
  obtain ⟨d, hd, rfl⟩ := (Part.mem_map_iff _).mp hm
  exact ⟨ha, emitCode_spec s a root d ha hd⟩

theorem literalDelta_height_lt_root (s a root : Nat) (ha : inputCheck s a root = true) :
    heightCode (literalDelta s a root) < heightCode root := by
  have hl := literalCode_height s a root (deltaCode root) (delta_input s a root ha)
  have hd := (Height.parts_code_height (sourceCode s a) 0 (OmegaQuotient.argumentCode root)
    ((Decomposition.inputCheck_exact _ _).mp (OmegaQuotient.argument_accepted s a root ha)).1).1
  obtain ⟨_, ⟨t, he, ht, hn, hh⟩, _⟩ := (rootCheck_exact s a root).mp ha
  have harg : heightCode (OmegaQuotient.argumentCode root) = t.height := by
    simp only [OmegaQuotient.argumentCode, he, Localization.argumentCode_theta, heightCode_code]
  have hr : heightCode root = max 1 t.height := by
    simp only [he, heightCode_code, RelativeTerm.height, Nat.zero_add]
  change heightCode (deltaCode root) ≤ heightCode (OmegaQuotient.argumentCode root) at hd
  change heightCode (literalDelta s a root) ≤ heightCode (deltaCode root) - 1 at hl
  rw [harg] at hd
  rw [hr]
  omega

theorem execute_height_lt_root (s a root out : Nat) (ho : out ∈ execute s a root) :
    heightCode out < heightCode root := by
  have ha := (execute_spec s a root out ho).1
  have hm : out ∈ (DirectZeta.execute (sourceCode s a) root).map (emitCode s a root) := by
    simpa only [execute, ha, Bool.cond_true] using ho
  obtain ⟨d, hd, rfl⟩ := (Part.mem_map_iff _).mp hm
  have hl := literalDelta_spec s a root ha
  have hz := zetaParameterCode_spec s a root d ha hd
  have hs := (Arithmetic.addCode_spec _ _ _ ((Comparison.acceptedCode_exact _ _).mp hl.2).1
    ((Comparison.acceptedCode_exact _ _).mp hz.2.1).1).2.2
  have hb := literalDelta_height_lt_root s a root ha
  have hzp : heightCode (zetaParameterCode s a root d) = 0 := by
    simp only [zetaParameterCode, OmegaPowers.parameterCode, heightCode_code, RelativeTerm.height]
  exact hs.trans_lt (by simpa only [hzp, max_zero] using hb)

theorem execute_canonical_height_lt_root (s a root out : Nat) (ho : out ∈ execute s a root) :
    CanonicalHeight.canonicalHeightCode (betaCode s a root) out <
      CanonicalHeight.canonicalHeightCode (sourceCode s a) root := by
  have hs := execute_spec s a root out ho
  have hr : Comparison.acceptedCode (sourceCode s a) root = true := by
    obtain ⟨_, ⟨t, he, ht, hn, hh⟩, _⟩ := (rootCheck_exact s a root).mp hs.1
    apply (Comparison.acceptedCode_exact _ _).mpr
    exact ⟨root_original s a root hs.1, by simpa only [he, ThetaCourse.rawTree_code] using hn⟩
  rw [CanonicalHeight.canonicalHeightCode_normal _ out hs.2.2.1,
    CanonicalHeight.canonicalHeightCode_normal _ root hr]
  exact execute_height_lt_root s a root out ho

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.BoundedContextIota.Lambda
