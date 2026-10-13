import Alexander313.Wilken.SourceOneOmegaQuotient
import Alexander313.Wilken.SourceOneNativeIotaCanonicalHeight
import Alexander313.Wilken.HereditaryNativeArithmetic

/-!
# Actual original-source-one epsilon lambda and its strict height bound

The original root supplies the genuine ANF high part and its full source-star
caller. The actual source-zero zeta search returns a canonical public payload
below that same root. Native addition executes iota(Delta)+zeta in the actual
alpha context. Original source-one finite admission bounds the reconstructed
high-part height; the literal shift and real normalizing addition prove the
printed strict height inequality. No positive-source parser at base one,
source-star, representation, height or return oracle. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.Lambda

open OrderSupport

abbrev inputCheck := rootCheck
abbrev argumentCode := OmegaQuotient.argumentCode
abbrev deltaCode := OmegaQuotient.deltaCode

theorem inputCheck_primrec : Primrec inputCheck := rootCheck_primrec

theorem argument_accepted (a : Nat) (ha : inputCheck a = true) :
    SourceDecomposition.inputCheck 0 (argumentCode a) = true :=
  OmegaQuotient.argument_accepted a ha

theorem deltaCode_primrec : Primrec deltaCode := OmegaQuotient.deltaCode_primrec

theorem delta_restricted (a : Nat) (ha : inputCheck a = true) :
    Restricted a (SourceDecomposition.highPartTerm 0 0 (argumentCode a)) := by
  apply OmegaQuotient.buildAtoms_restricted
  intro t ht
  have hw := (SourceDecomposition.highWord_mem 0 0 (argumentCode a) t).mp ht
  exact restricted_atoms a _ t (argument_restricted a ha) hw.1

theorem delta_input (a : Nat) (ha : inputCheck a = true) :
    SourceOneIota.inputCheck a (deltaCode a) = true := by
  have hc := argument_accepted a ha
  have hp := (SourceDecomposition.parts_checked 0 0 (argumentCode a) hc).1
  have hn := (SourceDecomposition.parts_normal 0 0 (argumentCode a) hc).1
  apply (SourceOneIota.inputCheck_exact a _).mpr
  refine ⟨ha, SourceDecomposition.highPartTerm 0 0 (argumentCode a), rfl, hp, hn, ?_⟩
  exact (restricted_iff_sourceStar a ha _ hp hn).mp (delta_restricted a ha)

theorem argument_not_low (a : Nat) (ha : inputCheck a = true) :
    omegaSequence (finiteBase 0) 1 ≤ interpretation 0 (argumentCode a) := by
  obtain ⟨t, he, ht, hn, hs⟩ := (rootCheck_exact a).mp ha
  have hc := argument_checked 0 t ht
  have hnot : ¬ denote 0 t < omegaSequence (finiteBase 0) 1 := by
    intro h
    have hsort := (denote_lt_iff_outerSort_le 0 t hc 1 (by omega)).mp h
    omega
  simpa only [OmegaQuotient.argumentCode, he, Localization.argumentCode_theta,
    interpretation_code] using le_of_not_gt hnot

theorem delta_nonzero (a : Nat) (ha : inputCheck a = true) :
    interpretation 0 (deltaCode a) ≠ 0 := by
  intro hz
  have hc := argument_accepted a ha
  have hv := SourceDecomposition.parts_reconstruct 0 0 (argumentCode a) hc
  have hl := SourceDecomposition.lowPart_bound 0 0 (argumentCode a) hc
  change interpretation 0 (SourceDecomposition.highCode 0 0 (argumentCode a)) = 0 at hz
  rw [hz, zero_add] at hv
  exact (not_lt_of_ge (argument_not_low a ha)) (hv ▸ hl)

def zetaParameter (d : Nat) : RelativeTerm Nat := .parameter d

theorem zetaParameter_primrec : Primrec zetaParameter := parameter_primrec

theorem zetaParameter_spec (a d : Nat) (ha : inputCheck a = true)
    (hd : d ∈ SourceZeta.zeta 0 a) :
    NativeContext.check (alphaCode a) (zetaParameter d) = true ∧
      NativeContext.denote (alphaCode a) (zetaParameter d) = SourceZeta.sourceValue 0 a := by
  have hs := SourceZeta.zeta_value 0 a d hd
  have hp : NativeContext.parameterCheck (alphaCode a) d = true := by
    apply (NativeContext.parameterCheck_exact _ _).mpr
    refine ⟨Canonical.check_original hs.2.1, Canonical.check_original (alphaCode_spec a ha).1, ?_⟩
    change unionInterpretation d < unionInterpretation (alphaCode a)
    rw [(alphaCode_spec a ha).2]
    exact SourceZeta.zeta_bound 0 a d hd
  refine ⟨?_, hs.2.2⟩
  simp only [zetaParameter, NativeContext.check, alphaCode_baseCheck a ha,
    NativeContext.finiteCheck_parameter, hp, Bool.true_and]

def emit (a d : Nat) : Nat := NativeContext.Arithmetic.addCode (alphaCode a)
  (literalCode a (deltaCode a)) (zetaParameter d).code

theorem emit_primrec : Primrec₂ emit := by
  have hq := alphaCode_primrec.comp Primrec.fst
  have hi := literalCode_primrec.comp Primrec.fst (deltaCode_primrec.comp Primrec.fst)
  have hz := code_primrec.comp (zetaParameter_primrec.comp Primrec.snd)
  exact (NativeContext.Arithmetic.addCode_primrec.comp (hq.pair (hi.pair hz))).to₂

def execute (a : Nat) : Part Nat := cond (inputCheck a)
  ((SourceZeta.zeta 0 a).map (emit a)) Part.none

theorem execute_partrec : Partrec execute := by
  have hp := SourceZeta.zeta_partrec.comp (Computable.const 0) Computable.id
  exact Partrec.cond inputCheck_primrec.to_comp (Partrec.map hp emit_primrec.to_comp) Partrec.none

theorem execute_domain (a : Nat) : (execute a).Dom ↔ inputCheck a = true := by
  cases ha : inputCheck a with
  | false => simp only [execute, ha, Bool.cond_false, Part.not_none_dom, Bool.false_eq_true]
  | true =>
    have hz : SourceZeta.inputCheck 0 a = true := (Bool.and_eq_true.mp ha).1
    simp only [execute, ha, Bool.cond_true, Part.map, SourceZeta.zeta_domain, hz]

theorem execute_returns (a : Nat) (ha : inputCheck a = true) : ∃ out, out ∈ execute a :=
  Part.dom_iff_mem.mp ((execute_domain a).mpr ha)

theorem execute_spec (a out : Nat) (ho : out ∈ execute a) :
    inputCheck a = true ∧ NativeContext.Comparison.acceptedCode (alphaCode a) out = true ∧
      NativeContext.interpretation (alphaCode a) out =
        NativeContext.interpretation (alphaCode a) (literalCode a (deltaCode a)) + SourceZeta.sourceValue 0 a := by
  have ha := (execute_domain a).mp (Part.dom_iff_mem.mpr ⟨out, ho⟩)
  have hm : out ∈ (SourceZeta.zeta 0 a).map (emit a) := by
    simpa only [execute, ha, Bool.cond_true] using ho
  obtain ⟨d, hd, rfl⟩ := (Part.mem_map_iff (emit a)).mp hm
  have hi := literalCode_accepted a _ (delta_input a ha)
  have hz := zetaParameter_spec a d ha hd
  have hc := NativeContext.Arithmetic.addCode_spec (alphaCode a) _ _
    ((NativeContext.Comparison.acceptedCode_exact _ _).mp hi).1
    (by simpa only [NativeContext.checkCode_code] using hz.1)
  exact ⟨ha, hc.1, hc.2.1.trans (by rw [NativeContext.interpretation_code, hz.2])⟩

theorem delta_height_le_argument (a : Nat) (ha : inputCheck a = true) :
    heightCode (deltaCode a) ≤ heightCode (argumentCode a) := by
  have hc := argument_accepted a ha
  have hh : (ThetaCourse.rawTree (argumentCode a)).height ≤ heightCode (argumentCode a) := by
    obtain ⟨t, he, ht⟩ := (checkCode_iff 0 _).mp ((SourceDecomposition.inputCheck_exact 0 _).mp hc).1
    simp only [← he, ThetaCourse.rawTree_code, heightCode_code, le_refl]
  have hs := (SourceDecomposition.parts_admissible 0 (heightCode (argumentCode a)) 0
    (argumentCode a) hc hh).1
  have had : SourceOne.admissible (heightCode (argumentCode a))
      (SourceDecomposition.highPartTerm 0 0 (argumentCode a)) := by
    simpa only [finiteBase_zero, parameters_zero] using hs.2
  simpa only [OmegaQuotient.deltaCode, SourceDecomposition.highCode, heightCode_code] using
    SourceOne.Height.admissible_height_le _ _ had

theorem literalDelta_height_lt_root (a : Nat) (ha : inputCheck a = true) :
    heightCode (literalCode a (deltaCode a)) < heightCode a := by
  have hi := literalCode_height a (deltaCode a) (delta_input a ha)
  have hd := delta_height_le_argument a ha
  obtain ⟨u, he, ht, hn, hs⟩ := (rootCheck_exact a).mp ha
  have harg : heightCode (argumentCode a) = u.height := by
    simp only [OmegaQuotient.argumentCode, he, Localization.argumentCode_theta, heightCode_code]
  have hroot : heightCode a = max 1 u.height := by
    simp only [he, heightCode_code, RelativeTerm.height, Nat.zero_add]
  rw [harg] at hd
  rw [hroot]
  omega

theorem emit_height_lt_root (a d : Nat) (ha : inputCheck a = true) (hd : d ∈ SourceZeta.zeta 0 a) :
    heightCode (emit a d) < heightCode a := by
  have hi := literalCode_accepted a _ (delta_input a ha)
  have hz := zetaParameter_spec a d ha hd
  have hh := (NativeContext.Arithmetic.addCode_spec (alphaCode a) _ _
    ((NativeContext.Comparison.acceptedCode_exact _ _).mp hi).1
    (by simpa only [NativeContext.checkCode_code] using hz.1)).2.2
  have hb := literalDelta_height_lt_root a ha
  exact hh.trans_lt (by
    simpa only [heightCode_code, zetaParameter, RelativeTerm.height, max_zero] using hb)

theorem execute_height_lt_root (a out : Nat) (ho : out ∈ execute a) :
    heightCode out < heightCode a := by
  have ha := (execute_spec a out ho).1
  have hm : out ∈ (SourceZeta.zeta 0 a).map (emit a) := by
    simpa only [execute, ha, Bool.cond_true] using ho
  obtain ⟨d, hd, rfl⟩ := (Part.mem_map_iff (emit a)).mp hm
  exact emit_height_lt_root a d ha hd

theorem source_lemma_2_48_c (a out : Nat) (ho : out ∈ execute a) :
    NativeContext.CanonicalHeight.canonicalHeightCode (alphaCode a) out <
      SourceOne.CanonicalHeight.canonicalHeightCode a := by
  have hs := execute_spec a out ho
  rw [NativeContext.CanonicalHeight.canonicalHeightCode_normal _ out hs.2.1,
    SourceOne.CanonicalHeight.canonicalHeightCode_normal _ (HeightSupport.root_source_accepted a hs.1)]
  exact execute_height_lt_root a out ho

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.Lambda
