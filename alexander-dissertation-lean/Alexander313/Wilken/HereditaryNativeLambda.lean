import Alexander313.Wilken.HereditaryNativeIota
import Alexander313.Wilken.HereditaryNativeArithmetic
import Alexander313.Wilken.HereditaryNativeSourceChiArithmetic

/-!
# Executing the epsilon/high-root branch of Definition 2.45 lambda

The ORIGINAL normal theta-zero root has nonzero cardinal high part at the
same positive public epsilon source. Its argument supplies the full support
restriction of the actual ANF high part. That derived caller executes iota.
The real zeta search supplies a canonical public parameter strictly below
the new epsilon. Actual native addition produces a weak-normal expression
with target value iota(Delta) + zeta(alpha), without a supplied translator.

This milestone implements this epsilon/high-root branch only. It does not
prove the shifted-collapse isomorphism in Lemma 2.46, arbitrary temporary
inverse/public return, source canonical-height claims or the bounds in 2.48.
All source proofs are uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Lambda

open NativePublicBridge (contextCode contextCode_checked)

private theorem atoms_full_support (t u : RelativeTerm Nat) :
    u ∈ Iota.fullList t ↔ ∃ v ∈ Comparison.atoms t, u ∈ Iota.fullList v := by
  induction t with
  | parameter p =>
    simp only [Iota.fullList, RelativeTerm.PrincipalSupport.principalList, List.not_mem_nil]
    constructor
    · intro h; exact False.elim h
    · rintro ⟨v, hv, hu⟩
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hv
      exact List.not_mem_nil hu
  | sum t v iht ihv =>
    change (u ∈ Iota.fullList t ++ Iota.fullList v) ↔ _
    simp only [List.mem_append, Comparison.atoms]
    constructor
    · rintro (h | h)
      · obtain ⟨w, hw, hu⟩ := iht.mp h
        exact ⟨w, Or.inl hw, hu⟩
      · obtain ⟨w, hw, hu⟩ := ihv.mp h
        exact ⟨w, Or.inr hw, hu⟩
    · rintro ⟨w, hw | hw, hu⟩
      · exact Or.inl (iht.mpr ⟨w, hw, hu⟩)
      · exact Or.inr (ihv.mpr ⟨w, hw, hu⟩)
  | theta k t => simp only [Comparison.atoms, List.mem_singleton, exists_eq_left]

private theorem buildRev_full_support (as : List (RelativeTerm Nat)) (u : RelativeTerm Nat) :
    u ∈ Iota.fullList (Normalization.buildRev as) ↔ ∃ v ∈ as, u ∈ Iota.fullList v := by
  induction as with
  | nil => simp only [Normalization.buildRev, Normalization.zeroTree,
      Iota.fullList, RelativeTerm.PrincipalSupport.principalList, List.not_mem_nil,
      false_and, exists_false]
  | cons a as ih =>
    simp only [Normalization.buildRev, Iota.fullList,
      RelativeTerm.PrincipalSupport.principalList, List.mem_append, ih, List.mem_cons]
    constructor
    · rintro (⟨v, hv, hu⟩ | hu)
      · exact ⟨v, Or.inr hv, hu⟩
      · exact ⟨a, Or.inl rfl, hu⟩
    · rintro ⟨v, rfl | hv, hu⟩
      · exact Or.inr hu
      · exact Or.inl ⟨v, hv, hu⟩

private theorem buildAtoms_full_support (as : List (RelativeTerm Nat)) (u : RelativeTerm Nat) :
    u ∈ Iota.fullList (Normalization.buildAtoms as) ↔ ∃ v ∈ as, u ∈ Iota.fullList v := by
  simpa only [Normalization.buildAtoms, List.mem_reverse] using buildRev_full_support as.reverse u

abbrev inputCheck := Iota.rootCheck

theorem inputCheck_primrec : Primrec₂ inputCheck := Iota.rootCheck_primrec

def argumentCode (a : Nat) : Nat := Localization.argumentCode a

def deltaCode (a : Nat) : Nat := Decomposition.highCode 0 (argumentCode a)

theorem deltaCode_primrec : Primrec deltaCode :=
  Decomposition.highCode_primrec.comp (Primrec.const 0) Localization.argumentCode_primrec

theorem argument_accepted (s a : Nat) (ha : inputCheck s a = true) :
    Decomposition.inputCheck (contextCode s) (argumentCode a) = true := by
  obtain ⟨t, he, ht, hn, hs⟩ := (Iota.rootCheck_exact s a).mp ha
  apply (Decomposition.inputCheck_exact _ _).mpr
  exact ⟨by simpa only [argumentCode, he, Localization.argumentCode_theta, checkCode_code]
      using BaseTransformation.theta_argument_check _ 0 t ht,
    by simpa only [argumentCode, he, Localization.argumentCode_theta,
      ThetaCourse.rawTree_code] using hn⟩

/-- Taking the true ANF high part preserves a subset of actual full P0
support. Its source-star restriction is derived from the original root. -/
theorem delta_restricted (s a : Nat) (ha : inputCheck s a = true) :
    Iota.Restricted s a (Decomposition.highPartTerm 0 (argumentCode a)) := by
  intro u hu
  obtain ⟨v, hv, hu⟩ := (buildAtoms_full_support _ u).mp hu
  have hw := ((Decomposition.highWord_mem 0 (argumentCode a) v).mp hv).1
  have hmem := (atoms_full_support _ u).mpr ⟨v, hw, hu⟩
  exact Iota.argument_restricted s a ha u hmem

theorem delta_input (s a : Nat) (ha : inputCheck s a = true) :
    Iota.inputCheck s a (deltaCode a) = true := by
  have hc := argument_accepted s a ha
  have hp := Decomposition.parts_checked (contextCode s) 0 (argumentCode a) hc
  have hn := Decomposition.parts_normal (contextCode s) 0 (argumentCode a) hc
  apply (Iota.inputCheck_exact _ _ _).mpr
  refine ⟨ha, Decomposition.highPartTerm 0 (argumentCode a), rfl, hp.1, hn.1, ?_⟩
  exact (Iota.restricted_iff_sourceStar s a ha _ hp.1 hn.1).mp (delta_restricted s a ha)

theorem argument_not_low (s a : Nat) (ha : inputCheck s a = true) :
    omegaSequence (base (contextCode s)) 1 ≤ interpretation (contextCode s) (argumentCode a) := by
  obtain ⟨t, he, ht, hn, hs⟩ := (Iota.rootCheck_exact s a).mp ha
  have hc := BaseTransformation.theta_argument_check _ 0 t ht
  have hnot : ¬ denote (contextCode s) t < omegaSequence (base (contextCode s)) 1 := by
    intro h
    have hsort := (denote_lt_iff_outerSort_le _ t hc 1 (by omega)).mp h
    omega
  simpa only [argumentCode, he, Localization.argumentCode_theta, interpretation_code] using
    le_of_not_gt hnot

theorem delta_nonzero (s a : Nat) (ha : inputCheck s a = true) :
    interpretation (contextCode s) (deltaCode a) ≠ 0 := by
  intro hz
  have hc := argument_accepted s a ha
  have hv := Decomposition.parts_reconstruct (contextCode s) 0 (argumentCode a) hc
  have hl := Decomposition.lowPart_bound (contextCode s) 0 (argumentCode a) hc
  have hzero : interpretation (contextCode s) (Decomposition.highCode 0 (argumentCode a)) = 0 := hz
  rw [hzero, zero_add] at hv
  exact (not_lt_of_ge (argument_not_low s a ha)) (hv ▸ hl)

theorem root_proper (s a : Nat) (ha : inputCheck s a = true) :
    base (contextCode s) < interpretation (contextCode s) a := by
  obtain ⟨t, he, ht, hn, hs⟩ := (Iota.rootCheck_exact s a).mp ha
  have haa := BaseTransformation.theta_argument_check _ 0 t ht
  have hnz : denote (contextCode s) t ≠ 0 := by
    intro hz
    have hl := argument_not_low s a ha
    rw [argumentCode, he, Localization.argumentCode_theta, interpretation_code, hz] at hl
    exact (not_le_of_gt (omegaSequence_isSuccLimit (base (contextCode s)) 0).bot_lt) hl
  simpa only [he, interpretation_code] using
    (SourceChi.Arithmetic.proper_theta_zero_iff _ t ht hn).mpr hnz

def zetaParameter (s d : Nat) : RelativeTerm Nat := .parameter (SourceZeta.canonicalOutput s d)

theorem zetaParameter_primrec : Primrec₂ zetaParameter :=
  parameter_primrec.comp₂ SourceZeta.canonicalOutput_primrec

theorem zetaParameter_spec (s a d : Nat) (hroot : inputCheck s a = true)
    (hd : d ∈ SourceZeta.zeta s a) :
    check (Iota.alphaCode s a) (zetaParameter s d) = true ∧
      denote (Iota.alphaCode s a) (zetaParameter s d) = SourceZeta.sourceValue s a := by
  have ha := (SourceZeta.zeta_spec s a d hd)
  have hc := SourceZeta.canonicalOutput_spec s d ha.2.1 ha.2.2.1
  have hp : parameterCheck (Iota.alphaCode s a) (SourceZeta.canonicalOutput s d) = true := by
    apply (parameterCheck_exact _ _).mpr
    refine ⟨Canonical.check_original hc.1, ?_, ?_⟩
    · exact Canonical.check_original (Iota.alphaCode_spec s a hroot).1
    · change unionInterpretation (SourceZeta.canonicalOutput s d) < unionInterpretation (Iota.alphaCode s a)
      rw [hc.2, (Iota.alphaCode_spec s a hroot).2]
      exact ha.2.2.2.2
  exact ⟨by simp only [zetaParameter, check, Iota.alphaCode_baseCheck s a hroot,
    finiteCheck_parameter, hp, Bool.true_and], hc.2.trans ha.2.2.2.1⟩

def emit (s a d : Nat) : Nat := Arithmetic.addCode (Iota.alphaCode s a)
  (Iota.literalCode s a (deltaCode a)) (zetaParameter s d).code

theorem emit_primrec : Primrec (fun p : (Nat × Nat) × Nat => emit p.1.1 p.1.2 p.2) := by
  have hs : Primrec (fun p : (Nat × Nat) × Nat => p.1.1) := Primrec.fst.comp Primrec.fst
  have ha : Primrec (fun p : (Nat × Nat) × Nat => p.1.2) := Primrec.snd.comp Primrec.fst
  have hq := Iota.alphaCode_primrec.comp hs ha
  have hi := Iota.literalCode_primrec.comp
    (Primrec.fst.pair (deltaCode_primrec.comp ha))
  have hz := code_primrec.comp (zetaParameter_primrec.comp hs Primrec.snd)
  exact Arithmetic.addCode_primrec.comp (hq.pair (hi.pair hz))

def execute (s a : Nat) : Part Nat := cond (inputCheck s a)
  ((SourceZeta.zeta s a).map (emit s a)) Part.none

theorem execute_partrec : Partrec₂ execute := by
  have hp := SourceZeta.zeta_partrec.comp Primrec.fst.to_comp Primrec.snd.to_comp
  have he := emit_primrec.to_comp.to₂
  exact (Partrec.cond inputCheck_primrec.to_comp (Partrec.map hp he) Partrec.none).to₂

theorem execute_domain (s a : Nat) : (execute s a).Dom ↔ inputCheck s a = true := by
  cases ha : inputCheck s a with
  | false => simp only [execute, ha, Bool.cond_false, Part.not_none_dom, Bool.false_eq_true]
  | true =>
    have hz : SourceZeta.inputCheck s a = true := (Bool.and_eq_true.mp ha).1
    simp only [execute, ha, Bool.cond_true, Part.map, SourceZeta.zeta_domain, hz]

theorem execute_returns (s a : Nat) (ha : inputCheck s a = true) : ∃ out, out ∈ execute s a :=
  Part.dom_iff_mem.mp ((execute_domain s a).mpr ha)

/-- The literal high-part iota value and the actual source zeta are added
in the genuine new epsilon context. No shifted-collapse equation is assumed. -/
theorem execute_spec (s a out : Nat) (hout : out ∈ execute s a) :
    inputCheck s a = true ∧ Comparison.acceptedCode (Iota.alphaCode s a) out = true ∧
      interpretation (Iota.alphaCode s a) out =
        interpretation (Iota.alphaCode s a) (Iota.literalCode s a (deltaCode a)) +
          SourceZeta.sourceValue s a := by
  have ha := (execute_domain s a).mp (Part.dom_iff_mem.mpr ⟨out, hout⟩)
  have hm : out ∈ (SourceZeta.zeta s a).map (emit s a) := by
    simpa only [execute, ha, Bool.cond_true] using hout
  obtain ⟨d, hd, rfl⟩ := (Part.mem_map_iff (emit s a)).mp hm
  obtain ⟨t, ht, he, hc, hh⟩ := Iota.literalCode_spec s a _ (delta_input s a ha)
  have hi : checkCode (Iota.alphaCode s a) (Iota.literalCode s a (deltaCode a)) = true := by
    simpa only [he, checkCode_code] using hc
  have hz := zetaParameter_spec s a d ha hd
  have hzc : checkCode (Iota.alphaCode s a) (zetaParameter s d).code = true := by
    simpa only [checkCode_code] using hz.1
  have ho := Arithmetic.addCode_spec (Iota.alphaCode s a) _ _ hi hzc
  exact ⟨ha, ho.1, ho.2.1.trans (by rw [interpretation_code, hz.2])⟩

theorem execute_unique (s a out other : Nat) (ho : out ∈ execute s a)
    (he : other ∈ execute s a) : other = out := Part.mem_unique he ho

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Lambda
