import Alexander313.Wilken.HereditaryNativeLambda

/-!
# Recognizing both original proper lambda branches

At the original positive public source, proper theta-zero roots are recognized
by actual weak-normal admission and a nonzero argument. The original high-root
guard is equivalent to the actual root being an epsilon. This derives the
branch test in Definition 2.45, including all proper non-epsilon roots.

The output context of the epsilon branch is the actual new epsilon; the
non-epsilon branch returns in the original context. No temporary-base return,
inverse, height descent or bound for the epsilon branch is claimed here.
Uncompiled proof candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Lambda.Branches

open NativePublicBridge (contextCode contextCode_checked)

def inputCheck (s a : Nat) : Bool := SourceZeta.inputCheck s a &&
  !FixedPoint.zeroCheck (Localization.argumentCode a)

theorem inputCheck_primrec : Primrec₂ inputCheck :=
  (Primrec.and.comp SourceZeta.inputCheck_primrec
    (Primrec.not.comp (FixedPoint.zeroCheck_primrec.comp
      (Localization.argumentCode_primrec.comp Primrec.snd)))).to₂

theorem inputCheck_exact (s a : Nat) : inputCheck s a = true ↔
    ∃ t : RelativeTerm Nat, a = (.theta 0 t).code ∧
      check (contextCode s) (.theta 0 t) = true ∧ Comparison.Normal (contextCode s) t ∧
        base (contextCode s) < denote (contextCode s) (.theta 0 t) := by
  constructor
  · intro ha
    obtain ⟨hz, hnz⟩ := Bool.and_eq_true.mp ha
    obtain ⟨t, he, ht, hn⟩ := (SourceZeta.inputCheck_exact s a).mp hz
    have hi := (SourceChi.theta_argument_parts (contextCode s) 0 t ht hn).1
    have hv : denote (contextCode s) t ≠ 0 := by
      intro hv
      have hh := (FixedPoint.zeroCheck_exact (contextCode s) t.code hi).mpr
        (by simpa only [interpretation_code] using hv)
      have hf : FixedPoint.zeroCheck t.code = false := by
        simpa only [he, Localization.argumentCode_theta, Bool.not_eq_true'] using hnz
      simp only [hf, Bool.false_eq_true] at hh
    exact ⟨t, he, ht, hn, (SourceChi.Arithmetic.proper_theta_zero_iff _ t ht hn).mpr hv⟩
  · rintro ⟨t, rfl, ht, hn, hp⟩
    have hi := (SourceChi.theta_argument_parts (contextCode s) 0 t ht hn).1
    have hv := (SourceChi.Arithmetic.proper_theta_zero_iff _ t ht hn).mp hp
    apply Bool.and_eq_true.mpr
    refine ⟨(SourceZeta.inputCheck_exact s _).mpr ⟨t, rfl, ht, hn⟩, ?_⟩
    simp only [Localization.argumentCode_theta, Bool.not_eq_true']
    cases hz : FixedPoint.zeroCheck t.code with
    | false => rfl
    | true =>
      exact False.elim (hv (by simpa only [interpretation_code] using
        (FixedPoint.zeroCheck_exact (contextCode s) t.code hi).mp hz))

theorem original_input (s a : Nat) (ha : inputCheck s a = true) :
    SourceZeta.inputCheck s a = true := (Bool.and_eq_true.mp ha).1

theorem high_input (s a : Nat) (ha : Iota.rootCheck s a = true) :
    inputCheck s a = true := by
  obtain ⟨t, he, ht, hn, hs⟩ := (Iota.rootCheck_exact s a).mp ha
  apply (inputCheck_exact s a).mpr
  refine ⟨t, he, ht, hn, ?_⟩
  simpa only [he, interpretation_code] using Lambda.root_proper s a ha

/-- Real epsilon classification, using the actual public return of the
original source root. The zero-argument exception is excluded by properness. -/
theorem theta_epsilon_iff (s : Nat) (t : RelativeTerm Nat)
    (ht : check (contextCode s) (.theta 0 t) = true)
    (hn : Comparison.Normal (contextCode s) t)
    (hp : base (contextCode s) < denote (contextCode s) (.theta 0 t)) :
    Ordinal.omega0 ^ denote (contextCode s) (.theta 0 t) =
      denote (contextCode s) (.theta 0 t) ↔ 1 < t.outerSort := by
  have hr := NativePublicReturn.returnTerm_checked s (.theta 0 t) ht
  have hv := NativePublicReturn.returnTerm_denote s (.theta 0 t)
    (checked_admissible _ _ ht).1
  have ha := FixedPoint.checked_theta_argument (contextCode s) 0 t ht
  have hva := NativePublicReturn.returnTerm_denote s t (checked_admissible _ _ ha).1
  have hnz := (SourceChi.Arithmetic.proper_theta_zero_iff _ t ht hn).mp hp
  have he := Epsilon.theta_epsilon_iff (s + 1) 0 (NativePublicReturn.returnTerm s t) hr
  have hroot : Hereditary.denote (s + 1) (.theta 0 (NativePublicReturn.returnTerm s t)) =
      NativeContext.denote (contextCode s) (.theta 0 t) := hv
  rw [hroot, NativePublicReturn.returnTerm_outerSort, hva] at he
  simpa only [Nat.zero_add, hnz, false_and, or_false] using he

theorem high_iff_epsilon (s a : Nat) (ha : inputCheck s a = true) :
    Iota.rootCheck s a = true ↔
      Ordinal.omega0 ^ interpretation (contextCode s) a = interpretation (contextCode s) a := by
  obtain ⟨t, he, ht, hn, hp⟩ := (inputCheck_exact s a).mp ha
  have hz := original_input s a ha
  simp only [Iota.rootCheck, hz, Bool.true_and, decide_eq_true_eq,
    he, Localization.argumentCode_theta, ThetaCourse.rawTree_code, interpretation_code]
  exact (theta_epsilon_iff s t ht hn hp).symm

def outputContext (s a : Nat) : Nat :=
  cond (Iota.rootCheck s a) (Iota.alphaCode s a) (contextCode s)

theorem outputContext_primrec : Primrec₂ outputContext :=
  (Iota.rootCheck_primrec.cond Iota.alphaCode_primrec
    (NativePublicBridge.contextCode_primrec.comp Primrec.fst)).to₂

theorem outputContext_checked (s a : Nat) (ha : inputCheck s a = true) :
    baseCheck (outputContext s a) = true := by
  cases hh : Iota.rootCheck s a with
  | false => simpa only [outputContext, hh, Bool.cond_false] using contextCode_checked s
  | true => simpa only [outputContext, hh, Bool.cond_true] using Iota.alphaCode_baseCheck s a hh

/-- The real value in the two cases of Definition 2.45. -/
noncomputable def sourceValue (s a : Nat) : Ordinal.{0} :=
  if Iota.rootCheck s a = true then
    interpretation (Iota.alphaCode s a) (Iota.literalCode s a (Lambda.deltaCode a)) +
      SourceZeta.sourceValue s a
  else SourceZeta.sourceValue s a

theorem source_definition_2_45 (s a : Nat) (ha : inputCheck s a = true) :
    sourceValue s a =
      if Ordinal.omega0 ^ interpretation (contextCode s) a = interpretation (contextCode s) a then
        interpretation (Iota.alphaCode s a) (Iota.literalCode s a (Lambda.deltaCode a)) +
          SourceZeta.sourceValue s a
      else SourceZeta.sourceValue s a := by
  rw [← high_iff_epsilon s a ha]
  rfl

def execute (s a : Nat) : Part Nat := cond (inputCheck s a)
  (cond (Iota.rootCheck s a) (Lambda.execute s a) (SourceZeta.zeta s a)) Part.none

theorem execute_partrec : Partrec₂ execute :=
  (Partrec.cond inputCheck_primrec.to_comp
    (Partrec.cond Iota.rootCheck_primrec.to_comp Lambda.execute_partrec
      SourceZeta.zeta_partrec) Partrec.none).to₂

theorem execute_domain (s a : Nat) : (execute s a).Dom ↔ inputCheck s a = true := by
  cases ha : inputCheck s a with
  | false => simp only [execute, ha, Bool.cond_false, Part.not_none_dom, Bool.false_eq_true]
  | true =>
    cases hh : Iota.rootCheck s a with
    | false => simp only [execute, ha, hh, Bool.cond_true, Bool.cond_false,
        SourceZeta.zeta_domain, original_input s a ha]
    | true => simp only [execute, ha, hh, Bool.cond_true, Lambda.execute_domain,
        Lambda.inputCheck, hh]

theorem execute_returns (s a : Nat) (ha : inputCheck s a = true) :
    ∃ out, out ∈ execute s a := Part.dom_iff_mem.mp ((execute_domain s a).mpr ha)

theorem execute_spec (s a out : Nat) (ho : out ∈ execute s a) :
    inputCheck s a = true ∧ Comparison.acceptedCode (outputContext s a) out = true ∧
      interpretation (outputContext s a) out = sourceValue s a := by
  have ha := (execute_domain s a).mp (Part.dom_iff_mem.mpr ⟨out, ho⟩)
  cases hh : Iota.rootCheck s a with
  | false =>
    have hz : out ∈ SourceZeta.zeta s a := by
      simpa only [execute, ha, hh, Bool.cond_true, Bool.cond_false] using ho
    have hs := SourceZeta.zeta_spec s a out hz
    exact ⟨ha, by simpa only [outputContext, hh, Bool.cond_false] using hs.2.1,
      by simpa only [outputContext, hh, Bool.cond_false, sourceValue, Bool.false_eq_true,
        if_false] using hs.2.2.2.1⟩
  | true =>
    have hz : out ∈ Lambda.execute s a := by
      simpa only [execute, ha, hh, Bool.cond_true] using ho
    have hs := Lambda.execute_spec s a out hz
    exact ⟨ha, by simpa only [outputContext, hh, Bool.cond_true] using hs.2.1,
      by simpa only [outputContext, hh, Bool.cond_true, sourceValue, if_true] using hs.2.2⟩

/-- All original non-epsilon proper roots use zeta and remain below the root
in the original context. This is the non-epsilon branch of 2.48(b). -/
theorem execute_non_epsilon (s a out : Nat) (ho : out ∈ execute s a)
    (hne : Ordinal.omega0 ^ interpretation (contextCode s) a ≠ interpretation (contextCode s) a) :
    outputContext s a = contextCode s ∧ lowCheckCode (contextCode s) out = true ∧
      interpretation (contextCode s) out = SourceZeta.sourceValue s a ∧
        interpretation (contextCode s) out < interpretation (contextCode s) a := by
  have ha := (execute_spec s a out ho).1
  have hh : Iota.rootCheck s a = false := by
    cases hh : Iota.rootCheck s a with
    | false => rfl
    | true => exact False.elim (hne ((high_iff_epsilon s a ha).mp hh))
  have hz : out ∈ SourceZeta.zeta s a := by
    simpa only [execute, ha, hh, Bool.cond_true, Bool.cond_false] using ho
  have hs := SourceZeta.zeta_spec s a out hz
  exact ⟨by simp only [outputContext, hh, Bool.cond_false], hs.2.2⟩

theorem execute_unique (s a out other : Nat) (ho : out ∈ execute s a)
    (he : other ∈ execute s a) : other = out := Part.mem_unique he ho

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Lambda.Branches
