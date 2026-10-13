import Alexander313.Wilken.HereditaryNativeBoundedPublicReturnCodes
import Alexander313.Wilken.HereditaryNativeLambdaRawAlphaPlus

/-!
# Genuine public execution of both lambda branches and raw mu

The epsilon lambda branch uses the full proved bounded SAME-value converter.
The non-epsilon branch uses the actual source LOW return. Raw wrappers compute
the real original normalizer before these conversions; their domains remain
the ORIGINAL execution guards. No Normal, hidden-call, elementary-fragment,
selected-context or supplied-return guard is added. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.BoundedPublicReturn

open NativePublicBridge (contextCode)

/-- Actual selected-branch public code, with no independent branch oracle. -/
def lambdaCode (s a out : Nat) : Nat := cond (Iota.rootCheck s a)
  (publicCode s a out) (Canonical.canonicalize (LowArithmetic.publicCode s out))

theorem lambdaCode_primrec : Primrec
    (fun p : (Nat × Nat) × Nat => lambdaCode p.1.1 p.1.2 p.2) :=
  (Iota.rootCheck_primrec.comp (Primrec.fst.comp Primrec.fst)
    (Primrec.snd.comp Primrec.fst)).cond publicCode_primrec
      (Canonical.Effective.canonicalize_primrec.comp
        (LowArithmetic.publicCode_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd))

theorem lambdaCode_spec (s a out : Nat) (ho : out ∈ Lambda.Branches.execute s a) :
    Canonical.check (lambdaCode s a out) = true ∧
      unionInterpretation (lambdaCode s a out) =
        interpretation (Lambda.Branches.outputContext s a) out := by
  have ha := (Lambda.Branches.execute_spec s a out ho).1
  cases hh : Iota.rootCheck s a with
  | true =>
    have hl : out ∈ Lambda.execute s a := by
      simpa only [Lambda.Branches.execute, ha, hh, Bool.cond_true] using ho
    simpa only [lambdaCode, hh, Bool.cond_true, Lambda.Branches.outputContext] using
      lambda_public_spec s a out hl
  | false =>
    have hz : out ∈ SourceZeta.zeta s a := by
      simpa only [Lambda.Branches.execute, ha, hh, Bool.cond_true, Bool.cond_false] using ho
    have hs := SourceZeta.zeta_spec s a out hz
    have hp := LowArithmetic.publicCode_spec s out hs.2.2.1
    refine ⟨by simpa only [lambdaCode, hh, Bool.cond_false] using
      Canonical.canonicalize_check _ hp.1, ?_⟩
    simpa only [lambdaCode, hh, Bool.cond_false, Lambda.Branches.outputContext] using
      (Canonical.canonicalize_value _ hp.1).trans hp.2

/-- Both original normal lambda branches now execute canonical SAME-value
public output, using their already proved original partial execution. -/
def lambdaPublic (s a : Nat) : Part Nat :=
  (Lambda.Branches.execute s a).map (lambdaCode s a)

theorem lambdaPublic_partrec : Partrec₂ lambdaPublic :=
  (Partrec.map Lambda.Branches.execute_partrec lambdaCode_primrec.to_comp.to₂).to₂

theorem lambdaPublic_domain (s a : Nat) :
    (lambdaPublic s a).Dom ↔ Lambda.Branches.inputCheck s a = true := by
  simpa only [lambdaPublic, Part.map] using Lambda.Branches.execute_domain s a

theorem lambdaPublic_graph (s a out : Nat) : out ∈ lambdaPublic s a ↔
    ∃ nativeOut ∈ Lambda.Branches.execute s a, lambdaCode s a nativeOut = out :=
  Part.mem_map_iff (lambdaCode s a)

theorem lambdaPublic_spec (s a out : Nat) (ho : out ∈ lambdaPublic s a) :
    Lambda.Branches.inputCheck s a = true ∧ Canonical.check out = true ∧
      unionInterpretation out = Lambda.Branches.sourceValue s a := by
  obtain ⟨nativeOut, hn, rfl⟩ := (lambdaPublic_graph s a out).mp ho
  have hn' := Lambda.Branches.execute_spec s a nativeOut hn
  have hp := lambdaCode_spec s a nativeOut hn
  exact ⟨hn'.1, hp.1, hp.2.trans hn'.2.2⟩

def rawLambdaCode (s a out : Nat) : Nat :=
  lambdaCode s (Lambda.Branches.Raw.normalizedRoot s a) out

theorem rawLambdaCode_primrec : Primrec
    (fun p : (Nat × Nat) × Nat => rawLambdaCode p.1.1 p.1.2 p.2) :=
  lambdaCode_primrec.comp
    (((Primrec.fst.comp Primrec.fst).pair
      (Lambda.Branches.Raw.normalizedRoot_primrec.comp Primrec.fst)).pair Primrec.snd)

theorem rawLambdaCode_spec (s a out : Nat) (ho : out ∈ Lambda.Branches.Raw.execute s a) :
    Canonical.check (rawLambdaCode s a out) = true ∧
      unionInterpretation (rawLambdaCode s a out) =
        interpretation (Lambda.Branches.outputContext s (Lambda.Branches.Raw.normalizedRoot s a)) out := by
  have ha := (Lambda.Branches.Raw.execute_spec s a out ho).1
  have hn : out ∈ Lambda.Branches.execute s (Lambda.Branches.Raw.normalizedRoot s a) := by
    simpa only [Lambda.Branches.Raw.execute, ha, Bool.cond_true] using ho
  exact lambdaCode_spec s _ out hn

def rawLambdaPublic (s a : Nat) : Part Nat :=
  (Lambda.Branches.Raw.execute s a).map (rawLambdaCode s a)

theorem rawLambdaPublic_partrec : Partrec₂ rawLambdaPublic :=
  (Partrec.map Lambda.Branches.Raw.execute_partrec rawLambdaCode_primrec.to_comp.to₂).to₂

theorem rawLambdaPublic_domain (s a : Nat) :
    (rawLambdaPublic s a).Dom ↔ Lambda.Branches.Raw.inputCheck s a = true := by
  simpa only [rawLambdaPublic, Part.map] using Lambda.Branches.Raw.execute_domain s a

theorem rawLambdaPublic_domain_original (s a : Nat) : (rawLambdaPublic s a).Dom ↔
    ∃ t : RelativeTerm Nat, a = (.theta 0 t).code ∧
      check (contextCode s) (.theta 0 t) = true ∧
        base (contextCode s) < denote (contextCode s) (.theta 0 t) := by
  rw [rawLambdaPublic_domain, Lambda.Branches.Raw.inputCheck_exact]

theorem rawLambdaPublic_graph (s a out : Nat) : out ∈ rawLambdaPublic s a ↔
    ∃ nativeOut ∈ Lambda.Branches.Raw.execute s a, rawLambdaCode s a nativeOut = out :=
  Part.mem_map_iff (rawLambdaCode s a)

theorem rawLambdaPublic_spec (s a out : Nat) (ho : out ∈ rawLambdaPublic s a) :
    Lambda.Branches.Raw.inputCheck s a = true ∧ Canonical.check out = true ∧
      unionInterpretation out =
        Lambda.Branches.sourceValue s (Lambda.Branches.Raw.normalizedRoot s a) := by
  obtain ⟨nativeOut, hn, rfl⟩ := (rawLambdaPublic_graph s a out).mp ho
  have hn' := Lambda.Branches.Raw.execute_spec s a nativeOut hn
  have hp := rawLambdaCode_spec s a nativeOut hn
  exact ⟨hn'.1, hp.1, hp.2.trans hn'.2.2⟩

def muPublic (s a : Nat) : Part Nat := (Mu.execute s a).map (publicCode s a)

theorem muPublic_partrec : Partrec₂ muPublic :=
  (Partrec.map Mu.execute_partrec publicCode_primrec.to_comp.to₂).to₂

theorem muPublic_domain (s a : Nat) : (muPublic s a).Dom ↔ Mu.inputCheck s a = true := by
  simpa only [muPublic, Part.map] using Mu.execute_domain s a

theorem muPublic_graph (s a out : Nat) : out ∈ muPublic s a ↔
    ∃ nativeOut ∈ Mu.execute s a, publicCode s a nativeOut = out :=
  Part.mem_map_iff (publicCode s a)

theorem muPublic_spec (s a out : Nat) (ho : out ∈ muPublic s a) :
    Mu.inputCheck s a = true ∧ Canonical.check out = true ∧
      unionInterpretation out = Mu.sourceValue s a := by
  obtain ⟨nativeOut, hn, rfl⟩ := (muPublic_graph s a out).mp ho
  have hn' := Mu.execute_spec s a nativeOut hn
  have hp := mu_public_spec s a nativeOut hn
  exact ⟨hn'.1, hp.1, hp.2.trans hn'.2.2.2⟩

/-- The concrete raw-mu conversion uses the genuinely computed normalized
root; the original raw-mu execution itself supplies its complete caller. -/
def rawMuCode (s a out : Nat) : Nat := publicCode s (Mu.Raw.normalizedRoot s a) out

theorem rawMuCode_primrec : Primrec
    (fun p : (Nat × Nat) × Nat => rawMuCode p.1.1 p.1.2 p.2) :=
  publicCode_primrec.comp
    (((Primrec.fst.comp Primrec.fst).pair
      (Lambda.Branches.Raw.normalizedRoot_primrec.comp Primrec.fst)).pair Primrec.snd)

theorem rawMuCode_caller (s a out : Nat) (ho : out ∈ Mu.Raw.execute s a) :
    inputCheck s (Mu.Raw.normalizedRoot s a) out = true := by
  obtain ⟨ha, rfl⟩ := (Mu.Raw.execute_graph s a out).mp ho
  have hs := Bool.and_eq_true.mp ha
  have hn : Mu.muCode s (Mu.Raw.normalizedRoot s a) ∈ Mu.execute s (Mu.Raw.normalizedRoot s a) :=
    (Mu.execute_graph s _ _).mpr ⟨hs.2, rfl⟩
  simpa only [Mu.Raw.muCode, ha, Bool.cond_true] using mu_caller s _ _ hn

theorem rawMuCode_spec (s a out : Nat) (ho : out ∈ Mu.Raw.execute s a) :
    Canonical.check (rawMuCode s a out) = true ∧
      unionInterpretation (rawMuCode s a out) = interpretation (Mu.Raw.outputContext s a) out :=
  publicCode_spec s _ out (rawMuCode_caller s a out ho)

def rawMuPublic (s a : Nat) : Part Nat := (Mu.Raw.execute s a).map (rawMuCode s a)

theorem rawMuPublic_partrec : Partrec₂ rawMuPublic :=
  (Partrec.map Mu.Raw.execute_partrec rawMuCode_primrec.to_comp.to₂).to₂

theorem rawMuPublic_domain (s a : Nat) :
    (rawMuPublic s a).Dom ↔ Mu.Raw.inputCheck s a = true := by
  simpa only [rawMuPublic, Part.map] using Mu.Raw.execute_domain s a

theorem rawMuPublic_domain_original (s a : Nat) : (rawMuPublic s a).Dom ↔
    (∃ t : RelativeTerm Nat, a = (.theta 0 t).code ∧
      check (contextCode s) (.theta 0 t) = true ∧
        base (contextCode s) < denote (contextCode s) (.theta 0 t)) ∧
      Ordinal.omega0 ^ interpretation (contextCode s) a = interpretation (contextCode s) a := by
  rw [rawMuPublic_domain, Mu.Raw.inputCheck_exact]

theorem rawMuPublic_graph (s a out : Nat) : out ∈ rawMuPublic s a ↔
    ∃ nativeOut ∈ Mu.Raw.execute s a, rawMuCode s a nativeOut = out :=
  Part.mem_map_iff (rawMuCode s a)

theorem rawMuPublic_spec (s a out : Nat) (ho : out ∈ rawMuPublic s a) :
    Mu.Raw.inputCheck s a = true ∧ Canonical.check out = true ∧
      unionInterpretation out = Mu.sourceValue s (Mu.Raw.normalizedRoot s a) := by
  obtain ⟨nativeOut, hn, rfl⟩ := (rawMuPublic_graph s a out).mp ho
  have hn' := Mu.Raw.execute_spec s a nativeOut hn
  have hp := rawMuCode_spec s a nativeOut hn
  exact ⟨hn'.1, hp.1, hp.2.trans hn'.2.2.2⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.BoundedPublicReturn
