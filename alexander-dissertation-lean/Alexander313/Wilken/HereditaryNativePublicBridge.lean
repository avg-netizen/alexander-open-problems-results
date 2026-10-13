import Alexander313.Wilken.HereditaryNativeSourceChi
import Alexander313.Wilken.HereditarySourceChi
import Alexander313.Wilken.HereditaryLocalization

/-!
# Original positive public levels as genuine native epsilon contexts

At public level s+1 each atomic parameter is an original low code at level s.
The actual mapParameters operation tags that payload with s, while the native
base is the original public code for finiteBase(s+1). No ordinal recoding or
temporary translation interface is assumed. Denotation agrees even on raw
trees; original admission and every finite fragment agree on the translated
syntax. Native normality is exactly the public local normal-sum condition.
Full hereditary public normality additionally checks earlier payload trees,
so only its preservation into native normality is claimed.

Canonical ANF and actual high/low decomposition agree in VALUE. Their literal
parameter representatives and their independently constructed normalizers
need not agree. The raw adapter explicitly normalizes in the original public
grammar, then translates that constructed normal tree. All proofs remain
uncompiled; this module never executes Lean, Lake or a source oracle.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativePublicBridge

def baseCode (r : Nat) : Nat := Nat.pair r (Localization.baseRaw r)

theorem baseCode_primrec : Primrec baseCode :=
  Primrec₂.natPair.comp Primrec.id Localization.baseRaw_primrec

theorem baseCode_original (r : Nat) : unionCheck (baseCode r) = true := by
  simpa only [baseCode, unionCheck_pair] using
    Localization.node_low r (Localization.baseRaw r) (Localization.baseRaw_node r)

theorem baseCode_value (r : Nat) : NativeContext.base (baseCode r) = finiteBase r := by
  simpa only [NativeContext.base, baseCode, unionInterpretation_pair, Localization.value] using
    Localization.baseRaw_value r

def contextCode (s : Nat) : Nat := baseCode (s + 1)

theorem contextCode_primrec : Primrec contextCode := baseCode_primrec.comp Primrec.succ

theorem contextCode_value (s : Nat) : NativeContext.base (contextCode s) = finiteBase (s + 1) :=
  baseCode_value (s + 1)

theorem contextCode_checked (s : Nat) : NativeContext.baseCheck (contextCode s) = true := by
  apply (NativeContext.baseCheck_exact _).mpr
  exact ⟨baseCode_original (s + 1), by rw [contextCode_value];
    exact finiteBase_succ_omegaPower_eq_self s⟩

def parameterCode (s p : Nat) : Nat := Nat.pair s p

theorem parameterCode_primrec : Primrec₂ parameterCode := Primrec₂.natPair

theorem parameterCode_value (s p : Nat) :
    NativeContext.parameters (parameterCode s p) = parameters (s + 1) p := by
  simp only [NativeContext.parameters, parameterCode, unionInterpretation_pair, parameters_succ]

theorem parameterCode_check (s p : Nat) :
    NativeContext.parameterCheck (contextCode s) (parameterCode s p) = parameterCheck (s + 1) p := by
  apply Bool.eq_iff_iff.mpr
  rw [NativeContext.parameterCheck_exact]
  constructor
  · intro hp
    simpa only [parameterCode, unionCheck_pair, parameterCheck_succ] using hp.1
  · intro hp
    refine ⟨?_, baseCode_original (s + 1), ?_⟩
    · simpa only [parameterCode, unionCheck_pair, parameterCheck_succ] using hp
    · rw [parameterCode_value, contextCode_value]
      exact parameter_sound (s + 1) p hp

def translate (s : Nat) (t : RelativeTerm Nat) : RelativeTerm Nat :=
  t.mapParameters (parameterCode s)

theorem translate_primrec : Primrec₂ translate :=
  mapParameters_primrec parameterCode parameterCode_primrec

@[simp] theorem translate_parameter (s p : Nat) :
    translate s (.parameter p) = .parameter (parameterCode s p) := rfl

@[simp] theorem translate_sum (s : Nat) (a b : RelativeTerm Nat) :
    translate s (.sum a b) = .sum (translate s a) (translate s b) := rfl

@[simp] theorem translate_theta (s k : Nat) (a : RelativeTerm Nat) :
    translate s (.theta k a) = .theta k (translate s a) := rfl

@[simp] theorem translate_size (s : Nat) (t : RelativeTerm Nat) :
    (translate s t).size = t.size := size_mapParameters _ _

@[simp] theorem translate_height (s : Nat) (t : RelativeTerm Nat) :
    (translate s t).height = t.height := height_mapParameters _ _

@[simp] theorem translate_indices (s : Nat) (t : RelativeTerm Nat) :
    (translate s t).indices = t.indices := indices_mapParameters _ _

@[simp] theorem translate_outerSort (s : Nat) (t : RelativeTerm Nat) :
    (translate s t).outerSort = t.outerSort := by
  induction t <;> simp_all only [translate_parameter, translate_sum, translate_theta, outerSort]

theorem translate_eval (s : Nat) (t : RelativeTerm Nat) (theta : Nat → Ordinal.{0} → Ordinal.{0}) :
    (translate s t).eval NativeContext.parameters theta = t.eval (parameters (s + 1)) theta := by
  induction t with
  | parameter p => exact parameterCode_value s p
  | sum a b iha ihb =>
    simpa only [translate_sum, eval] using congrArg₂ (· + ·) iha ihb
  | theta k a ih =>
    simpa only [translate_theta, eval] using congrArg (theta k) ih

theorem translate_denote (s : Nat) (t : RelativeTerm Nat) :
    NativeContext.denote (contextCode s) (translate s t) = denote (s + 1) t := by
  unfold NativeContext.denote denote
  rw [contextCode_value]
  exact translate_eval s t _

theorem translate_finiteDenote (s n : Nat) (t : RelativeTerm Nat) :
    NativeContext.finiteDenote (contextCode s) n (translate s t) = finiteDenote (s + 1) n t := by
  unfold NativeContext.finiteDenote finiteDenote
  rw [contextCode_value]
  exact translate_eval s t _

theorem translate_payloads (s : Nat) (t : RelativeTerm Nat) :
    NativeContext.Payloads (contextCode s) (translate s t) ↔ Payloads (s + 1) t := by
  induction t <;> simp_all only [translate_parameter, translate_sum, translate_theta,
    NativeContext.Payloads, Payloads, parameterCode_check]

theorem translate_finiteCheck (s n : Nat) (t : RelativeTerm Nat) :
    NativeContext.finiteCheck (contextCode s) n (translate s t) = finiteCheck (s + 1) n t := by
  induction t <;> simp_all only [translate_parameter, translate_sum, translate_theta,
    NativeContext.finiteCheck_parameter, NativeContext.finiteCheck_sum,
    NativeContext.finiteCheck_theta, finiteCheck_parameter, finiteCheck_sum,
    finiteCheck_theta, parameterCode_check, translate_outerSort]

theorem translate_admissible (s n : Nat) (t : RelativeTerm Nat) :
    NativeContext.admissible (contextCode s) n (translate s t) ↔ admissible (s + 1) n t := by
  rw [← NativeContext.finiteCheck_exact, translate_finiteCheck, finiteCheck_iff]

theorem translate_check (s : Nat) (t : RelativeTerm Nat) :
    NativeContext.check (contextCode s) (translate s t) = check (s + 1) t := by
  simp only [NativeContext.check, contextCode_checked, Bool.true_and, check,
    SourceOne.PublicCodes.fragment, translate_height, translate_finiteCheck]

/-- Native parameters are atomic; earlier hereditary payload normality is
not recovered by this equivalence. -/
theorem translate_normal_iff (s : Nat) (t : RelativeTerm Nat) :
    NativeContext.Comparison.Normal (contextCode s) (translate s t) ↔
      Theta.GlobalNormalSums (s + 1) t := by
  induction t <;> simp_all only [translate_parameter, translate_sum, translate_theta,
    NativeContext.Comparison.Normal, Theta.GlobalNormalSums, translate_denote]

theorem translate_normal (s : Nat) (t : RelativeTerm Nat) (hn : Theta.Normal (s + 1) t) :
    NativeContext.Comparison.Normal (contextCode s) (translate s t) :=
  (translate_normal_iff s t).mpr hn.«local»

def translateCode (s c : Nat) : Nat := (translate s (ThetaCourse.rawTree c)).code

theorem translateCode_primrec : Primrec₂ translateCode :=
  (code_primrec.comp (translate_primrec.comp Primrec.fst
    (ThetaCourse.rawTree_primrec.comp Primrec.snd))).to₂

@[simp] theorem translateCode_code (s : Nat) (t : RelativeTerm Nat) :
    translateCode s t.code = (translate s t).code := by
  simp only [translateCode, ThetaCourse.rawTree_code]

theorem translateCode_value (s c : Nat) :
    NativeContext.interpretation (contextCode s) (translateCode s c) = interpretation (s + 1) c := by
  rw [translateCode, NativeContext.interpretation_code, translate_denote]
  rfl

theorem translateCode_checked (s c : Nat) (hc : checkCode (s + 1) c = true) :
    NativeContext.checkCode (contextCode s) (translateCode s c) = true := by
  obtain ⟨t, rfl, ht⟩ := (checkCode_iff (s + 1) c).mp hc
  simpa only [translateCode_code, NativeContext.checkCode_code, translate_check] using ht

theorem translateCode_accepted (s c : Nat) (hc : SourceDecomposition.inputCheck (s + 1) c = true) :
    NativeContext.Decomposition.inputCheck (contextCode s) (translateCode s c) = true := by
  have hs := (SourceDecomposition.inputCheck_exact (s + 1) c).mp hc
  apply (NativeContext.Decomposition.inputCheck_exact _ _).mpr
  exact ⟨translateCode_checked s c hs.1, by
    simpa only [translateCode, ThetaCourse.rawTree_code] using
      translate_normal s (ThetaCourse.rawTree c) hs.2⟩

/-- The two actual principal words have equal ordinal entries in order;
no literal equality of their rewrapped public payloads is asserted. -/
theorem word_values (s c : Nat) (hc : SourceDecomposition.inputCheck (s + 1) c = true) :
    (NativeContext.Decomposition.word (translateCode s c)).map (NativeContext.denote (contextCode s)) =
      (SourceDecomposition.word (s + 1) c).map (denote (s + 1)) := by
  rw [(NativeContext.Decomposition.word_spec _ _ (translateCode_accepted s c hc)).2,
    (SourceDecomposition.word_spec _ _ hc).2, translateCode_value]

theorem parts_values (s m c : Nat) (hc : SourceDecomposition.inputCheck (s + 1) c = true) :
    NativeContext.interpretation (contextCode s)
        (NativeContext.Decomposition.highCode m (translateCode s c)) =
      interpretation (s + 1) (SourceDecomposition.highCode (s + 1) m c) ∧
    NativeContext.interpretation (contextCode s)
        (NativeContext.Decomposition.lowCode m (translateCode s c)) =
      interpretation (s + 1) (SourceDecomposition.lowCode (s + 1) m c) := by
  have hn := NativeContext.Decomposition.parts_code_value (contextCode s) m (translateCode s c)
    (translateCode_accepted s c hc)
  have hp := SourceDecomposition.parts_code_value (s + 1) m c hc
  simpa only [contextCode_value, translateCode_value, hp.1, hp.2] using hn

theorem parts_word_values (s m c : Nat) (hc : SourceDecomposition.inputCheck (s + 1) c = true) :
    (NativeContext.Decomposition.highWord m (translateCode s c)).map (NativeContext.denote (contextCode s)) =
      (SourceDecomposition.highWord (s + 1) m c).map (denote (s + 1)) ∧
    (NativeContext.Decomposition.lowWord m (translateCode s c)).map (NativeContext.denote (contextCode s)) =
      (SourceDecomposition.lowWord (s + 1) m c).map (denote (s + 1)) := by
  have hn := NativeContext.Decomposition.parts_anf (contextCode s) m (translateCode s c)
    (translateCode_accepted s c hc)
  have hp := SourceDecomposition.parts_anf (s + 1) m c hc
  have hv := parts_values s m c hc
  rw [hn.1, hp.1, hv.1, hn.2, hp.2, hv.2]
  exact ⟨rfl, rfl⟩

/-- Construct the public normal spelling first, then translate it. -/
def normalizedCode (s c : Nat) : Nat := translateCode s (Theta.Normalization.normalizeCode (s + 1) c)

theorem normalizedCode_primrec : Primrec₂ normalizedCode := by
  have hn := Theta.Normalization.Effective.normalizeCode_primrec.comp
    (Primrec.succ.comp Primrec.fst) Primrec.snd
  exact (translateCode_primrec.comp Primrec.fst hn).to₂

theorem normalizedCode_spec (s c : Nat) (hc : checkCode (s + 1) c = true) :
    NativeContext.Decomposition.inputCheck (contextCode s) (normalizedCode s c) = true ∧
      NativeContext.interpretation (contextCode s) (normalizedCode s c) = interpretation (s + 1) c := by
  have hn := Theta.Normalization.normalizeCode_accepted (s + 1) c hc
  exact ⟨translateCode_accepted s _ hn.1, (translateCode_value s _).trans hn.2⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativePublicBridge
