import Alexander313.Wilken.HereditaryNativePublicBridge
import Alexander313.Wilken.HereditarySourceZetaTransport

/-!
# Executing original-native return at the same positive public epsilon

Each atomic native parameter is an ORIGINAL union code below contextCode s.
Its genuine canonicalization and the existing finite embedding/bounded
lowering algorithm return an admitted normal low payload at public level s.
The native parameter bound supplies every actual conversion caller guard.
The real mapParameters operation therefore returns an original public term
at level s+1 with the same finite/global denotation and constructor sorts.
Native weak normality yields full hereditary public normality because the
returned earlier payloads are themselves normal. Raw input additionally uses
the actual public normalizer after the parameter conversion.

Whole terms can have arbitrary sorts. They are public checkCode/acceptedCode
outputs, and belong to the low public union only under an actual native low
guard. This is a representation conversion at ONE AND THE SAME epsilon;
neither arbitrary-base translation nor independent-normalizer or chi spelling
invariance is asserted. All proof candidates remain uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativePublicReturn

open NativePublicBridge (contextCode contextCode_value contextCode_checked)

def parameterReturn (s p : Nat) : Nat :=
  SourceZeta.Transport.returnCode s (Canonical.canonicalize p)

theorem parameterReturn_primrec : Primrec₂ parameterReturn :=
  (SourceZeta.Transport.returnCode_primrec.comp Primrec.fst
    (Canonical.Effective.canonicalize_primrec.comp Primrec.snd)).to₂

/-- Native payload admission supplies original public admission and the
strict bound needed by every actual bounded lowering call. -/
theorem parameterReturn_spec (s p : Nat)
    (hp : NativeContext.parameterCheck (contextCode s) p = true) :
    Theta.acceptedLowCode s (parameterReturn s p) = true ∧
      interpretation s (parameterReturn s p) = NativeContext.parameters p := by
  have hs := (NativeContext.parameterCheck_exact _ p).mp hp
  have hv := Canonical.canonicalize_value p hs.1
  have hb : unionInterpretation (Canonical.canonicalize p) < finiteBase (s + 1) := by
    rw [hv]
    simpa only [NativeContext.parameters, contextCode_value] using hs.2.2
  have hr := SourceZeta.Transport.returnCode_spec s _ (Canonical.canonicalize_check p hs.1) hb
  exact ⟨hr.1, hr.2.trans hv⟩

theorem parameterReturn_checked (s p : Nat)
    (hp : NativeContext.parameterCheck (contextCode s) p = true) :
    parameterCheck (s + 1) (parameterReturn s p) = true := by
  rw [parameterCheck_succ]
  exact ((Theta.acceptedLowCode_iff s _).mp (parameterReturn_spec s p hp).1).1

theorem parameterReturn_value (s p : Nat)
    (hp : NativeContext.parameterCheck (contextCode s) p = true) :
    parameters (s + 1) (parameterReturn s p) = NativeContext.parameters p := by
  rw [parameters_succ]
  exact (parameterReturn_spec s p hp).2

def returnTerm (s : Nat) (t : RelativeTerm Nat) : RelativeTerm Nat :=
  t.mapParameters (parameterReturn s)

theorem returnTerm_primrec : Primrec₂ returnTerm :=
  mapParameters_primrec parameterReturn parameterReturn_primrec

@[simp] theorem returnTerm_parameter (s p : Nat) :
    returnTerm s (.parameter p) = .parameter (parameterReturn s p) := rfl

@[simp] theorem returnTerm_sum (s : Nat) (a b : RelativeTerm Nat) :
    returnTerm s (.sum a b) = .sum (returnTerm s a) (returnTerm s b) := rfl

@[simp] theorem returnTerm_theta (s k : Nat) (a : RelativeTerm Nat) :
    returnTerm s (.theta k a) = .theta k (returnTerm s a) := rfl

@[simp] theorem returnTerm_size (s : Nat) (t : RelativeTerm Nat) : (returnTerm s t).size = t.size :=
  size_mapParameters _ _

@[simp] theorem returnTerm_height (s : Nat) (t : RelativeTerm Nat) : (returnTerm s t).height = t.height :=
  height_mapParameters _ _

@[simp] theorem returnTerm_indices (s : Nat) (t : RelativeTerm Nat) : (returnTerm s t).indices = t.indices :=
  indices_mapParameters _ _

@[simp] theorem returnTerm_outerSort (s : Nat) (t : RelativeTerm Nat) :
    (returnTerm s t).outerSort = t.outerSort := by
  induction t <;> simp_all only [returnTerm_parameter, returnTerm_sum, returnTerm_theta, outerSort]

theorem returnTerm_eval (s : Nat) (t : RelativeTerm Nat)
    (hp : NativeContext.Payloads (contextCode s) t) (theta : Nat → Ordinal.{0} → Ordinal.{0}) :
    (returnTerm s t).eval (parameters (s + 1)) theta = t.eval NativeContext.parameters theta := by
  revert hp
  induction t with
  | parameter p => intro hp; exact parameterReturn_value s p hp
  | sum a b iha ihb =>
    intro hp
    simpa only [returnTerm_sum, eval] using congrArg₂ (· + ·) (iha hp.1) (ihb hp.2)
  | theta k a ih =>
    intro hp
    simpa only [returnTerm_theta, eval] using congrArg (theta k) (ih hp)

theorem returnTerm_denote (s : Nat) (t : RelativeTerm Nat)
    (hp : NativeContext.Payloads (contextCode s) t) :
    denote (s + 1) (returnTerm s t) = NativeContext.denote (contextCode s) t := by
  unfold denote NativeContext.denote
  rw [contextCode_value]
  exact returnTerm_eval s t hp _

theorem returnTerm_finiteDenote (s n : Nat) (t : RelativeTerm Nat)
    (hp : NativeContext.Payloads (contextCode s) t) :
    finiteDenote (s + 1) n (returnTerm s t) = NativeContext.finiteDenote (contextCode s) n t := by
  unfold finiteDenote NativeContext.finiteDenote
  rw [contextCode_value]
  exact returnTerm_eval s t hp _

theorem returnTerm_finiteCheck (s n : Nat) (t : RelativeTerm Nat)
    (hp : NativeContext.Payloads (contextCode s) t) :
    finiteCheck (s + 1) n (returnTerm s t) = NativeContext.finiteCheck (contextCode s) n t := by
  revert hp
  induction t with
  | parameter p =>
    intro hp
    simp only [returnTerm_parameter, finiteCheck_parameter, NativeContext.finiteCheck_parameter,
      parameterReturn_checked s p hp, hp]
  | sum a b iha ihb =>
    intro hp
    simp only [returnTerm_sum, finiteCheck_sum, NativeContext.finiteCheck_sum, iha hp.1, ihb hp.2]
  | theta k a ih =>
    intro hp
    simp only [returnTerm_theta, finiteCheck_theta, NativeContext.finiteCheck_theta,
      returnTerm_outerSort, ih hp]

theorem returnTerm_admissible (s n : Nat) (t : RelativeTerm Nat)
    (ht : NativeContext.admissible (contextCode s) n t) : admissible (s + 1) n (returnTerm s t) := by
  apply (finiteCheck_iff _ _ _).mp
  rw [returnTerm_finiteCheck s n t ht.1]
  exact (NativeContext.finiteCheck_exact _ n t).mpr ht

theorem returnTerm_checked (s : Nat) (t : RelativeTerm Nat)
    (ht : NativeContext.check (contextCode s) t = true) : check (s + 1) (returnTerm s t) = true :=
  Theta.admitted_checked (returnTerm_admissible s _ t (NativeContext.checked_admissible _ t ht))

/-- Each returned atomic payload is genuinely normal at its earlier level;
this upgrades native local weak normality to full public hereditary normality. -/
theorem returnTerm_normal (s : Nat) (t : RelativeTerm Nat)
    (hp : NativeContext.Payloads (contextCode s) t) (hn : NativeContext.Comparison.Normal (contextCode s) t) :
    Theta.Normal (s + 1) (returnTerm s t) := by
  revert hp hn
  induction t with
  | parameter p =>
    intro hp hn
    apply (Theta.normal_parameter_succ s _).mpr
    exact ((Theta.acceptedLowCode_iff s _).mp (parameterReturn_spec s p hp).1).2
  | sum a b iha ihb =>
    intro hp hn
    apply Theta.Normal.sum (iha hp.1 hn.1) (ihb hp.2 hn.2.1)
    simpa only [returnTerm_sum, returnTerm_denote s (.sum a b) hp,
      returnTerm_denote s a hp.1, returnTerm_denote s b hp.2] using hn.2.2
  | theta k a ih =>
    intro hp hn
    exact (Theta.normal_theta (s + 1) k _).mpr (ih hp hn)

def returnedCode (s c : Nat) : Nat := (returnTerm s (ThetaCourse.rawTree c)).code

theorem returnedCode_primrec : Primrec₂ returnedCode :=
  (code_primrec.comp (returnTerm_primrec.comp Primrec.fst
    (ThetaCourse.rawTree_primrec.comp Primrec.snd))).to₂

@[simp] theorem returnedCode_code (s : Nat) (t : RelativeTerm Nat) :
    returnedCode s t.code = (returnTerm s t).code := by simp only [returnedCode, ThetaCourse.rawTree_code]

theorem returnedCode_checked_value (s c : Nat) (hc : NativeContext.checkCode (contextCode s) c = true) :
    checkCode (s + 1) (returnedCode s c) = true ∧
      interpretation (s + 1) (returnedCode s c) = NativeContext.interpretation (contextCode s) c := by
  obtain ⟨t, rfl, ht⟩ := (NativeContext.checkCode_exact _ c).mp hc
  have hp := (NativeContext.checked_admissible _ t ht).1
  simpa only [returnedCode_code, checkCode_code, interpretation_code, NativeContext.interpretation_code] using
    And.intro (returnTerm_checked s t ht) (returnTerm_denote s t hp)

theorem returnedCode_normal_spec (s c : Nat)
    (hc : NativeContext.Comparison.acceptedCode (contextCode s) c = true) :
    Theta.acceptedCode (s + 1) (returnedCode s c) = true ∧
      interpretation (s + 1) (returnedCode s c) = NativeContext.interpretation (contextCode s) c := by
  have hs := (NativeContext.Comparison.acceptedCode_exact _ c).mp hc
  have hv := returnedCode_checked_value s c hs.1
  obtain ⟨t, rfl, ht⟩ := (NativeContext.checkCode_exact _ c).mp hs.1
  have hp := (NativeContext.checked_admissible _ t ht).1
  have hn : NativeContext.Comparison.Normal (contextCode s) t := by
    simpa only [ThetaCourse.rawTree_code] using hs.2
  exact ⟨(Theta.acceptedCode_iff _ _).mpr ⟨hv.1, by
    simpa only [returnedCode_code, ThetaCourse.rawTree_code] using returnTerm_normal s t hp hn⟩, hv.2⟩

theorem returnedCode_low (s c : Nat) (hc : NativeContext.lowCheckCode (contextCode s) c = true) :
    lowCheckCode (s + 1) (returnedCode s c) = true := by
  obtain ⟨t, rfl, ht⟩ := (NativeContext.lowCheckCode_exact _ c).mp hc
  have hs := Bool.and_eq_true.mp ht
  simp only [returnedCode_code, lowCheckCode_code, lowCheck, returnTerm_checked s t hs.1,
    returnTerm_outerSort, Bool.true_and]
  exact hs.2

theorem returnedCode_normal_low_spec (s c : Nat)
    (hc : NativeContext.Comparison.acceptedCode (contextCode s) c = true)
    (hl : NativeContext.lowCheckCode (contextCode s) c = true) :
    Theta.acceptedLowCode (s + 1) (returnedCode s c) = true ∧
      interpretation (s + 1) (returnedCode s c) = NativeContext.interpretation (contextCode s) c := by
  have hs := returnedCode_normal_spec s c hc
  exact ⟨(Theta.acceptedLowCode_iff _ _).mpr
    ⟨returnedCode_low s c hl, ((Theta.acceptedCode_iff _ _).mp hs.1).2⟩, hs.2⟩

/-- Raw admission is normalized in the real public grammar AFTER payload return. -/
def rawReturnCode (s c : Nat) : Nat := Theta.Normalization.normalizeCode (s + 1) (returnedCode s c)

theorem rawReturnCode_primrec : Primrec₂ rawReturnCode :=
  (Theta.Normalization.Effective.normalizeCode_primrec.comp (Primrec.succ.comp Primrec.fst)
    returnedCode_primrec).to₂

theorem rawReturnCode_spec (s c : Nat) (hc : NativeContext.checkCode (contextCode s) c = true) :
    Theta.acceptedCode (s + 1) (rawReturnCode s c) = true ∧
      interpretation (s + 1) (rawReturnCode s c) = NativeContext.interpretation (contextCode s) c := by
  have hs := returnedCode_checked_value s c hc
  have hn := Theta.Normalization.normalizeCode_accepted (s + 1) _ hs.1
  exact ⟨hn.1, hn.2.trans hs.2⟩

theorem rawReturnCode_low_spec (s c : Nat) (hc : NativeContext.lowCheckCode (contextCode s) c = true) :
    Theta.acceptedLowCode (s + 1) (rawReturnCode s c) = true ∧
      interpretation (s + 1) (rawReturnCode s c) = NativeContext.interpretation (contextCode s) c := by
  have hn := Theta.Normalization.normalizeCode_acceptedLow (s + 1) _ (returnedCode_low s c hc)
  have hi := (Bool.and_eq_true.mp hc).1
  exact ⟨hn.1, hn.2.trans (returnedCode_checked_value s c hi).2⟩

theorem rawReturnCode_union (s c : Nat) (hc : NativeContext.lowCheckCode (contextCode s) c = true) :
    unionCheck (Nat.pair (s + 1) (rawReturnCode s c)) = true ∧
      unionInterpretation (Nat.pair (s + 1) (rawReturnCode s c)) = NativeContext.interpretation (contextCode s) c := by
  have hs := rawReturnCode_low_spec s c hc
  simpa only [unionCheck_pair, unionInterpretation_pair] using
    And.intro ((Theta.acceptedLowCode_iff _ _).mp hs.1).1 hs.2

end Alexander313.Wilken.RelativeTerm.Hereditary.NativePublicReturn
