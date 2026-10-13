import Alexander313.Wilken.SourceOneNativeBoundedPublicReturn

/-!
# Exact original source-one bounded SAME-value return guard

The finite SAME-index presentation computes the genuine Delta enclosure.
The real alpha comparator therefore tests exactly the original raw LOW
interval below ORIGINAL source alpha-plus. No target Normality or hidden
support guard is added. Real lambda and mu executions supply every caller.
Uncompiled source candidates; Program packaging is separate.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.BoundedPublicReturn

def unshiftedThetaState (a k : Nat) (x : SourceOneIota.State) : SourceOneIota.State :=
  let t := RelativeTerm.theta k x.2.1
  (a, (t, cond (small a t) (.parameter (parameterCode t)) (.theta k x.2.2)))

theorem unshiftedThetaState_primrec : Primrec
    (fun p : Nat × (Nat × SourceOneIota.State) => unshiftedThetaState p.1 p.2.1 p.2.2) := by
  have hk : Primrec (fun p : Nat × (Nat × SourceOneIota.State) => p.2.1) := Primrec.fst.comp Primrec.snd
  have ht : Primrec (fun p : Nat × (Nat × SourceOneIota.State) => RelativeTerm.theta p.2.1 p.2.2.2.1) :=
    theta_primrec.comp hk (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hs := small_primrec.comp Primrec.fst ht
  have hp := parameter_primrec.comp (parameterCode_primrec.comp ht)
  have ho := theta_primrec.comp hk (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  exact Primrec.fst.pair (ht.pair (hs.cond hp ho))

def unshiftedStateCode (a c : Nat) : SourceOneIota.State := ValueFold.code
  SourceOneIota.parameterState SourceOneIota.sumState unshiftedThetaState
  (0, (.parameter 0, .parameter 0)) a c

theorem unshiftedStateCode_primrec : Primrec₂ unshiftedStateCode :=
  ValueFold.code_primrec SourceOneIota.parameterState SourceOneIota.sumState unshiftedThetaState
    (0, (.parameter 0, .parameter 0)) SourceOneIota.parameterState_primrec
    SourceOneIota.sumState_primrec unshiftedThetaState_primrec

theorem unshiftedStateCode_code (a : Nat) (t : RelativeTerm Nat) :
    unshiftedStateCode a t.code = (a, (t, unshifted a t)) := by
  rw [unshiftedStateCode, ValueFold.code_term]
  induction t <;> simp_all only [ValueFold.term, SourceOneIota.parameterState, SourceOneIota.sumState,
    unshiftedThetaState, unshifted]

def enclosureCode (a : Nat) : Nat :=
  (.theta 0 (unshiftedStateCode a (Lambda.deltaCode a)).2.2 : RelativeTerm Nat).code

theorem enclosureCode_primrec : Primrec enclosureCode :=
  code_primrec.comp (theta_primrec.comp (Primrec.const 0)
    (Primrec.snd.comp (Primrec.snd.comp
      (unshiftedStateCode_primrec.comp Primrec.id Lambda.deltaCode_primrec))))

theorem enclosureCode_eq (a : Nat) : enclosureCode a = (Enclosure.deltaEnclosureTerm a).code := by
  rw [enclosureCode, show Lambda.deltaCode a = (Enclosure.deltaTerm a).code from rfl,
    unshiftedStateCode_code]
  rfl

def inputCheck (a c : Nat) : Bool :=
  (rootCheck a && NativeContext.lowCheckCode (alphaCode a) c) &&
    NativeContext.Normalization.lessRawCode (alphaCode a) c (enclosureCode a)

theorem inputCheck_primrec : Primrec₂ inputCheck := by
  have ha := Primrec.fst
  have hα := alphaCode_primrec.comp ha
  have hc := NativeContext.lowCheckCode_primrec.comp hα Primrec.snd
  have he := enclosureCode_primrec.comp ha
  exact (Primrec.and.comp (Primrec.and.comp (rootCheck_primrec.comp ha) hc)
    (NativeContext.Normalization.Effective.lessRawCode_primrec.comp
      (hα.pair (Primrec.snd.pair he)))).to₂

theorem inputCheck_exact (a c : Nat) : inputCheck a c = true ↔
    rootCheck a = true ∧ NativeContext.lowCheckCode (alphaCode a) c = true ∧
      NativeContext.interpretation (alphaCode a) c < Enclosure.sourceAlphaPlus a := by
  constructor
  · intro h
    obtain ⟨hfirst, hless⟩ := Bool.and_eq_true.mp h
    obtain ⟨ha, hc⟩ := Bool.and_eq_true.mp hfirst
    have hs := (NativeContext.Normalization.lessRawCode_exact _ _ _).mp hless
    refine ⟨ha, hc, ?_⟩
    simpa only [enclosureCode_eq, NativeContext.interpretation_code,
      Enclosure.delta_enclosure_eq_sourceAlphaPlus a ha] using hs.2.2
  · rintro ⟨ha, hc, hb⟩
    have he := Enclosure.delta_enclosure_spec a ha
    have hech : NativeContext.checkCode (alphaCode a) (enclosureCode a) = true := by
      simpa only [enclosureCode_eq, NativeContext.checkCode_code] using he.1
    refine Bool.and_eq_true.mpr ⟨Bool.and_eq_true.mpr ⟨ha, hc⟩, ?_⟩
    apply (NativeContext.Normalization.lessRawCode_exact _ _ _).mpr
    refine ⟨(Bool.and_eq_true.mp hc).1, hech, ?_⟩
    simpa only [enclosureCode_eq, NativeContext.interpretation_code,
      Enclosure.delta_enclosure_eq_sourceAlphaPlus a ha] using hb

def publicCode (a c : Nat) : Nat := cond (inputCheck a c) (rawPublicCode a c) 0

theorem publicCode_primrec : Primrec₂ publicCode :=
  (inputCheck_primrec.cond rawPublicCode_primrec (Primrec.const 0)).to₂

theorem publicCode_spec (a c : Nat) (hi : inputCheck a c = true) :
    Canonical.check (publicCode a c) = true ∧
      unionInterpretation (publicCode a c) = NativeContext.interpretation (alphaCode a) c := by
  have hs := (inputCheck_exact a c).mp hi
  simpa only [publicCode, hi, Bool.cond_true] using rawPublicCode_spec a c hs.1 hs.2.1 hs.2.2

theorem publicCode_rejected (a c : Nat) (hi : inputCheck a c = false) : publicCode a c = 0 := by
  simp only [publicCode, hi, Bool.cond_false]

def execute (a c : Nat) : Part Nat := cond (inputCheck a c) (Part.some (publicCode a c)) Part.none

theorem execute_partrec : Partrec₂ execute :=
  (Partrec.cond inputCheck_primrec.to_comp publicCode_primrec.to_comp.partrec Partrec.none).to₂

theorem execute_dom (a c : Nat) : (execute a c).Dom ↔ inputCheck a c = true := by
  cases h : inputCheck a c <;> simp [execute, h]

theorem execute_graph (a c out : Nat) : out ∈ execute a c ↔
    inputCheck a c = true ∧ out = publicCode a c := by
  cases h : inputCheck a c <;> simp [execute, h]

theorem execute_spec (a c out : Nat) (ho : out ∈ execute a c) :
    Canonical.check out = true ∧ unionInterpretation out = NativeContext.interpretation (alphaCode a) c := by
  obtain ⟨hi, rfl⟩ := (execute_graph a c out).mp ho
  exact publicCode_spec a c hi

def graphBool (a c out : Nat) : Bool := inputCheck a c && (out == publicCode a c)

theorem graphBool_primrec : Primrec
    (fun p : (Nat × Nat) × Nat => graphBool p.1.1 p.1.2 p.2) :=
  Primrec.and.comp (inputCheck_primrec.comp Primrec.fst)
    (Primrec.beq.comp Primrec.snd (publicCode_primrec.comp Primrec.fst))

theorem graphBool_exact (a c out : Nat) : graphBool a c out = true ↔ out ∈ execute a c := by
  rw [execute_graph]
  simp only [graphBool, Bool.and_eq_true, beq_iff_eq]

theorem lambda_caller (a out : Nat) (ho : out ∈ Lambda.execute a) : inputCheck a out = true := by
  have hs := Lambda.execute_spec a out ho
  exact (inputCheck_exact a out).mpr ⟨hs.1, Enclosure.lambda_low a out ho,
    Enclosure.source_lemma_2_48_b a out ho⟩

theorem lambda_public_spec (a out : Nat) (ho : out ∈ Lambda.execute a) :
    Canonical.check (publicCode a out) = true ∧
      unionInterpretation (publicCode a out) = NativeContext.interpretation (alphaCode a) out :=
  publicCode_spec a out (lambda_caller a out ho)

theorem raw_lambda_caller (a out : Nat) (ho : out ∈ Lambda.Raw.execute a) :
    inputCheck (Lambda.Raw.normalizedRoot a) out = true := by
  have hs := (Lambda.Raw.execute_graph a out).mp ho
  exact lambda_caller _ out hs.2

theorem raw_lambda_public_spec (a out : Nat) (ho : out ∈ Lambda.Raw.execute a) :
    Canonical.check (publicCode (Lambda.Raw.normalizedRoot a) out) = true ∧
      unionInterpretation (publicCode (Lambda.Raw.normalizedRoot a) out) =
        NativeContext.interpretation (Lambda.Raw.outputContext a) out :=
  publicCode_spec _ out (raw_lambda_caller a out ho)

theorem mu_caller (a out : Nat) (ho : out ∈ Mu.execute a) : inputCheck a out = true := by
  have hs := Mu.execute_spec a out ho
  exact (inputCheck_exact a out).mpr ⟨hs.1, hs.2.1, Mu.Bounds.execute_lt_source_alphaPlus a out ho⟩

theorem mu_public_spec (a out : Nat) (ho : out ∈ Mu.execute a) :
    Canonical.check (publicCode a out) = true ∧
      unionInterpretation (publicCode a out) = NativeContext.interpretation (alphaCode a) out :=
  publicCode_spec a out (mu_caller a out ho)

theorem raw_mu_caller (a out : Nat) (ho : out ∈ Mu.Raw.execute a) :
    inputCheck (Mu.Raw.normalizedRoot a) out = true := by
  obtain ⟨ha, rfl⟩ := (Mu.Raw.execute_graph a out).mp ho
  have hn := (Bool.and_eq_true.mp ha).2
  have hm : Mu.muCode (Mu.Raw.normalizedRoot a) ∈ Mu.execute (Mu.Raw.normalizedRoot a) :=
    (Mu.execute_graph _ _).mpr ⟨hn, rfl⟩
  simpa only [Mu.Raw.muCode, ha, Bool.cond_true] using
    mu_caller _ _ hm

theorem raw_mu_public_spec (a out : Nat) (ho : out ∈ Mu.Raw.execute a) :
    Canonical.check (publicCode (Mu.Raw.normalizedRoot a) out) = true ∧
      unionInterpretation (publicCode (Mu.Raw.normalizedRoot a) out) =
        NativeContext.interpretation (Mu.Raw.outputContext a) out :=
  publicCode_spec _ out (raw_mu_caller a out ho)

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.BoundedPublicReturn
