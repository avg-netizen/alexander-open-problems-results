import Alexander313.Wilken.PublicEpsilonNativeUnboundedLambdaSupport
import Alexander313.Wilken.PublicEpsilonNativeUnboundedLambdaSource

/-!
# Actual beta-context lambda and the complete source3.14(a) equality

The actual full-domain iota divided head is added to the public return of
the real source zeta. Both LOW callers and the actual source zeta bound
are derived from the unchanged original ANY-q high-root guard. The true
rho(mu)=iotaDelta identity identifies the executing lambda with rho(mu)
plus zeta. This is a beta-context producer; original-source Par/pi output
is proved separately by its provenance construction. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.Lambda

def emit (q root out : Nat) : Nat := Arithmetic.addCode (betaCode q root)
  (literalCode q root (deltaCode root)) (zetaParameter q out).code

theorem emit_primrec : Primrec (fun p : Context × Nat => emit p.1.1 p.1.2 p.2) := by
  have hq : Primrec (fun p : Context × Nat => p.1.1) := Primrec.fst.comp Primrec.fst
  have hr : Primrec (fun p : Context × Nat => p.1.2) := Primrec.snd.comp Primrec.fst
  have hbeta := betaCode_primrec.comp hq hr
  have hdelta := Primrec.comp literalCode_primrec
    (Primrec.fst.pair (OmegaQuotient.deltaCode_primrec.comp hr))
  have hz := code_primrec.comp (zetaParameter_primrec.comp hq Primrec.snd)
  exact Arithmetic.addCode_primrec.comp (hbeta.pair (hdelta.pair hz))

noncomputable def sourceValue (q root : Nat) : Ordinal.{0} :=
  interpretation (betaCode q root) (literalCode q root (deltaCode root)) +
    DirectZeta.sourceValue q root

theorem emit_spec (q root out : Nat) (ha : inputCheck q root = true)
    (ho : out ∈ DirectZeta.execute q root) :
    lowCheckCode (betaCode q root) (emit q root out) = true ∧
      Comparison.acceptedCode (betaCode q root) (emit q root out) = true ∧
      interpretation (betaCode q root) (emit q root out) = sourceValue q root := by
  have hd := literalCode_accepted q root _ (delta_input q root ha)
  have hz := zetaParameter_spec q root out ha ho
  have hs := Arithmetic.addCode_spec (betaCode q root) _ _
    ((Comparison.acceptedCode_exact _ _).mp hd).1
    (by simpa only [checkCode_code] using hz.1)
  have hl := OmegaPowerHeight.addCode_low_height (betaCode q root) _ _
    (literalDelta_low q root ha) hz.2.1
  exact ⟨hl.1, hs.1, hs.2.1.trans (by
    rw [interpretation_code, hz.2.2]; rfl)⟩

def execute (q root : Nat) : Part Nat := cond (inputCheck q root)
  ((DirectZeta.execute q root).map (emit q root)) Part.none

theorem execute_partrec : Partrec (fun p : Context => execute p.1 p.2) :=
  Partrec.cond inputCheck_primrec.to_comp
    (Partrec.map DirectZeta.execute_partrec emit_primrec.to_comp.to₂) Partrec.none

theorem execute_domain (q root : Nat) : (execute q root).Dom ↔ inputCheck q root = true := by
  cases hi : inputCheck q root with
  | false => simp only [execute, hi, Bool.cond_false, Part.not_none_dom, Bool.false_eq_true]
  | true => simp only [execute, hi, Bool.cond_true, Part.map, DirectZeta.execute_domain,
      zeta_input q root hi]

theorem execute_returns (q root : Nat) (ha : inputCheck q root = true) :
    ∃ out, out ∈ execute q root := Part.dom_iff_mem.mp ((execute_domain q root).mpr ha)

theorem execute_spec (q root out : Nat) (ho : out ∈ execute q root) :
    inputCheck q root = true ∧ lowCheckCode (betaCode q root) out = true ∧
      Comparison.acceptedCode (betaCode q root) out = true ∧
      interpretation (betaCode q root) out = sourceValue q root := by
  have ha := (execute_domain q root).mp (Part.dom_iff_mem.mpr ⟨out, ho⟩)
  have hm : out ∈ (DirectZeta.execute q root).map (emit q root) := by
    simpa only [execute, ha, Bool.cond_true] using ho
  obtain ⟨z, hz, rfl⟩ := (Part.mem_map_iff (emit q root)).mp hm
  exact ⟨ha, emit_spec q root z ha hz⟩

/-- Original-source provenance and the actual beta-context output have
the SAME lambda value; this does not identify their code spellings. -/
theorem execute_source_value (q root out sourceOut : Nat) (ho : out ∈ execute q root)
    (hs : sourceOut ∈ LambdaSource.execute q root) :
    interpretation (betaCode q root) out = interpretation q sourceOut :=
  (execute_spec q root out ho).2.2.2.trans (LambdaSource.execute_spec q root sourceOut hs).2.2.2.symm

theorem execute_product (q root out : Nat) (ho : out ∈ execute q root) :
    interpretation (betaCode q root) out = base (betaCode q root) *
      (interpretation (betaCode q root) (Mu.mappedCoefficient q root) +
        (OmegaQuotient.coefficientOffset q root : Ordinal.{0})) + DirectZeta.sourceValue q root := by
  have hs := execute_spec q root out ho
  rw [hs.2.2.2, sourceValue, MappedOmegaQuotient.literal_delta_coefficient_product q root hs.1]
  rfl

/-- The complete printed3.14(a) hence equation uses actual executions
of lambda, mu and rho, without inferring numerical spelling equality. -/
theorem source_lemma_3_14_a_lambda (q root lambdaOut rhoOut : Nat)
    (hl : lambdaOut ∈ execute q root)
    (hr : rhoOut ∈ SourceRho.Uniform.execute (betaCode q root) (Mu.muCode q root)) :
    interpretation (betaCode q root) lambdaOut =
      interpretation (betaCode q root) rhoOut + DirectZeta.sourceValue q root := by
  have hs := execute_spec q root lambdaOut hl
  rw [hs.2.2.2, sourceValue, RhoMu.source_lemma_3_14_a q root rhoOut hs.1 hr]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.Lambda
