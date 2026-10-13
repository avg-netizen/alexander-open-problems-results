import Alexander313.Wilken.PublicEpsilonNativeUnboundedRhoMu
import Alexander313.Wilken.PublicEpsilonNativeUnboundedLambdaSourceSupport
import Alexander313.Wilken.HereditaryNativeUniformPublicReturn

/-!
# Actual beta-context lambda callers on the full original epsilon domain

The original ANY-q admitted Normal high root supplies its actual divided
head and every literal iota caller. Its real zeta execution is LOW at q;
the genuine uniform finite return produces a canonical public parameter
strictly below that same root. No selected endpoint, return, Normality,
support or zeta bound oracle is supplied. Source-only and uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.Lambda

open ThetaCourse

abbrev inputCheck := PublicEpsilonUnboundedIota.rootCheck
abbrev deltaCode := OmegaQuotient.deltaCode

theorem inputCheck_primrec : Primrec (fun p : Context => inputCheck p.1 p.2) :=
  PublicEpsilonUnboundedIota.rootCheck_primrec

theorem zeta_input (q root : Nat) (ha : inputCheck q root = true) :
    DirectZeta.inputCheck q root = true := LambdaSource.zeta_input q root ha

theorem zeta_value_lt_root (q root : Nat) (ha : inputCheck q root = true) :
    DirectZeta.sourceValue q root < interpretation q root := by
  obtain ⟨out, ho⟩ := DirectZeta.execute_returns q root (zeta_input q root ha)
  rw [← (DirectZeta.execute_spec q root out ho).2.2.2]
  exact DirectZeta.execute_bound q root out ho

theorem delta_input (q root : Nat) (ha : inputCheck q root = true) :
    PublicEpsilonUnboundedIota.inputCheck q root (deltaCode root) = true :=
  LambdaSource.delta_iota_caller q root ha

theorem literalDelta_low (q root : Nat) (ha : inputCheck q root = true) :
    lowCheckCode (betaCode q root) (literalCode q root (deltaCode root)) = true :=
  (LambdaSource.mappedDelta_spec q root ha).1

def zetaParameter (q out : Nat) : RelativeTerm Nat :=
  .parameter (UniformPublicReturn.publicCode q out)

theorem zetaParameter_primrec : Primrec₂ zetaParameter :=
  parameter_primrec.comp₂ UniformPublicReturn.publicCode_primrec

theorem zetaParameter_spec (q root out : Nat) (ha : inputCheck q root = true)
    (ho : out ∈ DirectZeta.execute q root) :
    check (betaCode q root) (zetaParameter q out) = true ∧
      lowCheckCode (betaCode q root) (zetaParameter q out).code = true ∧
      denote (betaCode q root) (zetaParameter q out) = DirectZeta.sourceValue q root := by
  have hz := DirectZeta.execute_spec q root out ho
  have hp := UniformPublicReturn.publicCode_spec q out
    ((UniformPublicReturn.inputCheck_exact q out).mpr hz.2.1)
  have hparameter : parameterCheck (betaCode q root) (UniformPublicReturn.publicCode q out) = true := by
    apply (parameterCheck_exact _ _).mpr
    refine ⟨Canonical.check_original hp.1,
      Canonical.check_original (betaCode_spec q root ha).1, ?_⟩
    change unionInterpretation (UniformPublicReturn.publicCode q out) <
      unionInterpretation (betaCode q root)
    rw [hp.2, (betaCode_spec q root ha).2]
    exact DirectZeta.execute_bound q root out ho
  have ht : check (betaCode q root) (zetaParameter q out) = true := by
    simp only [zetaParameter, check, betaCode_baseCheck q root ha,
      finiteCheck_parameter, hparameter, Bool.true_and]
  refine ⟨ht, ?_, hp.2.trans hz.2.2.2⟩
  simp only [lowCheckCode_code, lowCheck, ht, zetaParameter, outerSort,
    Nat.zero_le, decide_true, Bool.true_and]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.Lambda
