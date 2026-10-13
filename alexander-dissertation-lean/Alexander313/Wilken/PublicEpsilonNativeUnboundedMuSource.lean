import Alexander313.Wilken.PublicEpsilonNativeUnboundedMuSourceSupport

/-!
# Actual original-source mu output with genuine provenance

Actual ANY-q omega power on the constructed original-source exponent
returns a LOW Normal original-q code for the actual Definition3.6 mu value.
The input is exactly the genuine original admitted Normal high root;
neither a selected endpoint nor a supplied mu representation is required.
The executing guard and complete graph retain numerical zero. Syntactic
Par and the actual pi equation are proved in the companion. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.MuSource

def sourceCode (q root : Nat) : Nat := cond (inputCheck q root)
  (OmegaPowers.powerCode q (exponentCode q root)) 0

theorem sourceCode_primrec : Primrec (fun p : Context => sourceCode p.1 p.2) :=
  inputCheck_primrec.cond
    (OmegaPowers.powerCode_primrec.comp Primrec.fst exponentCode_primrec) (Primrec.const 0)

theorem sourceCode_literal (q root : Nat) (ha : inputCheck q root = true) :
    sourceCode q root = OmegaPowers.powerCode q (exponentCode q root) := by
  simp only [sourceCode, ha, Bool.cond_true]

theorem sourceCode_rejected (q root : Nat) (ha : inputCheck q root = false) :
    sourceCode q root = 0 := by simp only [sourceCode, ha, Bool.cond_false]

/-- Original-source LOW and weak Normality are actual producer outputs,
and its value is the real NEW-base executing mu value. -/
theorem sourceCode_spec (q root : Nat) (ha : inputCheck q root = true) :
    lowCheckCode q (sourceCode q root) = true ∧
      Comparison.acceptedCode q (sourceCode q root) = true ∧
        interpretation q (sourceCode q root) =
          interpretation (betaCode q root) (Mu.muCode q root) := by
  have hq := OmegaPowers.powerCode_spec q _ (exponentCode_spec q root ha).1
  have hβ := OmegaPowers.powerCode_spec (betaCode q root) _ (Mu.exponentCode_spec q root ha).1
  rw [sourceCode_literal q root ha]
  refine ⟨hq.1, hq.2.1, ?_⟩
  rw [Mu.muCode_literal q root ha, hq.2.2, hβ.2.2, (exponentCode_spec q root ha).2.2]

theorem source_definition_3_6 (q root : Nat) (ha : inputCheck q root = true) :
    interpretation q (sourceCode q root) = Mu.sourceValue q root :=
  (sourceCode_spec q root ha).2.2.trans (Mu.muCode_spec q root ha).2.2

def execute (q root : Nat) : Part Nat :=
  cond (inputCheck q root) (Part.some (sourceCode q root)) Part.none

theorem execute_partrec : Partrec (fun p : Context => execute p.1 p.2) :=
  Partrec.cond inputCheck_primrec.to_comp sourceCode_primrec.to_comp.partrec Partrec.none

theorem execute_domain (q root : Nat) : (execute q root).Dom ↔ inputCheck q root = true := by
  cases ha : inputCheck q root <;> simp [execute, ha]

theorem execute_graph (q root out : Nat) : out ∈ execute q root ↔
    inputCheck q root = true ∧ out = sourceCode q root := by
  cases ha : inputCheck q root <;> simp [execute, ha]

theorem execute_spec (q root out : Nat) (ho : out ∈ execute q root) :
    inputCheck q root = true ∧ lowCheckCode q out = true ∧
      Comparison.acceptedCode q out = true ∧ interpretation q out = Mu.sourceValue q root := by
  obtain ⟨ha, rfl⟩ := (execute_graph q root out).mp ho
  have hs := sourceCode_spec q root ha
  exact ⟨ha, hs.1, hs.2.1, source_definition_3_6 q root ha⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.MuSource
