import Alexander313.Wilken.PublicEpsilonNativeLambdaSourceBranchesSupport

/-!
# Executing original-source lambda on both genuine proper-root branches

The original admitted Normal proper theta-zero root has an exhaustive
epsilon/high or non-epsilon/LOW classification. The actual high source
producer and actual low zeta branch both return LOW Normal source codes.
Their real partial executions retain the original proper-root domain,
complete numerical graphs and literal Definition2.45 value. No branch,
source representation, LOW result or lambda identity is supplied.
Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Lambda.SourceBranches

def execute (q root : Nat) : Part Nat := cond (inputCheck q root)
  (cond (high root) (PublicEpsilonUnboundedIota.LambdaSource.execute q root)
    (NonEpsilonBaseChange.execute q root)) Part.none

theorem execute_partrec : Partrec₂ execute :=
  (Partrec.cond inputCheck_primrec.to_comp
    (Partrec.cond (high_primrec.comp Primrec.snd).to_comp
      PublicEpsilonUnboundedIota.LambdaSource.execute_partrec
      NonEpsilonBaseChange.execute_partrec) Partrec.none).to₂

theorem execute_high (q root : Nat) (ha : inputCheck q root = true)
    (hh : high root = true) :
    execute q root = PublicEpsilonUnboundedIota.LambdaSource.execute q root := by
  simp only [execute, ha, hh, Bool.cond_true]

theorem execute_low (q root : Nat) (ha : inputCheck q root = true)
    (hh : high root = false) : execute q root = NonEpsilonBaseChange.execute q root := by
  simp only [execute, ha, hh, Bool.cond_true, Bool.cond_false]

theorem execute_domain (q root : Nat) : (execute q root).Dom ↔ inputCheck q root = true := by
  cases ha : inputCheck q root with
  | false => simp only [execute, ha, Bool.cond_false, Part.not_none_dom, Bool.false_eq_true]
  | true =>
    cases hh : high root with
    | true => simp only [execute_high q root ha hh,
        PublicEpsilonUnboundedIota.LambdaSource.execute_domain, high_input q root ha hh]
    | false => simp only [execute_low q root ha hh,
        NonEpsilonBaseChange.execute_domain, low_input q root ha hh]

theorem execute_returns (q root : Nat) (ha : inputCheck q root = true) :
    ∃ out, out ∈ execute q root := Part.dom_iff_mem.mp ((execute_domain q root).mpr ha)

theorem execute_graph (q root out : Nat) : out ∈ execute q root ↔
    inputCheck q root = true ∧
      ((high root = true ∧ out ∈ PublicEpsilonUnboundedIota.LambdaSource.execute q root) ∨
        (high root = false ∧ out ∈ NonEpsilonBaseChange.execute q root)) := by
  cases ha : inputCheck q root <;> cases hh : high root <;> simp [execute, ha, hh]

noncomputable def sourceValue (q root : Nat) : Ordinal.{0} := cond (high root)
  (PublicEpsilonUnboundedIota.LambdaSource.sourceValue q root) (DirectZeta.sourceValue q root)

theorem execute_spec (q root out : Nat) (ho : out ∈ execute q root) :
    inputCheck q root = true ∧ lowCheckCode q out = true ∧
      Comparison.acceptedCode q out = true ∧ interpretation q out = sourceValue q root := by
  have ha := (execute_domain q root).mp (Part.dom_iff_mem.mpr ⟨out, ho⟩)
  cases hh : high root with
  | true =>
    have hs := PublicEpsilonUnboundedIota.LambdaSource.execute_spec q root out
      (by rw [← execute_high q root ha hh]; exact ho)
    exact ⟨ha, hs.2.1, hs.2.2.1, by simpa only [sourceValue, hh, Bool.cond_true] using hs.2.2.2⟩
  | false =>
    have hs := NonEpsilonBaseChange.definition_2_45_spec q root out
      (by rw [← execute_low q root ha hh]; exact ho)
    exact ⟨ha, hs.2.1, hs.2.2.1, by simpa only [sourceValue, hh, Bool.cond_false] using hs.2.2.2⟩

/-- The full executing Definition2.45 uses the genuine mathematical
epsilon test; the original syntax classifier has been proved equivalent. -/
theorem source_definition_2_45 (q root out : Nat) (ho : out ∈ execute q root) :
    interpretation q out =
      if Ordinal.omega0 ^ interpretation q root = interpretation q root then
        PublicEpsilonUnboundedIota.LambdaSource.sourceValue q root else DirectZeta.sourceValue q root := by
  have hs := execute_spec q root out ho
  rw [hs.2.2.2, sourceValue]
  cases hh : high root with
  | true => simp only [hh, Bool.cond_true, if_pos ((high_iff_epsilon q root hs.1).mp hh)]
  | false =>
    have hn := ((NonEpsilonBaseChange.inputCheck_exact q root).mp (low_input q root hs.1 hh)).2.2
    simp only [hh, Bool.cond_false, if_neg hn]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Lambda.SourceBranches
