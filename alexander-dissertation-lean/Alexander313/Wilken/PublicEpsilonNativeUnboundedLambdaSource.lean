import Alexander313.Wilken.PublicEpsilonNativeUnboundedLambdaSourceSupport

/-!
# Actual original-source high lambda execution

The genuine original high-root guard executes direct zeta and actual
original-source addition to the returned iota divided head. The real output
is LOW checked Normal and has exactly iota(Delta)+zeta, the HIGH branch of
Definition2.45. No target representation or output caller is supplied.
The partial execution retains the original guard and complete graph,
including numerical zero. Primitive recursion concerns the finite emit
operation; the actual zeta execution is partial recursive. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.LambdaSource

def sourceCode (q root zeta : Nat) : Nat :=
  Arithmetic.addCode q (returnedDelta q root) zeta

theorem sourceCode_primrec : Primrec₂ (fun p : Context => sourceCode p.1 p.2) :=
  (Arithmetic.addCode_primrec.comp ((Primrec.fst.comp Primrec.fst).pair
    ((returnedDelta_primrec.comp Primrec.fst).pair Primrec.snd))).to₂

noncomputable def sourceValue (q root : Nat) : Ordinal.{0} :=
  interpretation (betaCode q root) (literalCode q root (deltaCode root)) +
    DirectZeta.sourceValue q root

/-- Every output and addition caller follows from the original high
root and the actual direct-zeta graph row. -/
theorem sourceCode_spec (q root zeta : Nat) (ha : inputCheck q root = true)
    (hz : zeta ∈ DirectZeta.execute q root) :
    lowCheckCode q (sourceCode q root zeta) = true ∧
      Comparison.acceptedCode q (sourceCode q root zeta) = true ∧
      interpretation q (sourceCode q root zeta) = sourceValue q root := by
  have hd := returnedDelta_spec q root ha
  have hzs := DirectZeta.execute_spec q root zeta hz
  have hs := Arithmetic.addCode_spec q _ _ ((Comparison.acceptedCode_exact q _).mp hd.1).1
    ((Comparison.acceptedCode_exact q _).mp hzs.2.2.1).1
  refine ⟨(OmegaPowerHeight.addCode_low_height q _ _ (returnedDelta_low q root ha) hzs.2.1).1,
    hs.1, ?_⟩
  simpa only [sourceCode, sourceValue, hd.2, hzs.2.2.2] using hs.2.1

/-- The actual source value is the epsilon/high branch of the printed
Definition2.45, because the original high root genuinely is epsilon. -/
theorem source_definition_2_45 (q root zeta : Nat) (ha : inputCheck q root = true)
    (hz : zeta ∈ DirectZeta.execute q root) :
    interpretation q (sourceCode q root zeta) =
      if Ordinal.omega0 ^ interpretation q root = interpretation q root then
        interpretation (betaCode q root) (literalCode q root (deltaCode root)) +
          DirectZeta.sourceValue q root else DirectZeta.sourceValue q root := by
  rw [if_pos (root_epsilon q root ha)]
  exact (sourceCode_spec q root zeta ha hz).2.2

def execute (q root : Nat) : Part Nat := cond (inputCheck q root)
  ((DirectZeta.execute q root).map (sourceCode q root)) Part.none

theorem execute_partrec : Partrec₂ execute :=
  (Partrec.cond inputCheck_primrec.to_comp
    (DirectZeta.execute_partrec.map sourceCode_primrec.to_comp) Partrec.none).to₂

theorem execute_domain (q root : Nat) : (execute q root).Dom ↔ inputCheck q root = true := by
  cases ha : inputCheck q root with
  | false => simp only [execute, ha, Bool.cond_false, Part.not_none_dom, Bool.false_eq_true]
  | true => simp only [execute, ha, Bool.cond_true, Part.map, DirectZeta.execute_domain,
      zeta_input q root ha]

theorem execute_returns (q root : Nat) (ha : inputCheck q root = true) :
    ∃ out, out ∈ execute q root := Part.dom_iff_mem.mp ((execute_domain q root).mpr ha)

theorem execute_graph (q root out : Nat) : out ∈ execute q root ↔
    inputCheck q root = true ∧
      ∃ zeta ∈ DirectZeta.execute q root, sourceCode q root zeta = out := by
  cases ha : inputCheck q root <;>
    simp [execute, ha, Part.mem_map_iff]

theorem execute_spec (q root out : Nat) (ho : out ∈ execute q root) :
    inputCheck q root = true ∧ lowCheckCode q out = true ∧
      Comparison.acceptedCode q out = true ∧ interpretation q out = sourceValue q root := by
  obtain ⟨ha, zeta, hz, rfl⟩ := (execute_graph q root out).mp ho
  exact ⟨ha, sourceCode_spec q root zeta ha hz⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.LambdaSource
