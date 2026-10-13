import Alexander313.Wilken.PublicEpsilonNativeUnboundedMuHeightSupport

/-!
# Source3.7 height inequalities on the whole original native epsilon domain

Actual high-part decomposition and unrestricted iota lower the written
divided-head height. Genuine zeta becomes an admitted beta parameter of
height zero, and the real normalized addition bounds lambda's output height.
Normal input/output identify literal heights with the canonical heights at
their actual different bases. The actual mu producer then gives the full
printed height inequalities. No selected endpoint, canonical q spelling,
supplied height or translated input is assumed. The ambiguous parameter
branch of mu-plus is not defined here. All candidates are uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.Mu.Height

open ThetaCourse HeightSupport

theorem literalDelta_height_lt_root (q root : Nat) (ha : inputCheck q root = true) :
    heightCode (literalCode q root (OmegaQuotient.deltaCode root)) < heightCode root := by
  have hi := literalCode_height q root _ (Lambda.delta_input q root ha)
  have hd := (NativeContext.Height.parts_code_height q 0 (Localization.argumentCode root)
    ((Comparison.acceptedCode_exact q _).mp
      (OmegaQuotient.Support.argument_accepted q root ha)).1).1
  change heightCode (OmegaQuotient.deltaCode root) ≤
    heightCode (Localization.argumentCode root) at hd
  obtain ⟨t, he, ht, hn, hh⟩ := (rootCheck_exact q root).mp ha
  have harg : heightCode (Localization.argumentCode root) = t.height := by
    simp only [he, Localization.argumentCode_theta, heightCode_code]
  have hr : heightCode root = max 1 t.height := by
    simp only [he, heightCode_code, RelativeTerm.height, Nat.zero_add]
  rw [harg] at hd
  rw [hr]
  omega

theorem emit_height_lt_root (q root z : Nat) (ha : inputCheck q root = true)
    (hz : z ∈ DirectZeta.execute q root) : heightCode (Lambda.emit q root z) < heightCode root := by
  have hd := literalCode_accepted q root _ (Lambda.delta_input q root ha)
  have hp := Lambda.zetaParameter_spec q root z ha hz
  have hs := (Arithmetic.addCode_spec (betaCode q root)
    (literalCode q root (OmegaQuotient.deltaCode root)) (Lambda.zetaParameter q z).code
    ((Comparison.acceptedCode_exact _ _).mp hd).1
    (by simpa only [checkCode_code] using hp.1)).2.2
  have hb := literalDelta_height_lt_root q root ha
  change heightCode (Arithmetic.addCode (betaCode q root)
    (literalCode q root (OmegaQuotient.deltaCode root)) (Lambda.zetaParameter q z).code) <
      heightCode root
  exact hs.trans_lt (by
    simpa only [heightCode_code, Lambda.zetaParameter, RelativeTerm.height, max_zero] using hb)

theorem lambda_execute_height_lt_root (q root out : Nat) (ho : out ∈ Lambda.execute q root) :
    heightCode out < heightCode root := by
  have ha := (Lambda.execute_spec q root out ho).1
  have hm : out ∈ (DirectZeta.execute q root).map (Lambda.emit q root) := by
    simpa only [Lambda.execute, ha, Bool.cond_true] using ho
  obtain ⟨z, hz, rfl⟩ := (Part.mem_map_iff (Lambda.emit q root)).mp hm
  exact emit_height_lt_root q root z ha hz

theorem lambda_execute_canonical_height_lt_root (q root out : Nat)
    (ho : out ∈ Lambda.execute q root) :
    CanonicalHeight.canonicalHeightCode (betaCode q root) out <
      CanonicalHeight.canonicalHeightCode q root := by
  have hs := Lambda.execute_spec q root out ho
  rw [CanonicalHeight.canonicalHeightCode_normal _ out hs.2.2.1,
    CanonicalHeight.canonicalHeightCode_normal q root (RootLowCollapse.root_accepted q root hs.1)]
  exact lambda_execute_height_lt_root q root out ho

theorem muCode_height_le_lambda (q root out : Nat) (ho : out ∈ Lambda.execute q root) :
    heightCode (muCode q root) ≤ CanonicalHeight.canonicalHeightCode (betaCode q root) out :=
  (muCode_height_mappedCoefficient q root (Lambda.execute_spec q root out ho).1).trans
    (mappedCoefficient_canonical_height_le_lambda q root out ho)

theorem muCode_canonical_height_le_lambda (q root out : Nat) (ho : out ∈ Lambda.execute q root) :
    CanonicalHeight.canonicalHeightCode (betaCode q root) (muCode q root) ≤
      CanonicalHeight.canonicalHeightCode (betaCode q root) out := by
  rw [CanonicalHeight.canonicalHeightCode_normal _ _
    (muCode_spec q root (Lambda.execute_spec q root out ho).1).2.1]
  exact muCode_height_le_lambda q root out ho

/-- The unchanged original high-root execution guards derive both genuine
height inequalities at their stated bases on every admitted coded epsilon. -/
theorem source_lemma_3_7_height (q root muOut lambdaOut : Nat)
    (hm : muOut ∈ execute q root) (hl : lambdaOut ∈ Lambda.execute q root) :
    CanonicalHeight.canonicalHeightCode (betaCode q root) muOut ≤
        CanonicalHeight.canonicalHeightCode (betaCode q root) lambdaOut ∧
      CanonicalHeight.canonicalHeightCode (betaCode q root) lambdaOut <
        CanonicalHeight.canonicalHeightCode q root := by
  obtain ⟨ha, rfl⟩ := (execute_graph q root muOut).mp hm
  exact ⟨muCode_canonical_height_le_lambda q root lambdaOut hl,
    lambda_execute_canonical_height_lt_root q root lambdaOut hl⟩

theorem source_lemma_3_7_normal_height (q root muOut lambdaOut : Nat)
    (hm : muOut ∈ execute q root) (hl : lambdaOut ∈ Lambda.execute q root) :
    heightCode muOut ≤ heightCode lambdaOut ∧ heightCode lambdaOut < heightCode root := by
  have hs := source_lemma_3_7_height q root muOut lambdaOut hm hl
  have hm' := execute_spec q root muOut hm
  have hl' := Lambda.execute_spec q root lambdaOut hl
  simpa only [CanonicalHeight.canonicalHeightCode_normal _ muOut hm'.2.2.1,
    CanonicalHeight.canonicalHeightCode_normal _ lambdaOut hl'.2.2.1,
    CanonicalHeight.canonicalHeightCode_normal q root
      (RootLowCollapse.root_accepted q root hl'.1)] using hs

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.Mu.Height
