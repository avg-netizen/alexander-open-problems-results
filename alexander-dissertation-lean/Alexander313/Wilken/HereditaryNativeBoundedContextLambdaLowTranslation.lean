import Alexander313.Wilken.HereditaryNativeDirectZetaLowValue
import Alexander313.Wilken.HereditaryNativeBoundedPublicReturnCodes
import Alexander313.Wilken.HereditaryNativeLambdaBranches
import Alexander313.Wilken.HereditaryNativeBoundedContextIotaSupport

/-!
# Actual lambda transport for the non-epsilon intermediate branch

The ORIGINAL proper Normal theta-zero root at the actual alpha context is
returned by the genuine bounded source producer. Its final principal atom
has the same value as the whole root. Original admission and the strict
base bound exclude a parameter atom, and LOW admission forces theta index
zero. Thus the actual finite producer supplies an ORIGINAL proper source
lambda caller, with no root-shape or representation oracle.

On the non-epsilon branch, zeta is the exact last exponent of the logarithm
of the root value. Actual DirectZeta and original Lambda.Branches executions
therefore agree across the two genuine epsilon contexts. Uncompiled source
candidates. The epsilon branch is covered separately by LambdaTranslation.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.BoundedContextIota.Lambda.LowTranslation

open NativePublicBridge (contextCode)

def returnedCode (s a c : Nat) : Nat := LogEndZero.endCode
  (BoundedPublicReturn.sourceTermCode s a (ThetaCourse.rawTree c))

theorem returnedCode_primrec : Primrec₂
    (fun ctx : Nat × Nat => returnedCode ctx.1 ctx.2) :=
  (LogEndZero.endCode_primrec.comp (BoundedPublicReturn.sourceTermCode_primrec.comp
    Primrec.fst (ThetaCourse.rawTree_primrec.comp Primrec.snd))).to₂

private theorem rawTree_code_eq (q c : Nat) (hc : checkCode q c = true) :
    (ThetaCourse.rawTree c).code = c := by
  obtain ⟨t, he, ht⟩ := (checkCode_exact q c).mp hc
  rw [← he, ThetaCourse.rawTree_code]

/-- The actual final-atom producer derives the full ORIGINAL proper source
lambda guard from the original intermediate guard and original endpoint. -/
theorem returnedCode_spec (s a c : Nat) (ha : Iota.rootCheck s a = true)
    (hc : DirectZeta.inputCheck (sourceCode s a) c = true)
    (hp : base (sourceCode s a) < interpretation (sourceCode s a) c)
    (hb : interpretation (sourceCode s a) c < Iota.AlphaPlus.sourceValue s a) :
    NativeContext.Lambda.Branches.inputCheck s (returnedCode s a c) = true ∧
      interpretation (contextCode s) (returnedCode s a c) = interpretation (sourceCode s a) c := by
  obtain ⟨t, rfl, ht, hn⟩ := (DirectZeta.inputCheck_exact _ c).mp hc
  let b := BoundedPublicReturn.sourceTermCode s a (.theta 0 t)
  have hs := BoundedPublicReturn.sourceTermCode_low_spec s a ha (.theta 0 t) ht hn
    (by simp only [RelativeTerm.outerSort]) (by simpa only [interpretation_code] using hb)
  have hbn := hs.1
  have hbl : lowCheckCode (contextCode s) b = true := hs.2.1
  have hvalue : interpretation (contextCode s) b = denote (sourceCode s a) (.theta 0 t) := hs.2.2
  have hprincipal := SourceChi.Powers.theta_principal (sourceCode s a) t ht
  have hpositive : 0 < interpretation (contextCode s) b := by rw [hvalue]; exact hprincipal.1
  have he := LogEnd.Support.endCode_spec (contextCode s) b hbl hbn (ne_of_gt hpositive)
  have hend : interpretation (contextCode s) (LogEndZero.endCode b) =
      denote (sourceCode s a) (.theta 0 t) := by
    rw [LogEndZero.endCode_value _ _ hbn, hvalue,
      SourceChi.Powers.endValue_principal _ hprincipal.1 hprincipal.2]
  have holdproper : base (contextCode s) < interpretation (contextCode s) (LogEndZero.endCode b) := by
    rw [hend]
    exact (Iota.root_base_le s a ha).trans_lt (by
      simpa only [sourceCode, Iota.alpha_base s a ha, interpretation_code] using hp)
  have hec := (Comparison.acceptedCode_exact _ _).mp he.2.1
  have heraw := Arithmetic.raw_checked _ _ hec.1
  have hecode := rawTree_code_eq _ _ hec.1
  rcases he.2.2.2.2.2 with ⟨p, hshape⟩ | ⟨k, u, hshape⟩
  · have hparam : check (contextCode s) (.parameter p) = true := by
      simpa only [hshape] using heraw
    have hbound := (checked_parameters (contextCode s) (.parameter p) hparam p
      (by simp only [RelativeTerm.parameters, List.mem_singleton])).2
    have hv : interpretation (contextCode s) (LogEndZero.endCode b) = parameters p := by
      rw [← Arithmetic.raw_value _ _ hec.1, hshape]
      rfl
    have hbnd : interpretation (contextCode s) (LogEndZero.endCode b) < base (contextCode s) := by
      simpa only [hv] using hbound
    exact False.elim ((not_lt_of_ge (le_of_lt holdproper)) hbnd)
  · have hcode : LogEndZero.endCode b = (.theta k u : RelativeTerm Nat).code :=
      hecode.symm.trans (congrArg RelativeTerm.code hshape)
    have hk : k = 0 := LogEnd.Support.theta_low_index (contextCode s) k u (by
      simpa only [hcode] using he.1)
    subst k
    have hu : check (contextCode s) (.theta 0 u) = true := by
      simpa only [hshape] using heraw
    have hun : Comparison.Normal (contextCode s) u := by
      simpa only [hshape, Comparison.Normal] using hec.2
    have hguard := (NativeContext.Lambda.Branches.inputCheck_exact s _).mpr
      ⟨u, hcode, hu, hun, by simpa only [hcode, interpretation_code] using holdproper⟩
    simpa only [returnedCode, ThetaCourse.rawTree_code, interpretation_code, b] using
      And.intro hguard hend

theorem returnedCode_direct_input (s a c : Nat) (ha : Iota.rootCheck s a = true)
    (hc : DirectZeta.inputCheck (sourceCode s a) c = true)
    (hp : base (sourceCode s a) < interpretation (sourceCode s a) c)
    (hb : interpretation (sourceCode s a) c < Iota.AlphaPlus.sourceValue s a) :
    DirectZeta.inputCheck (contextCode s) (returnedCode s a c) = true := by
  have hs := (returnedCode_spec s a c ha hc hp hb).1
  obtain ⟨t, he, ht, hn, hp⟩ := (NativeContext.Lambda.Branches.inputCheck_exact s _).mp hs
  exact (DirectZeta.inputCheck_exact _ _).mpr ⟨t, he, ht, hn⟩

/-- Cross-base zeta agreement at the actual finite returned source root. -/
theorem zeta_value (s a c : Nat) (ha : Iota.rootCheck s a = true)
    (hc : DirectZeta.inputCheck (sourceCode s a) c = true)
    (hp : base (sourceCode s a) < interpretation (sourceCode s a) c)
    (hb : interpretation (sourceCode s a) c < Iota.AlphaPlus.sourceValue s a)
    (hε : Ordinal.omega0 ^ interpretation (sourceCode s a) c ≠ interpretation (sourceCode s a) c) :
    SourceZeta.sourceValue s (returnedCode s a c) = DirectZeta.sourceValue (sourceCode s a) c := by
  exact (DirectZeta.LowValue.sourceValue_invariant_non_epsilon _ _ _ _ hc
    (returnedCode_direct_input s a c ha hc hp hb)
    (returnedCode_spec s a c ha hc hp hb).2.symm hε).symm

/-- Every actual non-epsilon intermediate lambda output has a genuine
original-source lambda execution of the same ordinal value. -/
theorem execute_translation (s a c out : Nat) (ha : Iota.rootCheck s a = true)
    (ho : out ∈ DirectZeta.execute (sourceCode s a) c)
    (hp : base (sourceCode s a) < interpretation (sourceCode s a) c)
    (hb : interpretation (sourceCode s a) c < Iota.AlphaPlus.sourceValue s a)
    (hε : Ordinal.omega0 ^ interpretation (sourceCode s a) c ≠ interpretation (sourceCode s a) c) :
    ∃ other, other ∈ NativeContext.Lambda.Branches.execute s (returnedCode s a c) ∧
      NativeContext.Lambda.Branches.outputContext s (returnedCode s a c) = contextCode s ∧
      interpretation (contextCode s) other = interpretation (sourceCode s a) out := by
  have hs := DirectZeta.execute_spec _ _ _ ho
  have hr := returnedCode_spec s a c ha hs.1 hp hb
  obtain ⟨other, he⟩ := NativeContext.Lambda.Branches.execute_returns s _ hr.1
  have hne : Ordinal.omega0 ^ interpretation (contextCode s) (returnedCode s a c) ≠
      interpretation (contextCode s) (returnedCode s a c) := by simpa only [hr.2] using hε
  have ht := NativeContext.Lambda.Branches.execute_non_epsilon s _ other he hne
  exact ⟨other, he, ht.1, ht.2.2.1.trans ((zeta_value s a c ha hs.1 hp hb hε).trans hs.2.2.2.symm)⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.BoundedContextIota.Lambda.LowTranslation
