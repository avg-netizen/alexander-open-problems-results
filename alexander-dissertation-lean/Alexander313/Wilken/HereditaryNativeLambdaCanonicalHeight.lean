import Alexander313.Wilken.HereditaryNativeIotaCanonicalHeight
import Alexander313.Wilken.HereditaryNativeLambdaBranches

/-!
# The actual epsilon lambda height in source Lemma 2.48(c)

The genuine high-part decomposition stays within the original argument's
written height. Actual iota lowers that height by one, the actual returned
zeta parameter has height zero, and native addition supplies a normal output
within the maximum of these two heights. Original root and output Normality
identify these bounds with the corresponding canonical ordinal heights.

Every admission and height bound follows from the original executing high-
root domain. No target representation, supplied translator or height premise
is added. The full recognized epsilon branch is included. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Lambda.Height

open NativePublicBridge (contextCode contextCode_checked)

theorem literalDelta_height_lt_root (s a : Nat) (ha : Iota.rootCheck s a = true) :
    heightCode (Iota.literalCode s a (deltaCode a)) < heightCode a := by
  obtain ⟨u, he, hl, hc, hh⟩ := Iota.literalCode_spec s a (deltaCode a) (delta_input s a ha)
  have hi : heightCode (Iota.literalCode s a (deltaCode a)) ≤ heightCode (deltaCode a) - 1 := by
    simpa only [he, hl, heightCode_code] using hh
  have hd := (NativeContext.Height.parts_code_height (contextCode s) 0 (argumentCode a)
    ((Decomposition.inputCheck_exact _ _).mp (argument_accepted s a ha)).1).1
  change heightCode (deltaCode a) ≤ heightCode (argumentCode a) at hd
  obtain ⟨t, hroot, ht, hn, hs⟩ := (Iota.rootCheck_exact s a).mp ha
  have harg : heightCode (argumentCode a) = t.height := by
    simp only [argumentCode, hroot, Localization.argumentCode_theta, heightCode_code]
  have hr : heightCode a = max 1 t.height := by
    simp only [hroot, heightCode_code, RelativeTerm.height, Nat.zero_add]
  rw [harg] at hd
  rw [hr]
  omega

theorem emit_height_lt_root (s a d : Nat) (ha : Iota.rootCheck s a = true)
    (hd : d ∈ SourceZeta.zeta s a) : heightCode (emit s a d) < heightCode a := by
  obtain ⟨t, he, hl, hc, hh⟩ := Iota.literalCode_spec s a (deltaCode a) (delta_input s a ha)
  have hi : checkCode (Iota.alphaCode s a) (Iota.literalCode s a (deltaCode a)) = true := by
    simpa only [hl, checkCode_code] using hc
  have hz := zetaParameter_spec s a d ha hd
  have hzc : checkCode (Iota.alphaCode s a) (zetaParameter s d).code = true := by
    simpa only [checkCode_code] using hz.1
  have hs := (Arithmetic.addCode_spec (Iota.alphaCode s a)
    (Iota.literalCode s a (deltaCode a)) (zetaParameter s d).code hi hzc).2.2
  have hb := literalDelta_height_lt_root s a ha
  change heightCode (Arithmetic.addCode (Iota.alphaCode s a)
    (Iota.literalCode s a (deltaCode a)) (zetaParameter s d).code) < heightCode a
  exact hs.trans_lt
    (by simpa only [heightCode_code, zetaParameter, RelativeTerm.height, max_zero] using hb)

theorem execute_height_lt_root (s a out : Nat) (ho : out ∈ execute s a) :
    heightCode out < heightCode a := by
  have ha := (execute_spec s a out ho).1
  have hm : out ∈ (SourceZeta.zeta s a).map (emit s a) := by
    simpa only [execute, ha, Bool.cond_true] using ho
  obtain ⟨d, hd, rfl⟩ := (Part.mem_map_iff (emit s a)).mp hm
  exact emit_height_lt_root s a d ha hd

/-- The heights use their actual different bases, exactly as printed:
ht_alpha(lambda_tau_alpha) < ht_tau(alpha). -/
theorem execute_canonical_height_lt_root (s a out : Nat) (ho : out ∈ execute s a) :
    CanonicalHeight.canonicalHeightCode (Iota.alphaCode s a) out <
      CanonicalHeight.canonicalHeightCode (contextCode s) a := by
  have hs := execute_spec s a out ho
  rw [CanonicalHeight.canonicalHeightCode_normal _ out hs.2.1,
    CanonicalHeight.canonicalHeightCode_normal _ a (Iota.HeightSupport.root_accepted s a hs.1)]
  exact execute_height_lt_root s a out ho

theorem source_lemma_2_48_c (s a out : Nat) (ho : out ∈ execute s a) :
    CanonicalHeight.canonicalHeightCode (Iota.alphaCode s a) out <
      CanonicalHeight.canonicalHeightCode (contextCode s) a :=
  execute_canonical_height_lt_root s a out ho

/-- The same bound for the actual two-branch caller on its original proper
domain. The epsilon test is exactly the printed branch condition. -/
theorem branch_execute_canonical_height_lt_root (s a out : Nat)
    (ho : out ∈ Branches.execute s a)
    (he : Ordinal.omega0 ^ interpretation (contextCode s) a = interpretation (contextCode s) a) :
    CanonicalHeight.canonicalHeightCode (Branches.outputContext s a) out <
      CanonicalHeight.canonicalHeightCode (contextCode s) a := by
  have hb := (Branches.execute_spec s a out ho).1
  have ha := (Branches.high_iff_epsilon s a hb).mpr he
  have hl : out ∈ execute s a := by
    simpa only [Branches.execute, hb, ha, Bool.cond_true] using ho
  simp only [Branches.outputContext, ha, Bool.cond_true]
  exact execute_canonical_height_lt_root s a out hl

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Lambda.Height
