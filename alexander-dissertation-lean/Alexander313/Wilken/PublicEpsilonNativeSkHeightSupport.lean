import Alexander313.Wilken.PublicEpsilonNativeUnboundedMuHeight

/-!
# Actual strict height decrease for LOW mu-bounded next values

The original ANY-q high-root guard derives lambda's total execution and
the full printed mu height inequality. Any actual LOW next value at the
root context with value at most mu therefore has strictly smaller canonical
height than the original root. An actual next HIGH root is Normal, so its
written height decreases as well. No successor convention, translation,
height, LOW or next-root representative is supplied as an operator oracle.
The step is a proof kernel; no executing sk sequence is claimed. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.SkHeight

theorem mu_height_lt_root (q root : Nat) (ha : Mu.inputCheck q root = true) :
    CanonicalHeight.canonicalHeightCode (betaCode q root) (Mu.muCode q root) <
      CanonicalHeight.canonicalHeightCode q root := by
  obtain ⟨out, ho⟩ := Lambda.execute_returns q root ha
  exact (Mu.Height.muCode_canonical_height_le_lambda q root out ho).trans_lt
    (Mu.Height.lambda_execute_canonical_height_lt_root q root out ho)

/-- The next value need not be Normal or epsilon for the canonical bound. -/
theorem low_next_height_lt_root (q root next : Nat) (ha : Mu.inputCheck q root = true)
    (hn : lowCheckCode (betaCode q root) next = true)
    (hle : interpretation (betaCode q root) next ≤ Mu.sourceValue q root) :
    CanonicalHeight.canonicalHeightCode (betaCode q root) next <
      CanonicalHeight.canonicalHeightCode q root := by
  have hmu := Mu.muCode_spec q root ha
  have hbound : interpretation (betaCode q root) next ≤
      interpretation (betaCode q root) (Mu.muCode q root) := by
    rw [hmu.2.2]
    exact hle
  exact (NativeContext.Mu.HeightSupport.canonicalHeightCode_mono_low _ _ _ hn hmu.1 hbound).trans_lt
    (mu_height_lt_root q root ha)

/-- Genuine HIGH root admission converts the actual canonical bound into
strict written height decrease across the two real source contexts. -/
theorem next_root_height_lt_root (q root next : Nat) (ha : Mu.inputCheck q root = true)
    (hn : Mu.inputCheck (betaCode q root) next = true)
    (hle : interpretation (betaCode q root) next ≤ Mu.sourceValue q root) :
    heightCode next < heightCode root := by
  have hs := low_next_height_lt_root q root next ha
    (RootLowCollapse.root_low (betaCode q root) next hn) hle
  simpa only [CanonicalHeight.canonicalHeightCode_normal _ _
    (RootLowCollapse.root_accepted (betaCode q root) next hn),
    CanonicalHeight.canonicalHeightCode_normal q root (RootLowCollapse.root_accepted q root ha)] using hs

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.SkHeight
