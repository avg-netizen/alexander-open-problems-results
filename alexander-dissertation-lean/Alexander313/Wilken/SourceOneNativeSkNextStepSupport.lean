import Alexander313.Wilken.SourceOneNativeMuHeight
import Alexander313.Wilken.PublicEpsilonNativeTrackingSequencesSupport
import Alexander313.Wilken.PublicEpsilonNativeSkNextSearchSupport

/-!
# Genuine original source-one first sk-step callers and height decrease

The original check-zero HIGH root executes actual source-one mu and lambda.
Their genuine different-context height inequalities bound every LOW next
value at its real epsilon alpha context by a strictly smaller height.
Actual public mu and overlined factor truncation supply the canonical
search query and its native LOW boundary. Native parsing is used only at
the genuine epsilon alpha, never at the original base one. No supplied
representative, cutoff, successor convention or height oracle. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SkNextStepSupport

theorem mu_height_lt_root (root : Nat) (ha : Mu.inputCheck root = true) :
    NativeContext.CanonicalHeight.canonicalHeightCode (alphaCode root) (Mu.muCode root) <
      SourceOne.CanonicalHeight.canonicalHeightCode root := by
  obtain ⟨out, ho⟩ := Lambda.execute_returns root ha
  exact (Mu.Height.muCode_canonical_height_le_lambda root out ho).trans_lt
    (Lambda.source_lemma_2_48_c root out ho)

theorem low_next_height_lt_root (root next : Nat) (ha : Mu.inputCheck root = true)
    (hn : NativeContext.lowCheckCode (alphaCode root) next = true)
    (hle : NativeContext.interpretation (alphaCode root) next ≤ Mu.sourceValue root) :
    NativeContext.CanonicalHeight.canonicalHeightCode (alphaCode root) next <
      SourceOne.CanonicalHeight.canonicalHeightCode root := by
  have hmu := Mu.muCode_spec root ha
  have hbound : NativeContext.interpretation (alphaCode root) next ≤
      NativeContext.interpretation (alphaCode root) (Mu.muCode root) := by
    rw [hmu.2.2]
    exact hle
  exact (Mu.HeightSupport.canonicalHeightCode_mono_low _ _ _ hn hmu.1 hbound).trans_lt
    (mu_height_lt_root root ha)

theorem next_root_height_lt_root (root next : Nat) (ha : Mu.inputCheck root = true)
    (hn : NativeContext.PublicEpsilonUnboundedIota.Mu.inputCheck (alphaCode root) next = true)
    (hle : NativeContext.interpretation (alphaCode root) next ≤ Mu.sourceValue root) :
    heightCode next < heightCode root := by
  have hs := low_next_height_lt_root root next ha
    (NativeContext.RootLowCollapse.root_low (alphaCode root) next hn) hle
  simpa only [NativeContext.CanonicalHeight.canonicalHeightCode_normal _ _
    (NativeContext.RootLowCollapse.root_accepted (alphaCode root) next hn),
    SourceOne.CanonicalHeight.canonicalHeightCode_normal _
      (SourceOneIota.HeightSupport.root_source_accepted root ha)] using hs

noncomputable def nextValue (root : Nat) (cutoff : Ordinal.{0}) : Ordinal.{0} :=
  Alexander313.Wilken.MultiplicativeFactorTruncation.truncate (Mu.sourceValue root) cutoff

theorem mu_pos_principal (root : Nat) :
    0 < Mu.sourceValue root ∧ Ordinal.IsPrincipal (· + ·) (Mu.sourceValue root) := by
  unfold Mu.sourceValue
  exact ⟨Ordinal.opow_pos _ Ordinal.omega0_pos, Ordinal.isPrincipal_add_omega0_opow _⟩

theorem nextValue_le_mu (root : Nat) (cutoff : Ordinal.{0}) : nextValue root cutoff ≤ Mu.sourceValue root :=
  Alexander313.Wilken.MultiplicativeFactorTruncation.truncate_le
    (mu_pos_principal root).1 (mu_pos_principal root).2 cutoff

theorem nextValue_boundary (root : Nat) (ha : Mu.inputCheck root = true) (cutoff : Ordinal.{0}) :
    nextValue root cutoff < globalBoundary (NativeContext.base (alphaCode root)) 0 := by
  have hb := NativeContext.checked_low_bound (alphaCode root) (Mu.muCode root) (Mu.muCode_spec root ha).1
  rw [(Mu.muCode_spec root ha).2.2] at hb
  exact (nextValue_le_mu root cutoff).trans_lt hb

theorem muPublicCode_principal (root : Nat) (ha : Mu.inputCheck root = true) :
    Principal.unionPrincipalCheck (SourceTrackingSupport.muPublicCode root) = true := by
  have hs := SourceTrackingSupport.muPublicCode_spec root ha
  apply (Principal.unionPrincipalCheck_exact _).mpr
  rw [hs.2]
  exact ⟨Canonical.check_original hs.1, mu_pos_principal root⟩

theorem truncation_spec (root cutoff out : Nat) (ha : Mu.inputCheck root = true)
    (ho : out ∈ FactorTruncation.truncate (SourceTrackingSupport.muPublicCode root) cutoff) :
    Canonical.check out = true ∧ unionInterpretation out = nextValue root (unionInterpretation cutoff) := by
  have hs := FactorTruncation.truncate_value _ _ out ho
  exact ⟨hs.2.2.1, hs.2.2.2.trans (by rw [(SourceTrackingSupport.muPublicCode_spec root ha).2]; rfl)⟩

theorem truncation_search_returns (root cutoff out : Nat) (ha : Mu.inputCheck root = true)
    (ho : out ∈ FactorTruncation.truncate (SourceTrackingSupport.muPublicCode root) cutoff) :
    ∃ d, d ∈ NativeContext.PublicEpsilonUnboundedIota.SkNextSearch.Support.search (alphaCode root) out := by
  have hs := truncation_spec root cutoff out ha ho
  exact NativeContext.PublicEpsilonUnboundedIota.SkNextSearch.Support.search_returns _ out
    (alphaCode_baseCheck root ha) hs.1 (by rw [hs.2]; exact nextValue_boundary root ha _)

theorem source_definition_3_33_bounds (root : Nat) (cutoff : Ordinal.{0})
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal cutoff) (hpos : 1 < cutoff)
    (hc : cutoff ≤ Mu.sourceValue root) :
    cutoff ≤ nextValue root cutoff ∧ nextValue root cutoff ≤ Mu.sourceValue root ∧
      cutoff ≤ Alexander313.Wilken.MultiplicativeNormalForm.lf (nextValue root cutoff) :=
  ⟨Alexander313.Wilken.MultiplicativeFactorTruncation.truncate_ge_source
      (mu_pos_principal root).1 (mu_pos_principal root).2 hm hpos hc,
    nextValue_le_mu root cutoff,
    Alexander313.Wilken.MultiplicativeFactorTruncation.truncate_lf_ge_source
      (mu_pos_principal root).1 (mu_pos_principal root).2 hm hpos hc⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SkNextStepSupport
