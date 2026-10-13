import Alexander313.Wilken.PublicEpsilonNativeSkHeightSupport
import Alexander313.Wilken.PublicEpsilonNativeContextTranslationSupport
import Alexander313.Wilken.MultiplicativeFactorTruncation

/-!
# Genuine LOW truncation and epsilon representative for a sk next step

The next ordinal is the independently constructed overlined MNF truncation
of actual mu, as in Definition3.33. Real retained-factor bounds make it at
most mu. The actual native LOW interval theorem therefore supplies a finite
checked next representation. When that truncation is epsilon strictly above
the current root, the real normalizer and last-atom parser construct an
actual HIGH root at that root's coded context, of strictly smaller height.
The threshold M>1 lower and last-factor bounds are the actual source ones.
No arbitrary representative, boundary or plus convention is assumed.
This is a proof-only next-step kernel, not an executing sk construction.
All candidates are uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.SkNextStep

open MultiplicativePrincipalArithmetic

noncomputable def nextValue (q root : Nat) (cutoff : Ordinal.{0}) : Ordinal.{0} :=
  Alexander313.Wilken.MultiplicativeFactorTruncation.truncate (Mu.sourceValue q root) cutoff

theorem mu_pos_principal (q root : Nat) :
    0 < Mu.sourceValue q root ∧ Ordinal.IsPrincipal (· + ·) (Mu.sourceValue q root) := by
  unfold Mu.sourceValue
  exact ⟨Ordinal.opow_pos _ Ordinal.omega0_pos, Ordinal.isPrincipal_add_omega0_opow _⟩

theorem nextValue_le_mu (q root : Nat) (cutoff : Ordinal.{0}) :
    nextValue q root cutoff ≤ Mu.sourceValue q root :=
  Alexander313.Wilken.MultiplicativeFactorTruncation.truncate_le
    (mu_pos_principal q root).1 (mu_pos_principal q root).2 cutoff

theorem nextValue_boundary (q root : Nat) (ha : Mu.inputCheck q root = true)
    (cutoff : Ordinal.{0}) :
    nextValue q root cutoff < globalBoundary (base (betaCode q root)) 0 := by
  have hb := checked_low_bound (betaCode q root) (Mu.muCode q root) (Mu.muCode_spec q root ha).1
  rw [(Mu.muCode_spec q root ha).2.2] at hb
  exact (nextValue_le_mu q root cutoff).trans_lt hb

/-- Every original mu caller derives an actual finite LOW representation
of its truncation, even if the next value does not continue the sk step. -/
theorem nextValue_low_exists (q root : Nat) (ha : Mu.inputCheck q root = true)
    (cutoff : Ordinal.{0}) :
    ∃ c, lowCheckCode (betaCode q root) c = true ∧
      interpretation (betaCode q root) c = nextValue q root cutoff :=
  (lt_boundary_iff_code (betaCode q root) (betaCode_baseCheck q root ha)
    (nextValue q root cutoff)).mp (nextValue_boundary q root ha cutoff)

/-- Precisely the epsilon-above-current-root continuation branch derives
its genuine HIGH next caller and strict written height decrease. -/
theorem nextValue_high_exists (q root : Nat) (ha : Mu.inputCheck q root = true)
    (cutoff : Ordinal.{0})
    (he : Ordinal.omega0 ^ nextValue q root cutoff = nextValue q root cutoff)
    (hp : interpretation q root < nextValue q root cutoff) :
    ∃ next, Mu.inputCheck (betaCode q root) next = true ∧
      interpretation (betaCode q root) next = nextValue q root cutoff ∧
        heightCode next < heightCode root := by
  obtain ⟨c, hc, hv⟩ := nextValue_low_exists q root ha cutoff
  have hpc : base (betaCode q root) < interpretation (betaCode q root) c := by
    rw [beta_base q root ha, hv]
    exact hp
  have hec : Ordinal.omega0 ^ interpretation (betaCode q root) c =
      interpretation (betaCode q root) c := by rw [hv]; exact he
  have hs := ContextTranslation.Support.rootAtomCode_spec (betaCode q root) c hc hpc hec
  have hvalue : interpretation (betaCode q root)
      (ContextTranslation.Support.rootAtomCode (betaCode q root) c) = nextValue q root cutoff :=
    hs.2.trans hv
  refine ⟨ContextTranslation.Support.rootAtomCode (betaCode q root) c, hs.1, hvalue, ?_⟩
  exact SkHeight.next_root_height_lt_root q root _ ha hs.1
    (hvalue.le.trans (nextValue_le_mu q root cutoff))

/-- The genuine source M>1 cutoff condition supplies both the lower bound
and retained final factor; ordinary multiplication is not used here. -/
theorem source_definition_3_33_bounds (q root : Nat) (cutoff : Ordinal.{0})
    (hm : IsMultiplicativePrincipal cutoff) (hpos : 1 < cutoff)
    (hc : cutoff ≤ Mu.sourceValue q root) :
    cutoff ≤ nextValue q root cutoff ∧ nextValue q root cutoff ≤ Mu.sourceValue q root ∧
      cutoff ≤ Alexander313.Wilken.MultiplicativeNormalForm.lf (nextValue q root cutoff) :=
  ⟨Alexander313.Wilken.MultiplicativeFactorTruncation.truncate_ge_source
      (mu_pos_principal q root).1 (mu_pos_principal q root).2 hm hpos hc,
    nextValue_le_mu q root cutoff,
    Alexander313.Wilken.MultiplicativeFactorTruncation.truncate_lf_ge_source
      (mu_pos_principal q root).1 (mu_pos_principal q root).2 hm hpos hc⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.SkNextStep
