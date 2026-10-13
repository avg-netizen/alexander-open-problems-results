import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingFactor
import Alexander313.Wilken.MultiplicativeFactorRemovalBounds

/-!
# Original factor inequalities from the actual native split execution

The actual logarithm and retained exponent prefix identify the executed
prefix with the genuine canonical MNF prefix product. Descending reduced
factors then bound the removed factor by that prefix's last factor and
product. No factor interval, last-factor comparison or tracking endpoint
is supplied. The later source3.21 headword bound remains separate. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.Factor.Bounds

open FactorSupport
open Alexander313.Wilken.MultiplicativeNormalForm MultiplicativePrincipalArithmetic

theorem execute_prefix_value (q c : Nat) (out : Output) (ho : out ∈ execute q c) :
    interpretation q out.1 = factorProduct (factorPrefix (canonicalMNF (interpretation q c))) := by
  have hc := (execute_domain q c).mp (Part.dom_iff_mem.mpr ⟨out, ho⟩)
  have hi := (splitCheck_exact q c).mp hc
  have hq := (HeightBoundary.input_spec q c hi.1).2.1
  have hpos := (base_pos q hq).trans_le hi.2.1
  rw [execute, hc, Bool.cond_true] at ho
  obtain ⟨d, hd, rfl⟩ := (Part.mem_map_iff _).mp ho
  have hs := LogEnd.execute_spec q c d hd
  have hlog : Ordinal.omega0 ^ interpretation q d = interpretation q c := by
    have h : Ordinal.omega0 ^ interpretation q d = Hereditary.LogEnd.endValue (interpretation q c) := by
      simpa only [Hereditary.LogEnd.SourceLogSpec, if_neg (ne_of_gt hpos),
        Hereditary.LogEnd.endValue] using hs.2.2.2
    exact h.trans (SourceChi.Powers.endValue_principal _ hpos hi.2.2.1)
  have hp := prefixCode_spec q d hs.2.1 hs.2.2.1
  have hword : omegaFactors (interpretation q d) = canonicalMNF (interpretation q c) := by
    rw [← hlog, canonicalMNF_omegaPower]
  rw [hword] at hp
  exact hp.2.2

/-- The actual final factor is below the last MNF factor of the actual
prefix output. This is the descending-factor part of the printed footnote. -/
theorem execute_last_le_prefix_last (q c : Nat) (out : Output) (ho : out ∈ execute q c) :
    interpretation q out.2 ≤ lf (interpretation q out.1) := by
  have hs := execute_spec q c out ho
  have hi := (splitCheck_exact q c).mp hs.1
  have hq := (HeightBoundary.input_spec q c hi.1).2.1
  have hpos := (base_pos q hq).trans_le hi.2.1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hlast, _⟩ := hs
  rw [hlast, execute_prefix_value q c out ho]
  exact MultiplicativeFactorRemoval.Bounds.source_last_le_prefix_last hpos hi.2.2.1 hi.2.2.2.1

theorem execute_last_le_prefix (q c : Nat) (out : Output) (ho : out ∈ execute q c) :
    interpretation q out.2 ≤ interpretation q out.1 := by
  have hs := execute_spec q c out ho
  have hi := (splitCheck_exact q c).mp hs.1
  have hq := (HeightBoundary.input_spec q c hi.1).2.1
  have hpos := (base_pos q hq).trans_le hi.2.1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hlast, _⟩ := hs
  rw [hlast, execute_prefix_value q c out ho]
  exact MultiplicativeFactorRemoval.Bounds.source_last_le_prefix_product hpos hi.2.2.1 hi.2.2.2.1

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.Factor.Bounds
