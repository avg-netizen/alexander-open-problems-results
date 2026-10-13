import Alexander313.Wilken.SourceOneNativeAdditiveTrackingFactor
import Alexander313.Wilken.MultiplicativeFactorRemovalBounds

/-!
# Original source-one last-factor bounds from actual factor execution

The genuine public logarithm, retained canonical coefficient prefix and
real original-zero return identify the executed prefix product. Actual
descending reduced factors bound the last factor by its prefix's last
factor and product. No Native base-one dictionary or tracking endpoint is
substituted; source3.21's computed headword bound remains separate. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.Factor.Bounds

open FactorSupport
open Alexander313.Wilken.MultiplicativeNormalForm MultiplicativePrincipalArithmetic

theorem execute_prefix_value (c : Nat) (out : Output) (ho : out ∈ execute c) :
    interpretation 0 out.1 = factorProduct (factorPrefix (canonicalMNF (interpretation 0 c))) := by
  have hc := (execute_domain c).mp (Part.dom_iff_mem.mpr ⟨out, ho⟩)
  rw [execute, hc, Bool.cond_true] at ho
  obtain ⟨d, hd, rfl⟩ := (Part.mem_map_iff _).mp ho
  have hlog := PrincipalLogarithm.logarithm_value (publicCode c) d hd
  have hp := prefixPublicCode_spec d (Canonical.check_original hlog.2.2.2.1)
  have hpow : Ordinal.omega0 ^ unionInterpretation d = interpretation 0 c := by
    simpa only [publicCode, unionInterpretation_pair] using hlog.2.2.2.2
  have hword : omegaFactors (unionInterpretation d) = canonicalMNF (interpretation 0 c) := by
    rw [← hpow, canonicalMNF_omegaPower]
  rw [hword] at hp
  have hb : unionInterpretation (prefixPublicCode d) < finiteBase 1 := by
    rw [hp.2]
    have hi := (inputCheck_exact c).mp hc
    have hone : IsMultiplicativePrincipal (1 : Ordinal.{0}) :=
      ⟨zero_lt_one, Ordinal.isPrincipal_add_one, Ordinal.isPrincipal_mul_one⟩
    have hs := MultiplicativeFactorRemoval.source_prefix_last_interval hone
      (Order.one_le_iff_pos.mp hi.2.1) hi.2.2.1 hi.2.1 hi.2.2.2
    exact hs.2.1.trans_lt ((lt_nextBase_iff_code 0 _).mpr ⟨c, hi.1, rfl⟩)
  exact (SourceZeta.Transport.returnCode_spec 0 _ hp.1 hb).2.trans hp.2

theorem execute_last_le_prefix_last (c : Nat) (out : Output) (ho : out ∈ execute c) :
    interpretation 0 out.2 ≤ lf (interpretation 0 out.1) := by
  have hs := execute_spec c out ho
  have hi := (inputCheck_exact c).mp hs.1
  obtain ⟨_, _, _, _, _, _, _, _, _, hlast, _⟩ := hs
  rw [hlast, execute_prefix_value c out ho]
  exact MultiplicativeFactorRemoval.Bounds.source_last_le_prefix_last
    (Order.one_le_iff_pos.mp hi.2.1) hi.2.2.1 hi.2.2.2

theorem execute_last_le_prefix (c : Nat) (out : Output) (ho : out ∈ execute c) :
    interpretation 0 out.2 ≤ interpretation 0 out.1 := by
  have hs := execute_spec c out ho
  have hi := (inputCheck_exact c).mp hs.1
  obtain ⟨_, _, _, _, _, _, _, _, _, hlast, _⟩ := hs
  rw [hlast, execute_prefix_value c out ho]
  exact MultiplicativeFactorRemoval.Bounds.source_last_le_prefix_product
    (Order.one_le_iff_pos.mp hi.2.1) hi.2.2.1 hi.2.2.2

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.Factor.Bounds
