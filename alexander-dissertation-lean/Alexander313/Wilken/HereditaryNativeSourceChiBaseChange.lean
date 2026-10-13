import Alexander313.Wilken.HereditaryNativeSourceChiBaseChangeSupport
import Alexander313.Wilken.HereditaryNativeSourceChiInvariance

/-!
# The source indicator commutes with genuine smaller-epsilon pi

The exact original BaseTransformation guard supplies target admission from
the chosen presentation's atomic-stop Par bound. The weak-normal operation
retains the original word and changes its collapse context. Both indicators
therefore commute with its actual piCode, by the branch and labelled-fold
proofs in the support module. No extra fixed-point hypothesis is imposed.

The raw operation is the existing normalize-first rawPiCode: its target need
not admit a discarded raw summand. Its exact original raw guard and its real
normalized output are retained. This closes the chi and dual commutation law
on the constructed coded-epsilon pi domain, including zero and base words.
Identification of this chosen-presentation Par bound with unique printed Par
sets on arbitrary spellings, target base one, and rho/zeta commutation are
separate questions. All proof candidates remain uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceChi.BaseChange

theorem normal_inputs (q v c : Nat) (hc : BaseTransformation.normalInputCheck q v c = true) :
    SourceChi.inputCheck q c = true ∧
      SourceChi.inputCheck v (BaseTransformation.piCode q v c) = true := by
  obtain ⟨hi, hn⟩ := (BaseTransformation.normalInputCheck_exact q v c).mp hc
  have hs := BaseTransformation.inputCheck_checks q v c hi
  exact ⟨(SourceChi.inputCheck_exact q c).mpr ⟨hs.1, hn⟩,
    BaseTransformation.piCode_normal q v c hc⟩

/-- The actual chi triangle in source Lemma 3.4, on the original finite
coded-epsilon pi domain. Target admission is derived by the original guard. -/
theorem source_lemma_3_4 (q v c : Nat)
    (hc : BaseTransformation.normalInputCheck q v c = true) :
    SourceChi.chiCode v (BaseTransformation.piCode q v c) = SourceChi.chiCode q c := by
  have hs := normal_inputs q v c hc
  have hi := ((BaseTransformation.normalInputCheck_exact q v c).mp hc).1
  rw [BaseTransformation.piCode_eq q v c hi] at hs ⊢
  exact (chiCode_context q v c hs.1 hs.2).symm

theorem source_lemma_3_4_dual (q v c : Nat)
    (hc : BaseTransformation.normalInputCheck q v c = true) :
    SourceChi.dualCode v (BaseTransformation.piCode q v c) = SourceChi.dualCode q c := by
  have hs := normal_inputs q v c hc
  have hi := ((BaseTransformation.normalInputCheck_exact q v c).mp hc).1
  rw [BaseTransformation.piCode_eq q v c hi] at hs ⊢
  exact (dualCode_context q v c hs.1 hs.2).symm

theorem source_lemma_3_4_tree (q v : Nat) (t : RelativeTerm Nat)
    (ht : check q t = true) (hv : baseCheck v = true) (hl : base v < base q)
    (hp : BaseTransformation.ParBounded q v t) (hn : Comparison.Normal q t) :
    SourceChi.indicator v t = SourceChi.indicator q t := by
  have hi := (BaseTransformation.inputCheck_exact q v t.code).mpr
    ⟨by simpa only [checkCode_code] using ht, hv, hl,
      by simpa only [ThetaCourse.rawTree_code] using hp⟩
  have htv : check v t = true := by
    simpa only [checkCode_code] using (BaseTransformation.inputCheck_checks q v t.code hi).2.1
  exact (indicator_context q v t ht htv hn).symm

theorem raw_inputs (q v c : Nat) (hc : BaseTransformation.rawInputCheck q v c = true) :
    checkCode q c = true ∧
      SourceChi.inputCheck q (Normalization.normalizeCode q c) = true ∧
      SourceChi.inputCheck v (BaseTransformation.rawPiCode q v c) = true := by
  have hs := BaseTransformation.rawPiCode_spec q v c hc
  rw [BaseTransformation.rawPiCode_eq q v c hc] at hs
  exact ⟨(Bool.and_eq_true.mp hc).1, hs.1, by
    rw [BaseTransformation.rawPiCode_eq q v c hc]; exact hs.2.1⟩

/-- Normalize-first raw commutation retains exactly the existing raw pi
domain; original target admission of discarded syntax is not required. -/
theorem raw_chi_commute (q v c : Nat) (hc : BaseTransformation.rawInputCheck q v c = true) :
    SourceChi.chiCode v (BaseTransformation.rawPiCode q v c) = SourceChi.rawChiCode q c := by
  have hs := raw_inputs q v c hc
  rw [BaseTransformation.rawPiCode_eq q v c hc] at hs ⊢
  simp only [SourceChi.rawChiCode, SourceChi.rawInputCheck, hs.1, Bool.true_and]
  exact (chiCode_context q v _ hs.2.1 hs.2.2).symm

theorem raw_dual_commute (q v c : Nat) (hc : BaseTransformation.rawInputCheck q v c = true) :
    SourceChi.dualCode v (BaseTransformation.rawPiCode q v c) = SourceChi.rawDualCode q c := by
  have hs := raw_inputs q v c hc
  rw [BaseTransformation.rawPiCode_eq q v c hc] at hs ⊢
  simp only [SourceChi.rawDualCode, SourceChi.rawInputCheck, hs.1, Bool.true_and]
  exact (dualCode_context q v _ hs.2.1 hs.2.2).symm

theorem raw_target_chi (q v c : Nat) (hc : BaseTransformation.rawInputCheck q v c = true) :
    SourceChi.rawChiCode v (BaseTransformation.rawPiCode q v c) = SourceChi.rawChiCode q c := by
  have hs := raw_inputs q v c hc
  have ht := (SourceChi.inputCheck_exact v _).mp hs.2.2
  have hn := Normalization.normalizeCode_accepted v _ ht.1
  have he := SourceChi.Invariance.chiCode_invariant v _ _ hn.1 hs.2.2 hn.2
  have hv : SourceChi.rawChiCode v (BaseTransformation.rawPiCode q v c) =
      SourceChi.chiCode v (BaseTransformation.rawPiCode q v c) := by
    simp only [SourceChi.rawChiCode, SourceChi.rawInputCheck, ht.1, Bool.true_and]
    exact he
  exact hv.trans (raw_chi_commute q v c hc)

theorem raw_target_dual (q v c : Nat) (hc : BaseTransformation.rawInputCheck q v c = true) :
    SourceChi.rawDualCode v (BaseTransformation.rawPiCode q v c) = SourceChi.rawDualCode q c := by
  have hs := raw_inputs q v c hc
  have ht := (SourceChi.inputCheck_exact v _).mp hs.2.2
  have hn := Normalization.normalizeCode_accepted v _ ht.1
  have he := SourceChi.Invariance.dualCode_invariant v _ _ hn.1 hs.2.2 hn.2
  have hv : SourceChi.rawDualCode v (BaseTransformation.rawPiCode q v c) =
      SourceChi.dualCode v (BaseTransformation.rawPiCode q v c) := by
    simp only [SourceChi.rawDualCode, SourceChi.rawInputCheck, ht.1, Bool.true_and]
    exact he
  exact hv.trans (raw_dual_commute q v c hc)

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceChi.BaseChange
