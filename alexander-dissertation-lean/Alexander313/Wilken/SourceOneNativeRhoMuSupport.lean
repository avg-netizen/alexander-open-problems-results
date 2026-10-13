import Alexander313.Wilken.SourceOneNativeMappedOmegaQuotient
import Alexander313.Wilken.SourceOneNativeMu
import Alexander313.Wilken.HereditaryNativeRhoMu

/-!
# Actual original source-one coefficient remains zero or a proper limit

The real quotient ANF and literal unit filter exclude every unit from the
original coefficient word. Original source-one iota reflects order against
its genuine unit and maps positive principals by actual ANF singleton
shape. This derives the required mapped limit condition. Only the genuine
alpha target enters native rho; no Native base-one source is supplied.
These source-only proof candidates are uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.RhoMuSupport

open OrderSupport OmegaQuotient

private theorem principalSum_limit_zero (as : List Ordinal.{0})
    (hs : ∀ p ∈ as, 1 < p ∧ Ordinal.IsPrincipal (· + ·) p) :
    principalSum as = 0 ∨ IsSuccLimit (principalSum as) := by
  revert hs
  induction as with
  | nil => intro hs; exact Or.inl rfl
  | cons p as ih =>
    intro hs
    have hp := hs p List.mem_cons_self
    rcases ih (fun q hq => hs q (List.mem_cons_of_mem _ hq)) with hz | hl
    · exact Or.inr (by simpa only [principalSum, hz, add_zero] using
        Ordinal.isSuccLimit_of_isPrincipal_add hp.1 hp.2)
    · exact Or.inr (Ordinal.isSuccLimit_add _ hl)

/-- Every actual original stripped coefficient word maps to zero or a
proper limit; the source word's genuine unit filter supplies the proof. -/
theorem mapped_limitTerm_zero_or_limit (a c : Nat) (ha : rootCheck a = true)
    (hc : SourceDecomposition.inputCheck 0 c = true) (hr : Restricted a (ThetaCourse.rawTree c)) :
    NativeContext.denote (alphaCode a) (transform a (limitTerm c)) = 0 ∨
      IsSuccLimit (NativeContext.denote (alphaCode a) (transform a (limitTerm c))) := by
  have hg := quotientWord_good a c ha hc hr
  have hmem : ∀ t ∈ limitWord c, t ∈ quotientWord c :=
    fun t ht => ((selectUnits_mem false _ t).mp ht).1
  have hgl : Theta.Normalization.GoodAtoms 0 (wordHeight (quotientWord c)) (limitWord c) :=
    fun t ht => hg t (hmem t ht)
  have hrest : ∀ t ∈ limitWord c, Restricted a t := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp (hmem t ht)
    exact (high_atom_spec a c ha hc hr u hu).2.2.1
  have hut : NativeContext.denote (alphaCode a) (transform a unitTerm) = 1 :=
    (transform_low_value a ha unitTerm unitTerm_spec.1
      (MappedOmegaQuotient.unitTerm_restricted a ha) (by
        simp only [unitTerm, RelativeTerm.outerSort]; omega)).trans unitTerm_spec.2.2
  rw [limitTerm, Addition.transform_buildAtoms_value a _ ha _ hgl hrest]
  apply principalSum_limit_zero
  intro p hp
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hp
  have htgood := hgl t ht
  have htc := Theta.admitted_checked htgood.1
  have htp := Addition.transform_positive_principal a ha t htc htgood.2.1
    (hrest t ht) htgood.2.2.1 htgood.2.2.2
  refine ⟨?_, htp.2⟩
  rw [← hut]
  apply (transform_lt_iff a ha unitTerm t unitTerm_spec.1 htc unitTerm_spec.2.1
    htgood.2.1 (MappedOmegaQuotient.unitTerm_restricted a ha) (hrest t ht)).mpr
  rw [unitTerm_spec.2.2]
  apply lt_of_le_of_ne (Order.one_le_iff_pos.mpr htgood.2.2.1)
  intro he
  have hu := (unitTest_exact t htc htgood.2.1).mpr he.symm
  have hnot := ((selectUnits_mem false _ t).mp ht).2
  simp only [Bool.cond_false, hu, Bool.not_true, Bool.false_eq_true] at hnot

theorem mappedCoefficient_zero_or_limit (a : Nat) (ha : Mu.inputCheck a = true) :
    NativeContext.interpretation (alphaCode a) (Mu.mappedCoefficient a) = 0 ∨
      IsSuccLimit (NativeContext.interpretation (alphaCode a) (Mu.mappedCoefficient a)) := by
  have hs := root_coefficient_spec a ha
  have he : Mu.mappedCoefficient a = (transform a (limitTerm (argumentCode a))).code := by
    rw [Mu.mappedCoefficient, coefficientCode_literal a ha,
      literalCode_code a ha _ hs.1 hs.2.1 hs.2.2.1]
  rw [he, NativeContext.interpretation_code]
  exact mapped_limitTerm_zero_or_limit a _ ha (argument_accepted a ha) (argument_restricted a ha)

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.RhoMuSupport
