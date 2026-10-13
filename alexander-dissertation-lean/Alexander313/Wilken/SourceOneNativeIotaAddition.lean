import Alexander313.Wilken.SourceOneNativeIotaAdditionSupport

/-!
# Actual ordinary addition on the original source-one iota domain

The actual ORIGINAL atom normalizer and source-one builder construct a
checked Normal fully restricted source sum. Genuine principal absorption
derives its mapped ordinary addition value. No raw-normal sum or
normalization-commutation premise is assumed. Source-only and uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.Addition

open OrderSupport

def sourceSum (t u : RelativeTerm Nat) : RelativeTerm Nat :=
  Theta.Normalization.buildAtoms 0
    (Theta.Normalization.normalizeAtoms 0 (thetaAtoms t ++ thetaAtoms u))

theorem sourceSum_primrec : Primrec₂ sourceSum :=
  (Theta.Normalization.Effective.buildAtoms_primrec.comp (Primrec.const 0)
    (Theta.Normalization.Effective.normalizeAtoms_primrec.comp (Primrec.const 0)
      (Primrec.list_append.comp
        (Theta.Effective.atoms_primrec.comp (Primrec.const 0) Primrec.fst)
        (Theta.Effective.atoms_primrec.comp (Primrec.const 0) Primrec.snd)))).to₂

theorem sourceSum_spec (a : Nat) (ha : rootCheck a = true)
    (t u : RelativeTerm Nat) (ht : check 0 t = true) (hu : check 0 u = true)
    (hnt : Theta.Normal 0 t) (hnu : Theta.Normal 0 u)
    (hrt : Restricted a t) (hru : Restricted a u) :
    check 0 (sourceSum t u) = true ∧ Theta.Normal 0 (sourceSum t u) ∧
      Restricted a (sourceSum t u) ∧
      denote 0 (sourceSum t u) = denote 0 t + denote 0 u ∧
      NativeContext.denote (alphaCode a) (transform a (sourceSum t u)) =
        NativeContext.denote (alphaCode a) (transform a t) +
          NativeContext.denote (alphaCode a) (transform a u) := by
  let n := max (SourceOne.PublicCodes.fragment t) (SourceOne.PublicCodes.fragment u)
  have htn := Theta.checked_admissible 0 n t ht
    ((SourceOne.PublicCodes.height_le_fragment t).trans (le_max_left _ _))
  have hun := Theta.checked_admissible 0 n u hu
    ((SourceOne.PublicCodes.height_le_fragment u).trans (le_max_right _ _))
  let xs := thetaAtoms t ++ thetaAtoms u
  have hg : Theta.Normalization.GoodAtoms 0 n xs :=
    (Theta.Normalization.GoodAtoms.atoms 0 n t htn hnt).append
      (Theta.Normalization.GoodAtoms.atoms 0 n u hun hnu)
  have hr : ∀ x ∈ xs, Restricted a x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact restricted_atoms a t x hrt hx
    · exact restricted_atoms a u x hru hx
  have hrn : ∀ x ∈ Theta.Normalization.normalizeAtoms 0 xs, Restricted a x :=
    fun x hx => hr x (Theta.Normalization.normalizeAtoms_mem 0 x xs hx)
  have had := Theta.Normalization.buildAtoms_admissible 0 n _ hg.normalizeAtoms
  have hn := Theta.Normalization.buildAtoms_normal 0 n _ hg.normalizeAtoms
    (Theta.Normalization.normalizeAtoms_normal 0 n xs hg)
  refine ⟨Theta.admitted_checked had, hn, OmegaQuotient.buildAtoms_restricted a _ hrn, ?_, ?_⟩
  · rw [sourceSum, Theta.Normalization.buildAtoms_denote,
      Theta.Normalization.normalizeAtoms_denote 0 n xs hg]
    rw [List.map_append, principalSum_append, source_atoms_value t ht hnt,
      source_atoms_value u hu hnu]
  · rw [sourceSum, transform_buildAtoms_value a n ha _ hg.normalizeAtoms hrn,
      normalizeAtoms_mapped a n ha xs hg hr]
    have hpr : ∀ p ∈ xs.map (fun x => NativeContext.denote (alphaCode a) (transform a x)),
        0 < p ∧ Ordinal.IsPrincipal (· + ·) p := by
      intro p hp
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
      rcases List.mem_append.mp hx with hx | hx
      · exact transform_atom_principal a ha t x ht hnt hrt hx
      · exact transform_atom_principal a ha u x hu hnu hru hx
    rw [principalSum_normalizePrincipal _ hpr, List.map_append, principalSum_append,
      mapped_atoms_value a ha t ht hnt hrt, mapped_atoms_value a ha u hu hnu hru]

theorem sourceSum_iota_caller (a : Nat) (ha : rootCheck a = true)
    (t u : RelativeTerm Nat) (ht : check 0 t = true) (hu : check 0 u = true)
    (hnt : Theta.Normal 0 t) (hnu : Theta.Normal 0 u)
    (hrt : Restricted a t) (hru : Restricted a u) : inputCheck a (sourceSum t u).code = true := by
  have hs := sourceSum_spec a ha t u ht hu hnt hnu hrt hru
  exact (inputCheck_exact a _).mpr ⟨ha, sourceSum t u, rfl, hs.1, hs.2.1,
    (restricted_iff_sourceStar a ha _ hs.1 hs.2.1).mp hs.2.2.1⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.Addition
