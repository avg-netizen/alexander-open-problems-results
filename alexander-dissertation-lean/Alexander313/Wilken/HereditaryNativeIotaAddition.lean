import Alexander313.Wilken.HereditaryNativeIotaAdditionSupport

/-!
# Addition on the actual normal restricted value domain

Ordinary ordinal addition can absorb source summands, so the written raw sum
need not itself be a normal source representation. The real atom absorption
and reconstruction algorithms construct an admitted, normal and restricted
representation of every sum. Its transformed value is the sum of the two
transformed values, deriving closure and the full additive clause on original
normal inputs without a normalization-commutation premise. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Iota.Addition

open NativePublicBridge (contextCode contextCode_checked)
open OrderInduction

def sourceSum (q : Nat) (t u : RelativeTerm Nat) : RelativeTerm Nat :=
  Normalization.buildAtoms (Normalization.normalizeAtoms q (Comparison.atoms t ++ Comparison.atoms u))

theorem sourceSum_primrec : Primrec
    (fun p : Nat × (RelativeTerm Nat × RelativeTerm Nat) => sourceSum p.1 p.2.1 p.2.2) :=
  Normalization.Effective.buildAtoms_primrec.comp
    (Normalization.Effective.normalizeAtoms_primrec.comp Primrec.fst
      (Primrec.list_append.comp (Comparison.atoms_primrec.comp (Primrec.fst.comp Primrec.snd))
        (Comparison.atoms_primrec.comp (Primrec.snd.comp Primrec.snd))))

/-- Genuine domain closure and ordinal addition in both real contexts.
All source and target admissions are conclusions of the original checks. -/
theorem sourceSum_spec (s a : Nat) (ha : rootCheck s a = true)
    (t u : RelativeTerm Nat) (ht : check (contextCode s) t = true)
    (hu : check (contextCode s) u = true)
    (hnt : Comparison.Normal (contextCode s) t) (hnu : Comparison.Normal (contextCode s) u)
    (hrt : Restricted s a t) (hru : Restricted s a u) :
    check (contextCode s) (sourceSum (contextCode s) t u) = true ∧
      Comparison.Normal (contextCode s) (sourceSum (contextCode s) t u) ∧
      Restricted s a (sourceSum (contextCode s) t u) ∧
      denote (contextCode s) (sourceSum (contextCode s) t u) =
        denote (contextCode s) t + denote (contextCode s) u ∧
      denote (alphaCode s a) (transform s a (sourceSum (contextCode s) t u)) =
        denote (alphaCode s a) (transform s a t) + denote (alphaCode s a) (transform s a u) := by
  let n := max (SourceOne.PublicCodes.fragment t) (SourceOne.PublicCodes.fragment u)
  have htn := Comparison.checked_admissible (contextCode s) n t ht
    ((SourceOne.PublicCodes.height_le_fragment t).trans (le_max_left _ _))
  have hun := Comparison.checked_admissible (contextCode s) n u hu
    ((SourceOne.PublicCodes.height_le_fragment u).trans (le_max_right _ _))
  let xs := Comparison.atoms t ++ Comparison.atoms u
  have hg : Normalization.GoodAtoms (contextCode s) n xs :=
    (Normalization.GoodAtoms.atoms _ n (contextCode_checked s) t htn hnt).append
      (Normalization.GoodAtoms.atoms _ n (contextCode_checked s) u hun hnu)
  have hr : ∀ x ∈ xs, Restricted s a x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact restricted_atoms s a t x hrt hx
    · exact restricted_atoms s a u x hru hx
  have hrn : ∀ x ∈ Normalization.normalizeAtoms (contextCode s) xs, Restricted s a x :=
    fun x hx => hr x (Normalization.normalizeAtoms_mem _ x xs hx)
  have had := Normalization.buildAtoms_admissible (contextCode s) n (contextCode_checked s) _
    hg.normalizeAtoms
  have hn := Normalization.buildAtoms_normal (contextCode s) n _ hg.normalizeAtoms
    (Normalization.normalizeAtoms_normal _ n (contextCode_checked s) xs hg)
  refine ⟨Comparison.admitted_checked _ n (contextCode_checked s) _ had, hn,
    buildAtoms_restricted s a _ hrn, ?_, ?_⟩
  · rw [sourceSum, Normalization.buildAtoms_denote,
      Normalization.normalizeAtoms_denote _ n (contextCode_checked s) xs hg]
    rw [List.map_append, principalSum_append,
      source_atoms_value _ t ht hnt, source_atoms_value _ u hu hnu]
  · rw [sourceSum, transform_buildAtoms_value s a n ha _ hg.normalizeAtoms hrn,
      normalizeAtoms_mapped s a n ha xs hg hr]
    have hpr : ∀ p ∈ xs.map (fun x => denote (alphaCode s a) (transform s a x)),
        0 < p ∧ Ordinal.IsPrincipal (· + ·) p := by
      intro p hp
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
      rcases List.mem_append.mp hx with hx | hx
      · exact transform_atom_principal s a ha t x ht hnt hrt hx
      · exact transform_atom_principal s a ha u x hu hnu hru hx
    rw [principalSum_normalizePrincipal _ hpr, List.map_append, principalSum_append,
      mapped_atoms_value s a ha t ht hnt hrt, mapped_atoms_value s a ha u hu hnu hru]

theorem sourceSum_iota_caller (s a : Nat) (ha : rootCheck s a = true)
    (t u : RelativeTerm Nat) (ht : check (contextCode s) t = true)
    (hu : check (contextCode s) u = true)
    (hnt : Comparison.Normal (contextCode s) t) (hnu : Comparison.Normal (contextCode s) u)
    (hrt : Restricted s a t) (hru : Restricted s a u) :
    inputCheck s a (sourceSum (contextCode s) t u).code = true := by
  have hs := sourceSum_spec s a ha t u ht hu hnt hnu hrt hru
  exact (inputCheck_exact s a _).mpr ⟨ha, sourceSum (contextCode s) t u, rfl, hs.1, hs.2.1,
    (restricted_iff_sourceStar s a ha _ hs.1 hs.2.1).mp hs.2.2.1⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Iota.Addition
