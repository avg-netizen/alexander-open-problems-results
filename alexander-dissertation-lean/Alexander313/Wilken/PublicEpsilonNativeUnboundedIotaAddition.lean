import Alexander313.Wilken.PublicEpsilonNativeUnboundedIotaAdditionSupport

/-!
# Addition on the actual normal restricted value domain

Ordinary ordinal addition can absorb source summands at the ANY literal admitted coded epsilon q, so the written raw sum
need not itself be a normal source representation. The real atom absorption
and reconstruction algorithms construct an admitted, normal and restricted
representation of every sum. Its transformed value is the sum of the two
transformed values, deriving closure and the full additive clause on original
normal inputs without a normalization-commutation premise. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.Addition

open OrderSupport
open Iota.OrderInduction (atoms_checked_normal source_atoms_value checked_theta_pos_principal)

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
theorem sourceSum_spec (q root : Nat) (ha : rootCheck q root = true)
    (t u : RelativeTerm Nat) (ht : check q t = true)
    (hu : check q u = true)
    (hnt : Comparison.Normal q t) (hnu : Comparison.Normal q u)
    (hrt : Restricted q root t) (hru : Restricted q root u) :
    check q (sourceSum q t u) = true ∧
      Comparison.Normal q (sourceSum q t u) ∧
      Restricted q root (sourceSum q t u) ∧
      denote q (sourceSum q t u) =
        denote q t + denote q u ∧
      denote (betaCode q root) (transform q root (sourceSum q t u)) =
        denote (betaCode q root) (transform q root t) + denote (betaCode q root) (transform q root u) := by
  let n := max (SourceOne.PublicCodes.fragment t) (SourceOne.PublicCodes.fragment u)
  have htn := Comparison.checked_admissible q n t ht
    ((SourceOne.PublicCodes.height_le_fragment t).trans (le_max_left _ _))
  have hun := Comparison.checked_admissible q n u hu
    ((SourceOne.PublicCodes.height_le_fragment u).trans (le_max_right _ _))
  let xs := Comparison.atoms t ++ Comparison.atoms u
  have hg : Normalization.GoodAtoms q n xs :=
    (Normalization.GoodAtoms.atoms _ n (source_checked q root ha) t htn hnt).append
      (Normalization.GoodAtoms.atoms _ n (source_checked q root ha) u hun hnu)
  have hr : ∀ x ∈ xs, Restricted q root x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact restricted_atoms q root t x hrt hx
    · exact restricted_atoms q root u x hru hx
  have hrn : ∀ x ∈ Normalization.normalizeAtoms q xs, Restricted q root x :=
    fun x hx => hr x (Normalization.normalizeAtoms_mem _ x xs hx)
  have had := Normalization.buildAtoms_admissible q n (source_checked q root ha) _
    hg.normalizeAtoms
  have hn := Normalization.buildAtoms_normal q n _ hg.normalizeAtoms
    (Normalization.normalizeAtoms_normal _ n (source_checked q root ha) xs hg)
  refine ⟨Comparison.admitted_checked _ n (source_checked q root ha) _ had, hn,
    buildAtoms_restricted q root _ hrn, ?_, ?_⟩
  · rw [sourceSum, Normalization.buildAtoms_denote,
      Normalization.normalizeAtoms_denote _ n (source_checked q root ha) xs hg]
    rw [List.map_append, principalSum_append,
      source_atoms_value _ t ht hnt, source_atoms_value _ u hu hnu]
  · rw [sourceSum, transform_buildAtoms_value q root n ha _ hg.normalizeAtoms hrn,
      normalizeAtoms_mapped q root n ha xs hg hr]
    have hpr : ∀ p ∈ xs.map (fun x => denote (betaCode q root) (transform q root x)),
        0 < p ∧ Ordinal.IsPrincipal (· + ·) p := by
      intro p hp
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
      rcases List.mem_append.mp hx with hx | hx
      · exact transform_atom_principal q root ha t x ht hnt hrt hx
      · exact transform_atom_principal q root ha u x hu hnu hru hx
    rw [principalSum_normalizePrincipal _ hpr, List.map_append, principalSum_append,
      mapped_atoms_value q root ha t ht hnt hrt, mapped_atoms_value q root ha u hu hnu hru]

theorem sourceSum_iota_caller (q root : Nat) (ha : rootCheck q root = true)
    (t u : RelativeTerm Nat) (ht : check q t = true)
    (hu : check q u = true)
    (hnt : Comparison.Normal q t) (hnu : Comparison.Normal q u)
    (hrt : Restricted q root t) (hru : Restricted q root u) :
    inputCheck q root (sourceSum q t u).code = true := by
  have hs := sourceSum_spec q root ha t u ht hu hnt hnu hrt hru
  exact (inputCheck_exact q root _).mpr ⟨ha, sourceSum q t u, rfl, hs.1, hs.2.1,
    (restricted_iff_sourceStar q root ha _ hs.1 hs.2.1).mp hs.2.2.1⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.Addition
