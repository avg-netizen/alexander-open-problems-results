import Alexander313.Wilken.PublicEpsilonNativeUnboundedIotaInverseSupport

/-!
# Complete semantic image and two genuine inverses without an endpoint

Every target parameter acquires an ORIGINAL-q LOW source representative
from actual interval coverage. The raised-index lift has full source
restriction and recovers target value. Actual mapped ANF and full order
reflection derive original weak Normality, including the genuine
final-principal binary sum clause. Real target normalization then supplies
an original Normal restricted inverse for EVERY checked target expression.
No representative, coverage, inverse, target Normal or presentation oracle
is an input. These semantic choices establish termination of the actual
least-code search in the companion module; no primitive-recursive choice
or syntactic inverse of arbitrary presentations is asserted. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.Inverse

open OrderSupport
open Iota.OrderInduction (normalSum_words_iff atoms_checked_normal source_atoms_normal source_atoms_value)

/-- Reflect the actual final-principal sum clause by comparing the SAME
source atom words in the two contexts. Word shape is preserved even when
the whole transformed low expression is a single public parameter. -/
theorem reflect_normalSum (q root : Nat) (ha : rootCheck q root = true)
    (t u : RelativeTerm Nat) (ht : check q t = true)
    (hu : check q u = true)
    (hnt : Comparison.Normal q t) (hnu : Comparison.Normal q u)
    (hrt : Restricted q root t) (hru : Restricted q root u)
    (hs : SourceNormalSum
      (denote (betaCode q root) (transform q root t) + denote (betaCode q root) (transform q root u))
      (denote (betaCode q root) (transform q root t)) (denote (betaCode q root) (transform q root u))) :
    SourceNormalSum (denote q t + denote q u)
      (denote q t) (denote q u) := by
  have htw : IsAdditiveNormalForm ((Comparison.atoms t).map
      (fun x => denote (betaCode q root) (transform q root x))) := by
    rw [transform_atoms_anf q root ha t ht hnt hrt]
    exact canonicalANF_normal _
  have huw : IsAdditiveNormalForm ((Comparison.atoms u).map
      (fun x => denote (betaCode q root) (transform q root x))) := by
    rw [transform_atoms_anf q root ha u hu hnu hru]
    exact canonicalANF_normal _
  have htarget := (normalSum_words_iff
    (fun x => denote (betaCode q root) (transform q root x))
    (Comparison.atoms t) (Comparison.atoms u) htw huw).mp (by
      simpa only [mapped_atoms_value q root ha t ht hnt hrt,
        mapped_atoms_value q root ha u hu hnu hru] using hs)
  have hshape : (Comparison.atoms t = [] ∧ Comparison.atoms u = []) ∨
      ∃ y, Comparison.atoms u = [y] ∧ ∀ x ∈ Comparison.atoms t,
        denote q y ≤ denote q x := by
    rcases htarget with hz | ⟨y, hy, hle⟩
    · exact Or.inl hz
    · refine Or.inr ⟨y, hy, ?_⟩
      intro x hx
      have hxc := atoms_checked_normal _ t x ht hnt hx
      have hyc := atoms_checked_normal _ u y hu hnu (by rw [hy]; exact List.mem_singleton_self _)
      exact (transform_le_iff q root ha y x hyc.1 hxc.1 hyc.2 hxc.2
        (restricted_atoms q root u y hru (by rw [hy]; exact List.mem_singleton_self _))
        (restricted_atoms q root t x hrt hx)).mp (hle x hx)
  have hsource := (normalSum_words_iff (denote q)
    (Comparison.atoms t) (Comparison.atoms u) (source_atoms_normal _ t ht hnt)
    (source_atoms_normal _ u hu hnu)).mpr hshape
  simpa only [source_atoms_value _ t ht hnt, source_atoms_value _ u hu hnu] using hsource

theorem lift_normal (q root : Nat) (ha : rootCheck q root = true)
    (t : RelativeTerm Nat) (ht : check (betaCode q root) t = true)
    (hn : Comparison.Normal (betaCode q root) t) : Comparison.Normal q (lift q root t) := by
  revert ht hn
  induction t with
  | parameter p =>
    intro ht hn
    exact (atom_spec q root p ha (NativeContext.checked_admissible _ _ ht).1).2.1
  | sum t u iht ihu =>
    intro ht hn
    have hc := BaseTransformation.sum_checks _ t u ht
    have hnt := iht hc.1 hn.1
    have hnu := ihu hc.2 hn.2.1
    refine ⟨hnt, hnu, ?_⟩
    apply reflect_normalSum q root ha (lift q root t) (lift q root u)
      (lift_checked q root ha t hc.1) (lift_checked q root ha u hc.2) hnt hnu
      (lift_restricted q root ha t hc.1) (lift_restricted q root ha u hc.2)
    simpa only [lift_right_inverse q root ha t hc.1,
      lift_right_inverse q root ha u hc.2] using hn.2.2
  | theta k t ih =>
    intro ht hn
    exact ih (BaseTransformation.theta_argument_check _ k t ht) hn

/-- The semantic inverse first applies the genuine target normalizer.
Its input is the original target tree, with no supplied normality guard. -/
noncomputable def inverse (q root : Nat) (t : RelativeTerm Nat) : RelativeTerm Nat :=
  lift q root (Normalization.normalize (betaCode q root) t)

theorem inverse_spec (q root : Nat) (ha : rootCheck q root = true)
    (t : RelativeTerm Nat) (ht : check (betaCode q root) t = true) :
    check q (inverse q root t) = true ∧
      Comparison.Normal q (inverse q root t) ∧
      Restricted q root (inverse q root t) ∧
      denote (betaCode q root) (transform q root (inverse q root t)) = denote (betaCode q root) t := by
  have hn := Normalization.normalize_checked _ t ht
  exact ⟨lift_checked q root ha _ hn.1, lift_normal q root ha _ hn.1 hn.2.1,
    lift_restricted q root ha _ hn.1, (lift_right_inverse q root ha _ hn.1).trans hn.2.2⟩

theorem inverse_sourceStar (q root : Nat) (ha : rootCheck q root = true)
    (t : RelativeTerm Nat) (ht : check (betaCode q root) t = true) :
    Iota.sourceStar q (inverse q root t) < interpretation q root := by
  have hs := inverse_spec q root ha t ht
  exact (restricted_iff_sourceStar q root ha _ hs.1 hs.2.1).mp hs.2.2.1

theorem inverse_iota_caller (q root : Nat) (ha : rootCheck q root = true)
    (t : RelativeTerm Nat) (ht : check (betaCode q root) t = true) :
    inputCheck q root (inverse q root t).code = true := by
  have hs := inverse_spec q root ha t ht
  exact (inputCheck_exact q root _).mpr ⟨ha, inverse q root t, rfl, hs.1, hs.2.1,
    inverse_sourceStar q root ha t ht⟩

theorem inverse_left_inverse (q root : Nat) (ha : rootCheck q root = true)
    (t : RelativeTerm Nat) (ht : check q t = true)
    (hn : Comparison.Normal q t) (hr : Restricted q root t) :
    denote q (inverse q root (transform q root t)) = denote q t := by
  have hs := inverse_spec q root ha _ (transform_checked q root ha t ht hr)
  exact (transform_eq_iff q root ha _ t hs.1 ht hs.2.1 hn hs.2.2.1 hr).mp hs.2.2.2

theorem inverse_lt_iff (q root : Nat) (ha : rootCheck q root = true)
    (t u : RelativeTerm Nat) (ht : check (betaCode q root) t = true)
    (hu : check (betaCode q root) u = true) :
    denote q (inverse q root t) < denote q (inverse q root u) ↔
      denote (betaCode q root) t < denote (betaCode q root) u := by
  have hs := inverse_spec q root ha t ht
  have hs' := inverse_spec q root ha u hu
  have he := transform_lt_iff q root ha _ _ hs.1 hs'.1 hs.2.1 hs'.2.1 hs.2.2.1 hs'.2.2.1
  rw [hs.2.2.2, hs'.2.2.2] at he
  exact he.symm

theorem inverse_eq_iff (q root : Nat) (ha : rootCheck q root = true)
    (t u : RelativeTerm Nat) (ht : check (betaCode q root) t = true)
    (hu : check (betaCode q root) u = true) :
    denote q (inverse q root t) = denote q (inverse q root u) ↔
      denote (betaCode q root) t = denote (betaCode q root) u := by
  have hs := inverse_spec q root ha t ht
  have hs' := inverse_spec q root ha u hu
  have he := transform_eq_iff q root ha _ _ hs.1 hs'.1 hs.2.1 hs'.2.1 hs.2.2.1 hs'.2.2.1
  rw [hs.2.2.2, hs'.2.2.2] at he
  exact he.symm

/-- Complete semantic image at the actual target epsilon, with the original
weak-normal restricted source domain. This is genuine T_alpha coverage. -/
theorem image_iff (q root : Nat) (ha : rootCheck q root = true) (ξ : Ordinal.{0}) :
    (∃ t : RelativeTerm Nat, check q t = true ∧
      Comparison.Normal q t ∧ Restricted q root t ∧
      denote (betaCode q root) (transform q root t) = ξ) ↔ GlobalNotation (base (betaCode q root)) 0 ξ := by
  constructor
  · rintro ⟨t, ht, hn, hr, rfl⟩
    exact checked_globalNotation _ _ (transform_checked q root ha t ht hr)
  · intro hξ
    obtain ⟨t, ht, hv⟩ := (globalNotation_iff_checked _ (betaCode_baseCheck q root ha) ξ).mp hξ
    have hs := inverse_spec q root ha t ht
    exact ⟨inverse q root t, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.trans hv⟩

theorem image_sourceStar_iff (q root : Nat) (ha : rootCheck q root = true) (ξ : Ordinal.{0}) :
    (∃ t : RelativeTerm Nat, check q t = true ∧
      Comparison.Normal q t ∧
      Iota.sourceStar q t < interpretation q root ∧
      denote (betaCode q root) (transform q root t) = ξ) ↔ GlobalNotation (base (betaCode q root)) 0 ξ := by
  rw [← image_iff q root ha ξ]
  constructor
  · rintro ⟨t, ht, hn, hr, hv⟩
    exact ⟨t, ht, hn, (restricted_iff_sourceStar q root ha t ht hn).mpr hr, hv⟩
  · rintro ⟨t, ht, hn, hr, hv⟩
    exact ⟨t, ht, hn, (restricted_iff_sourceStar q root ha t ht hn).mp hr, hv⟩


end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.Inverse
