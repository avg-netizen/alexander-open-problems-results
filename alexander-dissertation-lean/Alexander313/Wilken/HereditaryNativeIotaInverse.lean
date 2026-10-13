import Alexander313.Wilken.HereditaryNativeIotaInverseSupport
import Alexander313.Wilken.HereditaryNativeIotaOrderInduction

/-!
# Actual inverse and complete semantic image on the original iota domain

The finite lift has source weak Normality on every target weak-normal term.
This is derived from the genuine canonical principal words and the proved
order reflection, including the source's final-principal binary-sum clause.
Normalizing the original target before lifting therefore supplies an actual
source-normal inverse for EVERY admitted target code. Its full source-star
restriction, iota caller and two semantic inverse equations are proved.

No inverse, coverage, Normal transport or normalization-commutation oracle is
assumed. This constructs the image/inverse clause of Lemma 2.46(a) at the
same positive public source context. The printed height inequalities (b/c)
and a syntactic inverse of arbitrary original presentations are not claimed.
All proof terms remain uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Iota.Inverse

open NativePublicBridge (contextCode contextCode_checked)
open OrderInduction

/-- Reflect the actual final-principal sum clause by comparing the SAME
source atom words in the two contexts. Word shape is preserved even when
the whole transformed low expression is a single public parameter. -/
theorem reflect_normalSum (s a : Nat) (ha : rootCheck s a = true)
    (t u : RelativeTerm Nat) (ht : check (contextCode s) t = true)
    (hu : check (contextCode s) u = true)
    (hnt : Comparison.Normal (contextCode s) t) (hnu : Comparison.Normal (contextCode s) u)
    (hrt : Restricted s a t) (hru : Restricted s a u)
    (hs : SourceNormalSum
      (denote (alphaCode s a) (transform s a t) + denote (alphaCode s a) (transform s a u))
      (denote (alphaCode s a) (transform s a t)) (denote (alphaCode s a) (transform s a u))) :
    SourceNormalSum (denote (contextCode s) t + denote (contextCode s) u)
      (denote (contextCode s) t) (denote (contextCode s) u) := by
  have htw : IsAdditiveNormalForm ((Comparison.atoms t).map
      (fun x => denote (alphaCode s a) (transform s a x))) := by
    rw [transform_atoms_anf s a ha t ht hnt hrt]
    exact canonicalANF_normal _
  have huw : IsAdditiveNormalForm ((Comparison.atoms u).map
      (fun x => denote (alphaCode s a) (transform s a x))) := by
    rw [transform_atoms_anf s a ha u hu hnu hru]
    exact canonicalANF_normal _
  have htarget := (normalSum_words_iff
    (fun x => denote (alphaCode s a) (transform s a x))
    (Comparison.atoms t) (Comparison.atoms u) htw huw).mp (by
      simpa only [mapped_atoms_value s a ha t ht hnt hrt,
        mapped_atoms_value s a ha u hu hnu hru] using hs)
  have hshape : (Comparison.atoms t = [] ∧ Comparison.atoms u = []) ∨
      ∃ y, Comparison.atoms u = [y] ∧ ∀ x ∈ Comparison.atoms t,
        denote (contextCode s) y ≤ denote (contextCode s) x := by
    rcases htarget with hz | ⟨y, hy, hle⟩
    · exact Or.inl hz
    · refine Or.inr ⟨y, hy, ?_⟩
      intro x hx
      have hxc := atoms_checked_normal _ t x ht hnt hx
      have hyc := atoms_checked_normal _ u y hu hnu (by rw [hy]; exact List.mem_singleton_self _)
      exact (transform_le_iff s a ha y x hyc.1 hxc.1 hyc.2 hxc.2
        (restricted_atoms s a u y hru (by rw [hy]; exact List.mem_singleton_self _))
        (restricted_atoms s a t x hrt hx)).mp (hle x hx)
  have hsource := (normalSum_words_iff (denote (contextCode s))
    (Comparison.atoms t) (Comparison.atoms u) (source_atoms_normal _ t ht hnt)
    (source_atoms_normal _ u hu hnu)).mpr hshape
  simpa only [source_atoms_value _ t ht hnt, source_atoms_value _ u hu hnu] using hsource

theorem lift_normal (s a : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (alphaCode s a) t = true)
    (hn : Comparison.Normal (alphaCode s a) t) : Comparison.Normal (contextCode s) (lift s t) := by
  revert ht hn
  induction t with
  | parameter p =>
    intro ht hn
    exact (atom_spec s a p ha (NativeContext.checked_admissible _ _ ht).1).2.1
  | sum t u iht ihu =>
    intro ht hn
    have hc := BaseTransformation.sum_checks _ t u ht
    have hnt := iht hc.1 hn.1
    have hnu := ihu hc.2 hn.2.1
    refine ⟨hnt, hnu, ?_⟩
    apply reflect_normalSum s a ha (lift s t) (lift s u)
      (lift_checked s a ha t hc.1) (lift_checked s a ha u hc.2) hnt hnu
      (lift_restricted s a ha t hc.1) (lift_restricted s a ha u hc.2)
    simpa only [lift_right_inverse s a ha t hc.1,
      lift_right_inverse s a ha u hc.2] using hn.2.2
  | theta k t ih =>
    intro ht hn
    exact ih (BaseTransformation.theta_argument_check _ k t ht) hn

/-- The executing inverse first applies the genuine target normalizer.
Its input is the original target tree, with no supplied normality guard. -/
def inverse (s a : Nat) (t : RelativeTerm Nat) : RelativeTerm Nat :=
  lift s (Normalization.normalize (alphaCode s a) t)

theorem inverse_primrec : Primrec
    (fun p : (Nat × Nat) × RelativeTerm Nat => inverse p.1.1 p.1.2 p.2) :=
  lift_primrec.comp (Primrec.fst.comp Primrec.fst)
    (Normalization.Effective.normalize_primrec.comp
      (alphaCode_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)) Primrec.snd)

theorem inverse_spec (s a : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (alphaCode s a) t = true) :
    check (contextCode s) (inverse s a t) = true ∧
      Comparison.Normal (contextCode s) (inverse s a t) ∧
      Restricted s a (inverse s a t) ∧
      denote (alphaCode s a) (transform s a (inverse s a t)) = denote (alphaCode s a) t := by
  have hn := Normalization.normalize_checked _ t ht
  exact ⟨lift_checked s a ha _ hn.1, lift_normal s a ha _ hn.1 hn.2.1,
    lift_restricted s a ha _ hn.1, (lift_right_inverse s a ha _ hn.1).trans hn.2.2⟩

theorem inverse_sourceStar (s a : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (alphaCode s a) t = true) :
    sourceStar (contextCode s) (inverse s a t) < interpretation (contextCode s) a := by
  have hs := inverse_spec s a ha t ht
  exact (restricted_iff_sourceStar s a ha _ hs.1 hs.2.1).mp hs.2.2.1

theorem inverse_iota_caller (s a : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (alphaCode s a) t = true) :
    inputCheck s a (inverse s a t).code = true := by
  have hs := inverse_spec s a ha t ht
  exact (inputCheck_exact s a _).mpr ⟨ha, inverse s a t, rfl, hs.1, hs.2.1,
    inverse_sourceStar s a ha t ht⟩

theorem inverse_left_inverse (s a : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (contextCode s) t = true)
    (hn : Comparison.Normal (contextCode s) t) (hr : Restricted s a t) :
    denote (contextCode s) (inverse s a (transform s a t)) = denote (contextCode s) t := by
  have hs := inverse_spec s a ha _ (transform_checked s a ha t ht hr)
  exact (transform_eq_iff s a ha _ t hs.1 ht hs.2.1 hn hs.2.2.1 hr).mp hs.2.2.2

theorem inverse_lt_iff (s a : Nat) (ha : rootCheck s a = true)
    (t u : RelativeTerm Nat) (ht : check (alphaCode s a) t = true)
    (hu : check (alphaCode s a) u = true) :
    denote (contextCode s) (inverse s a t) < denote (contextCode s) (inverse s a u) ↔
      denote (alphaCode s a) t < denote (alphaCode s a) u := by
  have hs := inverse_spec s a ha t ht
  have hs' := inverse_spec s a ha u hu
  have he := transform_lt_iff s a ha _ _ hs.1 hs'.1 hs.2.1 hs'.2.1 hs.2.2.1 hs'.2.2.1
  rw [hs.2.2.2, hs'.2.2.2] at he
  exact he.symm

theorem inverse_eq_iff (s a : Nat) (ha : rootCheck s a = true)
    (t u : RelativeTerm Nat) (ht : check (alphaCode s a) t = true)
    (hu : check (alphaCode s a) u = true) :
    denote (contextCode s) (inverse s a t) = denote (contextCode s) (inverse s a u) ↔
      denote (alphaCode s a) t = denote (alphaCode s a) u := by
  have hs := inverse_spec s a ha t ht
  have hs' := inverse_spec s a ha u hu
  have he := transform_eq_iff s a ha _ _ hs.1 hs'.1 hs.2.1 hs'.2.1 hs.2.2.1 hs'.2.2.1
  rw [hs.2.2.2, hs'.2.2.2] at he
  exact he.symm

/-- Complete semantic image at the actual target epsilon, with the original
weak-normal restricted source domain. This is genuine T_alpha coverage. -/
theorem image_iff (s a : Nat) (ha : rootCheck s a = true) (ξ : Ordinal.{0}) :
    (∃ t : RelativeTerm Nat, check (contextCode s) t = true ∧
      Comparison.Normal (contextCode s) t ∧ Restricted s a t ∧
      denote (alphaCode s a) (transform s a t) = ξ) ↔ GlobalNotation (base (alphaCode s a)) 0 ξ := by
  constructor
  · rintro ⟨t, ht, hn, hr, rfl⟩
    exact checked_globalNotation _ _ (transform_checked s a ha t ht hr)
  · intro hξ
    obtain ⟨t, ht, hv⟩ := (globalNotation_iff_checked _ (alphaCode_baseCheck s a ha) ξ).mp hξ
    have hs := inverse_spec s a ha t ht
    exact ⟨inverse s a t, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.trans hv⟩

theorem image_sourceStar_iff (s a : Nat) (ha : rootCheck s a = true) (ξ : Ordinal.{0}) :
    (∃ t : RelativeTerm Nat, check (contextCode s) t = true ∧
      Comparison.Normal (contextCode s) t ∧
      sourceStar (contextCode s) t < interpretation (contextCode s) a ∧
      denote (alphaCode s a) (transform s a t) = ξ) ↔ GlobalNotation (base (alphaCode s a)) 0 ξ := by
  rw [← image_iff s a ha ξ]
  constructor
  · rintro ⟨t, ht, hn, hr, hv⟩
    exact ⟨t, ht, hn, (restricted_iff_sourceStar s a ha t ht hn).mpr hr, hv⟩
  · rintro ⟨t, ht, hn, hr, hv⟩
    exact ⟨t, ht, hn, (restricted_iff_sourceStar s a ha t ht hn).mp hr, hv⟩

def inverseInput (s a c : Nat) : Bool := rootCheck s a && checkCode (alphaCode s a) c

def inverseCode (s a c : Nat) : Nat :=
  cond (inverseInput s a c) (inverse s a (ThetaCourse.rawTree c)).code 0

theorem inverseInput_primrec : Primrec (fun p : (Nat × Nat) × Nat => inverseInput p.1.1 p.1.2 p.2) :=
  Primrec.and.comp (rootCheck_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst))
    (checkCode_primrec.comp (alphaCode_primrec.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.snd.comp Primrec.fst)) Primrec.snd)

theorem inverseCode_primrec : Primrec (fun p : (Nat × Nat) × Nat => inverseCode p.1.1 p.1.2 p.2) :=
  inverseInput_primrec.cond
    (code_primrec.comp (inverse_primrec.comp (Primrec.fst.pair (ThetaCourse.rawTree_primrec.comp Primrec.snd))))
    (Primrec.const 0)

theorem inverseCode_spec (s a c : Nat) (hi : inverseInput s a c = true) :
    Comparison.acceptedCode (contextCode s) (inverseCode s a c) = true ∧
      inputCheck s a (inverseCode s a c) = true ∧
      interpretation (alphaCode s a) (literalCode s a (inverseCode s a c)) =
        interpretation (alphaCode s a) c := by
  obtain ⟨ha, hc⟩ := Bool.and_eq_true.mp hi
  obtain ⟨t, he, ht⟩ := (checkCode_exact _ c).mp hc
  have hout : inverseCode s a c = (inverse s a t).code := by
    simp only [inverseCode, hi, Bool.cond_true, ← he, ThetaCourse.rawTree_code]
  have hs := inverse_spec s a ha t ht
  have hcall := inverse_iota_caller s a ha t ht
  rw [hout]
  refine ⟨(Comparison.acceptedCode_exact _ _).mpr
    ⟨by simpa only [checkCode_code] using hs.1, by simpa only [ThetaCourse.rawTree_code] using hs.2.1⟩,
    hcall, ?_⟩
  simpa only [literalCode, hcall, Bool.cond_true, stateCode_code,
    interpretation_code, ← he] using hs.2.2.2

theorem inverseCode_rejected (s a c : Nat) (hi : inverseInput s a c = false) :
    inverseCode s a c = 0 := by
  simp only [inverseCode, hi, Bool.cond_false]

def inverseGraph (s a c out : Nat) : Bool := inverseInput s a c && (out == inverseCode s a c)

theorem inverseGraph_primrec : Primrec
    (fun p : ((Nat × Nat) × Nat) × Nat => inverseGraph p.1.1.1 p.1.1.2 p.1.2 p.2) :=
  Primrec.and.comp (inverseInput_primrec.comp Primrec.fst)
    (Primrec.beq.comp Primrec.snd (inverseCode_primrec.comp Primrec.fst))

theorem inverseGraph_exact (s a c out : Nat) : inverseGraph s a c out = true ↔
    inverseInput s a c = true ∧ out = inverseCode s a c := by
  simp only [inverseGraph, Bool.and_eq_true, beq_iff_eq]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Iota.Inverse
