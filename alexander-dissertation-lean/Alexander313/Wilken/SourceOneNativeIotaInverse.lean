import Alexander313.Wilken.SourceOneNativeIotaInverseSupport

/-!
# Actual full original source-one inverse and target image

The executing finite lift reflects target Normal sums through the proved
original two-sided iota order and genuine original theta-atom ANF. Applying
the actual target normalizer before this lift supplies an originally
admitted Normal restricted inverse for EVERY admitted target expression.
Both semantic inverse equations and the whole target grammar image follow.
No inverse, Normality, representation or coverage oracle is supplied.
Original source base one retains its own checker throughout. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.Inverse

open OrderSupport
open NativeContext.Iota.OrderInduction (normalSum_words_iff)

theorem reflect_normalSum (a : Nat) (ha : rootCheck a = true)
    (t u : RelativeTerm Nat) (ht : check 0 t = true) (hu : check 0 u = true)
    (hnt : Theta.Normal 0 t) (hnu : Theta.Normal 0 u)
    (hrt : Restricted a t) (hru : Restricted a u)
    (hs : SourceNormalSum
      (NativeContext.denote (alphaCode a) (transform a t) + NativeContext.denote (alphaCode a) (transform a u))
      (NativeContext.denote (alphaCode a) (transform a t))
      (NativeContext.denote (alphaCode a) (transform a u))) :
    SourceNormalSum (denote 0 t + denote 0 u) (denote 0 t) (denote 0 u) := by
  have htw : IsAdditiveNormalForm ((thetaAtoms t).map
      (fun x => NativeContext.denote (alphaCode a) (transform a x))) := by
    rw [transform_atoms_anf a ha t ht hnt hrt]
    exact canonicalANF_normal _
  have huw : IsAdditiveNormalForm ((thetaAtoms u).map
      (fun x => NativeContext.denote (alphaCode a) (transform a x))) := by
    rw [transform_atoms_anf a ha u hu hnu hru]
    exact canonicalANF_normal _
  have htarget := (normalSum_words_iff
    (fun x => NativeContext.denote (alphaCode a) (transform a x))
    (thetaAtoms t) (thetaAtoms u) htw huw).mp (by
      simpa only [mapped_atoms_value a ha t ht hnt hrt,
        mapped_atoms_value a ha u hu hnu hru] using hs)
  have hshape : (thetaAtoms t = [] ∧ thetaAtoms u = []) ∨
      ∃ y, thetaAtoms u = [y] ∧ ∀ x ∈ thetaAtoms t, denote 0 y ≤ denote 0 x := by
    rcases htarget with hz | ⟨y, hy, hle⟩
    · exact Or.inl hz
    · refine Or.inr ⟨y, hy, ?_⟩
      intro x hx
      have hxc := atoms_checked_normal t x ht hnt hx
      have hyc := atoms_checked_normal u y hu hnu (by rw [hy]; exact List.mem_singleton_self _)
      exact (transform_le_iff a ha y x hyc.1 hxc.1 hyc.2 hxc.2
        (restricted_atoms a u y hru (by rw [hy]; exact List.mem_singleton_self _))
        (restricted_atoms a t x hrt hx)).mp (hle x hx)
  have hsource := (normalSum_words_iff (denote 0)
    (thetaAtoms t) (thetaAtoms u) (source_atoms_normal t ht hnt)
    (source_atoms_normal u hu hnu)).mpr hshape
  simpa only [source_atoms_value t ht hnt, source_atoms_value u hu hnu] using hsource

theorem lift_normal (a : Nat) (ha : rootCheck a = true) (t : RelativeTerm Nat)
    (ht : NativeContext.check (alphaCode a) t = true)
    (hn : NativeContext.Comparison.Normal (alphaCode a) t) : Theta.Normal 0 (lift t) := by
  revert ht hn
  induction t with
  | parameter p =>
    intro ht hn
    exact (atom_spec a p ha (NativeContext.checked_admissible _ _ ht).1).2.1
  | sum t u iht ihu =>
    intro ht hn
    have hc := NativeContext.BaseTransformation.sum_checks _ t u ht
    have hnt := iht hc.1 hn.1
    have hnu := ihu hc.2 hn.2.1
    refine ⟨hnt, hnu, ?_⟩
    apply reflect_normalSum a ha (lift t) (lift u)
      (lift_checked a ha t hc.1) (lift_checked a ha u hc.2) hnt hnu
      (lift_restricted a ha t hc.1) (lift_restricted a ha u hc.2)
    simpa only [lift_right_inverse a ha t hc.1, lift_right_inverse a ha u hc.2] using hn.2.2
  | theta k t ih =>
    intro ht hn
    exact ih (NativeContext.BaseTransformation.theta_argument_check _ k t ht) hn

def inverse (a : Nat) (t : RelativeTerm Nat) : RelativeTerm Nat :=
  lift (NativeContext.Normalization.normalize (alphaCode a) t)

theorem inverse_primrec : Primrec₂ inverse :=
  lift_primrec.comp (NativeContext.Normalization.Effective.normalize_primrec.comp
    (alphaCode_primrec.comp Primrec.fst) Primrec.snd)

theorem inverse_spec (a : Nat) (ha : rootCheck a = true) (t : RelativeTerm Nat)
    (ht : NativeContext.check (alphaCode a) t = true) :
    check 0 (inverse a t) = true ∧ Theta.Normal 0 (inverse a t) ∧ Restricted a (inverse a t) ∧
      NativeContext.denote (alphaCode a) (transform a (inverse a t)) = NativeContext.denote (alphaCode a) t := by
  have hn := NativeContext.Normalization.normalize_checked _ t ht
  exact ⟨lift_checked a ha _ hn.1, lift_normal a ha _ hn.1 hn.2.1,
    lift_restricted a ha _ hn.1, (lift_right_inverse a ha _ hn.1).trans hn.2.2⟩

theorem inverse_sourceStar (a : Nat) (ha : rootCheck a = true) (t : RelativeTerm Nat)
    (ht : NativeContext.check (alphaCode a) t = true) : sourceStar (inverse a t) < interpretation 0 a := by
  have hs := inverse_spec a ha t ht
  exact (restricted_iff_sourceStar a ha _ hs.1 hs.2.1).mp hs.2.2.1

theorem inverse_iota_caller (a : Nat) (ha : rootCheck a = true) (t : RelativeTerm Nat)
    (ht : NativeContext.check (alphaCode a) t = true) : inputCheck a (inverse a t).code = true := by
  have hs := inverse_spec a ha t ht
  exact (inputCheck_exact a _).mpr
    ⟨ha, inverse a t, rfl, hs.1, hs.2.1, inverse_sourceStar a ha t ht⟩

theorem inverse_left_inverse (a : Nat) (ha : rootCheck a = true) (t : RelativeTerm Nat)
    (ht : check 0 t = true) (hn : Theta.Normal 0 t) (hr : Restricted a t) :
    denote 0 (inverse a (transform a t)) = denote 0 t := by
  have hs := inverse_spec a ha _ (transform_checked a ha t ht hr)
  exact (transform_eq_iff a ha _ t hs.1 ht hs.2.1 hn hs.2.2.1 hr).mp hs.2.2.2

theorem inverse_lt_iff (a : Nat) (ha : rootCheck a = true) (t u : RelativeTerm Nat)
    (ht : NativeContext.check (alphaCode a) t = true)
    (hu : NativeContext.check (alphaCode a) u = true) :
    denote 0 (inverse a t) < denote 0 (inverse a u) ↔
      NativeContext.denote (alphaCode a) t < NativeContext.denote (alphaCode a) u := by
  have hs := inverse_spec a ha t ht
  have hs' := inverse_spec a ha u hu
  have he := transform_lt_iff a ha _ _ hs.1 hs'.1 hs.2.1 hs'.2.1 hs.2.2.1 hs'.2.2.1
  rw [hs.2.2.2, hs'.2.2.2] at he
  exact he.symm

theorem inverse_eq_iff (a : Nat) (ha : rootCheck a = true) (t u : RelativeTerm Nat)
    (ht : NativeContext.check (alphaCode a) t = true)
    (hu : NativeContext.check (alphaCode a) u = true) :
    denote 0 (inverse a t) = denote 0 (inverse a u) ↔
      NativeContext.denote (alphaCode a) t = NativeContext.denote (alphaCode a) u := by
  have hs := inverse_spec a ha t ht
  have hs' := inverse_spec a ha u hu
  have he := transform_eq_iff a ha _ _ hs.1 hs'.1 hs.2.1 hs'.2.1 hs.2.2.1 hs'.2.2.1
  rw [hs.2.2.2, hs'.2.2.2] at he
  exact he.symm

theorem image_iff (a : Nat) (ha : rootCheck a = true) (ξ : Ordinal.{0}) :
    (∃ t : RelativeTerm Nat, check 0 t = true ∧ Theta.Normal 0 t ∧ Restricted a t ∧
      NativeContext.denote (alphaCode a) (transform a t) = ξ) ↔
      GlobalNotation (NativeContext.base (alphaCode a)) 0 ξ := by
  constructor
  · rintro ⟨t, ht, hn, hr, rfl⟩
    exact NativeContext.checked_globalNotation _ _ (transform_checked a ha t ht hr)
  · intro hξ
    obtain ⟨t, ht, hv⟩ := (NativeContext.globalNotation_iff_checked _ (alphaCode_baseCheck a ha) ξ).mp hξ
    have hs := inverse_spec a ha t ht
    exact ⟨inverse a t, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.trans hv⟩

theorem image_sourceStar_iff (a : Nat) (ha : rootCheck a = true) (ξ : Ordinal.{0}) :
    (∃ t : RelativeTerm Nat, check 0 t = true ∧ Theta.Normal 0 t ∧
      sourceStar t < interpretation 0 a ∧ NativeContext.denote (alphaCode a) (transform a t) = ξ) ↔
      GlobalNotation (NativeContext.base (alphaCode a)) 0 ξ := by
  rw [← image_iff a ha ξ]
  constructor
  · rintro ⟨t, ht, hn, hr, hv⟩
    exact ⟨t, ht, hn, (restricted_iff_sourceStar a ha t ht hn).mpr hr, hv⟩
  · rintro ⟨t, ht, hn, hr, hv⟩
    exact ⟨t, ht, hn, (restricted_iff_sourceStar a ha t ht hn).mp hr, hv⟩

def inverseInput (a c : Nat) : Bool := rootCheck a && NativeContext.checkCode (alphaCode a) c

def inverseCode (a c : Nat) : Nat :=
  cond (inverseInput a c) (inverse a (ThetaCourse.rawTree c)).code 0

theorem inverseInput_primrec : Primrec₂ inverseInput :=
  (Primrec.and.comp (rootCheck_primrec.comp Primrec.fst)
    (NativeContext.checkCode_primrec.comp (alphaCode_primrec.comp Primrec.fst) Primrec.snd)).to₂

theorem inverseCode_primrec : Primrec₂ inverseCode :=
  (inverseInput_primrec.cond (code_primrec.comp (inverse_primrec.comp Primrec.fst
    (ThetaCourse.rawTree_primrec.comp Primrec.snd))) (Primrec.const 0)).to₂

theorem inverseCode_spec (a c : Nat) (hi : inverseInput a c = true) :
    Theta.acceptedCode 0 (inverseCode a c) = true ∧ inputCheck a (inverseCode a c) = true ∧
      NativeContext.interpretation (alphaCode a) (literalCode a (inverseCode a c)) =
        NativeContext.interpretation (alphaCode a) c := by
  obtain ⟨ha, hc⟩ := Bool.and_eq_true.mp hi
  obtain ⟨t, he, ht⟩ := (NativeContext.checkCode_exact _ c).mp hc
  have hout : inverseCode a c = (inverse a t).code := by
    simp only [inverseCode, hi, Bool.cond_true, ← he, ThetaCourse.rawTree_code]
  have hs := inverse_spec a ha t ht
  have hcall := inverse_iota_caller a ha t ht
  rw [hout]
  refine ⟨(Theta.acceptedCode_iff _ _).mpr
    ⟨by simpa only [checkCode_code] using hs.1,
      by simpa only [ThetaCourse.rawTree_code] using hs.2.1⟩, hcall, ?_⟩
  simpa only [literalCode, hcall, Bool.cond_true, stateCode_code,
    NativeContext.interpretation_code, ← he] using hs.2.2.2

theorem inverseCode_rejected (a c : Nat) (hi : inverseInput a c = false) : inverseCode a c = 0 := by
  simp only [inverseCode, hi, Bool.cond_false]

def inverseGraph (a c out : Nat) : Bool := inverseInput a c && (out == inverseCode a c)

theorem inverseGraph_primrec : Primrec
    (fun p : (Nat × Nat) × Nat => inverseGraph p.1.1 p.1.2 p.2) :=
  Primrec.and.comp (inverseInput_primrec.comp Primrec.fst)
    (Primrec.beq.comp Primrec.snd (inverseCode_primrec.comp Primrec.fst))

theorem inverseGraph_exact (a c out : Nat) : inverseGraph a c out = true ↔
    inverseInput a c = true ∧ out = inverseCode a c := by
  simp only [inverseGraph, Bool.and_eq_true, beq_iff_eq]

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.Inverse
