import Alexander313.Wilken.HereditaryNativeIotaBaseChangeImageSupport

/-!
# The complete smaller-base image clause of source Lemma 2.47

At the same positive public source context, the original weak-normal
gamma-restricted domain maps onto all admitted weak-normal alpha terms
whose actual atomic-stop Par is below gamma. The inverse is the actual
finite lift, not a supplied preimage. Its original source admission,
Normality, full source-star restriction and both executing iota callers
are derived from the target's genuine original domain.

The semantic image uses the chosen original target representation's true
Par condition. It does not assert arbitrary-presentation Par uniqueness,
uncoded root coverage or the remaining printed height inequalities.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Iota.BaseChange.Image

open NativePublicBridge (contextCode contextCode_checked)

theorem target_preimage (s g a : Nat)
    (hg : rootCheck s g = true) (ha : rootCheck s a = true)
    (hsg : base (contextCode s) < interpretation (contextCode s) g)
    (hga : interpretation (contextCode s) g < interpretation (contextCode s) a)
    (t : RelativeTerm Nat) (ht : check (alphaCode s a) t = true)
    (hn : Comparison.Normal (alphaCode s a) t)
    (hp : BaseTransformation.ParBounded (alphaCode s a) (alphaCode s g) t) :
    check (contextCode s) (Inverse.lift s t) = true ∧
      Comparison.Normal (contextCode s) (Inverse.lift s t) ∧
      Restricted s g (Inverse.lift s t) ∧
      inputCheck s g a (Inverse.lift s t).code = true ∧
      denote (alphaCode s a) (transform s a (Inverse.lift s t)) = denote (alphaCode s a) t := by
  have hc := Inverse.lift_checked s a ha t ht
  have hnormal := Inverse.lift_normal s a ha t ht hn
  have hr := lift_par_restricted_gamma s g a hg ha t ht hp
  refine ⟨hc, hnormal, hr, ?_, Inverse.lift_right_inverse s a ha t ht⟩
  exact (inputCheck_exact s g a _).mpr ⟨hg, ha, hsg, hga, Inverse.lift s t, rfl,
    hc, hnormal, (restricted_iff_sourceStar s g hg _ hc hnormal).mp hr⟩

/-- Exact semantic image equality with ALL original target T_alpha[gamma]
weak-normal representatives, not just terms already obtained by iota. -/
theorem image_iff (s g a : Nat)
    (hg : rootCheck s g = true) (ha : rootCheck s a = true)
    (hsg : base (contextCode s) < interpretation (contextCode s) g)
    (hga : interpretation (contextCode s) g < interpretation (contextCode s) a)
    (ξ : Ordinal.{0}) :
    (∃ u : RelativeTerm Nat, check (contextCode s) u = true ∧
      Comparison.Normal (contextCode s) u ∧ Restricted s g u ∧
      denote (alphaCode s a) (transform s a u) = ξ) ↔
    ∃ t : RelativeTerm Nat, check (alphaCode s a) t = true ∧
      Comparison.Normal (alphaCode s a) t ∧
      BaseTransformation.ParBounded (alphaCode s a) (alphaCode s g) t ∧
      denote (alphaCode s a) t = ξ := by
  constructor
  · rintro ⟨u, hu, hn, hr, hv⟩
    have hra := restricted_mono s g a hga u hr
    exact ⟨transform s a u, transform_checked s a ha u hu hra,
      transform_normal s a ha u hu hn hra, transform_parBounded s g a hg ha hga u hu hr, hv⟩
  · rintro ⟨t, ht, hn, hp, hv⟩
    have hs := target_preimage s g a hg ha hsg hga t ht hn hp
    exact ⟨Inverse.lift s t, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.2.trans hv⟩

theorem image_sourceStar_iff (s g a : Nat)
    (hg : rootCheck s g = true) (ha : rootCheck s a = true)
    (hsg : base (contextCode s) < interpretation (contextCode s) g)
    (hga : interpretation (contextCode s) g < interpretation (contextCode s) a)
    (ξ : Ordinal.{0}) :
    (∃ u : RelativeTerm Nat, check (contextCode s) u = true ∧
      Comparison.Normal (contextCode s) u ∧
      sourceStar (contextCode s) u < interpretation (contextCode s) g ∧
      denote (alphaCode s a) (transform s a u) = ξ) ↔
    ∃ t : RelativeTerm Nat, check (alphaCode s a) t = true ∧
      Comparison.Normal (alphaCode s a) t ∧
      BaseTransformation.ParBounded (alphaCode s a) (alphaCode s g) t ∧
      denote (alphaCode s a) t = ξ := by
  rw [← image_iff s g a hg ha hsg hga ξ]
  constructor
  · rintro ⟨u, hu, hn, hr, hv⟩
    exact ⟨u, hu, hn, (restricted_iff_sourceStar s g hg u hu hn).mpr hr, hv⟩
  · rintro ⟨u, hu, hn, hr, hv⟩
    exact ⟨u, hu, hn, (restricted_iff_sourceStar s g hg u hu hn).mp hr, hv⟩

def targetInput (s g a c : Nat) : Bool := rootsCheck s g a &&
  BaseTransformation.normalInputCheck (alphaCode s a) (alphaCode s g) c

theorem targetInput_primrec : Primrec
    (fun p : (Nat × (Nat × Nat)) × Nat => targetInput p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  have hs := Primrec.fst.comp Primrec.fst
  have hg := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have ha := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  exact Primrec.and.comp (rootsCheck_primrec.comp Primrec.fst)
    (BaseTransformation.normalInputCheck_primrec.comp
      ((alphaCode_primrec.comp hs ha).pair ((alphaCode_primrec.comp hs hg).pair Primrec.snd)))

theorem targetInput_exact (s g a c : Nat) : targetInput s g a c = true ↔
    rootCheck s g = true ∧ rootCheck s a = true ∧
      base (contextCode s) < interpretation (contextCode s) g ∧
      interpretation (contextCode s) g < interpretation (contextCode s) a ∧
      ∃ t : RelativeTerm Nat, c = t.code ∧ check (alphaCode s a) t = true ∧
        Comparison.Normal (alphaCode s a) t ∧
        BaseTransformation.ParBounded (alphaCode s a) (alphaCode s g) t := by
  constructor
  · intro hi
    obtain ⟨hr, hp⟩ := Bool.and_eq_true.mp hi
    obtain ⟨hg, ha, hsg, hga⟩ := (rootsCheck_exact s g a).mp hr
    obtain ⟨hpi, hn⟩ := (BaseTransformation.normalInputCheck_exact _ _ _).mp hp
    obtain ⟨hc, hv, hl, hpar⟩ := (BaseTransformation.inputCheck_exact _ _ _).mp hpi
    obtain ⟨t, he, ht⟩ := (checkCode_exact _ c).mp hc
    exact ⟨hg, ha, hsg, hga, t, he.symm, ht,
      by simpa only [← he, ThetaCourse.rawTree_code] using hn,
      by simpa only [← he, ThetaCourse.rawTree_code] using hpar⟩
  · rintro ⟨hg, ha, hsg, hga, t, rfl, ht, hn, hp⟩
    exact Bool.and_eq_true.mpr ⟨(rootsCheck_exact s g a).mpr ⟨hg, ha, hsg, hga⟩,
      (BaseTransformation.normalInputCheck_exact _ _ _).mpr
        ⟨target_pi_caller s g a hg ha hga t ht hp,
          by simpa only [ThetaCourse.rawTree_code] using hn⟩⟩

def preimageCode (s g a c : Nat) : Nat :=
  cond (targetInput s g a c) (Inverse.lift s (ThetaCourse.rawTree c)).code 0

theorem preimageCode_primrec : Primrec
    (fun p : (Nat × (Nat × Nat)) × Nat => preimageCode p.1.1 p.1.2.1 p.1.2.2 p.2) :=
  targetInput_primrec.cond (code_primrec.comp
    (Inverse.lift_primrec.comp (Primrec.fst.comp Primrec.fst)
      (ThetaCourse.rawTree_primrec.comp Primrec.snd))) (Primrec.const 0)

theorem preimageCode_spec (s g a c : Nat) (hi : targetInput s g a c = true) :
    inputCheck s g a (preimageCode s g a c) = true ∧
      interpretation (alphaCode s a) (literalCode s a (preimageCode s g a c)) =
        interpretation (alphaCode s a) c ∧
      BaseTransformation.piCode (alphaCode s a) (alphaCode s g)
        (literalCode s a (preimageCode s g a c)) = literalCode s g (preimageCode s g a c) := by
  obtain ⟨hg, ha, hsg, hga, t, he, ht, hn, hp⟩ := (targetInput_exact s g a c).mp hi
  have hs := target_preimage s g a hg ha hsg hga t ht hn hp
  have hout : preimageCode s g a c = (Inverse.lift s t).code := by
    simp only [preimageCode, hi, Bool.cond_true, he, ThetaCourse.rawTree_code]
  have haCall := alpha_input s g a _ hs.2.2.2.1
  rw [hout]
  refine ⟨hs.2.2.2.1, ?_, literal_commutes s g a _ hs.2.2.2.1⟩
  simpa only [literalCode, haCall, Bool.cond_true, stateCode_code,
    interpretation_code, he] using hs.2.2.2.2

def preimageGraph (s g a c out : Nat) : Bool := targetInput s g a c && (out == preimageCode s g a c)

theorem preimageCode_rejected (s g a c : Nat) (hi : targetInput s g a c = false) :
    preimageCode s g a c = 0 := by
  simp only [preimageCode, hi, Bool.cond_false]

theorem preimageGraph_primrec : Primrec
    (fun p : ((Nat × (Nat × Nat)) × Nat) × Nat =>
      preimageGraph p.1.1.1 p.1.1.2.1 p.1.1.2.2 p.1.2 p.2) :=
  Primrec.and.comp (targetInput_primrec.comp Primrec.fst)
    (Primrec.beq.comp Primrec.snd (preimageCode_primrec.comp Primrec.fst))

theorem preimageGraph_exact (s g a c out : Nat) : preimageGraph s g a c out = true ↔
    targetInput s g a c = true ∧ out = preimageCode s g a c := by
  simp only [preimageGraph, Bool.and_eq_true, beq_iff_eq]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Iota.BaseChange.Image
