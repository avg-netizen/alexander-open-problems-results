import Alexander313.Wilken.HereditaryNativeIotaAddition
import Alexander313.Wilken.HereditaryNativeIotaCanonicalHeight

/-!
# The actual value isomorphism in Wilken Lemma 2.46(a)

The source consists of ordinal values with original admitted weak-normal
restricted representatives. The target is the actual global notation system
at alpha. Representative independence follows from the constructed comparison
theorem, and surjectivity uses the genuine executing inverse. The actual
normal-source addition construction proves addition on the value domain.

Classical choice selects representatives of these two defined value sets;
neither representatives nor inverse/coverage/order/addition contracts are
supplied as hypotheses. This module does not yet prove the separate bound
iota(Delta) < alpha-plus. These proof candidates remain uncompiled.
-/

noncomputable section

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Iota.ValueIsomorphism

open NativePublicBridge (contextCode contextCode_checked)

def SourceValue (s a : Nat) (ξ : Ordinal.{0}) : Prop :=
  ∃ t : RelativeTerm Nat, check (contextCode s) t = true ∧
    Comparison.Normal (contextCode s) t ∧ Restricted s a t ∧ denote (contextCode s) t = ξ

abbrev SourceValues (s a : Nat) := {ξ : Ordinal.{0} // SourceValue s a ξ}

abbrev TargetValues (s a : Nat) :=
  {ξ : Ordinal.{0} // GlobalNotation (base (alphaCode s a)) 0 ξ}

def sourceRepresentative (s a : Nat) (x : SourceValues s a) : RelativeTerm Nat :=
  Classical.choose x.property

theorem sourceRepresentative_spec (s a : Nat) (x : SourceValues s a) :
    check (contextCode s) (sourceRepresentative s a x) = true ∧
      Comparison.Normal (contextCode s) (sourceRepresentative s a x) ∧
      Restricted s a (sourceRepresentative s a x) ∧
      denote (contextCode s) (sourceRepresentative s a x) = x.val :=
  Classical.choose_spec x.property

def targetRepresentative (s a : Nat) (ha : rootCheck s a = true)
    (y : TargetValues s a) : RelativeTerm Nat :=
  Classical.choose ((globalNotation_iff_checked _ (alphaCode_baseCheck s a ha) y.val).mp y.property)

theorem targetRepresentative_spec (s a : Nat) (ha : rootCheck s a = true)
    (y : TargetValues s a) :
    check (alphaCode s a) (targetRepresentative s a ha y) = true ∧
      denote (alphaCode s a) (targetRepresentative s a ha y) = y.val :=
  Classical.choose_spec ((globalNotation_iff_checked _ (alphaCode_baseCheck s a ha) y.val).mp y.property)

def image (s a : Nat) (ha : rootCheck s a = true) (x : SourceValues s a) : TargetValues s a :=
  ⟨denote (alphaCode s a) (transform s a (sourceRepresentative s a x)),
    checked_globalNotation _ _ (transform_checked s a ha _
      (sourceRepresentative_spec s a x).1 (sourceRepresentative_spec s a x).2.2.1)⟩

def preimage (s a : Nat) (ha : rootCheck s a = true) (y : TargetValues s a) : SourceValues s a :=
  ⟨denote (contextCode s) (Inverse.inverse s a (targetRepresentative s a ha y)), by
    have hs := Inverse.inverse_spec s a ha _ (targetRepresentative_spec s a ha y).1
    exact ⟨Inverse.inverse s a (targetRepresentative s a ha y), hs.1, hs.2.1, hs.2.2.1, rfl⟩⟩

/-- The actual value map agrees with EVERY original normal representative. -/
theorem image_represented (s a : Nat) (ha : rootCheck s a = true) (x : SourceValues s a)
    (t : RelativeTerm Nat) (ht : check (contextCode s) t = true)
    (hn : Comparison.Normal (contextCode s) t) (hr : Restricted s a t)
    (hv : denote (contextCode s) t = x.val) :
    (image s a ha x).val = denote (alphaCode s a) (transform s a t) := by
  have hs := sourceRepresentative_spec s a x
  exact (transform_eq_iff s a ha _ t hs.1 ht hs.2.1 hn hs.2.2.1 hr).mpr
    (hs.2.2.2.trans hv.symm)

theorem preimage_image (s a : Nat) (ha : rootCheck s a = true) (x : SourceValues s a) :
    preimage s a ha (image s a ha x) = x := by
  apply Subtype.ext
  have hs := sourceRepresentative_spec s a x
  have ht := targetRepresentative_spec s a ha (image s a ha x)
  have hi := Inverse.inverse_spec s a ha _ ht.1
  change denote (contextCode s)
    (Inverse.inverse s a (targetRepresentative s a ha (image s a ha x))) = x.val
  have hv : denote (alphaCode s a) (targetRepresentative s a ha (image s a ha x)) =
      denote (alphaCode s a) (transform s a (sourceRepresentative s a x)) := ht.2
  exact ((transform_eq_iff s a ha _ _ hi.1 hs.1 hi.2.1 hs.2.1 hi.2.2.1 hs.2.2.1).mp
    (hi.2.2.2.trans hv)).trans hs.2.2.2

theorem image_preimage (s a : Nat) (ha : rootCheck s a = true) (y : TargetValues s a) :
    image s a ha (preimage s a ha y) = y := by
  apply Subtype.ext
  have ht := targetRepresentative_spec s a ha y
  have hs := Inverse.inverse_spec s a ha _ ht.1
  exact (image_represented s a ha (preimage s a ha y)
    (Inverse.inverse s a (targetRepresentative s a ha y)) hs.1 hs.2.1 hs.2.2.1 rfl).trans
    (hs.2.2.2.trans ht.2)

/-- An actual order isomorphism between the ORIGINAL restricted value
domain and the full actual target notation system, not a supplied map. -/
def orderIso (s a : Nat) (ha : rootCheck s a = true) : SourceValues s a ≃o TargetValues s a where
  toFun := image s a ha
  invFun := preimage s a ha
  left_inv := preimage_image s a ha
  right_inv := image_preimage s a ha
  map_rel_iff' := by
    intro x y
    have hx := sourceRepresentative_spec s a x
    have hy := sourceRepresentative_spec s a y
    change denote (alphaCode s a) (transform s a (sourceRepresentative s a x)) ≤
      denote (alphaCode s a) (transform s a (sourceRepresentative s a y)) ↔ x.val ≤ y.val
    rw [transform_le_iff s a ha _ _ hx.1 hy.1 hx.2.1 hy.2.1 hx.2.2.1 hy.2.2.1,
      hx.2.2.2, hy.2.2.2]

/-- Original source-star restriction, rather than an additional domain
promise, characterizes exactly the source of the constructed isomorphism. -/
theorem sourceValue_iff_sourceStar (s a : Nat) (ha : rootCheck s a = true) (ξ : Ordinal.{0}) :
    SourceValue s a ξ ↔ ∃ t : RelativeTerm Nat, check (contextCode s) t = true ∧
      Comparison.Normal (contextCode s) t ∧
      sourceStar (contextCode s) t < interpretation (contextCode s) a ∧ denote (contextCode s) t = ξ := by
  constructor
  · rintro ⟨t, ht, hn, hr, hv⟩
    exact ⟨t, ht, hn, (restricted_iff_sourceStar s a ha t ht hn).mp hr, hv⟩
  · rintro ⟨t, ht, hn, hr, hv⟩
    exact ⟨t, ht, hn, (restricted_iff_sourceStar s a ha t ht hn).mpr hr, hv⟩

/-- Absorption is performed by the genuine source algorithm. The source
value set is closed under ordinary ordinal addition. -/
theorem sourceValue_add (s a : Nat) (ha : rootCheck s a = true)
    {ξ η : Ordinal.{0}} (hξ : SourceValue s a ξ) (hη : SourceValue s a η) :
    SourceValue s a (ξ + η) := by
  obtain ⟨t, ht, hn, hr, hv⟩ := hξ
  obtain ⟨u, hu, hnu, hru, hvu⟩ := hη
  have hs := Addition.sourceSum_spec s a ha t u ht hu hn hnu hr hru
  exact ⟨Addition.sourceSum (contextCode s) t u, hs.1, hs.2.1, hs.2.2.1,
    by simpa only [hv, hvu] using hs.2.2.2.1⟩

def sumValue (s a : Nat) (ha : rootCheck s a = true) (x y : SourceValues s a) : SourceValues s a :=
  ⟨x.val + y.val, sourceValue_add s a ha x.property y.property⟩

/-- The isomorphism preserves ORDINARY ordinal sums of values. The raw
written source sum need not itself be normal; the actual absorber supplies
the required original-domain representative. -/
theorem orderIso_add (s a : Nat) (ha : rootCheck s a = true) (x y : SourceValues s a) :
    (orderIso s a ha (sumValue s a ha x y)).val =
      (orderIso s a ha x).val + (orderIso s a ha y).val := by
  have hx := sourceRepresentative_spec s a x
  have hy := sourceRepresentative_spec s a y
  have hs := Addition.sourceSum_spec s a ha _ _ hx.1 hy.1 hx.2.1 hy.2.1 hx.2.2.1 hy.2.2.1
  have hv : denote (contextCode s)
      (Addition.sourceSum (contextCode s) (sourceRepresentative s a x) (sourceRepresentative s a y)) =
      (sumValue s a ha x y).val := by
    simpa only [sumValue, hx.2.2.2, hy.2.2.2] using hs.2.2.2.1
  exact (image_represented s a ha (sumValue s a ha x y) _ hs.1 hs.2.1 hs.2.2.1 hv).trans hs.2.2.2.2

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Iota.ValueIsomorphism
