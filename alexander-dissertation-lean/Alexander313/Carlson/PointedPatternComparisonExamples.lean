import Alexander313.Carlson.PointedPatternComparison
import Alexander313.Carlson.CoreTallness
import Alexander313.Carlson.ExactnessExamples

/-!
# Controls for compatible amalgamation uniqueness and pointed comparison

The singleton controls identify different rational carriers and target
placements. The strict two-point R2 chain controls include both positive
and negative relation comparisons, and distinguish its first least label
from the least label of a singleton seed.
-/

noncomputable section

namespace Alexander313.Carlson

open Finite

private def orderStr (S : Finset ℚ) : Str ℚ := ⟨S, (· ≤ ·), (· ≤ ·)⟩

private instance (S : Finset ℚ) : DecidableRel (orderStr S).r₁ :=
  fun x y => inferInstanceAs (Decidable (x ≤ y))

private instance (S : Finset ℚ) : DecidableRel (orderStr S).r₂ :=
  fun x y => inferInstanceAs (Decidable (x ≤ y))

private instance (n : ℕ) : DecidableRel (rationalFullChain n).r₁ :=
  fun x y => inferInstanceAs (Decidable (x ≤ y))

private instance (n : ℕ) : DecidableRel (rationalFullChain n).r₂ :=
  fun x y => inferInstanceAs (Decidable (x ≤ y))

private theorem orderStr_isPattern (S : Finset ℚ) : (orderStr S).IsPattern :=
  ⟨fun _ _ _ _ h => h, fun _ _ _ _ h => h, fun _ _ => le_rfl,
    fun _ _ => le_rfl, fun _ _ _ _ _ _ h₁ h₂ => h₁.trans h₂,
    fun _ _ _ _ _ _ h₁ h₂ => h₁.trans h₂, fun _ _ _ _ _ _ h _ _ => h,
    fun _ _ _ _ _ _ h _ _ _ => h⟩

private def singletonSeed (a : ℚ) : CoreSeed :=
  ⟨RationalPresentation.ofDecidable (orderStr {a}),
    (RationalPresentation.ofDecidable_iso (orderStr {a})).isPattern
      (orderStr_isPattern {a})⟩

private def singletonPoint (a : ℚ) : PointedPattern :=
  ⟨singletonSeed a, a, Finset.mem_singleton_self a⟩

private theorem singleton_amalgamation {n : ℕ} (a : Fin n → ℚ) (hn : 0 < n)
    (b : ℚ) :
    Str.Amalgamation (fun i => (singletonSeed (a i)).val.toStr)
      (orderStr {b}) (fun _ _ => b) := by
  classical
  refine ⟨orderStr_isPattern _, ?_, ?_, ?_⟩
  · intro i
    refine ⟨by simp [singletonSeed, RationalPresentation.ofDecidable, Str.restrict, orderStr], ?_, ?_⟩
    · intro x hx y hy hxy
      have hx' : x = a i := Finset.mem_singleton.mp hx
      have hy' : y = a i := Finset.mem_singleton.mp hy
      exact (lt_irrefl _ (hx' ▸ hy' ▸ hxy)).elim
    · intro x hx y hy
      have hx' : x = a i := Finset.mem_singleton.mp hx
      have hy' : y = a i := Finset.mem_singleton.mp hy
      subst x; subst y
      simp [singletonSeed, RationalPresentation.ofDecidable, Str.restrict, orderStr]
  · ext x
    simp only [orderStr, Finset.mem_singleton, Finset.mem_biUnion,
      Finset.mem_univ, true_and, singletonSeed, RationalPresentation.toStr_U,
      RationalPresentation.ofDecidable_U, Finset.image_singleton,
      Finset.mem_singleton]
    exact ⟨fun h => ⟨⟨0, hn⟩, h⟩, fun ⟨_, h⟩ => h⟩
  · intro i
    simpa only [singletonSeed, RationalPresentation.toStr_U,
      RationalPresentation.ofDecidable_U, orderStr, Finset.image_singleton,
      Str.restrict] using Str.Exact.refl (orderStr_isPattern {b})

/-- Distinct input labels may coincide in the actual core, and every
rational amalgamation must realize that coincidence. -/
theorem distinct_singleton_pointed_labels_agree :
    (singletonPoint 0).iota = (singletonPoint 1).iota ∧
    ∀ (Q : Str ℚ) (f : Fin 2 → ℚ → ℚ),
      Str.Amalgamation (fun i => (singletonSeed (i.val : ℚ)).val.toStr) Q f →
        f 0 0 = f 1 1 := by
  let p (i : Fin 2) := singletonPoint (i.val : ℚ)
  have d := singleton_amalgamation (fun i : Fin 2 => (i.val : ℚ)) (by decide) 0
  have heq : (p 0).iota = (p 1).iota := (d.pointed_eq_iff (p := p) 0 1).mpr rfl
  refine ⟨heq, ?_⟩
  intro Q f d'
  exact (d'.pointed_eq_iff (p := p) 0 1).mp heq

/-- The finite inverse in Theorem 15.9(2) actually changes labels when
two target carriers occupy different rational positions. -/
theorem displaced_singleton_amalgamations_compatible :
    ∃ g : ℚ → ℚ, Str.IsIso (orderStr {0}) (orderStr {17}) g ∧ g 0 = 17 ∧
      ∀ h : ℚ → ℚ, Str.IsIso (orderStr {0}) (orderStr {17}) h →
        Set.EqOn h g {0} := by
  let a (i : Fin 2) : ℚ := i.val
  obtain ⟨g, hg, hfix⟩ :=
    (singleton_amalgamation a (by decide) 0).exists_compatible_iso
      (singleton_amalgamation a (by decide) 17) (fun i => (singletonSeed (a i)).property)
  refine ⟨g, hg, hfix 0 0 (Finset.mem_singleton_self 0), ?_⟩
  intro h eh
  simpa only [orderStr, Finset.coe_singleton] using eh.eqOn hg

/-- Carrier uniqueness must not be strengthened to equality of total
functions: their unconstrained values away from the finite pattern differ. -/
theorem isomorphisms_can_differ_off_carrier :
    ∃ g h : ℚ → ℚ, Str.IsIso (orderStr {0}) (orderStr {0}) g ∧
      Str.IsIso (orderStr {0}) (orderStr {0}) h ∧
      Set.EqOn g h {0} ∧ g 1 ≠ h 1 := by
  let h : ℚ → ℚ := fun x => if x = 0 then 0 else 2
  have eh : Str.IsIso (orderStr {0}) (orderStr {0}) h := by
    refine ⟨by simp [orderStr, h], ?_, ?_⟩
    · intro x hx y hy hxy
      have hx' : x = 0 := Finset.mem_singleton.mp hx
      have hy' : y = 0 := Finset.mem_singleton.mp hy
      exact (lt_irrefl _ (hx' ▸ hy' ▸ hxy)).elim
    · intro x hx y hy
      have hx' : x = 0 := Finset.mem_singleton.mp hx
      have hy' : y = 0 := Finset.mem_singleton.mp hy
      subst x; subst y
      simp [orderStr, h]
  refine ⟨id, h, Str.IsIso.refl _, eh, ?_, by norm_num [h]⟩
  simpa only [orderStr, Finset.coe_singleton] using (Str.IsIso.refl _).eqOn eh

/-- Empty families require no distinguished maximum or nonempty carrier
in the compatible-isomorphism construction. -/
theorem empty_rational_amalgamations_compatible (P : Fin 0 → Str ℚ)
    (Q Q' : Str ℚ) (f f' : Fin 0 → ℚ → ℚ)
    (d : Str.Amalgamation P Q f) (d' : Str.Amalgamation P Q' f') :
    ∃ g : ℚ → ℚ, Str.IsIso Q Q' g := by
  obtain ⟨g, hg, _⟩ := d.exists_compatible_iso d' (fun i => Fin.elim0 i)
  exact ⟨g, hg⟩

private def chainSeed : CoreSeed :=
  ⟨RationalPresentation.ofDecidable (rationalFullChain 2),
    (RationalPresentation.ofDecidable_iso (rationalFullChain 2)).isPattern
      (rationalFullChain_isPattern 2)⟩

private def chainPoint (i : Fin 2) : PointedPattern :=
  ⟨chainSeed, i.val, rationalFullChain_mem i.isLt⟩

private theorem chain_self_amalgamation :
    Str.Amalgamation (fun _ : Fin 2 => chainSeed.val.toStr)
      chainSeed.val.toStr (fun _ => id) := by
  classical
  refine ⟨chainSeed.property, ?_, ?_, ?_⟩
  · intro i
    simpa only [Finset.image_id, Str.restrict] using Str.IsIso.refl chainSeed.val.toStr
  · ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.image_id]
    exact ⟨fun h => ⟨0, h⟩, fun ⟨_, h⟩ => h⟩
  · intro i
    simpa only [Finset.image_id, Str.restrict] using Str.Exact.refl chainSeed.property

/-- A genuine strict R2 pair has distinct core labels. Both reflection
relations hold forward and fail backward in every pointed amalgamation. -/
theorem strict_chain_pointed_comparisons :
    (chainPoint 0).iota < (chainPoint 1).iota ∧
    (chainPoint 0).iota ≠ (chainPoint 1).iota ∧
    R1 (chainPoint 0).iota (chainPoint 1).iota ∧
    R2 (chainPoint 0).iota (chainPoint 1).iota ∧
    ¬R1 (chainPoint 1).iota (chainPoint 0).iota ∧
    ¬R2 (chainPoint 1).iota (chainPoint 0).iota := by
  have hlt : (chainPoint 0).iota < (chainPoint 1).iota :=
    (chain_self_amalgamation.pointed_lt_iff (p := chainPoint) 0 1).mpr (by
      norm_num [chainPoint])
  have hone : R1 (chainPoint 0).iota (chainPoint 1).iota :=
    (chain_self_amalgamation.pointed_one_iff (p := chainPoint) 0 1).mpr (by
      simp [chainPoint, chainSeed, RationalPresentation.ofDecidable,
        rationalFullChain, Finset.range_add_one])
  have htwo : R2 (chainPoint 0).iota (chainPoint 1).iota :=
    (chain_self_amalgamation.pointed_two_iff (p := chainPoint) 0 1).mpr (by
      simp [chainPoint, chainSeed, RationalPresentation.ofDecidable,
        rationalFullChain, Finset.range_add_one])
  refine ⟨hlt, hlt.ne, hone, htwo, ?_, ?_⟩
  · rw [chain_self_amalgamation.pointed_one_iff (p := chainPoint) 1 0]
    simp [chainPoint, chainSeed, RationalPresentation.ofDecidable,
      rationalFullChain, Finset.range_add_one]
  · rw [chain_self_amalgamation.pointed_two_iff (p := chainPoint) 1 0]
    simp [chainPoint, chainSeed, RationalPresentation.ofDecidable,
      rationalFullChain, Finset.range_add_one]

/-- The first point of a strict R2 seed differs from the least singleton
point, despite being the first point of its own finite ordered carrier. -/
theorem singleton_before_strict_chain_first :
    (singletonPoint 0).iota < (chainPoint 0).iota := by
  have hzero : (singletonPoint 0).iota = 0 := by
    have hc : (singletonSeed 0).val.toStr.CoveringR (fun _ => 0) := by
      refine ⟨?_, fun _ _ _ _ _ => R1_refl 0, fun _ _ _ _ _ => R2_refl 0⟩
      intro x hx y hy hxy
      have hx' : x = 0 := Finset.mem_singleton.mp hx
      have hy' : y = 0 := Finset.mem_singleton.mp hy
      exact (lt_irrefl _ (hx' ▸ hy' ▸ hxy)).elim
    exact ((coreRealization (singletonSeed 0)).seed_minimal hc
      (singletonPoint 0).mem).antisymm zero_le
  rw [hzero]
  exact positive_of_strict_first strict_chain_pointed_comparisons.2.2.1
    strict_chain_pointed_comparisons.1

end Alexander313.Carlson
