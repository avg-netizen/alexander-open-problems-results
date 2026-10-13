import Alexander313.Carlson.PatternLiftingExistence

/-!
# Isomorphisms as minimal pattern liftings

A compatible change of labels of a continuous rule is a minimal lifting
along the isomorphism of its base. The lifting map covers the entire target
carrier, so its relation equivalences determine every relation on that
carrier. This gives isomorphism invariance of the generating rules through
the minimal-lifting clause of Carlson's Definition 13.10.

All compatibility and uniqueness assertions concern the finite carriers;
the total maps and relations outside those carriers remain unrestricted.

Source: https://people.math.osu.edu/carlson.6/research/patternstwofinal.pdf,
Definitions 12.1, 12.4 and Lemma 13.11(1) of the author's October 16, 2008
manuscript, in the pure case.
-/

noncomputable section

namespace Alexander313.Carlson

variable {α β : Type*} [LinearOrder α] [LinearOrder β]

namespace Str

/-- An isomorphism onto the target is a continuous embedding. -/
theorem IsIso.continuousEmbedding {P : Str α} {Q : Str β} {f : α → β}
    (e : IsIso P Q f) : ContinuousEmbedding P Q f := by
  unfold ContinuousEmbedding
  rw [e.1]
  exact ⟨e, Continuous.refl Q⟩

end Str

namespace PatternLifting

variable {P Pplus : Str α} {Q Qplus : Str β} {h f : α → β}

/-- A compatible isomorphism of a continuous rule is a pattern lifting
along the base isomorphism. -/
theorem of_isIso (hS : Pplus.IsPattern) (hC : Str.Continuous P Pplus)
    (e : Str.IsIso P Q h) (eplus : Str.IsIso Pplus Qplus f)
    (hfix : ∀ x ∈ P.U, f x = h x) : PatternLifting P Pplus Q Qplus h f := by
  have hCQ := hC.of_isIso e eplus hfix
  refine
    { source_pattern := hS
      target_pattern := eplus.isPattern hS
      source_sub := hC.1
      target_sub := hCQ.1
      arithmetic :=
        { source_sub := hC.1.1
          source_bounded := hC.2.1
          base_mono := e.2.1
          base_mem := fun _ hx => e.mem hx
          target_sub := hCQ.1.1
          mono := eplus.2.1
          mem := fun _ hx => eplus.mem hx
          agrees := hfix
          carrier_eq := ?_
          justBelow := ?_ }
      relations := eplus.2.2 }
  · rw [eplus.1, Finset.union_eq_right.mpr hCQ.1.1]
  · intro a x hx hax
    refine ⟨e.mem hax.1, ?_, ?_⟩
    · have hlt := eplus.2.1 x hx a (hC.1.1 hax.1) hax.2.1
      simpa only [hfix a hax.1] using hlt
    · intro q hq hqa
      obtain ⟨p, hp, rfl⟩ := e.preimage hq
      have hpa := (e.lt_iff hp hax.1).mp hqa
      have hlt := eplus.2.1 p (hC.1.1 hp) x hx (hax.2.2 p hp hpa)
      simpa only [hfix p hp] using hlt

/-- If the extended source maps onto the whole target carrier, every
competing lifting has the same relations on that carrier. In particular,
an isomorphic copy of a continuous source rule is a minimal lifting. -/
theorem isMinimal_of_isIso (D : PatternLifting P Pplus Q Qplus h f)
    (eplus : Str.IsIso Pplus Qplus f) : IsMinimal P Pplus Q Qplus h := by
  intro S g hU E
  have A : ArithmeticLifting P.U Pplus.U Q.U Qplus.U h g := by
    simpa only [hU] using E.arithmetic
  have heq : ∀ x ∈ Pplus.U, f x = g x := fun _ hx => D.arithmetic.unique A hx
  refine ⟨fun _ hx => hU.symm ▸ hx, fun _ _ _ _ hxy => hxy, ?_, ?_⟩
  · intro u hu v hv huv
    obtain ⟨x, hx, rfl⟩ := eplus.preimage hu
    obtain ⟨y, hy, rfl⟩ := eplus.preimage hv
    change S.r₁ (f x) (f y)
    rw [heq x hx, heq y hy]
    exact (E.relations x hx y hy).1.mp ((D.relations x hx y hy).1.mpr huv)
  · intro u hu v hv huv
    obtain ⟨x, hx, rfl⟩ := eplus.preimage hu
    obtain ⟨y, hy, rfl⟩ := eplus.preimage hv
    change S.r₂ (f x) (f y)
    rw [heq x hx, heq y hy]
    exact (E.relations x hx y hy).2.mp ((D.relations x hx y hy).2.mpr huv)

end PatternLifting
end Alexander313.Carlson
