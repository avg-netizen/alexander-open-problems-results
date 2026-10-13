import Alexander313.Carlson.ArithmeticLifting

/-!
# Pattern liftings and a least choice of relations

Carlson, *Patterns of resemblance of order 2*, Definition 12.1 and the
existence assertion of Lemma 12.5, in the pure case.
Source: https://people.math.osu.edu/carlson.6/research/patternstwofinal.pdf,
printed pp. 47–49 of the author's October 16, 2008 manuscript.

A pattern lifting is an arithmetic lifting that also preserves and reflects
both relations on the extended source and leaves the old target unchanged.
Once one such lifting exists, intersecting the relations of all liftings on
the same arithmetic carrier gives a minimal lifting. Arithmetic uniqueness
ensures that minimality also compares candidates using other total maps.

The existence hypothesis here is explicit. Constructing a pattern lifting
from continuous source data is the separate assertion of Lemma 12.6.
-/

noncomputable section

namespace Alexander313.Carlson

variable {α β : Type*} [LinearOrder α] [LinearOrder β]

/-- Definition 12.1 for finite pure patterns. The relation equivalences
express a closed embedding of the extended source, rather than just a
covering. The embedding of the old source follows by restriction. -/
structure PatternLifting (P Pplus : Str α) (Q Qplus : Str β)
    (h f : α → β) : Prop where
  source_pattern : Pplus.IsPattern
  target_pattern : Qplus.IsPattern
  source_sub : Str.IsSub P Pplus
  target_sub : Str.IsSub Q Qplus
  arithmetic : ArithmeticLifting P.U Pplus.U Q.U Qplus.U h f
  relations : ∀ x ∈ Pplus.U, ∀ y ∈ Pplus.U,
    (Pplus.r₁ x y ↔ Qplus.r₁ (f x) (f y)) ∧ (Pplus.r₂ x y ↔ Qplus.r₂ (f x) (f y))

namespace PatternLifting

/-- Definition 12.4 on a fixed arithmetic carrier. A lifting is minimal
when every other lifting on that carrier covers it by the identity map.
The assertion that the structure is itself a lifting is supplied separately. -/
def IsMinimal (P Pplus : Str α) (Q Qplus : Str β) (h : α → β) : Prop :=
  ∀ (S : Str β) (g : α → β), S.U = Qplus.U →
    PatternLifting P Pplus Q S h g → Str.CoversInto Qplus S id

/-- Minimal liftings on the same carrier agree on both relations. This is
the fixed-carrier uniqueness assertion; it does not identify different
arithmetic carriers. -/
theorem IsMinimal.iso_of_same_carrier
    {P Pplus : Str α} {Q R S : Str β} {h f g : α → β}
    (hR : IsMinimal P Pplus Q R h) (hS : IsMinimal P Pplus Q S h)
    (D : PatternLifting P Pplus Q R h f) (E : PatternLifting P Pplus Q S h g)
    (hU : S.U = R.U) : Str.IsIso R S id := by
  have hRS := hR S g hU E
  have hSR := hS R f hU.symm D
  refine ⟨?_, hRS.2.1, ?_⟩
  · simpa only [Finset.image_id] using hU.symm
  · intro x hx y hy
    have hxS : x ∈ S.U := hRS.1 x hx
    have hyS : y ∈ S.U := hRS.1 y hy
    exact ⟨⟨hRS.2.2.1 x hx y hy, hSR.2.2.1 x hxS y hyS⟩,
      ⟨hRS.2.2.2 x hx y hy, hSR.2.2.2 x hxS y hyS⟩⟩

variable {P Pplus : Str α} {Q Qplus : Str β} {h f : α → β}
  (D : PatternLifting P Pplus Q Qplus h f)
include D

theorem base_source_pattern : P.IsPattern :=
  D.source_pattern.mono D.source_sub

theorem base_target_pattern : Q.IsPattern :=
  D.target_pattern.mono D.target_sub

/-- The given base map is a closed embedding on both relations. -/
theorem base_relations {x y : α} (hx : x ∈ P.U) (hy : y ∈ P.U) :
    (P.r₁ x y ↔ Q.r₁ (h x) (h y)) ∧ (P.r₂ x y ↔ Q.r₂ (h x) (h y)) := by
  have hsource := D.source_sub.2 x hx y hy
  have hlift := D.relations x (D.source_sub.1 hx) y (D.source_sub.1 hy)
  rw [D.arithmetic.agrees x hx, D.arithmetic.agrees y hy] at hlift
  have htarget := D.target_sub.2 (h x) (D.arithmetic.base_mem x hx)
    (h y) (D.arithmetic.base_mem y hy)
  exact ⟨hsource.1.trans (hlift.1.trans htarget.1.symm),
    hsource.2.trans (hlift.2.trans htarget.2.symm)⟩

theorem base_covering : Str.CoversInto P Q h :=
  ⟨D.arithmetic.base_mem, D.arithmetic.base_mono,
    fun x hx y hy hr => (D.base_relations hx hy).1.mp hr,
    fun x hx y hy hr => (D.base_relations hx hy).2.mp hr⟩

theorem source_covering : Str.CoversInto Pplus Qplus f :=
  ⟨D.arithmetic.mem, D.arithmetic.mono,
    fun x hx y hy hr => (D.relations x hx y hy).1.mp hr,
    fun x hx y hy hr => (D.relations x hx y hy).2.mp hr⟩

/-- Lifting an extension at `a` produces an extension at its image `h a`.
This is the extension-point assertion of Lemma 12.6, under the already
constructed lifting; it does not need continuity. -/
theorem extensionAt {a : α} (hAt : Str.ExtensionAt P Pplus a) :
    Str.ExtensionAt Q Qplus (h a) := by
  refine ⟨D.target_sub, D.arithmetic.base_mem a hAt.2.1, ?_, ?_⟩
  · obtain ⟨x, hx, hxP⟩ := hAt.2.2.1
    exact ⟨f x, D.arithmetic.mem x hx, D.arithmetic.new_not_mem hx hxP⟩
  · intro y hy hyQ
    obtain ⟨x, hx, hxP, rfl⟩ := D.arithmetic.exists_new_preimage hy hyQ
    exact D.arithmetic.justBelow a x hx (hAt.2.2.2 x hx hxP)

/-- Lemma 12.5, first assertion, on a fixed arithmetic carrier. Whenever a
pattern lifting exists, a minimal one exists on that same carrier with the
same lifting map. Every competing lifting on the carrier covers it by the
identity, even when the competing total map is presented differently. -/
theorem exists_minimal :
    ∃ R : Str β, R.U = Qplus.U ∧ PatternLifting P Pplus Q R h f ∧
      IsMinimal P Pplus Q R h := by
  let R : Str β :=
    { U := Qplus.U
      r₁ := fun x y => ∀ S : Str β, S.U = Qplus.U →
        PatternLifting P Pplus Q S h f → S.r₁ x y
      r₂ := fun x y => ∀ S : Str β, S.U = Qplus.U →
        PatternLifting P Pplus Q S h f → S.r₂ x y }
  have hRpattern : R.IsPattern := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx y hy hxy
      exact D.target_pattern.le₁ x hx y hy (hxy Qplus rfl D)
    · intro x hx y hy hxy S hS E
      exact E.target_pattern.sub₂ x (hS.symm ▸ hx) y (hS.symm ▸ hy) (hxy S hS E)
    · intro x hx S hS E
      exact E.target_pattern.refl₁ x (hS.symm ▸ hx)
    · intro x hx S hS E
      exact E.target_pattern.refl₂ x (hS.symm ▸ hx)
    · intro x hx y hy z hz hxy hyz S hS E
      exact E.target_pattern.trans₁ x (hS.symm ▸ hx) y (hS.symm ▸ hy) z (hS.symm ▸ hz)
        (hxy S hS E) (hyz S hS E)
    · intro x hx y hy z hz hxy hyz S hS E
      exact E.target_pattern.trans₂ x (hS.symm ▸ hx) y (hS.symm ▸ hy) z (hS.symm ▸ hz)
        (hxy S hS E) (hyz S hS E)
    · intro x hx y hy z hz hxy hyz hxz S hS E
      exact E.target_pattern.convex₁ x (hS.symm ▸ hx) y (hS.symm ▸ hy) z (hS.symm ▸ hz)
        hxy hyz (hxz S hS E)
    · intro x hx y hy z hz hxy hyz hxz hyz' S hS E
      exact E.target_pattern.respect₂ x (hS.symm ▸ hx) y (hS.symm ▸ hy) z (hS.symm ▸ hz)
        hxy hyz (hxz S hS E) (hyz' S hS E)
  have DR : PatternLifting P Pplus Q R h f :=
    { source_pattern := D.source_pattern
      target_pattern := hRpattern
      source_sub := D.source_sub
      target_sub := by
        refine ⟨D.target_sub.1, ?_⟩
        intro x hx y hy
        refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
        · intro hxy S hS E
          exact (E.target_sub.2 x hx y hy).1.mp hxy
        · intro hxy
          exact (D.target_sub.2 x hx y hy).1.mpr (hxy Qplus rfl D)
        · intro hxy S hS E
          exact (E.target_sub.2 x hx y hy).2.mp hxy
        · intro hxy
          exact (D.target_sub.2 x hx y hy).2.mpr (hxy Qplus rfl D)
      arithmetic := D.arithmetic
      relations := by
        intro x hx y hy
        refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
        · intro hxy S hS E
          exact (E.relations x hx y hy).1.mp hxy
        · intro hxy
          exact (D.relations x hx y hy).1.mpr (hxy Qplus rfl D)
        · intro hxy S hS E
          exact (E.relations x hx y hy).2.mp hxy
        · intro hxy
          exact (D.relations x hx y hy).2.mpr (hxy Qplus rfl D) }
  refine ⟨R, rfl, DR, ?_⟩
  intro S g hS E
  have hS' : S.U = Qplus.U := hS
  have hE : ArithmeticLifting P.U Pplus.U Q.U Qplus.U h g := by
    simpa only [hS'] using E.arithmetic
  have heq : ∀ x ∈ Pplus.U, f x = g x :=
    fun x hx => D.arithmetic.unique hE hx
  have E' : PatternLifting P Pplus Q S h f :=
    { source_pattern := E.source_pattern
      target_pattern := E.target_pattern
      source_sub := E.source_sub
      target_sub := E.target_sub
      arithmetic := by
        simpa only [hS'] using D.arithmetic
      relations := by
        intro x hx y hy
        rw [heq x hx, heq y hy]
        exact E.relations x hx y hy }
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    exact hS.symm ▸ hx
  · intro x hx y hy hxy
    exact hxy
  · intro x hx y hy hxy
    exact hxy S hS' E'
  · intro x hx y hy hxy
    exact hxy S hS' E'

end PatternLifting

end Alexander313.Carlson
