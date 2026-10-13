import Alexander313.Carlson.Order

/-!
# Finite structures, patterns and coverings

Carlson, *Patterns of resemblance of order 2*, §2, §5 and §6, pure case. A
structure is a finite subset `U` of a linear order with two relations. Its
relations matter only on `U`, so substructures and isomorphisms compare them
there. Abstract patterns live in `ℚ`, where new points can always be inserted
between old ones. Finite sets of ordinals with Carlson's relations are the
concrete examples.

The pattern axioms (Definition 5.6, pure case) are the order conditions that
every finite substructure of `R₂` satisfies: `≤₁ ⊆ ≤`, `≤₂ ⊆ ≤₁`, both relations
reflexive and transitive, `≤₁` convex, and `≤₂` respects `≤₁`. Carlson's proofs
use the two inclusions explicitly (e.g. the proof of Lemma 9.2: "`≤₁` is
contained in `≤` and `≤₂` is contained in `≤₁`"); the indecomposability
conditions 2–3 are vacuous in the pure case.
-/

noncomputable section

namespace Alexander313.Carlson

/-- A finite structure for the language `{≤, ≤₁, ≤₂}`. -/
structure Str (α : Type*) [LinearOrder α] where
  U : Finset α
  r₁ : α → α → Prop
  r₂ : α → α → Prop

namespace Str

variable {α β γ : Type*} [LinearOrder α] [LinearOrder β] [LinearOrder γ]

/-- Carlson's Definition 5.6, pure case: a finite model of reflection of
order two. -/
structure IsPattern (P : Str α) : Prop where
  le₁ : ∀ x ∈ P.U, ∀ y ∈ P.U, P.r₁ x y → x ≤ y
  sub₂ : ∀ x ∈ P.U, ∀ y ∈ P.U, P.r₂ x y → P.r₁ x y
  refl₁ : ∀ x ∈ P.U, P.r₁ x x
  refl₂ : ∀ x ∈ P.U, P.r₂ x x
  trans₁ : ∀ x ∈ P.U, ∀ y ∈ P.U, ∀ z ∈ P.U, P.r₁ x y → P.r₁ y z → P.r₁ x z
  trans₂ : ∀ x ∈ P.U, ∀ y ∈ P.U, ∀ z ∈ P.U, P.r₂ x y → P.r₂ y z → P.r₂ x z
  convex₁ : ∀ x ∈ P.U, ∀ y ∈ P.U, ∀ z ∈ P.U, x ≤ y → y ≤ z → P.r₁ x z → P.r₁ x y
  respect₂ : ∀ x ∈ P.U, ∀ y ∈ P.U, ∀ z ∈ P.U, x ≤ y → y ≤ z → P.r₂ x z → P.r₁ y z →
    P.r₂ x y

/-- The same universe points carry the same relations in two structures. -/
def Agree (P Q : Str α) (S : Finset α) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, (P.r₁ x y ↔ Q.r₁ x y) ∧ (P.r₂ x y ↔ Q.r₂ x y)

/-- `Q` is a substructure of `P`. In the pure case every substructure is closed. -/
def IsSub (Q P : Str α) : Prop := Q.U ⊆ P.U ∧ Agree Q P Q.U

/-- The substructure of `P` on `S`. -/
def restrict (P : Str α) (S : Finset α) : Str α := ⟨S, P.r₁, P.r₂⟩

/-- `h` is a covering of `P` into the relations `S₁`, `S₂` on `β`
(Definition 5.2, pure case): strictly increasing on `U`, carrying both
relations forward. -/
def IsCovering (P : Str α) (S₁ S₂ : β → β → Prop) (h : α → β) : Prop :=
  (∀ x ∈ P.U, ∀ y ∈ P.U, x < y → h x < h y) ∧
  (∀ x ∈ P.U, ∀ y ∈ P.U, P.r₁ x y → S₁ (h x) (h y)) ∧
  (∀ x ∈ P.U, ∀ y ∈ P.U, P.r₂ x y → S₂ (h x) (h y))

/-- A covering of `P` into the structure `Q`, landing in `Q`'s universe. -/
def CoversInto (P : Str α) (Q : Str β) (h : α → β) : Prop :=
  (∀ x ∈ P.U, h x ∈ Q.U) ∧ IsCovering P Q.r₁ Q.r₂ h

/-- `h` is an isomorphism of `P` onto `Q`. -/
def IsIso (P : Str α) (Q : Str β) (h : α → β) : Prop :=
  P.U.image h = Q.U ∧ (∀ x ∈ P.U, ∀ y ∈ P.U, x < y → h x < h y) ∧
  ∀ x ∈ P.U, ∀ y ∈ P.U, (P.r₁ x y ↔ Q.r₁ (h x) (h y)) ∧ (P.r₂ x y ↔ Q.r₂ (h x) (h y))

/-- A covering of `P` in Carlson's ordinal structure `R₂`. -/
def CoveringR (P : Str α) (h : α → Ordinal.{0}) : Prop := IsCovering P R1 R2 h

/-- `P` is covered (Definition 14.1). -/
def Covered (P : Str α) : Prop := ∃ h, CoveringR P h

/-- The substructure of `R₂` on a finite set of ordinals. -/
def ofOrdinals (U : Finset Ordinal.{0}) : Str Ordinal.{0} := ⟨U, R1, R2⟩

theorem restrict_isSub (P : Str α) {S : Finset α} (hS : S ⊆ P.U) : IsSub (P.restrict S) P :=
  ⟨hS, fun _ _ _ _ => ⟨Iff.rfl, Iff.rfl⟩⟩

theorem IsPattern.mono {P Q : Str α} (hP : P.IsPattern) (hQ : IsSub Q P) : Q.IsPattern := by
  obtain ⟨hU, hA⟩ := hQ
  have r₁ : ∀ x ∈ Q.U, ∀ y ∈ Q.U, Q.r₁ x y ↔ P.r₁ x y := fun x hx y hy => (hA x hx y hy).1
  have r₂ : ∀ x ∈ Q.U, ∀ y ∈ Q.U, Q.r₂ x y ↔ P.r₂ x y := fun x hx y hy => (hA x hx y hy).2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy h
    exact hP.le₁ x (hU hx) y (hU hy) ((r₁ x hx y hy).mp h)
  · intro x hx y hy h
    exact (r₁ x hx y hy).mpr (hP.sub₂ x (hU hx) y (hU hy) ((r₂ x hx y hy).mp h))
  · intro x hx
    exact (r₁ x hx x hx).mpr (hP.refl₁ x (hU hx))
  · intro x hx
    exact (r₂ x hx x hx).mpr (hP.refl₂ x (hU hx))
  · intro x hx y hy z hz h₁ h₂
    exact (r₁ x hx z hz).mpr (hP.trans₁ x (hU hx) y (hU hy) z (hU hz)
      ((r₁ x hx y hy).mp h₁) ((r₁ y hy z hz).mp h₂))
  · intro x hx y hy z hz h₁ h₂
    exact (r₂ x hx z hz).mpr (hP.trans₂ x (hU hx) y (hU hy) z (hU hz)
      ((r₂ x hx y hy).mp h₁) ((r₂ y hy z hz).mp h₂))
  · intro x hx y hy z hz hxy hyz h
    exact (r₁ x hx y hy).mpr (hP.convex₁ x (hU hx) y (hU hy) z (hU hz) hxy hyz
      ((r₁ x hx z hz).mp h))
  · intro x hx y hy z hz hxy hyz h h'
    exact (r₂ x hx y hy).mpr (hP.respect₂ x (hU hx) y (hU hy) z (hU hz) hxy hyz
      ((r₂ x hx z hz).mp h) ((r₁ y hy z hz).mp h'))

theorem IsPattern.restrict {P : Str α} (hP : P.IsPattern) {S : Finset α} (hS : S ⊆ P.U) :
    (P.restrict S).IsPattern :=
  hP.mono (P.restrict_isSub hS)

/-- Lemma 5.7(2): every finite substructure of `R₂` is a pattern. -/
theorem ofOrdinals_isPattern (U : Finset Ordinal.{0}) : (ofOrdinals U).IsPattern := by
  obtain ⟨le₁, sub₂, refl₁, refl₂, trans₁, trans₂, convex₁, respect₂⟩ := model_of_reflection
  exact ⟨fun x _ y _ => le₁ x y, fun x _ y _ => sub₂ x y, fun x _ => refl₁ x,
    fun x _ => refl₂ x, fun x _ y _ z _ => trans₁ x y z, fun x _ y _ z _ => trans₂ x y z,
    fun x _ y _ z _ => convex₁ x y z, fun x _ y _ z _ => respect₂ x y z⟩

theorem IsCovering.comp {P : Str α} {S₁ S₂ : β → β → Prop} {T₁ T₂ : γ → γ → Prop}
    {h : α → β} {g : β → γ} (hh : IsCovering P S₁ S₂ h)
    (gmono : ∀ x ∈ P.U, ∀ y ∈ P.U, h x < h y → g (h x) < g (h y))
    (g₁ : ∀ x ∈ P.U, ∀ y ∈ P.U, S₁ (h x) (h y) → T₁ (g (h x)) (g (h y)))
    (g₂ : ∀ x ∈ P.U, ∀ y ∈ P.U, S₂ (h x) (h y) → T₂ (g (h x)) (g (h y))) :
    IsCovering P T₁ T₂ (g ∘ h) :=
  ⟨fun x hx y hy hxy => gmono x hx y hy (hh.1 x hx y hy hxy),
    fun x hx y hy hr => g₁ x hx y hy (hh.2.1 x hx y hy hr),
    fun x hx y hy hr => g₂ x hx y hy (hh.2.2 x hx y hy hr)⟩

theorem IsCovering.mono {P Q : Str α} {S₁ S₂ : β → β → Prop} {h : α → β}
    (hh : IsCovering P S₁ S₂ h) (hQ : IsSub Q P) : IsCovering Q S₁ S₂ h := by
  obtain ⟨hU, hA⟩ := hQ
  exact ⟨fun x hx y hy => hh.1 x (hU hx) y (hU hy),
    fun x hx y hy hr => hh.2.1 x (hU hx) y (hU hy) ((hA x hx y hy).1.mp hr),
    fun x hx y hy hr => hh.2.2 x (hU hx) y (hU hy) ((hA x hx y hy).2.mp hr)⟩

end Str

end Alexander313.Carlson
