import Alexander313.Wilken.PureRelationsFiniteGuardRoom

/-!
# Exact package assembly from an effective actual small-ordinal presentation

The inputs are an order isomorphism from natural labels onto one actual
ordinal interval, three actual recognizing programs, and finite tallness in
that interval. Reflection, connectedness, well-foundedness and separated
finite room are derived from the constructed pure relations. They are not
repeated as hypotheses. This is a conditional assembly, not a construction
of the effective presentation or its finite-tallness witness.
-/

noncomputable section

namespace Alexander313

theorem GuardHead.mapOrderIso {L M : Type} [LinearOrder L] [LinearOrder M]
    (e : L ≃o M) (R : L → L → Prop) (S : M → M → Prop)
    (hrel : ∀ x y, R x y → S (e x) (e y))
    {k : Nat} {top : L} (h : GuardHead R k top) : GuardHead S k (e top) := by
  obtain ⟨tail, hlen, hord, hrel'⟩ := h
  refine ⟨tail.map e, by simpa only [List.length_map] using hlen, ?_, ?_⟩
  · simpa only [List.map_cons] using
      guardRoom_pairwise_map (· < ·) (· < ·) e (top :: tail) hord
        (fun x _ y _ hxy => e.lt_iff_lt.mpr hxy)
  · simpa only [List.map_cons] using
      guardRoom_pairwise_map R S e (top :: tail) hrel'
        (fun x _ y _ hxy => hrel x y hxy)

/-- Transport the complete positive-and-negative finite reflection pattern
through an order isomorphism; equality and both relations are preserved. -/
theorem FiniteLabelReflection.ofOrderIso {L M : Type} [LinearOrder L] [LinearOrder M]
    (e : L ≃o M) (R₁ R₂ : M → M → Prop) (α β : L)
    (h : FiniteLabelReflection R₁ R₂ (e α) (e β)) :
    FiniteLabelReflection (fun x y => R₁ (e x) (e y))
      (fun x y => R₂ (e x) (e y)) α β := by
  intro F below
  let G := F.image e
  have memG (x : L) (hx : x ∈ F) : e x ∈ G := Finset.mem_image.mpr ⟨x, hx, rfl⟩
  obtain ⟨g, lower, fixed, pattern⟩ := h G (by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact e.lt_iff_lt.mpr (below x hx))
  let f : L → L := fun x => e.symm (g (e x))
  have mapped (x : L) : e (f x) = g (e x) := e.apply_symm_apply _
  refine ⟨f, ?_, ?_, ?_⟩
  · intro x hx
    apply e.lt_iff_lt.mp
    rw [mapped]
    exact lower _ (memG x hx)
  · intro x hx hxa
    apply e.injective
    rw [mapped]
    exact fixed _ (memG x hx) (e.lt_iff_lt.mpr hxa)
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro x hx y hy
      have hp := pattern.1 _ (memG x hx) _ (memG y hy)
      rw [← mapped x, ← mapped y] at hp
      exact e.injective.eq_iff.symm.trans (hp.trans e.injective.eq_iff)
    · intro x hx y hy
      have hp := pattern.2.1 _ (memG x hx) _ (memG y hy)
      rw [← mapped x, ← mapped y] at hp
      exact e.lt_iff_lt.symm.trans (hp.trans e.lt_iff_lt)
    · intro x hx y hy
      simp only [mapped]
      exact pattern.2.2.1 _ (memG x hx) _ (memG y hy)
    · intro x hx y hy
      simp only [mapped]
      exact pattern.2.2.2 _ (memG x hx) _ (memG y hy)

namespace OrdinalPackage

open Wilken.PureRelations

/-- All semantic package fields follow from the actual pure ordinal relations.
The only semantic size input is finite guard tallness *within this same Ω*.
The program hypotheses concern the actual transported relations on every pair
of public natural labels; an abstract enumerator or decidability oracle is
not accepted in their place. -/
def ofEffectiveSmallLabels (order : LinearOrder Nat) (Ω : Ordinal.{0})
    (e : CodedLabel order ≃o SmallLabels.Labels Ω)
    (ltProgram firstProgram secondProgram : Program)
    (hlt : ∀ μ ν : CodedLabel order,
      ltProgram.domain (Nat.pair μ ν) ↔ e μ < e ν)
    (hfirst : ∀ μ ν : CodedLabel order,
      firstProgram.domain (Nat.pair μ ν) ↔ SmallLabels.first Ω (e μ) (e ν))
    (hsecond : ∀ μ ν : CodedLabel order,
      secondProgram.domain (Nat.pair μ ν) ↔ SmallLabels.second Ω (e μ) (e ν))
    (htall : ∀ k, ∃ top : SmallLabels.Labels Ω, GuardHead (SmallLabels.second Ω) k top) :
    OrdinalPackage where
  order := order
  R₁ := fun μ ν => SmallLabels.first Ω (e μ) (e ν)
  R₂ := fun μ ν => SmallLabels.second Ω (e μ) (e ν)
  wf := by
    let h : ((· < ·) : CodedLabel order → CodedLabel order → Prop) →r
        ((· < ·) : SmallLabels.Labels Ω → SmallLabels.Labels Ω → Prop) :=
      ⟨e, fun hxy => e.lt_iff_lt.mpr hxy⟩
    exact RelHomClass.wellFounded h IsWellFounded.wf
  ltProgram := ltProgram
  R₁Program := firstProgram
  R₂Program := secondProgram
  lt_program := fun μ ν => (hlt μ ν).trans e.lt_iff_lt
  R₁_program := hfirst
  R₂_program := hsecond
  R₁_refl := fun α => R1_refl (SmallLabels.value Ω (e α))
  R₁_le := by
    intro α β h
    apply e.le_iff_le.mp
    exact (SmallLabels.SeparatedCopies.value_le_iff Ω (e α) (e β)).mp (R1_le h)
  reflection := by
    intro α β h
    exact (FiniteLabelReflection.ofOrderIso e _ _ α β
      (SmallLabels.finiteLabelReflection Ω _ _ h)).covering
  connected := by
    intro p q r h hpq hqr
    exact R1_between h
      ((SmallLabels.SeparatedCopies.value_le_iff Ω (e p) (e q)).mpr (e.le_iff_le.mpr hpq))
      ((SmallLabels.SeparatedCopies.value_le_iff Ω (e q) (e r)).mpr (e.le_iff_le.mpr hqr))
  room := by
    intro k top guard X hX N
    have hguard := guard.mapOrderIso e _ (SmallLabels.second Ω) (fun _ _ h => h)
    let Y := X.image e
    have memY (x : CodedLabel order) (hx : x ∈ X) : e x ∈ Y :=
      Finset.mem_image.mpr ⟨x, hx, rfl⟩
    obtain ⟨copy, shape, range, separated⟩ :=
      SmallLabels.finite_guard_room Ω k (e top) hguard Y (by
        intro y hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
        exact ⟨e.lt_iff_lt.mpr (hX x hx).1, (hX x hx).2⟩) N
    refine ⟨fun j => (copy j).map e.symm, ?_, ?_, ?_⟩
    · intro j hj
      obtain ⟨hlen, hord, hrel⟩ := shape j hj
      refine ⟨by simpa only [List.length_map] using hlen, ?_, ?_⟩
      · exact guardRoom_pairwise_map (· < ·) (· < ·) e.symm (copy j) hord
          (fun x _ y _ hxy => e.symm.lt_iff_lt.mpr hxy)
      · apply guardRoom_pairwise_map (SmallLabels.second Ω) _ e.symm (copy j) hrel
        intro x _ y _ hxy
        simpa only [e.apply_symm_apply] using hxy
    · intro j hj y hy
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
      have hrange := range j hj z hz
      refine ⟨?_, ?_, ?_⟩
      · intro x hx
        apply e.lt_iff_lt.mp
        simpa only [e.apply_symm_apply] using hrange.1 (e x) (memY x hx)
      · apply e.lt_iff_lt.mp
        simpa only [e.apply_symm_apply] using hrange.2.1
      · simpa only [e.apply_symm_apply] using hrange.2.2
    · intro i j hij hj y hy z hz
      obtain ⟨y', hy', rfl⟩ := List.mem_map.mp hy
      obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hz
      exact e.symm.lt_iff_lt.mpr (separated i j hij hj y' hy' z' hz')
  tall := by
    intro k
    obtain ⟨top, ht⟩ := htall k
    refine ⟨e.symm top, ?_⟩
    exact ht.mapOrderIso e.symm (SmallLabels.second Ω)
      (fun x y => SmallLabels.second Ω (e x) (e y))
      (fun x y h => by simpa only [e.apply_symm_apply] using h)

end OrdinalPackage
end Alexander313
