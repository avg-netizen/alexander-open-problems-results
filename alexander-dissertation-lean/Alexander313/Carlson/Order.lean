import Alexander313.Carlson.Basic

/-!
# Order properties of the second covering relation

Carlson, *Patterns of resemblance of order 2*, Lemma 5.5(4) and (6), pure case:
`≤₂` is transitive, and `≤₂` respects `≤₁` (`a ≤ b ≤ c`, `a ≤₂ c`, `b ≤₁ c`
give `a ≤₂ b`). Clause 2 of the definition is first restated with the global
relations, since all points it mentions lie below its upper endpoint.
-/

noncomputable section

namespace Alexander313.Carlson

/-- The increasing enumeration of a strictly increasing image is the image of
the increasing enumeration. -/
theorem orderEmbOfFin_image {α β : Type*} [LinearOrder α] [LinearOrder β]
    (S : Finset α) (f : α → β) (mono : ∀ x ∈ S, ∀ y ∈ S, x < y → f x < f y)
    {n : ℕ} (h : S.card = n) (h' : (S.image f).card = n) (i : Fin n) :
    (S.image f).orderEmbOfFin h' i = f (S.orderEmbOfFin h i) := by
  have hmono : StrictMono (fun j => f (S.orderEmbOfFin h j)) := by
    intro j k hjk
    exact mono _ (S.orderEmbOfFin_mem h j) _ (S.orderEmbOfFin_mem h k)
      ((S.orderEmbOfFin h).strictMono hjk)
  have hmem : ∀ j, f (S.orderEmbOfFin h j) ∈ S.image f :=
    fun j => Finset.mem_image_of_mem f (S.orderEmbOfFin_mem h j)
  exact (congrFun (Finset.orderEmbOfFin_unique h' hmem hmono) i).symm

theorem card_image_of_mono {α β : Type*} [LinearOrder α] [LinearOrder β]
    (S : Finset α) (f : α → β) (mono : ∀ x ∈ S, ∀ y ∈ S, x < y → f x < f y) :
    (S.image f).card = S.card := by
  apply Finset.card_image_of_injOn
  intro x hx y hy hxy
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact (mono x hx y hy hlt).ne hxy
  · exact (mono y hy x hx hlt).ne hxy.symm

/-- Coverings of a finite structure transport along a strictly increasing map
that carries both relations forward. -/
theorem CoversStructure.transport {α : Type*} [LinearOrder α] {S₁ S₂ : α → α → Prop}
    {S : Finset α} {n : ℕ} {P₁ P₂ : Fin n → Fin n → Prop}
    (h : CoversStructure S₁ S₂ S P₁ P₂) (f : α → α)
    (mono : ∀ x ∈ S, ∀ y ∈ S, x < y → f x < f y)
    (rel₁ : ∀ x ∈ S, ∀ y ∈ S, S₁ x y → S₁ (f x) (f y))
    (rel₂ : ∀ x ∈ S, ∀ y ∈ S, S₂ x y → S₂ (f x) (f y)) :
    CoversStructure S₁ S₂ (S.image f) P₁ P₂ := by
  obtain ⟨hcard, hrel⟩ := h
  have hcard' : (S.image f).card = n := (card_image_of_mono S f mono).trans hcard
  refine ⟨hcard', fun i j => ?_⟩
  rw [orderEmbOfFin_image S f mono hcard hcard' i, orderEmbOfFin_image S f mono hcard hcard' j]
  exact ⟨fun hp => rel₁ _ (S.orderEmbOfFin_mem hcard i) _ (S.orderEmbOfFin_mem hcard j)
      ((hrel i j).1 hp),
    fun hp => rel₂ _ (S.orderEmbOfFin_mem hcard i) _ (S.orderEmbOfFin_mem hcard j)
      ((hrel i j).2 hp)⟩

/-- Relations that agree on all points of a finite set give the same coverings. -/
theorem CoversStructure.congr {α : Type*} [LinearOrder α] {S₁ S₂ T₁ T₂ : α → α → Prop}
    {S : Finset α} {n : ℕ} {P₁ P₂ : Fin n → Fin n → Prop}
    (h₁ : ∀ x ∈ S, ∀ y ∈ S, S₁ x y ↔ T₁ x y) (h₂ : ∀ x ∈ S, ∀ y ∈ S, S₂ x y ↔ T₂ x y) :
    CoversStructure S₁ S₂ S P₁ P₂ ↔ CoversStructure T₁ T₂ S P₁ P₂ := by
  constructor
  · rintro ⟨hcard, hrel⟩
    refine ⟨hcard, fun i j => ⟨fun hp => ?_, fun hp => ?_⟩⟩
    · exact (h₁ _ (S.orderEmbOfFin_mem hcard i) _ (S.orderEmbOfFin_mem hcard j)).mp
        ((hrel i j).1 hp)
    · exact (h₂ _ (S.orderEmbOfFin_mem hcard i) _ (S.orderEmbOfFin_mem hcard j)).mp
        ((hrel i j).2 hp)
  · rintro ⟨hcard, hrel⟩
    refine ⟨hcard, fun i j => ⟨fun hp => ?_, fun hp => ?_⟩⟩
    · exact (h₁ _ (S.orderEmbOfFin_mem hcard i) _ (S.orderEmbOfFin_mem hcard j)).mpr
        ((hrel i j).1 hp)
    · exact (h₂ _ (S.orderEmbOfFin_mem hcard i) _ (S.orderEmbOfFin_mem hcard j)).mpr
        ((hrel i j).2 hp)

/-- Cofinal copies below `c`, read with the prefix relations of any `d ≥ c`, are
cofinal copies for the global relations, when the base set lies below `c`. -/
theorem cofinalCopies_prefix_iff {d c : Ordinal.{0}} (hcd : c ≤ d) (X : Finset Ordinal.{0})
    (hX : ∀ x ∈ X, x < c) {n : ℕ} (P₁ P₂ : Fin n → Fin n → Prop) :
    CofinalCopies (prefixFirst d) (prefixSecond d) X P₁ P₂ c ↔
      CofinalCopies R1 R2 X P₁ P₂ c := by
  have below (Y : Finset Ordinal.{0}) (hY : ∀ y ∈ Y, y < c) : ∀ z ∈ X ∪ Y, z < d := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact (hX z hz).trans_le hcd
    · exact (hY z hz).trans_le hcd
  constructor
  · intro h ξ hξ
    obtain ⟨Y, hY, cover⟩ := h ξ hξ
    refine ⟨Y, hY, (CoversStructure.congr ?_ ?_).mp cover⟩
    · intro x _ y hy
      exact prefixFirst_below (below Y (fun y hy => (hY y hy).2) y hy)
    · intro x _ y hy
      exact prefixSecond_below (below Y (fun y hy => (hY y hy).2) y hy)
  · intro h ξ hξ
    obtain ⟨Y, hY, cover⟩ := h ξ hξ
    refine ⟨Y, hY, (CoversStructure.congr ?_ ?_).mpr cover⟩
    · intro x _ y hy
      exact prefixFirst_below (below Y (fun y hy => (hY y hy).2) y hy)
    · intro x _ y hy
      exact prefixSecond_below (below Y (fun y hy => (hY y hy).2) y hy)

/-- Clause 2 of the second relation, with the global relations. -/
theorem R2_cofinal {a b : Ordinal.{0}} (h : R2 a b) (X : Finset Ordinal.{0})
    (hX : ∀ x ∈ X, x < a) {n : ℕ} (P₁ P₂ : Fin n → Fin n → Prop)
    (cof : CofinalCopies R1 R2 X P₁ P₂ a) : CofinalCopies R1 R2 X P₁ P₂ b := by
  obtain ⟨hab, _, cofinal⟩ := (R2_iff a b).mp h
  have hXb : ∀ x ∈ X, x < b := fun x hx => (hX x hx).trans_le hab
  exact (cofinalCopies_prefix_iff le_rfl X hXb P₁ P₂).mp
    (cofinal X hX n P₁ P₂ ((cofinalCopies_prefix_iff hab X hX P₁ P₂).mpr cof))

/-- Build a second relation from global linked copies and global clause 2. -/
theorem R2_of_global {a b : Ordinal.{0}} (hab : a ≤ b)
    (linked : ∀ F : Finset Ordinal.{0}, (∀ z ∈ F, z < b) →
      ∃ f, CoveringCopy R1 R2 F f a ∧ ∀ z ∈ F, a ≤ z → R1 z b → R1 (f z) a)
    (cofinal : ∀ X : Finset Ordinal.{0}, (∀ x ∈ X, x < a) →
      ∀ (n : ℕ) (P₁ P₂ : Fin n → Fin n → Prop),
        CofinalCopies R1 R2 X P₁ P₂ a → CofinalCopies R1 R2 X P₁ P₂ b) : R2 a b := by
  refine (R2_iff a b).mpr ⟨hab, fun F hF => ?_, fun X hX n P₁ P₂ cof => ?_⟩
  · obtain ⟨f, copy, links⟩ := linked F hF
    exact ⟨f, copy.prefix hab, fun z hz haz hzb =>
      ⟨lt_of_le_of_lt haz (hF z hz), links z hz haz hzb⟩⟩
  · have hXb : ∀ x ∈ X, x < b := fun x hx => (hX x hx).trans_le hab
    exact (cofinalCopies_prefix_iff le_rfl X hXb P₁ P₂).mpr
      (cofinal X hX n P₁ P₂ ((cofinalCopies_prefix_iff hab X hX P₁ P₂).mp cof))

/-- Lemma 5.5(4): the second relation is transitive. Copy the part above `b`
below `b` keeping links to `b`, then copy everything above `a` below `a`
keeping links to `a`. A point copied below `a` by the first map is linked to
`a` by connectedness. -/
theorem R2_trans {a b c : Ordinal.{0}} (hab : R2 a b) (hbc : R2 b c) : R2 a c := by
  have hab' := R2_le hab
  have hbc' := R2_le hbc
  refine R2_of_global (hab'.trans hbc') (fun F hF => ?_) (fun X hX n P₁ P₂ cof => ?_)
  · obtain ⟨g, copyG, linksG⟩ := R2_copy' hbc F hF
    let G := F.image g
    have hG : ∀ z ∈ G, z < b := by
      intro z hz
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
      exact copyG.1 w hw
    obtain ⟨h, copyH, linksH⟩ := R2_copy' hab G hG
    have mem (z : Ordinal.{0}) (hz : z ∈ F) : g z ∈ G := Finset.mem_image_of_mem g hz
    refine ⟨h ∘ g, ⟨fun z hz => copyH.1 (g z) (mem z hz), fun z hz hza => ?_,
      fun z hz w hw hzw => copyH.2.2.1 _ (mem z hz) _ (mem w hw) (copyG.2.2.1 z hz w hw hzw),
      fun z hz w hw hzw =>
        copyH.2.2.2.1 _ (mem z hz) _ (mem w hw) (copyG.2.2.2.1 z hz w hw hzw),
      fun z hz w hw hzw =>
        copyH.2.2.2.2 _ (mem z hz) _ (mem w hw) (copyG.2.2.2.2 z hz w hw hzw)⟩,
      fun z hz haz hzc => ?_⟩
    · have hgz : g z = z := copyG.2.1 z hz (hza.trans_le hab')
      change h (g z) = z
      rw [hgz]
      exact copyH.2.1 z (hgz ▸ mem z hz) hza
    · change R1 (h (g z)) a
      by_cases hzb : z < b
      · have hgz : g z = z := copyG.2.1 z hz hzb
        have hmem : z ∈ G := hgz ▸ mem z hz
        rw [hgz]
        exact linksH z hmem haz (R1_between hzc hzb.le hbc')
      · have hlink : R1 (g z) b := linksG z hz (not_lt.mp hzb) hzc
        by_cases hga : a ≤ g z
        · exact linksH (g z) (mem z hz) hga hlink
        · have hfix : h (g z) = g z := copyH.2.1 (g z) (mem z hz) (not_le.mp hga)
          rw [hfix]
          exact R1_between hlink (not_le.mp hga).le hab'
  · exact R2_cofinal hbc X (fun x hx => (hX x hx).trans_le hab') P₁ P₂
      (R2_cofinal hab X hX P₁ P₂ cof)

/-- Lemma 5.5(6): the second relation respects the first. -/
theorem R2_respects_R1 {a b c : Ordinal.{0}} (hac : R2 a c) (hab : a ≤ b) (hbc : R1 b c) :
    R2 a b := by
  have hbc' := R1_le hbc
  refine R2_of_global hab (fun F hF => ?_) (fun X hX n P₁ P₂ cof => ?_)
  · obtain ⟨f, copy, links⟩ := R2_copy' hac F (fun z hz => (hF z hz).trans_le hbc')
    exact ⟨f, copy, fun z hz haz hzb => links z hz haz (R1_trans hzb hbc)⟩
  · intro ξ hξ
    rcases hbc'.lt_or_eq with hlt | heq
    · obtain ⟨Y, hY, cover⟩ := R2_cofinal hac X hX P₁ P₂ cof b hlt
      have hYc : ∀ y ∈ Y, y < c := fun y hy => (hY y hy).2
      have hXb : ∀ x ∈ X, x < b := fun x hx => (hX x hx).trans_le hab
      let F := insert ξ (X ∪ Y)
      have hF : ∀ z ∈ F, z < c := by
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact hξ.trans hlt
        · rcases Finset.mem_union.mp hz with hz | hz
          · exact (hXb z hz).trans hlt
          · exact hYc z hz
      obtain ⟨f, copy⟩ := R1_copy' hbc F hF
      have inF (z : Ordinal.{0}) (hz : z ∈ X ∪ Y) : z ∈ F := Finset.mem_insert_of_mem hz
      refine ⟨Y.image f, fun y hy => ?_, ?_⟩
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
        have hwF : w ∈ F := inF w (Finset.mem_union_right X hw)
        refine ⟨?_, copy.1 w hwF⟩
        have hfix : f ξ = ξ := copy.2.1 ξ (Finset.mem_insert_self ξ _) hξ
        have := copy.2.2.1 ξ (Finset.mem_insert_self ξ _) w hwF (hξ.trans (hY w hw).1)
        rwa [hfix] at this
      · have himage : (X ∪ Y).image f = X ∪ Y.image f := by
          rw [Finset.image_union]
          congr 1
          calc X.image f = X.image id := Finset.image_congr fun x hx =>
                copy.2.1 x (inF x (Finset.mem_union_left Y hx)) (hXb x hx)
            _ = X := Finset.image_id
        rw [← himage]
        exact cover.transport f
          (fun x hx y hy hxy => copy.2.2.1 x (inF x hx) y (inF y hy) hxy)
          (fun x hx y hy hxy => copy.2.2.2.1 x (inF x hx) y (inF y hy) hxy)
          (fun x hx y hy hxy => copy.2.2.2.2 x (inF x hx) y (inF y hy) hxy)
    · subst heq
      exact R2_cofinal hac X hX P₁ P₂ cof ξ hξ

/-- Carlson's relations satisfy the order conditions of a model of reflection
(Definition 5.6(4)–(7)), with the inclusions `≤₁ ⊆ ≤` and `≤₂ ⊆ ≤₁`. -/
theorem model_of_reflection :
    (∀ a b, R1 a b → a ≤ b) ∧ (∀ a b, R2 a b → R1 a b) ∧
    (∀ a, R1 a a) ∧ (∀ a, R2 a a) ∧
    (∀ a b c, R1 a b → R1 b c → R1 a c) ∧ (∀ a b c, R2 a b → R2 b c → R2 a c) ∧
    (∀ a b c, a ≤ b → b ≤ c → R1 a c → R1 a b) ∧
    (∀ a b c, a ≤ b → b ≤ c → R2 a c → R1 b c → R2 a b) :=
  ⟨fun _ _ h => R1_le h, fun _ _ h => R2_R1 h, R1_refl, R2_refl,
    fun _ _ _ h₁ h₂ => R1_trans h₁ h₂, fun _ _ _ h₁ h₂ => R2_trans h₁ h₂,
    fun _ _ _ hab hbc h => R1_between h hab hbc,
    fun _ _ _ hab _ h hbc => R2_respects_R1 h hab hbc⟩

end Alexander313.Carlson
