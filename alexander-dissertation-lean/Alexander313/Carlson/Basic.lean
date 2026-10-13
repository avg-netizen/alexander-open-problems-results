import Alexander313.Carlson.Semantics

/-!
# First properties of Carlson's covering relations

Carlson, *Patterns of resemblance of order 2*, Lemma 5.5, pure case. Copy maps
are stated with the global relations `R1`, `R2`: every point involved lies
below the upper endpoint, where the prefix relations of the definition agree
with the global ones. Proved here: reflexivity, `≤₂ ⊆ ≤₁`, cofinal copies for
both relations, connectedness (5.5(5)) and transitivity of `≤₁` (part of
5.5(3)).
-/

noncomputable section

namespace Alexander313.Carlson

theorem CoveringCopy.transfer {α : Type*} [LinearOrder α] {S₁ S₂ T₁ T₂ : α → α → Prop}
    {F : Finset α} {f : α → α} {a : α}
    (h : CoveringCopy S₁ S₂ F f a)
    (in₁ : ∀ z ∈ F, ∀ w ∈ F, T₁ z w → S₁ z w)
    (out₁ : ∀ z ∈ F, ∀ w ∈ F, S₁ (f z) (f w) → T₁ (f z) (f w))
    (in₂ : ∀ z ∈ F, ∀ w ∈ F, T₂ z w → S₂ z w)
    (out₂ : ∀ z ∈ F, ∀ w ∈ F, S₂ (f z) (f w) → T₂ (f z) (f w)) :
    CoveringCopy T₁ T₂ F f a := by
  obtain ⟨below, fixed, mono, rel₁, rel₂⟩ := h
  exact ⟨below, fixed, mono,
    fun z hz w hw hzw => out₁ z hz w hw (rel₁ z hz w hw (in₁ z hz w hw hzw)),
    fun z hz w hw hzw => out₂ z hz w hw (rel₂ z hz w hw (in₂ z hz w hw hzw))⟩

theorem CoveringCopy.subset {α : Type*} [LinearOrder α] {S₁ S₂ : α → α → Prop}
    {F G : Finset α} {f : α → α} {a : α}
    (h : CoveringCopy S₁ S₂ F f a) (hGF : G ⊆ F) : CoveringCopy S₁ S₂ G f a := by
  obtain ⟨below, fixed, mono, rel₁, rel₂⟩ := h
  exact ⟨fun z hz => below z (hGF hz), fun z hz => fixed z (hGF hz),
    fun z hz w hw => mono z (hGF hz) w (hGF hw),
    fun z hz w hw => rel₁ z (hGF hz) w (hGF hw),
    fun z hz w hw => rel₂ z (hGF hz) w (hGF hw)⟩

/-- Copies made with the prefix relations of an upper endpoint `b ≥ a` are
copies for the global relations. -/
theorem CoveringCopy.global {b a : Ordinal.{0}} (hab : a ≤ b) {F : Finset Ordinal.{0}}
    (hF : ∀ z ∈ F, z < b) {f : Ordinal.{0} → Ordinal.{0}}
    (h : CoveringCopy (prefixFirst b) (prefixSecond b) F f a) :
    CoveringCopy R1 R2 F f a :=
  h.transfer (fun _ _ w hw hzw => ⟨hF w hw, hzw⟩) (fun _ _ _ _ h => h.2)
    (fun _ _ w hw hzw => ⟨hF w hw, hzw⟩) (fun _ _ _ _ h => h.2)

/-- The reverse: global copies are prefix copies for any upper endpoint above
both the copied points and their images. -/
theorem CoveringCopy.prefix {b a : Ordinal.{0}} (hab : a ≤ b) {F : Finset Ordinal.{0}}
    {f : Ordinal.{0} → Ordinal.{0}} (h : CoveringCopy R1 R2 F f a) :
    CoveringCopy (prefixFirst b) (prefixSecond b) F f a :=
  h.transfer (fun _ _ _ _ h => h.2) (fun _ hz _ hw hzw => ⟨(h.1 _ hw).trans_le hab, hzw⟩)
    (fun _ _ _ _ h => h.2) (fun _ hz _ hw hzw => ⟨(h.1 _ hw).trans_le hab, hzw⟩)

theorem R1_le {a b : Ordinal.{0}} (h : R1 a b) : a ≤ b := ((R1_iff a b).mp h).1

theorem R2_le {a b : Ordinal.{0}} (h : R2 a b) : a ≤ b := ((R2_iff a b).mp h).1

theorem identity_copy {α : Type*} [LinearOrder α] (S₁ S₂ : α → α → Prop) (a : α)
    (F : Finset α) (hF : ∀ z ∈ F, z < a) : CoveringCopy S₁ S₂ F id a :=
  ⟨hF, fun _ _ _ => rfl, fun _ _ _ _ h => h, fun _ _ _ _ h => h, fun _ _ _ _ h => h⟩

theorem R1_refl (a : Ordinal.{0}) : R1 a a :=
  (R1_iff a a).mpr ⟨le_rfl, fun F hF => ⟨id, identity_copy _ _ a F hF⟩⟩

theorem R2_refl (a : Ordinal.{0}) : R2 a a := by
  refine (R2_iff a a).mpr ⟨le_rfl, fun F hF => ⟨id, identity_copy _ _ a F hF, ?_⟩,
    fun _ _ _ _ _ h => h⟩
  intro z hz haz
  exact absurd (hF z hz) (not_lt.mpr haz)

theorem R2_R1 {a b : Ordinal.{0}} (h : R2 a b) : R1 a b := by
  obtain ⟨hab, linked, _⟩ := (R2_iff a b).mp h
  refine (R1_iff a b).mpr ⟨hab, fun F hF => ?_⟩
  obtain ⟨f, copy, _⟩ := linked F hF
  exact ⟨f, copy⟩

/-- Lemma 5.5(1): copies with the global relations, all copied points above a
prescribed cutoff `ξ < a`. -/
theorem R1_copy {a b : Ordinal.{0}} (h : R1 a b) (F : Finset Ordinal.{0})
    (hF : ∀ z ∈ F, z < b) (ξ : Ordinal.{0}) (hξ : ξ < a) :
    ∃ f, CoveringCopy R1 R2 F f a ∧ ∀ z ∈ F, a ≤ z → ξ < f z := by
  obtain ⟨hab, cond⟩ := (R1_iff a b).mp h
  have hF' : ∀ z ∈ insert ξ F, z < b := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hξ.trans_le hab
    · exact hF z hz
  obtain ⟨f, copy⟩ := cond (insert ξ F) hF'
  have global := copy.global hab hF'
  refine ⟨f, global.subset (Finset.subset_insert ξ F), fun z hz haz => ?_⟩
  have hfix : f ξ = ξ := global.2.1 ξ (Finset.mem_insert_self ξ F) hξ
  have := global.2.2.1 ξ (Finset.mem_insert_self ξ F) z (Finset.mem_insert_of_mem hz)
    (hξ.trans_le haz)
  rwa [hfix] at this

/-- Lemma 5.5(2): copies for the second relation keep first-relation links to
the endpoints, again above a prescribed cutoff. -/
theorem R2_copy {a b : Ordinal.{0}} (h : R2 a b) (F : Finset Ordinal.{0})
    (hF : ∀ z ∈ F, z < b) (ξ : Ordinal.{0}) (hξ : ξ < a) :
    ∃ f, CoveringCopy R1 R2 F f a ∧ (∀ z ∈ F, a ≤ z → ξ < f z) ∧
      ∀ z ∈ F, a ≤ z → R1 z b → R1 (f z) a := by
  obtain ⟨hab, linked, _⟩ := (R2_iff a b).mp h
  have hF' : ∀ z ∈ insert ξ F, z < b := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hξ.trans_le hab
    · exact hF z hz
  obtain ⟨f, copy, links⟩ := linked (insert ξ F) hF'
  have global := copy.global hab hF'
  refine ⟨f, global.subset (Finset.subset_insert ξ F), fun z hz haz => ?_,
    fun z hz haz hzb => (links z (Finset.mem_insert_of_mem hz) haz hzb).2⟩
  have hfix : f ξ = ξ := global.2.1 ξ (Finset.mem_insert_self ξ F) hξ
  have := global.2.2.1 ξ (Finset.mem_insert_self ξ F) z (Finset.mem_insert_of_mem hz)
    (hξ.trans_le haz)
  rwa [hfix] at this

/-- Lemma 5.5(5): the first relation respects the order (connectedness). -/
theorem R1_between {p q r : Ordinal.{0}} (h : R1 p r) (hpq : p ≤ q) (hqr : q ≤ r) :
    R1 p q := by
  obtain ⟨_, cond⟩ := (R1_iff p r).mp h
  refine (R1_iff p q).mpr ⟨hpq, fun F hF => ?_⟩
  obtain ⟨f, copy⟩ := cond F (fun z hz => (hF z hz).trans_le hqr)
  refine ⟨f, copy.transfer (fun _ _ w hw hzw => ⟨(hF w hw).trans_le hqr, hzw.2⟩)
    (fun _ _ w hw hzw => ⟨(copy.1 w hw).trans_le hpq, hzw.2⟩)
    (fun _ _ w hw hzw => ⟨(hF w hw).trans_le hqr, hzw.2⟩)
    (fun _ _ w hw hzw => ⟨(copy.1 w hw).trans_le hpq, hzw.2⟩)⟩

/-- Part of Lemma 5.5(3): the first relation is transitive. Copy the part
above `b` below `b`, then copy everything above `a` below `a`. -/
theorem R1_trans {a b c : Ordinal.{0}} (hab : R1 a b) (hbc : R1 b c) : R1 a c := by
  have hab' := R1_le hab
  have hbc' := R1_le hbc
  refine (R1_iff a c).mpr ⟨hab'.trans hbc', fun F hF => ?_⟩
  obtain ⟨_, condBC⟩ := (R1_iff b c).mp hbc
  obtain ⟨g, copyG⟩ := condBC F hF
  have globalG := copyG.global hbc' hF
  let G := F.image g
  have hG : ∀ z ∈ G, z < b := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    exact globalG.1 w hw
  obtain ⟨_, condAB⟩ := (R1_iff a b).mp hab
  obtain ⟨h, copyH⟩ := condAB G hG
  have globalH := copyH.global hab' hG
  have mem (z : Ordinal.{0}) (hz : z ∈ F) : g z ∈ G := Finset.mem_image_of_mem g hz
  refine ⟨h ∘ g, CoveringCopy.prefix (hab'.trans hbc') ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro z hz
    exact globalH.1 (g z) (mem z hz)
  · intro z hz hza
    change h (g z) = z
    rw [globalG.2.1 z hz (hza.trans_le hab')]
    exact globalH.2.1 z (by
      have := mem z hz
      rwa [globalG.2.1 z hz (hza.trans_le hab')] at this) hza
  · intro z hz w hw hzw
    exact globalH.2.2.1 _ (mem z hz) _ (mem w hw) (globalG.2.2.1 z hz w hw hzw)
  · intro z hz w hw hzw
    exact globalH.2.2.2.1 _ (mem z hz) _ (mem w hw) (globalG.2.2.2.1 z hz w hw hzw)
  · intro z hz w hw hzw
    exact globalH.2.2.2.2 _ (mem z hz) _ (mem w hw) (globalG.2.2.2.2 z hz w hw hzw)

/-- Copies without a cutoff: the prefix copy of the definition, globalized. -/
theorem R1_copy' {a b : Ordinal.{0}} (h : R1 a b) (F : Finset Ordinal.{0})
    (hF : ∀ z ∈ F, z < b) : ∃ f, CoveringCopy R1 R2 F f a := by
  obtain ⟨hab, cond⟩ := (R1_iff a b).mp h
  obtain ⟨f, copy⟩ := cond F hF
  exact ⟨f, copy.global hab hF⟩

theorem R2_copy' {a b : Ordinal.{0}} (h : R2 a b) (F : Finset Ordinal.{0})
    (hF : ∀ z ∈ F, z < b) :
    ∃ f, CoveringCopy R1 R2 F f a ∧ ∀ z ∈ F, a ≤ z → R1 z b → R1 (f z) a := by
  obtain ⟨hab, linked, _⟩ := (R2_iff a b).mp h
  obtain ⟨f, copy, links⟩ := linked F hF
  exact ⟨f, copy.global hab hF, fun z hz haz hzb => (links z hz haz hzb).2⟩

end Alexander313.Carlson
