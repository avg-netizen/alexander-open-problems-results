import Alexander313.Carlson.Basic
import Alexander313.OrdinalPackage
import Alexander313.Wilken.PureRelationsOrdinalGuardRoom

/-!
# An ordinal package from Carlson's covering relations

`OrdinalPresentation` is an order isomorphism of a label type onto an initial
segment `[0, bound)` of the ordinals, given by a value map and a section of it.
`OrdinalPackage.ofCarlson` builds the whole package on natural-number labels
from such a presentation, three recognizing Programs and finite tallness.
Well-foundedness, reflexivity, `R₁ ⊆ ≤`, covering reflection, connectedness and
separated guard room are proved from Carlson's relations. They are not inputs.

The only inputs left are the ones an initial segment of Carlson's structure
does not give for free: an effective presentation (the Programs) and guards of
every finite rank inside the segment. Carlson §14–§15 supply both for the core.
-/

noncomputable section

namespace Alexander313

/-- Labels presented as an initial segment `[0, bound)` of the ordinals. -/
structure OrdinalPresentation (Label : Type) [LinearOrder Label] where
  val : Label → Ordinal.{0}
  pre : Ordinal.{0} → Label
  bound : Ordinal.{0}
  lt_iff : ∀ x y, val x < val y ↔ x < y
  val_lt : ∀ x, val x < bound
  val_pre : ∀ ξ, ξ < bound → val (pre ξ) = ξ

namespace OrdinalPresentation

variable {Label : Type} [LinearOrder Label] (P : OrdinalPresentation Label)

theorem le_iff (x y : Label) : P.val x ≤ P.val y ↔ x ≤ y := by
  rw [← not_lt, ← not_lt, P.lt_iff]

theorem val_injective : Function.Injective P.val := by
  intro x y h
  exact le_antisymm ((P.le_iff x y).mp h.le) ((P.le_iff y x).mp h.ge)

theorem pre_val (x : Label) : P.pre (P.val x) = x :=
  P.val_injective (P.val_pre _ (P.val_lt x))

end OrdinalPresentation

namespace Carlson

/-- A guard with `k + 2` points has one copy of its first `k + 1` points below
its head, above any finite set already below the head, with every copied
point first-related to the head. -/
theorem guard_one_copy (k : Nat) (top : Ordinal.{0})
    (guard : ∃ tail : List Ordinal.{0}, tail.length = k + 1 ∧
      (top :: tail).Pairwise (· < ·) ∧ (top :: tail).Pairwise R2)
    (X : Finset Ordinal.{0}) (hX : ∀ x ∈ X, x < top ∧ R1 x top) :
    ∃ ys : List Ordinal.{0}, ys.length = k + 1 ∧ ys.Pairwise (· < ·) ∧
      ys.Pairwise R2 ∧
      ∀ y ∈ ys, (∀ x ∈ X, x < y) ∧ y < top ∧ R1 y top := by
  obtain ⟨tail, hlen, hord, hrel⟩ := guard
  have hne : tail ≠ [] := by
    intro h
    simp only [h, List.length_nil] at hlen
    omega
  obtain ⟨pre, endpoint, htail⟩ := guardRoom_last tail hne
  let body := top :: pre
  have hfull : top :: tail = body ++ [endpoint] := by
    simp only [body, htail, List.cons_append]
  have hord' := List.pairwise_append.mp (hfull ▸ hord)
  have hrel' := List.pairwise_append.mp (hfull ▸ hrel)
  have htop : top ∈ body := List.mem_cons_self
  have hlast : endpoint ∈ [endpoint] := List.mem_cons_self
  have hlt : top < endpoint := hord'.2.2 top htop endpoint hlast
  have hR : R2 top endpoint := hrel'.2.2 top htop endpoint hlast
  have below_end (z : Ordinal.{0}) (hz : z ∈ body) : z < endpoint := hord'.2.2 z hz endpoint hlast
  have above_top (z : Ordinal.{0}) (hz : z ∈ body) : top ≤ z := by
    rcases List.mem_cons.mp hz with rfl | hz
    · exact le_rfl
    · exact ((List.pairwise_cons.mp hord'.1).1 z hz).le
  let F := X ∪ body.toFinset
  have hF : ∀ z ∈ F, z < endpoint := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact (hX z hz).1.trans hlt
    · exact below_end z (List.mem_toFinset.mp hz)
  obtain ⟨f, copy, links⟩ := R2_copy' hR F hF
  have inF (z : Ordinal.{0}) (hz : z ∈ body) : z ∈ F :=
    Finset.mem_union.mpr (Or.inr (List.mem_toFinset.mpr hz))
  have inX (x : Ordinal.{0}) (hx : x ∈ X) : x ∈ F := Finset.mem_union.mpr (Or.inl hx)
  refine ⟨body.map f, ?_, ?_, ?_, ?_⟩
  · rw [List.length_map]
    have : pre.length = k := by
      simp only [htail, List.length_append, List.length_singleton] at hlen
      omega
    simp only [body, List.length_cons, this]
  · exact guardRoom_pairwise_map (· < ·) (· < ·) f body hord'.1
      (fun x hx y hy hxy => copy.2.2.1 x (inF x hx) y (inF y hy) hxy)
  · exact guardRoom_pairwise_map R2 R2 f body hrel'.1
      (fun x hx y hy hxy => copy.2.2.2.2 x (inF x hx) y (inF y hy) hxy)
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
    refine ⟨fun x hx => ?_, copy.1 z (inF z hz), ?_⟩
    · have hxz : x < z := (hX x hx).1.trans_le (above_top z hz)
      have := copy.2.2.1 x (inX x hx) z (inF z hz) hxz
      rwa [copy.2.1 x (inX x hx) (hX x hx).1] at this
    · apply links z (inF z hz) (above_top z hz)
      rcases List.mem_cons.mp hz with rfl | hz'
      · exact R2_R1 hR
      · exact R2_R1 (hrel'.2.2 z hz endpoint hlast)

/-- Separated finite guard room for Carlson's relations, on all ordinals. -/
theorem finite_guard_room (k : Nat) (top : Ordinal.{0})
    (guard : ∃ tail : List Ordinal.{0}, tail.length = k + 1 ∧
      (top :: tail).Pairwise (· < ·) ∧ (top :: tail).Pairwise R2)
    (X : Finset (Ordinal.{0})) (hX : ∀ x ∈ X, x < top ∧ R1 x top) (N : Nat) :
    ∃ copy : Nat → List (Ordinal.{0}),
      (∀ j < N, (copy j).length = k + 1 ∧ (copy j).Pairwise (· < ·) ∧
        (copy j).Pairwise R2) ∧
      (∀ j < N, ∀ y ∈ copy j, (∀ x ∈ X, x < y) ∧ y < top ∧ R1 y top) ∧
      (∀ i j, i < j → j < N → ∀ y ∈ copy i, ∀ z ∈ copy j, y < z) :=
  finite_guard_room_of_one_copy R1 R2 k top (guard_one_copy k top guard) X hX N

end Carlson

namespace OrdinalPresentation

variable {Label : Type} [LinearOrder Label] (P : OrdinalPresentation Label)

/-- The transported first and second relations. -/
def first (x y : Label) : Prop := Carlson.R1 (P.val x) (P.val y)

def second (x y : Label) : Prop := Carlson.R2 (P.val x) (P.val y)

include P in
theorem wf : WellFounded ((· < ·) : Label → Label → Prop) :=
  Subrelation.wf (fun h => (P.lt_iff _ _).mpr h) (InvImage.wf P.val Ordinal.lt_wf)

/-- Covering reflection on the labels. -/
theorem covering (α β : Label) (h : P.first α β) :
    FiniteLabelCovering P.first P.second α β := by
  intro F hF
  let G := F.image P.val
  have hG : ∀ z ∈ G, z < P.val β := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact (P.lt_iff x β).mpr (hF x hx)
  obtain ⟨f, below, fixed, mono, rel₁, rel₂⟩ := Carlson.R1_copy' h G hG
  have mem (x : Label) (hx : x ∈ F) : P.val x ∈ G := Finset.mem_image_of_mem P.val hx
  let g : Label → Label := fun x => P.pre (f (P.val x))
  have hg (x : Label) (hx : x ∈ F) : P.val (g x) = f (P.val x) :=
    P.val_pre _ ((below _ (mem x hx)).trans (P.val_lt α))
  have strict (x : Label) (hx : x ∈ F) (y : Label) (hy : y ∈ F) (hxy : x < y) : g x < g y := by
    rw [← P.lt_iff, hg x hx, hg y hy]
    exact mono _ (mem x hx) _ (mem y hy) ((P.lt_iff x y).mpr hxy)
  refine ⟨g, fun x hx => ?_, fun x hx hxα => ?_, ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [← P.lt_iff, hg x hx]
    exact below _ (mem x hx)
  · apply P.val_injective
    rw [hg x hx]
    exact fixed _ (mem x hx) ((P.lt_iff x α).mpr hxα)
  · intro x hx y hy
    constructor
    · intro hxy
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · exact (strict x hx y hy hlt).ne hxy
      · exact (strict y hy x hx hlt).ne hxy.symm
    · rintro rfl
      rfl
  · intro x hx y hy
    constructor
    · intro hxy
      by_contra hnot
      rcases (not_lt.mp hnot).lt_or_eq with hlt | heq
      · exact lt_asymm hxy (strict y hy x hx hlt)
      · rw [heq] at hxy
        exact lt_irrefl _ hxy
    · exact strict x hx y hy
  · intro x hx y hy hxy
    change Carlson.R1 (P.val (g x)) (P.val (g y))
    rw [hg x hx, hg y hy]
    exact rel₁ _ (mem x hx) _ (mem y hy) hxy
  · intro x hx y hy hxy
    change Carlson.R2 (P.val (g x)) (P.val (g y))
    rw [hg x hx, hg y hy]
    exact rel₂ _ (mem x hx) _ (mem y hy) hxy

theorem connected (p q r : Label) (h : P.first p r) (hpq : p ≤ q) (hqr : q ≤ r) :
    P.first p q :=
  Carlson.R1_between h ((P.le_iff p q).mpr hpq) ((P.le_iff q r).mpr hqr)

/-- Separated guard room on the labels, transported from the ordinals. -/
theorem room (k : Nat) (top : Label) (guard : GuardHead P.second (k + 1) top)
    (X : Finset Label) (hX : ∀ x ∈ X, x < top ∧ P.first x top) (N : Nat) :
    ∃ copy : Nat → List Label,
      (∀ j < N, (copy j).length = k + 1 ∧ (copy j).Pairwise (· < ·) ∧
        (copy j).Pairwise P.second) ∧
      (∀ j < N, ∀ y ∈ copy j, (∀ x ∈ X, x < y) ∧ y < top ∧ P.first y top) ∧
      (∀ i j, i < j → j < N → ∀ y ∈ copy i, ∀ z ∈ copy j, y < z) := by
  apply finite_guard_room_of_one_copy P.first P.second k top _ X hX N
  intro Y hY
  obtain ⟨tail, hlen, hord, hrel⟩ := guard
  have oguard : ∃ tail' : List Ordinal.{0}, tail'.length = k + 1 ∧
      (P.val top :: tail').Pairwise (· < ·) ∧ (P.val top :: tail').Pairwise Carlson.R2 := by
    refine ⟨tail.map P.val, by rw [List.length_map, hlen], ?_, ?_⟩
    · simpa only [List.map_cons] using guardRoom_pairwise_map (· < ·) (· < ·) P.val
        (top :: tail) hord (fun x _ y _ hxy => (P.lt_iff x y).mpr hxy)
    · simpa only [List.map_cons] using guardRoom_pairwise_map P.second Carlson.R2 P.val
        (top :: tail) hrel (fun x _ y _ hxy => hxy)
  obtain ⟨ys, ylen, yord, yrel, yrange⟩ := Carlson.guard_one_copy k (P.val top) oguard
    (Y.image P.val) (by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      exact ⟨(P.lt_iff x top).mpr (hY x hx).1, (hY x hx).2⟩)
  have hpre (z : Ordinal.{0}) (hz : z ∈ ys) : P.val (P.pre z) = z :=
    P.val_pre z ((yrange z hz).2.1.trans (P.val_lt top))
  refine ⟨ys.map P.pre, by rw [List.length_map, ylen], ?_, ?_, ?_⟩
  · exact guardRoom_pairwise_map (· < ·) (· < ·) P.pre ys yord (fun x hx y hy hxy => by
      rw [← P.lt_iff, hpre x hx, hpre y hy]
      exact hxy)
  · exact guardRoom_pairwise_map Carlson.R2 P.second P.pre ys yrel (fun x hx y hy hxy => by
      change Carlson.R2 (P.val (P.pre x)) (P.val (P.pre y))
      rw [hpre x hx, hpre y hy]
      exact hxy)
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
    obtain ⟨above, below, link⟩ := yrange z hz
    refine ⟨fun x hx => ?_, ?_, ?_⟩
    · rw [← P.lt_iff, hpre z hz]
      exact above (P.val x) (Finset.mem_image_of_mem P.val hx)
    · rw [← P.lt_iff, hpre z hz]
      exact below
    · change Carlson.R1 (P.val (P.pre z)) (P.val top)
      rw [hpre z hz]
      exact link

end OrdinalPresentation

namespace OrdinalPackage

/-- The whole ordinal package on natural-number labels from an ordinal
presentation of Carlson's relations, three recognizing Programs and finite
tallness. -/
def ofCarlson (order : LinearOrder Nat) (P : OrdinalPresentation (CodedLabel order))
    (ltProgram firstProgram secondProgram : Program)
    (hlt : ∀ μ ν : CodedLabel order, ltProgram.domain (Nat.pair μ ν) ↔ μ < ν)
    (hfirst : ∀ μ ν : CodedLabel order, firstProgram.domain (Nat.pair μ ν) ↔ P.first μ ν)
    (hsecond : ∀ μ ν : CodedLabel order, secondProgram.domain (Nat.pair μ ν) ↔ P.second μ ν)
    (htall : ∀ k, ∃ top : CodedLabel order, GuardHead P.second k top) : OrdinalPackage where
  order := order
  R₁ := P.first
  R₂ := P.second
  wf := P.wf
  ltProgram := ltProgram
  R₁Program := firstProgram
  R₂Program := secondProgram
  lt_program := hlt
  R₁_program := hfirst
  R₂_program := hsecond
  R₁_refl := fun α => Carlson.R1_refl (P.val α)
  R₁_le := fun α β h => (P.le_iff α β).mp (Carlson.R1_le h)
  reflection := P.covering
  connected := P.connected
  room := P.room
  tall := htall

end OrdinalPackage
end Alexander313
