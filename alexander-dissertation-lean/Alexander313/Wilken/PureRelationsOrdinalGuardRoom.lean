import Alexander313.Wilken.PureRelationsSeparatedCopies

/-!
# Exact finite guard room for the actual ordinal relations

This ordinal-only theorem does not depend on modal syntax or stage semantics.
The input guard contains k+2 points; its last point is excluded from the copied
pattern.  Iteration retains every copy point below and R1-related to its head.
No effective presentation or finite-tallness hypothesis is asserted here.
-/

noncomputable section

namespace Alexander313

theorem guardRoom_last {α : Type*} (xs : List α) (hne : xs ≠ []) :
    ∃ ys z, xs = ys ++ [z] := by
  induction xs with
  | nil => exact False.elim (hne rfl)
  | cons x xs ih =>
    cases xs with
    | nil => exact ⟨[], x, rfl⟩
    | cons y ys =>
      obtain ⟨zs, z, hz⟩ := ih (by simp)
      exact ⟨x :: zs, z, by simp only [hz, List.cons_append]⟩

theorem guardRoom_pairwise_map {α β : Type*}
    (R : α → α → Prop) (S : β → β → Prop) (f : α → β) (xs : List α)
    (h : xs.Pairwise R)
    (hf : ∀ x ∈ xs, ∀ y ∈ xs, R x y → S (f x) (f y)) :
    (xs.map f).Pairwise S := by
  induction xs with
  | nil => exact List.Pairwise.nil
  | cons x xs ih =>
    obtain ⟨hx, hs⟩ := List.pairwise_cons.mp h
    apply List.pairwise_cons.mpr
    constructor
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
      exact hf x List.mem_cons_self y (List.mem_cons_of_mem x hy) (hx y hy)
    · exact ih hs (fun y hy z hz =>
        hf y (List.mem_cons_of_mem x hy) z (List.mem_cons_of_mem x hz))

/-- One-copy room iterates to arbitrarily many fully separated copies.  The
old finite support is enlarged by every point of the newest copy. -/
theorem finite_guard_room_of_one_copy {Label : Type*} [LinearOrder Label]
    (R₁ R₂ : Label → Label → Prop) (k : Nat) (top : Label)
    (one : ∀ X : Finset Label, (∀ x ∈ X, x < top ∧ R₁ x top) →
      ∃ ys : List Label, ys.length = k + 1 ∧ ys.Pairwise (· < ·) ∧
        ys.Pairwise R₂ ∧
        ∀ y ∈ ys, (∀ x ∈ X, x < y) ∧ y < top ∧ R₁ y top)
    (X : Finset Label) (hX : ∀ x ∈ X, x < top ∧ R₁ x top) (N : Nat) :
    ∃ copy : Nat → List Label,
      (∀ j < N, (copy j).length = k + 1 ∧ (copy j).Pairwise (· < ·) ∧
        (copy j).Pairwise R₂) ∧
      (∀ j < N, ∀ y ∈ copy j, (∀ x ∈ X, x < y) ∧ y < top ∧ R₁ y top) ∧
      (∀ i j, i < j → j < N → ∀ y ∈ copy i, ∀ z ∈ copy j, y < z) := by
  induction N generalizing X with
  | zero =>
    exact ⟨fun _ => [], by simp, by simp, by simp⟩
  | succ N ih =>
    obtain ⟨ys, hlen, hord, hrel, hys⟩ := one X hX
    let X' := X ∪ ys.toFinset
    have hX' : ∀ x ∈ X', x < top ∧ R₁ x top := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact hX x hx
      · exact (hys x (List.mem_toFinset.mp hx)).2
    obtain ⟨old, hshape, hrange, hsep⟩ := ih X' hX'
    let copy : Nat → List Label
      | 0 => ys
      | j + 1 => old j
    refine ⟨copy, ?_, ?_, ?_⟩
    · intro j hj
      cases j with
      | zero => exact ⟨hlen, hord, hrel⟩
      | succ j => exact hshape j (Nat.lt_of_succ_lt_succ hj)
    · intro j hj y hy
      cases j with
      | zero => exact hys y hy
      | succ j =>
        have h := hrange j (Nat.lt_of_succ_lt_succ hj) y hy
        exact ⟨fun x hx => h.1 x (Finset.mem_union.mpr (Or.inl hx)), h.2⟩
    · intro i j hij hj y hy z hz
      cases j with
      | zero => exact False.elim (Nat.not_lt_zero i hij)
      | succ j =>
        cases i with
        | zero =>
          exact (hrange j (Nat.lt_of_succ_lt_succ hj) z hz).1 y
            (Finset.mem_union.mpr (Or.inr (List.mem_toFinset.mpr hy)))
        | succ i =>
          exact hsep i j (Nat.lt_of_succ_lt_succ hij)
            (Nat.lt_of_succ_lt_succ hj) y hy z hz

namespace Wilken.PureRelations

/-- A strict second-relation guard supplies one copy of its proper prefix.
In particular every copied point is first-related to the original head. -/
theorem finite_guard_one_copy (k : Nat) (top : Ordinal.{0})
    (guard : ∃ tail : List Ordinal.{0}, tail.length = k + 1 ∧
      (top :: tail).Pairwise (· < ·) ∧ (top :: tail).Pairwise R2)
    (X : Finset (Ordinal.{0})) (hX : ∀ x ∈ X, x < top ∧ R1 x top) :
    ∃ ys : List (Ordinal.{0}), ys.length = k + 1 ∧ ys.Pairwise (· < ·) ∧
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
  have lower_exists : ∃ c : Ordinal.{0}, c < top := by
    obtain ⟨f, below, _, _⟩ := finiteLabelReflection_of_R2 top endpoint hR
      {top} (by intro x hx; simpa only [Finset.mem_singleton.mp hx] using hlt)
    exact ⟨f top, below top (Finset.mem_singleton_self top)⟩
  obtain ⟨c, hc⟩ := lower_exists
  let Y := body.toFinset
  have hY : ∀ y ∈ Y, top ≤ y ∧ y < endpoint := by
    intro y hy
    have hm : y ∈ body := List.mem_toFinset.mp hy
    refine ⟨?_, hord'.2.2 y hm endpoint hlast⟩
    rcases List.mem_cons.mp hm with rfl | hm
    · exact le_rfl
    · exact ((List.pairwise_cons.mp hord'.1).1 y hm).le
  obtain ⟨f, pattern, _, range, separated, links⟩ :=
    SeparatedCopies.finite_separated_copy top endpoint hR hlt X Y
      (fun x hx => (hX x hx).1) hY c hc
  have inPattern (x : Ordinal.{0}) (hx : x ∈ body) : x ∈ X ∪ Y :=
    Finset.mem_union.mpr (Or.inr (List.mem_toFinset.mpr hx))
  refine ⟨body.map f, ?_, ?_, ?_, ?_⟩
  · rw [List.length_map]
    have : pre.length = k := by
      simp only [htail, List.length_append, List.length_singleton] at hlen
      omega
    simp only [body, List.length_cons, this]
  · exact guardRoom_pairwise_map (· < ·) (· < ·) f body hord'.1
      (fun x hx y hy hxy => (pattern.2.1 x (inPattern x hx) y (inPattern y hy)).mpr hxy)
  · exact guardRoom_pairwise_map R2 R2 f body hrel'.1
      (fun x hx y hy hxy => (pattern.2.2.2 x (inPattern x hx) y (inPattern y hy)).mpr hxy)
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
    have hzY : z ∈ Y := List.mem_toFinset.mpr hz
    exact ⟨fun x hx => separated x hx z hzY, (range z hzY).2,
      links z hzY (R2_R1 (hrel'.2.2 z hz endpoint hlast))⟩

/-- The exact separated finite-room field of `OrdinalPackage`, for the
genuine pure relations on any actual small ordinal interval. -/
theorem finite_guard_room (k : Nat) (top : Ordinal.{0})
    (guard : ∃ tail : List Ordinal.{0}, tail.length = k + 1 ∧
      (top :: tail).Pairwise (· < ·) ∧ (top :: tail).Pairwise R2)
    (X : Finset (Ordinal.{0})) (hX : ∀ x ∈ X, x < top ∧ R1 x top) (N : Nat) :
    ∃ copy : Nat → List (Ordinal.{0}),
      (∀ j < N, (copy j).length = k + 1 ∧ (copy j).Pairwise (· < ·) ∧
        (copy j).Pairwise R2) ∧
      (∀ j < N, ∀ y ∈ copy j, (∀ x ∈ X, x < y) ∧ y < top ∧ R1 y top) ∧
      (∀ i j, i < j → j < N → ∀ y ∈ copy i, ∀ z ∈ copy j, y < z) :=
  finite_guard_room_of_one_copy R1 R2 k top
    (finite_guard_one_copy k top guard) X hX N

end Wilken.PureRelations
end Alexander313
