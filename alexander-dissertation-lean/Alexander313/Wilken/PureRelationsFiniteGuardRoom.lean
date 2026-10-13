import Alexander313.OrdinalPackage
import Alexander313.Wilken.PureRelationsOrdinalGuardRoom
import Alexander313.Wilken.PureRelationsSmallSeparatedCopies

/-!
# Exact finite guard room from the actual pure separated-copy theorem

The last point of the input guard is the upper endpoint, not a point of the
copied pattern.  The other k+1 points are copied below the guard head.  Every
copied point retains its first-relation link to that head.  Iterating above
the entire preceding copies supplies the exact `OrdinalPackage.room` clause.

This proves room for every actual small ordinal interval.  It does not assert
effective recognizers for its pure relations or guards of arbitrary rank.
-/

noncomputable section

namespace Alexander313

namespace Wilken.PureRelations.SmallLabels

/-- A strict second-relation guard supplies one copy of its proper prefix.
In particular every copied point is first-related to the original head. -/
theorem finite_guard_one_copy (Ω : Ordinal.{0}) (k : Nat) (top : Labels Ω)
    (guard : GuardHead (second Ω) (k + 1) top)
    (X : Finset (Labels Ω)) (hX : ∀ x ∈ X, x < top ∧ first Ω x top) :
    ∃ ys : List (Labels Ω), ys.length = k + 1 ∧ ys.Pairwise (· < ·) ∧
      ys.Pairwise (second Ω) ∧
      ∀ y ∈ ys, (∀ x ∈ X, x < y) ∧ y < top ∧ first Ω y top := by
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
  have hR : second Ω top endpoint := hrel'.2.2 top htop endpoint hlast
  have lower_exists : ∃ c : Labels Ω, c < top := by
    obtain ⟨f, below, _, _⟩ := finiteLabelReflection_of_second Ω top endpoint hR
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
    SeparatedCopies.finite_separated_copy Ω top endpoint hR hlt X Y
      (fun x hx => (hX x hx).1) hY c hc
  have inPattern (x : Labels Ω) (hx : x ∈ body) : x ∈ X ∪ Y :=
    Finset.mem_union.mpr (Or.inr (List.mem_toFinset.mpr hx))
  refine ⟨body.map f, ?_, ?_, ?_, ?_⟩
  · rw [List.length_map]
    have : pre.length = k := by
      simp only [htail, List.length_append, List.length_singleton] at hlen
      omega
    simp only [body, List.length_cons, this]
  · exact guardRoom_pairwise_map (· < ·) (· < ·) f body hord'.1
      (fun x hx y hy hxy => (pattern.2.1 x (inPattern x hx) y (inPattern y hy)).mpr hxy)
  · exact guardRoom_pairwise_map (second Ω) (second Ω) f body hrel'.1
      (fun x hx y hy hxy => (pattern.2.2.2 x (inPattern x hx) y (inPattern y hy)).mpr hxy)
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
    have hzY : z ∈ Y := List.mem_toFinset.mpr hz
    exact ⟨fun x hx => separated x hx z hzY, (range z hzY).2,
      links z hzY (R2_R1 (hrel'.2.2 z hz endpoint hlast))⟩

/-- The exact separated finite-room field of `OrdinalPackage`, for the
genuine pure relations on any actual small ordinal interval. -/
theorem finite_guard_room (Ω : Ordinal.{0}) (k : Nat) (top : Labels Ω)
    (guard : GuardHead (second Ω) (k + 1) top)
    (X : Finset (Labels Ω)) (hX : ∀ x ∈ X, x < top ∧ first Ω x top) (N : Nat) :
    ∃ copy : Nat → List (Labels Ω),
      (∀ j < N, (copy j).length = k + 1 ∧ (copy j).Pairwise (· < ·) ∧
        (copy j).Pairwise (second Ω)) ∧
      (∀ j < N, ∀ y ∈ copy j, (∀ x ∈ X, x < y) ∧ y < top ∧ first Ω y top) ∧
      (∀ i j, i < j → j < N → ∀ y ∈ copy i, ∀ z ∈ copy j, y < z) :=
  finite_guard_room_of_one_copy (first Ω) (second Ω) k top
    (finite_guard_one_copy Ω k top guard) X hX N

end Wilken.PureRelations.SmallLabels
end Alexander313
