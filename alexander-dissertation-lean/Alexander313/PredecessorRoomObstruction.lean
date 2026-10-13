import Alexander313.OrdinalPackage
import Alexander313.Wilken.PredecessorDecision

/-!
# A limitation of direct unique-predecessor representations

A decreasing unique-predecessor walk has finite relation cones. In contrast,
finite guard room gives a guarded label infinitely many strict first-relation
predecessors. The generic walk therefore cannot directly recognize the full
first relation on the package's labels via its stated ancestry equivalence.
This does not rule out algorithms using auxiliary finite tracking structures.
-/

namespace Alexander313

theorem Wilken.PredecessorSystem.finite_predecessors {Carrier : Type}
    (S : Wilken.PredecessorSystem Carrier) (y : Carrier) :
    Set.Finite {x | S.relation x y} := by
  classical
  induction y using S.wf.induction with
  | h y ih =>
    cases hp : S.predecessor y with
    | none =>
      apply (Set.finite_singleton y).subset
      intro x hx
      have hx' := (S.relation_iff x y).mp hx
      simpa only [hp, reduceCtorEq, false_and, exists_false, or_false,
        Set.mem_singleton_iff] using hx'
    | some p =>
      apply ((Set.finite_singleton y).union (ih p (S.decreases y p hp))).subset
      intro x hx
      rcases (S.relation_iff x y).mp hx with he | ⟨q, hq, hr⟩
      · exact Or.inl he
      · have he : p = q := Option.some.inj (hp.symm.trans hq)
        exact Or.inr (he.symm ▸ hr)

theorem OrdinalPackage.strict_first_predecessors_infinite (P : OrdinalPackage)
    (top : P.Label) (guard : GuardHead P.R₂ 1 top) :
    Set.Infinite {x | x < top ∧ P.R₁ x top} := by
  classical
  intro finite
  let X := finite.toFinset
  have hX : ∀ x ∈ X, x < top ∧ P.R₁ x top := by
    intro x hx
    exact finite.mem_toFinset.mp hx
  obtain ⟨copy, shape, below, _⟩ := P.room 0 top guard X hX 1
  have nonempty : copy 0 ≠ [] := by
    intro empty
    have len := (shape 0 (by omega)).1
    rw [empty] at len
    simp at len
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ nonempty
  have hb := below 0 (by omega) x hx
  have member : x ∈ X := finite.mem_toFinset.mpr ⟨hb.2.1, hb.2.2⟩
  exact (lt_irrefl x) (hb.1 x member)

theorem OrdinalPackage.no_direct_first_predecessorSystem (P : OrdinalPackage)
    (S : Wilken.PredecessorSystem P.Label)
    (exactRelation : ∀ x y, S.relation x y ↔ P.R₁ x y) : False := by
  obtain ⟨top, guard⟩ := P.tall 1
  apply P.strict_first_predecessors_infinite top guard
  apply (S.finite_predecessors top).subset
  intro x hx
  exact (exactRelation x top).mpr hx.2

end Alexander313
