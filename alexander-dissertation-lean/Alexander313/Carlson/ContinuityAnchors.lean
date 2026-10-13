import Alexander313.Carlson.ArithmeticLifting

/-!
# Relations at the least old upper bound

These finite-carrier lemmas express the anchor calculations used in Carlson's
proof of Lemma 12.6, Claims 3 and 4, in the pure case. A continuous extension
transfers every relation crossing an old upper bound to the corresponding
old upper bounds. A relation ending at an old point factors through the
least old upper bound of its source.

Source: https://people.math.osu.edu/carlson.6/research/patternstwofinal.pdf,
printed pp. 51–54 of the author's October 16, 2008 manuscript.
-/

noncomputable section

namespace Alexander313.Carlson

namespace Str

variable {α : Type*} [LinearOrder α]

theorem IsPattern.rel_le {T : Str α} (hT : T.IsPattern) (k : Lvl)
    {x y : α} (hx : x ∈ T.U) (hy : y ∈ T.U) (hr : T.rel k x y) : x ≤ y := by
  cases k
  · exact hT.le₁ x hx y hy hr
  · exact hT.le₁ x hx y hy (hT.sub₂ x hx y hy hr)

theorem IsPattern.rel_refl {T : Str α} (hT : T.IsPattern) (k : Lvl)
    {x : α} (hx : x ∈ T.U) : T.rel k x x := by
  cases k
  · exact hT.refl₁ x hx
  · exact hT.refl₂ x hx

theorem IsPattern.rel_trans {T : Str α} (hT : T.IsPattern) (k : Lvl)
    {x y z : α} (hx : x ∈ T.U) (hy : y ∈ T.U) (hz : z ∈ T.U)
    (hxy : T.rel k x y) (hyz : T.rel k y z) : T.rel k x z := by
  cases k
  · exact hT.trans₁ x hx y hy z hz hxy hyz
  · exact hT.trans₂ x hx y hy z hz hxy hyz

theorem IsPattern.rel_sub_one {T : Str α} (hT : T.IsPattern) (k : Lvl)
    {x y : α} (hx : x ∈ T.U) (hy : y ∈ T.U) (hr : T.rel k x y) : T.r₁ x y := by
  cases k
  · exact hr
  · exact hT.sub₂ x hx y hy hr

theorem IsPattern.relDown_of_rel {T : Str α} (hT : T.IsPattern) (k : Lvl)
    {x y : α} (hx : x ∈ T.U) (hy : y ∈ T.U) (hr : T.rel k x y) :
    T.relDown k x y := by
  cases k
  · exact hT.le₁ x hx y hy hr
  · exact hT.sub₂ x hx y hy hr

theorem IsPattern.relDown_le {T : Str α} (hT : T.IsPattern) (k : Lvl)
    {x y : α} (hx : x ∈ T.U) (hy : y ∈ T.U) (hr : T.relDown k x y) : x ≤ y := by
  cases k
  · exact hr
  · exact hT.le₁ x hx y hy hr

/-- Convexity and respect combined into a single statement at either level. -/
theorem IsPattern.rel_between {T : Str α} (hT : T.IsPattern) (k : Lvl)
    {x y z : α} (hx : x ∈ T.U) (hy : y ∈ T.U) (hz : z ∈ T.U)
    (hxy : x ≤ y) (hyz : T.relDown k y z) (hxz : T.rel k x z) : T.rel k x y := by
  cases k
  · exact hT.convex₁ x hx y hy z hz hxy hyz hxz
  · exact hT.respect₂ x hx y hy z hz hxy (hT.le₁ y hy z hz hyz) hxz hyz

theorem Continuous.kcorrect {P T : Str α} (hC : Continuous P T) (k : Lvl) :
    KCorrect P T k := by
  cases k
  · exact hC.2.2.1
  · exact hC.2.2.2

/-- Normalize the existential upper bound in k-correctness to any specified
least old upper bound of the destination. -/
theorem Continuous.rel_up {P T : Str α} (hC : Continuous P T)
    {k : Lvl} {x y p q : α} (hx : x ∈ T.U) (hy : y ∈ T.U)
    (hp : LeastGE P.U x p) (hq : LeastGE P.U y q)
    (hpy : p < y) (hr : T.rel k x y) : P.rel k p q := by
  obtain ⟨q', hq', hpq'⟩ := hC.kcorrect k p x y hx hy hp hpy hr
  have heq : q' = q := hq'.unique hq
  simpa only [heq] using hpq'

/-- The least-old-upper-bound map preserves both relations. If an edge
does not cross its source's upper bound, the two upper bounds coincide. -/
theorem Continuous.rel_up_of_rel {P T : Str α} (hC : Continuous P T)
    (hT : T.IsPattern) (k : Lvl) {x y p q : α}
    (hx : x ∈ T.U) (hy : y ∈ T.U)
    (hp : LeastGE P.U x p) (hq : LeastGE P.U y q)
    (hr : T.rel k x y) : P.rel k p q := by
  by_cases hpy : p < y
  · exact hC.rel_up hx hy hp hq hpy hr
  · have hqp : q ≤ p := hq.2.2 p hp.1 (not_lt.mp hpy)
    have hpq : p ≤ q := hp.2.2 q hq.1 ((hT.rel_le k hx hy hr).trans hq.2.1)
    have heq : p = q := le_antisymm hpq hqp
    rw [heq]
    exact (hT.mono hC.1).rel_refl k hq.1

/-- A relation ending at an old point factors through the least old upper
bound of its source. Both factors retain the same relation level. -/
theorem Continuous.factor_rel_to_old {P T : Str α} (hC : Continuous P T)
    (hT : T.IsPattern) {k : Lvl} {x a p : α}
    (hx : x ∈ T.U) (ha : a ∈ P.U) (hp : LeastGE P.U x p)
    (hr : T.rel k x a) : T.rel k x p ∧ P.rel k p a := by
  have haT : a ∈ T.U := hC.1.1 ha
  have hpT : p ∈ T.U := hC.1.1 hp.1
  have hpaR : P.rel k p a :=
    hC.rel_up_of_rel hT k hx haT hp ⟨ha, le_rfl, fun _ _ h => h⟩ hr
  have hpaT : T.rel k p a := (hC.1.rel_iff hp.1 ha k).mp hpaR
  exact ⟨hT.rel_between k hx hpT haT hp.2.1 (hT.relDown_of_rel k hpT haT hpaT) hr,
    hpaR⟩

/-- A relation crossing its source's least old upper bound reaches that
bound and induces the same relation between the two old upper bounds. -/
theorem Continuous.factor_rel_cross {P T : Str α} (hC : Continuous P T)
    (hT : T.IsPattern) {k : Lvl} {x y p q : α}
    (hx : x ∈ T.U) (hy : y ∈ T.U)
    (hp : LeastGE P.U x p) (hq : LeastGE P.U y q)
    (hpy : p < y) (hr : T.rel k x y) : T.rel k x p ∧ P.rel k p q := by
  have hpT : p ∈ T.U := hC.1.1 hp.1
  have hqT : q ∈ T.U := hC.1.1 hq.1
  have hpq : P.rel k p q := hC.rel_up hx hy hp hq hpy hr
  have hpqT : T.rel k p q := (hC.1.rel_iff hp.1 hq.1 k).mp hpq
  have hpyDown : T.relDown k p y := by
    cases k
    · exact hpy.le
    · exact hT.convex₁ p hpT y hy q hqT hpy.le hq.2.1
        (hT.sub₂ p hpT q hqT hpqT)
  exact ⟨hT.rel_between k hx hpT hy hp.2.1 hpyDown hr, hpq⟩

/-- A relation from an old point extends to the least old upper bound of
its destination. This includes the reflexive case. -/
theorem Continuous.rel_from_old_up {P T : Str α} (hC : Continuous P T)
    (hT : T.IsPattern) {k : Lvl} {a y q : α}
    (ha : a ∈ P.U) (hy : y ∈ T.U) (hq : LeastGE P.U y q)
    (hr : T.rel k a y) : P.rel k a q :=
  hC.rel_up_of_rel hT k (hC.1.1 ha) hy ⟨ha, le_rfl, fun _ _ h => h⟩ hq hr

/-- Continuity passes to a structure whose carrier and relations map into
a continuous extension by the identity, provided it still extends the base. -/
theorem Continuous.of_covering_id {P R T : Str α} (hC : Continuous P T)
    (hPR : IsSub P R) (hRT : CoversInto R T id) : Continuous P R := by
  refine ⟨hPR, fun x hx => hC.2.1 x (hRT.1 x hx), ?_, ?_⟩
  · intro p x y hx hy hp hpy hr
    exact hC.2.2.1 p x y (hRT.1 x hx) (hRT.1 y hy) hp hpy
      (hRT.2.2.1 x hx y hy hr)
  · intro p x y hx hy hp hpy hr
    exact hC.2.2.2 p x y (hRT.1 x hx) (hRT.1 y hy) hp hpy
      (hRT.2.2.2 x hx y hy hr)

end Str

end Alexander313.Carlson
