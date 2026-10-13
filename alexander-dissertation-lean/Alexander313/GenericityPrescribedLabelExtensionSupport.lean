import Alexander313.RecordedGuardRoom

/-!
# Finite whole-guard reflection with prescribed labels fixed

One finite guard plan is reflected as a whole. Its marker set is constructed
from the actual bounded chain witnesses. The reflection set includes every
chain point, every request base, both endpoints of every R1 edge, and all
additional prescribed support. The original requests remain unchanged.

These are generic finite lemmas with an explicit FiniteLabelReflection
premise. They do not prove the actual ordinal R1/R2 reflection theorem,
separated-copy room, prescribed source-certificate extension or stage truth.
The cutoff may be a literal sourceBaseCut before an own prefix. A map for one
finite guard plan does not provide a fixed plan for an unbounded query column.
All candidates remain uncompiled.
-/

namespace Alexander313

namespace GuardRequirements

def support {Label : Type} [DecidableEq Label] (p : GuardRequirements Label) : Finset Label :=
  (p.1.map Prod.snd).toFinset ∪ (p.2.flatMap (fun q => [q.1, q.2])).toFinset

def relabel {Label : Type} (f : Label → Label) (p : GuardRequirements Label) :
    GuardRequirements Label :=
  (p.1.map (fun q => (q.1, f q.2)), p.2.map (fun q => (f q.1, f q.2)))

theorem base_mem_support {Label : Type} [DecidableEq Label]
    (p : GuardRequirements Label) (q : Nat × Label) (hq : q ∈ p.1) : q.2 ∈ support p :=
  Finset.mem_union.mpr (Or.inl
    (List.mem_toFinset.mpr (List.mem_map.mpr ⟨q, hq, rfl⟩)))

theorem edge_left_mem_support {Label : Type} [DecidableEq Label]
    (p : GuardRequirements Label) (q : Label × Label) (hq : q ∈ p.2) : q.1 ∈ support p :=
  Finset.mem_union.mpr (Or.inr
    (List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨q, hq, by simp⟩)))

theorem edge_right_mem_support {Label : Type} [DecidableEq Label]
    (p : GuardRequirements Label) (q : Label × Label) (hq : q ∈ p.2) : q.2 ∈ support p :=
  Finset.mem_union.mpr (Or.inr
    (List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨q, hq, by simp⟩)))

private theorem reflect_points {Label : Type} [LinearOrder Label]
    (R₁ R₂ : Label → Label → Prop) {α β : Label} (hαβ : α ≤ β)
    (reflection : FiniteLabelReflection R₁ R₂ α β) (B S K : Finset Label)
    (room : ∀ μ ∈ B, μ < β) (parameters : ∀ μ ∈ S, μ < α)
    (prescribed : ∀ μ ∈ K, μ < α) :
    ∃ f : Label → Label, PreservesLabelPattern R₁ R₂ (B ∪ S ∪ K) f ∧
      (∀ μ ∈ S ∪ K, f μ = μ) ∧ ∀ μ ∈ B ∪ S ∪ K, f μ < α := by
  have all_below : ∀ μ ∈ B ∪ S ∪ K, μ < β := by
    intro μ hμ
    rcases Finset.mem_union.mp hμ with hμ | hμ
    · rcases Finset.mem_union.mp hμ with hμ | hμ
      · exact room μ hμ
      · exact (parameters μ hμ).trans_le hαβ
    · exact (prescribed μ hμ).trans_le hαβ
  obtain ⟨f, below, fixed, pattern⟩ := reflection (B ∪ S ∪ K) all_below
  refine ⟨f, pattern, ?_, below⟩
  intro μ hμ
  rcases Finset.mem_union.mp hμ with hμ | hμ
  · exact fixed μ (Finset.mem_union.mpr (Or.inl
      (Finset.mem_union.mpr (Or.inr hμ)))) (parameters μ hμ)
  · exact fixed μ (Finset.mem_union.mpr (Or.inr hμ)) (prescribed μ hμ)

/-- Fresh source-plan labels may move. ONE finite pattern map transports all
request bases, complete R2 tails and both endpoints of every R1 edge, while
the already prescribed target support remains fixed. -/
theorem reflected_relabelled_points_exists {Label : Type} [LinearOrder Label]
    (R₁ R₂ : Label → Label → Prop) {α β : Label} (hαβ : α ≤ β)
    (reflection : FiniteLabelReflection R₁ R₂ α β)
    (p : GuardRequirements Label) (L K : Finset Label)
    (bounded : Bounded R₁ R₂ β p)
    (parameters : ∀ μ ∈ support p, μ < β)
    (extra : ∀ μ ∈ L, μ < β)
    (prescribed : ∀ μ ∈ K, μ < α) :
    ∃ B : Finset Label, ∃ f : Label → Label,
      Holds R₁ R₂ B p ∧ (∀ μ ∈ B, μ < β) ∧
      PreservesLabelPattern R₁ R₂ (B ∪ support p ∪ L ∪ K) f ∧
      (∀ μ ∈ K, f μ = μ) ∧
      Holds R₁ R₂ (B.image f) (relabel f p) ∧
      (∀ μ ∈ B ∪ support p ∪ L ∪ K, f μ < α) := by
  obtain ⟨B, holds, room⟩ := (bounded_iff_holds_room R₁ R₂ β p).mp bounded
  let F := B ∪ support p ∪ L ∪ K
  have points : B ⊆ F := fun μ hμ =>
    Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
      (Finset.mem_union.mpr (Or.inl hμ)))))
  have labels : support p ⊆ F := fun μ hμ =>
    Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
      (Finset.mem_union.mpr (Or.inr hμ)))))
  have all_below : ∀ μ ∈ F, μ < β := by
    intro μ hμ
    rcases Finset.mem_union.mp hμ with hμ | hμ
    · rcases Finset.mem_union.mp hμ with hμ | hμ
      · rcases Finset.mem_union.mp hμ with hμ | hμ
        · exact room μ hμ
        · exact parameters μ hμ
      · exact extra μ hμ
    · exact (prescribed μ hμ).trans_le hαβ
  obtain ⟨f, below, fixed, pattern⟩ := reflection F all_below
  refine ⟨B, f, holds, room, pattern, ?_, ?_, below⟩
  · intro μ hμ
    exact fixed μ (Finset.mem_union.mpr (Or.inr hμ)) (prescribed μ hμ)
  · constructor
    · intro q hq
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
      exact GuardChainIn.relabel (holds.1 r hr) f pattern.covers points
    · intro q hq
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
      have hl := labels (edge_left_mem_support p r hr)
      have hr' := labels (edge_right_mem_support p r hr)
      exact ⟨(pattern.2.1 _ hl _ hr').mpr (holds.2 r hr).1,
        (pattern.2.2.1 _ hl _ hr').mpr (holds.2 r hr).2⟩

theorem bounded_relabel_reflect {Label : Type} [LinearOrder Label]
    (R₁ R₂ : Label → Label → Prop) {α β : Label} (hαβ : α ≤ β)
    (reflection : FiniteLabelReflection R₁ R₂ α β)
    (p : GuardRequirements Label) (K : Finset Label)
    (bounded : Bounded R₁ R₂ β p)
    (parameters : ∀ μ ∈ support p, μ < β)
    (prescribed : ∀ μ ∈ K, μ < α) :
    ∃ f : Label → Label, (∀ μ ∈ K, f μ = μ) ∧ Bounded R₁ R₂ α (relabel f p) := by
  obtain ⟨B, f, _, _, _, fixed, holds, below⟩ :=
    reflected_relabelled_points_exists R₁ R₂ hαβ reflection p ∅ K bounded parameters
      (by simp) prescribed
  refine ⟨f, fixed, (bounded_iff_holds_room R₁ R₂ α (relabel f p)).mpr
    ⟨B.image f, holds, ?_⟩⟩
  intro μ hμ
  obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.mp hμ
  exact below ν (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
    (Finset.mem_union.mpr (Or.inl hν))))))

/-- Preserve the ACTUAL cut attached to a base row before its own prefixes.
The cut label is included in the same finite pattern as every chain point,
so each transported point is below its transported cut, not just a final
outer cutoff. This lemma has no target-bound or target-chain premise. -/
theorem cut_relabel {Label : Type} [LinearOrder Label]
    (R₁ R₂ : Label → Label → Prop) (p : GuardRequirements Label)
    (B F : Finset Label) (δ : Label) (f : Label → Label)
    (holds : Holds R₁ R₂ B p) (room : ∀ μ ∈ B, μ < δ)
    (pattern : PreservesLabelPattern R₁ R₂ F f)
    (points : B ⊆ F) (parameters : support p ⊆ F) (cut : δ ∈ F) :
    Bounded R₁ R₂ (f δ) (relabel f p) := by
  apply (bounded_iff_holds_room R₁ R₂ (f δ) (relabel f p)).mpr
  refine ⟨B.image f, ?_, ?_⟩
  · constructor
    · intro q hq
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
      exact GuardChainIn.relabel (holds.1 r hr) f pattern.covers points
    · intro q hq
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
      have hl := parameters (edge_left_mem_support p r hr)
      have hr' := parameters (edge_right_mem_support p r hr)
      exact ⟨(pattern.2.1 _ hl _ hr').mpr (holds.2 r hr).1,
        (pattern.2.2.1 _ hl _ hr').mpr (holds.2 r hr).2⟩
  · intro μ hμ
    obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.mp hμ
    exact (pattern.2.1 ν (points hν) δ cut).mpr (room ν hν)

/-- A SINGLE shared reflected marker set serves every indexed occurrence and
every repeated request. All original R1 endpoints and prescribed labels stay
fixed; fresh marker points and every whole-chain relation are transported. -/
theorem reflected_points_exists {Label : Type} [LinearOrder Label]
    (R₁ R₂ : Label → Label → Prop) {α β : Label} (hαβ : α ≤ β)
    (reflection : FiniteLabelReflection R₁ R₂ α β)
    (p : GuardRequirements Label) (K : Finset Label)
    (bounded : Bounded R₁ R₂ β p)
    (parameters : ∀ μ ∈ support p, μ < α)
    (prescribed : ∀ μ ∈ K, μ < α) :
    ∃ B : Finset Label, ∃ f : Label → Label,
      Holds R₁ R₂ B p ∧ (∀ μ ∈ B, μ < β) ∧
      PreservesLabelPattern R₁ R₂ (B ∪ support p ∪ K) f ∧
      (∀ μ ∈ support p ∪ K, f μ = μ) ∧
      Holds R₁ R₂ (B.image f) p ∧ ∀ μ ∈ B.image f, μ < α := by
  obtain ⟨B, holds, room⟩ := (bounded_iff_holds_room R₁ R₂ β p).mp bounded
  obtain ⟨f, pattern, fixed, below⟩ :=
    reflect_points R₁ R₂ hαβ reflection B (support p) K room parameters prescribed
  have points : B ⊆ B ∪ support p ∪ K := fun μ hμ =>
    Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hμ)))
  refine ⟨B, f, holds, room, pattern, fixed, ?_, ?_⟩
  · refine ⟨?_, holds.2⟩
    intro q hq
    have hfixed : f q.2 = q.2 := fixed q.2
      (Finset.mem_union.mpr (Or.inl (base_mem_support p q hq)))
    simpa only [hfixed] using GuardChainIn.relabel (holds.1 q hq) f pattern.covers points
  · intro μ hμ
    obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.mp hμ
    exact below ν (points hν)

theorem bounded_reflect {Label : Type} [LinearOrder Label]
    (R₁ R₂ : Label → Label → Prop) {α β : Label} (hαβ : α ≤ β)
    (reflection : FiniteLabelReflection R₁ R₂ α β)
    (p : GuardRequirements Label) (bounded : Bounded R₁ R₂ β p)
    (parameters : ∀ μ ∈ support p, μ < α) : Bounded R₁ R₂ α p := by
  obtain ⟨B, f, _, _, _, _, holds, room⟩ := reflected_points_exists R₁ R₂ hαβ
    reflection p ∅ bounded parameters (by simp)
  exact (bounded_iff_holds_room R₁ R₂ α p).mpr ⟨B.image f, holds, room⟩

/-- The base of the original indexed request stays fixed. Its tail is an
actual reflected list, rather than a supplied target-cut chain. -/
theorem boundedGuardChain_reflect {Label : Type} [LinearOrder Label]
    (R₁ R₂ : Label → Label → Prop) {α β : Label} (hαβ : α ≤ β)
    (reflection : FiniteLabelReflection R₁ R₂ α β) (k : Nat) (ν : Label)
    (chain : BoundedGuardChain R₂ β k ν) (base : ν < α) :
    BoundedGuardChain R₂ α k ν := by
  have bounded : Bounded R₁ R₂ β ([(k, ν)], []) := by
    constructor
    · intro q hq
      have he : q = (k, ν) := List.mem_singleton.mp hq
      simpa only [he] using chain
    · simp
  have parameters : ∀ μ ∈ support ([(k, ν)], []), μ < α := by
    intro μ hμ
    have he : μ = ν := by simpa only [support, List.map_cons, List.map_nil,
      List.flatMap_nil, List.toFinset_cons, List.toFinset_nil, Finset.union_empty,
      Finset.mem_insert, Finset.notMem_empty, or_false] using hμ
    simpa only [he] using base
  exact (bounded_reflect R₁ R₂ hαβ reflection ([(k, ν)], []) bounded parameters).1
    (k, ν) (List.mem_singleton_self _)

end GuardRequirements

namespace Formula

/-- Reflection of ALL literal main guards on the unchanged recorded atom.
The finite support includes the whole atom, including hidden live/ghost
arguments, and the caller may additionally prescribe any finite labels. -/
theorem mainGuarded_reflected_points_exists {Label : Type} [LinearOrder Label]
    (R₁ R₂ : Label → Label → Prop) {α β : Label} (hαβ : α ≤ β)
    (reflection : FiniteLabelReflection R₁ R₂ α β)
    (E : Finset Nat) (φ : Formula (RecordedHead Nat Label)) (K : Finset Label)
    (bounded : GuardRequirements.Bounded R₁ R₂ β (φ.mainGuardRequirements E))
    (support : ∀ μ ∈ φ.labelSupport, μ < α)
    (prescribed : ∀ μ ∈ K, μ < α) :
    ∃ B : Finset Label, ∃ f : Label → Label,
      φ.MainGuarded R₁ R₂ E B ∧ (∀ μ ∈ B, μ < β) ∧
      PreservesLabelPattern R₁ R₂ (B ∪ φ.labelSupport ∪ K) f ∧
      φ.relabel f = φ ∧ (∀ μ ∈ K, f μ = μ) ∧
      φ.MainGuarded R₁ R₂ E (B.image f) ∧ ∀ μ ∈ B.image f, μ < α := by
  obtain ⟨B, guarded, room⟩ :=
    (mainGuardRequirements_bounded_iff R₁ R₂ E β φ).mp bounded
  obtain ⟨f, pattern, fixed, below⟩ :=
    GuardRequirements.reflect_points R₁ R₂ hαβ reflection B φ.labelSupport K
      room support prescribed
  have points : B ⊆ B ∪ φ.labelSupport ∪ K := fun μ hμ =>
    Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hμ)))
  have labels : φ.labelSupport ⊆ B ∪ φ.labelSupport ∪ K := fun μ hμ =>
    Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hμ)))
  have hfixed : φ.relabel f = φ := φ.relabel_fixed f
    (fun μ hμ => fixed μ (Finset.mem_union.mpr (Or.inl hμ)))
  have hguard := mainGuarded_relabel R₁ R₂ E B (B ∪ φ.labelSupport ∪ K) φ f
    pattern.covers points labels guarded
  rw [hfixed] at hguard
  refine ⟨B, f, guarded, room, pattern, hfixed,
    fun μ hμ => fixed μ (Finset.mem_union.mpr (Or.inr hμ)), hguard, ?_⟩
  intro μ hμ
  obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.mp hμ
  exact below ν (points hν)

end Formula

end Alexander313
