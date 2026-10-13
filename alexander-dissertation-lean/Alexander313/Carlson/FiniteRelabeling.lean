import Alexander313.Carlson.PatternTransport

/-!
# Relabeling a finite ordered frame

A relabeling is increasing and invertible on a specified finite frame. Its
total maps may behave arbitrarily elsewhere. Keeping the frame explicit lets
one change the ambient type while retaining every intermediate carrier in a
finite derivation.
-/

noncomputable section

namespace Alexander313.Carlson

variable {α β : Type*} [LinearOrder α] [LinearOrder β]

/-- A change of labels with an inverse on a finite source frame. -/
structure FiniteRelabeling (S : Finset α) (β : Type*) [LinearOrder β] where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ x ∈ S, invFun (toFun x) = x
  mono : ∀ x ∈ S, ∀ y ∈ S, x < y → toFun x < toFun y

namespace FiniteRelabeling

variable {S : Finset α} (F : FiniteRelabeling S β)

/-- A globally increasing map restricts to a relabeling of any finite frame. -/
def ofStrictMono (S : Finset α) [Nonempty α] (f : α → β) (hf : StrictMono f) :
    FiniteRelabeling S β where
  toFun := f
  invFun := Function.invFun f
  left_inv := fun x _ => Function.leftInverse_invFun hf.injective x
  mono := fun _ _ _ _ h => hf h

theorem eq_iff {x y : α} (hx : x ∈ S) (hy : y ∈ S) :
    F.toFun x = F.toFun y ↔ x = y := by
  constructor
  · intro h
    simpa only [F.left_inv x hx, F.left_inv y hy] using congrArg F.invFun h
  · exact congrArg F.toFun

theorem lt_iff {x y : α} (hx : x ∈ S) (hy : y ∈ S) :
    F.toFun x < F.toFun y ↔ x < y := by
  constructor
  · intro h
    rcases lt_trichotomy x y with hxy | hxy | hxy
    · exact hxy
    · subst y
      exact (lt_irrefl _ h).elim
    · exact (lt_asymm h (F.mono y hy x hx hxy)).elim
  · exact F.mono x hx y hy

theorem le_iff {x y : α} (hx : x ∈ S) (hy : y ∈ S) :
    F.toFun x ≤ F.toFun y ↔ x ≤ y := by
  rw [← not_lt, ← not_lt, F.lt_iff hy hx]

theorem mem_image_iff {A : Finset α} (hA : A ⊆ S) {x : α} (hx : x ∈ S) :
    F.toFun x ∈ A.image F.toFun ↔ x ∈ A := by
  constructor
  · intro h
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp h
    exact (F.eq_iff (hA hy) hx).mp he ▸ hy
  · exact Finset.mem_image_of_mem F.toFun

theorem right_inv {y : β} (hy : y ∈ S.image F.toFun) :
    F.toFun (F.invFun y) = y := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  rw [F.left_inv x hx]

/-- Restrict a change of labels without changing either total map. -/
def restrict {A : Finset α} (hA : A ⊆ S) : FiniteRelabeling A β where
  toFun := F.toFun
  invFun := F.invFun
  left_inv := fun x hx => F.left_inv x (hA hx)
  mono := fun x hx y hy => F.mono x (hA hx) y (hA hy)

/-- The inverse change of labels, on the finite image frame. -/
def symm : FiniteRelabeling (S.image F.toFun) α where
  toFun := F.invFun
  invFun := F.toFun
  left_inv := fun _ hy => F.right_inv hy
  mono := by
    intro x hx y hy hxy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    rw [F.left_inv u hu, F.left_inv v hv]
    exact (F.lt_iff hu hv).mp hxy

/-- Transport a total auxiliary map; only its values on the frame are used. -/
def conjugate (g : α → α) : β → β := fun y => F.toFun (g (F.invFun y))

@[simp] theorem conjugate_apply (g : α → α) {x : α} (hx : x ∈ S) :
    F.conjugate g (F.toFun x) = F.toFun (g x) := by
  simp only [conjugate, F.left_inv x hx]

theorem isIso {P : Str α} (hP : P.U ⊆ S) :
    Str.IsIso P (P.map F.toFun) F.toFun :=
  P.map_isIso F.toFun (fun x hx y hy => F.mono x (hP hx) y (hP hy))

/-- The inverse recovers the original structure on its carrier, including
when its ambient relations have arbitrary values away from that carrier. -/
theorem inverse_isIso {P : Str α} (hP : P.U ⊆ S) :
    Str.IsIso (P.map F.toFun) P F.invFun := by
  refine ⟨?_, ?_, ?_⟩
  · change (P.U.image F.toFun).image F.invFun = P.U
    rw [Finset.image_image]
    calc
      P.U.image (F.invFun ∘ F.toFun) = P.U.image id :=
        Finset.image_congr (fun x hx => F.left_inv x (hP hx))
      _ = P.U := Finset.image_id
  · intro u hu v hv huv
    obtain ⟨x, hx, rfl⟩ := (F.isIso hP).preimage hu
    obtain ⟨y, hy, rfl⟩ := (F.isIso hP).preimage hv
    rw [F.left_inv x (hP hx), F.left_inv y (hP hy)]
    exact (F.lt_iff (hP hx) (hP hy)).mp huv
  · intro u hu v hv
    obtain ⟨x, hx, rfl⟩ := (F.isIso hP).preimage hu
    obtain ⟨y, hy, rfl⟩ := (F.isIso hP).preimage hv
    rw [F.left_inv x (hP hx), F.left_inv y (hP hy)]
    have e := (F.isIso hP).2.2 x hx y hy
    exact ⟨e.1.symm, e.2.symm⟩

theorem isSub {P Q : Str α} (hP : P.U ⊆ S) (hQ : Q.U ⊆ S)
    (h : Str.IsSub P Q) : Str.IsSub (P.map F.toFun) (Q.map F.toFun) := by
  refine ⟨Finset.image_subset_image h.1, ?_⟩
  intro u hu v hv
  obtain ⟨x, hx, rfl⟩ := (F.isIso hP).preimage hu
  obtain ⟨y, hy, rfl⟩ := (F.isIso hP).preimage hv
  have eP := (F.isIso hP).2.2 x hx y hy
  have eQ := (F.isIso hQ).2.2 x (h.1 hx) y (h.1 hy)
  exact ⟨eP.1.symm.trans ((h.2 x hx y hy).1.trans eQ.1),
    eP.2.symm.trans ((h.2 x hx y hy).2.trans eQ.2)⟩

theorem continuous {P Q : Str α} (hP : P.U ⊆ S) (hQ : Q.U ⊆ S)
    (h : Str.Continuous P Q) : Str.Continuous (P.map F.toFun) (Q.map F.toFun) :=
  h.of_isIso (F.isIso hP) (F.isIso hQ) (fun _ _ => rfl)

theorem justBelow_iff {A : Finset α} (hA : A ⊆ S) {a x : α}
    (ha : a ∈ S) (hx : x ∈ S) :
    Str.JustBelow (A.image F.toFun) (F.toFun a) (F.toFun x) ↔
      Str.JustBelow A a x := by
  constructor
  · rintro ⟨hmem, hlt, hgap⟩
    refine ⟨(F.mem_image_iff hA ha).mp hmem, (F.lt_iff hx ha).mp hlt, ?_⟩
    intro q hq hqa
    exact (F.lt_iff (hA hq) hx).mp
      (hgap (F.toFun q) (Finset.mem_image_of_mem _ hq) ((F.lt_iff (hA hq) ha).mpr hqa))
  · rintro ⟨hmem, hlt, hgap⟩
    refine ⟨Finset.mem_image_of_mem _ hmem, (F.lt_iff hx ha).mpr hlt, ?_⟩
    intro q hq hqa
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    exact (F.lt_iff (hA hp) hx).mpr (hgap p hp ((F.lt_iff (hA hp) ha).mp hqa))

theorem extensionAt {P Q : Str α} {a : α} (hP : P.U ⊆ S) (hQ : Q.U ⊆ S)
    (h : Str.ExtensionAt P Q a) :
    Str.ExtensionAt (P.map F.toFun) (Q.map F.toFun) (F.toFun a) := by
  refine ⟨F.isSub hP hQ h.1, Finset.mem_image_of_mem _ h.2.1, ?_, ?_⟩
  · obtain ⟨x, hxQ, hxP⟩ := h.2.2.1
    exact ⟨F.toFun x, Finset.mem_image_of_mem _ hxQ,
      fun hx => hxP ((F.mem_image_iff hP (hQ hxQ)).mp hx)⟩
  · intro u hu huP
    obtain ⟨x, hx, rfl⟩ := (F.isIso hQ).preimage hu
    have hxP : x ∉ P.U := fun hp => huP (Finset.mem_image_of_mem _ hp)
    exact (F.justBelow_iff hP (hP h.2.1) (hQ hx)).mpr (h.2.2.2 x hx hxP)

theorem image_sdiff {A B : Finset α} (hA : A ⊆ S) (hB : B ⊆ S) :
    (A \ B).image F.toFun = A.image F.toFun \ B.image F.toFun := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hxA, hxB⟩ := Finset.mem_sdiff.mp hx
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_image_of_mem _ hxA,
      fun h => hxB ((F.mem_image_iff hB (hA hxA)).mp h)⟩
  · intro hy
    obtain ⟨hyA, hyB⟩ := Finset.mem_sdiff.mp hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hyA
    exact Finset.mem_image.mpr ⟨x,
      Finset.mem_sdiff.mpr ⟨hx, fun h => hyB (Finset.mem_image_of_mem _ h)⟩, rfl⟩

end FiniteRelabeling

namespace Str

theorem IsIso.refl (P : Str α) : IsIso P P id :=
  ⟨Finset.image_id, fun _ _ _ _ h => h, fun _ _ _ _ => ⟨Iff.rfl, Iff.rfl⟩⟩

theorem IsIso.universe_eq_of_id {P Q : Str α} (e : IsIso P Q id) : P.U = Q.U := by
  simpa only [Finset.image_id] using e.1

theorem IsIso.isSub_of_id {P Q : Str α} (e : IsIso P Q id) : IsSub P Q :=
  ⟨e.universe_eq_of_id.subset, e.2.2⟩

theorem IsIso.symm_id {P Q : Str α} (e : IsIso P Q id) : IsIso Q P id := by
  refine ⟨?_, fun _ _ _ _ h => h, ?_⟩
  · rw [Finset.image_id, e.universe_eq_of_id]
  · intro x hx y hy
    rw [← e.universe_eq_of_id] at hx hy
    have h := e.2.2 x hx y hy
    exact ⟨h.1.symm, h.2.symm⟩

/-- Two copies under the same finite map agree on their common carrier. -/
theorem IsIso.id_of_same_map {P : Str α} {Q R : Str β} {f : α → β}
    (e : IsIso P Q f) (e' : IsIso P R f) : IsIso Q R id := by
  refine ⟨?_, fun _ _ _ _ h => h, ?_⟩
  · rw [Finset.image_id, ← e.1, e'.1]
  · intro u hu v hv
    obtain ⟨x, hx, rfl⟩ := e.preimage hu
    obtain ⟨y, hy, rfl⟩ := e.preimage hv
    have h := e.2.2 x hx y hy
    have h' := e'.2.2 x hx y hy
    exact ⟨h.1.symm.trans h'.1, h.2.symm.trans h'.2⟩

end Str
end Alexander313.Carlson
