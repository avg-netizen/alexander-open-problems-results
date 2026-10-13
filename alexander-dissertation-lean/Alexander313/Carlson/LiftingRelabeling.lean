import Alexander313.Carlson.FiniteRelabeling
import Alexander313.Carlson.PatternLifting

/-!
# Finite relabeling of liftings

A single increasing relabeling of a finite frame transports arithmetic
liftings, pattern liftings, continuous embeddings, and fixed-carrier
minimality. The original and relabeled maps need agree only on their finite
source carriers. The minimality proof pulls the relations of an arbitrary
competitor back to the original target carrier; arithmetic uniqueness
identifies its map there with the relabeled lifting map.
-/

noncomputable section

namespace Alexander313.Carlson

variable {α β : Type*} [LinearOrder α] [LinearOrder β]

namespace FiniteRelabeling

variable {S : Finset α} (F : FiniteRelabeling S β)

/-- Arithmetic lifting depends only on the ordered finite frame containing
the extended source and target. -/
theorem arithmeticLifting {A Aplus B Bplus : Finset α} {h f : α → α}
    (hAplus : Aplus ⊆ S) (hBplus : Bplus ⊆ S)
    (D : ArithmeticLifting A Aplus B Bplus h f) :
    ArithmeticLifting (A.image F.toFun) (Aplus.image F.toFun)
      (B.image F.toFun) (Bplus.image F.toFun) (F.conjugate h) (F.conjugate f) := by
  have hA : A ⊆ S := fun _ hx => hAplus (D.source_sub hx)
  have hB : B ⊆ S := fun _ hx => hBplus (D.target_sub hx)
  have hImage : (Aplus.image F.toFun).image (F.conjugate f) =
      (Aplus.image f).image F.toFun := by
    simp only [Finset.image_image]
    exact Finset.image_congr (fun x hx => F.conjugate_apply f (hAplus hx))
  refine
    { source_sub := Finset.image_subset_image D.source_sub
      source_bounded := ?_
      base_mono := ?_
      base_mem := ?_
      target_sub := Finset.image_subset_image D.target_sub
      mono := ?_
      mem := ?_
      agrees := ?_
      carrier_eq := ?_
      justBelow := ?_ }
  · intro u hu
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨a, ha, hxa⟩ := D.source_bounded x hx
    exact ⟨F.toFun a, Finset.mem_image_of_mem _ ha,
      (F.le_iff (hAplus hx) (hA ha)).mpr hxa⟩
  · intro u hu v hv huv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
    rw [F.conjugate_apply h (hA hx), F.conjugate_apply h (hA hy)]
    exact (F.lt_iff (hB (D.base_mem x hx)) (hB (D.base_mem y hy))).mpr
      (D.base_mono x hx y hy ((F.lt_iff (hA hx) (hA hy)).mp huv))
  · intro u hu
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    rw [F.conjugate_apply h (hA hx)]
    exact Finset.mem_image_of_mem _ (D.base_mem x hx)
  · intro u hu v hv huv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
    rw [F.conjugate_apply f (hAplus hx), F.conjugate_apply f (hAplus hy)]
    exact (F.lt_iff (hBplus (D.mem x hx)) (hBplus (D.mem y hy))).mpr
      (D.mono x hx y hy ((F.lt_iff (hAplus hx) (hAplus hy)).mp huv))
  · intro u hu
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    rw [F.conjugate_apply f (hAplus hx)]
    exact Finset.mem_image_of_mem _ (D.mem x hx)
  · intro u hu
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    rw [F.conjugate_apply f (hA hx), F.conjugate_apply h (hA hx), D.agrees x hx]
  · rw [hImage, ← Finset.image_union, ← D.carrier_eq]
  · intro a u hu hJ
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hJ.1
    rw [F.conjugate_apply h (hA hp), F.conjugate_apply f (hAplus hx)]
    exact (F.justBelow_iff hB (hB (D.base_mem p hp)) (hBplus (D.mem x hx))).mpr
      (D.justBelow p x hx ((F.justBelow_iff hA (hA hp) (hAplus hx)).mp hJ))

/-- Relabel all four structures and both maps of a pattern lifting in one
common ordered frame. -/
theorem patternLifting {P Pplus Q Qplus : Str α} {h f : α → α}
    (hPplus : Pplus.U ⊆ S) (hQplus : Qplus.U ⊆ S)
    (D : PatternLifting P Pplus Q Qplus h f) :
    PatternLifting (P.map F.toFun) (Pplus.map F.toFun)
      (Q.map F.toFun) (Qplus.map F.toFun) (F.conjugate h) (F.conjugate f) := by
  have hP : P.U ⊆ S := fun _ hx => hPplus (D.source_sub.1 hx)
  have hQ : Q.U ⊆ S := fun _ hx => hQplus (D.target_sub.1 hx)
  refine
    { source_pattern := (F.isIso hPplus).isPattern D.source_pattern
      target_pattern := (F.isIso hQplus).isPattern D.target_pattern
      source_sub := F.isSub hP hPplus D.source_sub
      target_sub := F.isSub hQ hQplus D.target_sub
      arithmetic := F.arithmeticLifting hPplus hQplus D.arithmetic
      relations := ?_ }
  intro u hu v hv
  obtain ⟨x, hx, rfl⟩ := (F.isIso hPplus).preimage hu
  obtain ⟨y, hy, rfl⟩ := (F.isIso hPplus).preimage hv
  rw [F.conjugate_apply f (hPplus hx), F.conjugate_apply f (hPplus hy)]
  have eP := (F.isIso hPplus).2.2 x hx y hy
  have eQ := (F.isIso hQplus).2.2 (f x) (D.arithmetic.mem x hx)
    (f y) (D.arithmetic.mem y hy)
  exact ⟨eP.1.symm.trans ((D.relations x hx y hy).1.trans eQ.1),
    eP.2.symm.trans ((D.relations x hx y hy).2.trans eQ.2)⟩

/-- Exact embeddings and continuity of their finite images are preserved
by the same change of labels on source and target. -/
theorem continuousEmbedding {P Q : Str α} {h : α → α}
    (hP : P.U ⊆ S) (hQ : Q.U ⊆ S) (E : Str.ContinuousEmbedding P Q h) :
    Str.ContinuousEmbedding (P.map F.toFun) (Q.map F.toFun) (F.conjugate h) := by
  let R := Q.restrict (P.U.image h)
  let R' := (Q.map F.toFun).restrict ((P.map F.toFun).U.image (F.conjugate h))
  have hR : R.U ⊆ S := fun _ hx => hQ (E.2.1.1 hx)
  have eR : Str.IsIso R R' F.toFun := by
    refine ⟨?_, fun x hx y hy => F.mono x (hR hx) y (hR hy), ?_⟩
    · change (P.U.image h).image F.toFun =
        (P.U.image F.toFun).image (F.conjugate h)
      simp only [Finset.image_image]
      exact Finset.image_congr (fun x hx => (F.conjugate_apply h (hP hx)).symm)
    · intro x hx y hy
      exact (F.isIso hQ).2.2 x (E.2.1.1 hx) y (E.2.1.1 hy)
  refine ⟨?_, E.2.of_isIso eR (F.isIso hQ) (fun _ _ => rfl)⟩
  refine ⟨rfl, ?_, ?_⟩
  · intro u hu v hv huv
    obtain ⟨x, hx, rfl⟩ := (F.isIso hP).preimage hu
    obtain ⟨y, hy, rfl⟩ := (F.isIso hP).preimage hv
    rw [F.conjugate_apply h (hP hx), F.conjugate_apply h (hP hy)]
    exact eR.2.1 (h x) (E.1.mem hx) (h y) (E.1.mem hy)
      (E.1.2.1 x hx y hy ((F.lt_iff (hP hx) (hP hy)).mp huv))
  · intro u hu v hv
    obtain ⟨x, hx, rfl⟩ := (F.isIso hP).preimage hu
    obtain ⟨y, hy, rfl⟩ := (F.isIso hP).preimage hv
    rw [F.conjugate_apply h (hP hx), F.conjugate_apply h (hP hy)]
    have eP := (F.isIso hP).2.2 x hx y hy
    have eH := E.1.2.2 x hx y hy
    have eHR := eR.2.2 (h x) (E.1.mem hx) (h y) (E.1.mem hy)
    exact ⟨eP.1.symm.trans (eH.1.trans eHR.1),
      eP.2.symm.trans (eH.2.trans eHR.2)⟩

/-- Fixed-carrier minimality survives a finite relabeling. Competitors may
have arbitrary relations and arbitrary total maps away from their carriers. -/
theorem isMinimal {P Pplus Q Qplus : Str α} {h f : α → α}
    (hPplus : Pplus.U ⊆ S) (hQplus : Qplus.U ⊆ S)
    (D : PatternLifting P Pplus Q Qplus h f)
    (hmin : PatternLifting.IsMinimal P Pplus Q Qplus h) :
    PatternLifting.IsMinimal (P.map F.toFun) (Pplus.map F.toFun)
      (Q.map F.toFun) (Qplus.map F.toFun) (F.conjugate h) := by
  have hQ : Q.U ⊆ S := fun _ hx => hQplus (D.target_sub.1 hx)
  have DF := F.patternLifting hPplus hQplus D
  intro T g hT E
  have EA : ArithmeticLifting (P.map F.toFun).U (Pplus.map F.toFun).U
      (Q.map F.toFun).U (Qplus.map F.toFun).U (F.conjugate h) g := by
    simpa only [hT] using E.arithmetic
  have hg : ∀ x ∈ Pplus.U, g (F.toFun x) = F.toFun (f x) := by
    intro x hx
    exact (DF.arithmetic.unique EA ((F.isIso hPplus).mem hx)).symm.trans
      (F.conjugate_apply f (hPplus hx))
  let R : Str α :=
    { U := Qplus.U
      r₁ := fun x y => T.r₁ (F.toFun x) (F.toFun y)
      r₂ := fun x y => T.r₂ (F.toFun x) (F.toFun y) }
  have eR : Str.IsIso T R F.invFun := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hT]
      change (Qplus.U.image F.toFun).image F.invFun = Qplus.U
      rw [Finset.image_image]
      calc
        Qplus.U.image (fun x => F.invFun (F.toFun x)) = Qplus.U.image id :=
          Finset.image_congr (fun x hx => F.left_inv x (hQplus hx))
        _ = Qplus.U := Finset.image_id
    · intro u hu v hv huv
      rw [hT] at hu hv
      obtain ⟨x, hx, rfl⟩ := (F.isIso hQplus).preimage hu
      obtain ⟨y, hy, rfl⟩ := (F.isIso hQplus).preimage hv
      rw [F.left_inv x (hQplus hx), F.left_inv y (hQplus hy)]
      exact (F.lt_iff (hQplus hx) (hQplus hy)).mp huv
    · intro u hu v hv
      rw [hT] at hu hv
      obtain ⟨x, hx, rfl⟩ := (F.isIso hQplus).preimage hu
      obtain ⟨y, hy, rfl⟩ := (F.isIso hQplus).preimage hv
      rw [F.left_inv x (hQplus hx), F.left_inv y (hQplus hy)]
      exact ⟨Iff.rfl, Iff.rfl⟩
  have ER : PatternLifting P Pplus Q R h f :=
    { source_pattern := D.source_pattern
      target_pattern := eR.isPattern E.target_pattern
      source_sub := D.source_sub
      target_sub := by
        refine ⟨D.target_sub.1, ?_⟩
        intro x hx y hy
        have eQ := (F.isIso hQ).2.2 x hx y hy
        have eT := E.target_sub.2 (F.toFun x) ((F.isIso hQ).mem hx)
          (F.toFun y) ((F.isIso hQ).mem hy)
        exact ⟨eQ.1.trans eT.1, eQ.2.trans eT.2⟩
      arithmetic := D.arithmetic
      relations := by
        intro x hx y hy
        have eP := (F.isIso hPplus).2.2 x hx y hy
        have eT := E.relations (F.toFun x) ((F.isIso hPplus).mem hx)
          (F.toFun y) ((F.isIso hPplus).mem hy)
        rw [hg x hx, hg y hy] at eT
        exact ⟨eP.1.trans eT.1, eP.2.trans eT.2⟩ }
  have hR := hmin R f rfl ER
  refine ⟨fun _ hx => hT.symm ▸ hx, fun _ _ _ _ hxy => hxy, ?_, ?_⟩
  · intro u hu v hv huv
    obtain ⟨x, hx, rfl⟩ := (F.isIso hQplus).preimage hu
    obtain ⟨y, hy, rfl⟩ := (F.isIso hQplus).preimage hv
    exact hR.2.2.1 x hx y hy (((F.isIso hQplus).2.2 x hx y hy).1.mpr huv)
  · intro u hu v hv huv
    obtain ⟨x, hx, rfl⟩ := (F.isIso hQplus).preimage hu
    obtain ⟨y, hy, rfl⟩ := (F.isIso hQplus).preimage hv
    exact hR.2.2.2 x hx y hy (((F.isIso hQplus).2.2 x hx y hy).2.mpr huv)

end FiniteRelabeling
end Alexander313.Carlson
