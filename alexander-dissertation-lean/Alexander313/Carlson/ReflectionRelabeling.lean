import Alexander313.Carlson.FiniteRelabeling
import Alexander313.Carlson.Downward
import Alexander313.Carlson.Upward

/-!
# Reflection on a relabeled finite frame

The hypotheses and carrier relations of both reflection constructions depend
only on their finite input carriers. Conjugating the matching map therefore
transports the reflection data, and the resulting reflection is isomorphic to
the original one under the chosen change of labels. No agreement is required
between relations away from their carriers.
-/

noncomputable section

namespace Alexander313.Carlson
namespace FiniteRelabeling

variable {α β : Type*} [LinearOrder α] [LinearOrder β]
variable {S : Finset α} (F : FiniteRelabeling S β)

private theorem image_conjugate {N : Finset α} (hN : N ⊆ S) (g : α → α) :
    (N.image F.toFun).image (F.conjugate g) = (N.image g).image F.toFun := by
  rw [Finset.image_image, Finset.image_image]
  exact Finset.image_congr fun x hx => F.conjugate_apply g (hN hx)

/-- Downward reflection data transport along an increasing finite relabeling. -/
theorem downwardData {P : Str α} {k : Lvl} {a b : α}
    {X N : Finset α} {g : α → α} (hP : P.U ⊆ S) (hN : N ⊆ S)
    (D : Str.DownData P k a b X N g) :
    Str.DownData (P.map F.toFun) k (F.toFun a) (F.toFun b)
      (X.image F.toFun) (N.image F.toFun) (F.conjugate g) := by
  have e := F.isIso hP
  refine
    { pat := e.isPattern D.pat
      ha := e.mem D.ha
      hb := e.mem D.hb
      hab := F.mono a (hP D.ha) b (hP D.hb) D.hab
      hrel := (e.rel_iff D.ha D.hb k).mp D.hrel
      hX := ?_
      hXne := D.hXne.image F.toFun
      hNP := ?_
      hNa := ?_
      hNL := ?_
      himage := ?_
      hmono := ?_ }
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hyP, hay, hyb⟩ := D.hX y hy
    exact ⟨e.mem hyP, (F.le_iff (hP D.ha) (hP hyP)).mpr hay,
      F.mono y (hP hyP) b (hP D.hb) hyb⟩
  · intro x hx hxP
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact D.hNP y hy ((F.mem_image_iff hP (hN hy)).mp hxP)
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact F.mono y (hN hy) a (hP D.ha) (D.hNa y hy)
  · intro x hx q hq hqa
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨p, hp, rfl⟩ := e.preimage hq
    exact F.mono p (hP hp) y (hN hy)
      (D.hNL y hy p hp ((F.lt_iff (hP hp) (hP D.ha)).mp hqa))
  · rw [F.image_conjugate hN g, D.himage]
  · intro x hx y hy hxy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    rw [F.conjugate_apply g (hN hu), F.conjugate_apply g (hN hv)]
    exact F.mono (g u) (hP (D.g_props hu).1) (g v) (hP (D.g_props hv).1)
      (D.hmono u hu v hv ((F.lt_iff (hN hu) (hN hv)).mp hxy))

private theorem back_apply {N : Finset α} (hN : N ⊆ S) (g : α → α)
    {x : α} (hx : x ∈ S) :
    Str.back (N.image F.toFun) (F.conjugate g) (F.toFun x) =
      F.toFun (Str.back N g x) := by
  by_cases hxN : x ∈ N
  · rw [Str.back_of_mem (Finset.mem_image_of_mem F.toFun hxN),
      Str.back_of_mem hxN, F.conjugate_apply g hx]
  · rw [Str.back_of_not_mem (fun h => hxN ((F.mem_image_iff hN hx).mp h)),
      Str.back_of_not_mem hxN]

private theorem inLow {P : Str α} {N : Finset α} {a x : α}
    (hP : P.U ⊆ S) (ha : a ∈ S) (hx : Str.InLow N P a x) :
    Str.InLow (N.image F.toFun) (P.map F.toFun) (F.toFun a) (F.toFun x) := by
  rcases hx with hx | ⟨hx, hxa⟩
  · exact Or.inl (Finset.mem_image_of_mem F.toFun hx)
  · exact Or.inr ⟨Finset.mem_image_of_mem F.toFun hx,
      F.mono x (hP hx) a ha hxa⟩

/-- The two downward reflections agree on their finite carriers after relabeling. -/
theorem downward_isIso {P : Str α} {k : Lvl} {a b : α}
    {X N : Finset α} {g : α → α} (hP : P.U ⊆ S) (hN : N ⊆ S)
    (D : Str.DownData P k a b X N g) :
    Str.IsIso (P.downward k a b N g)
      ((P.map F.toFun).downward k (F.toFun a) (F.toFun b)
        (N.image F.toFun) (F.conjugate g)) F.toFun := by
  have D' := F.downwardData hP hN D
  have e := F.isIso hP
  have hU : (P.downward k a b N g).U ⊆ S := Finset.union_subset hP hN
  refine ⟨?_, fun x hx y hy => F.mono x (hU hx) y (hU hy), ?_⟩
  · exact Finset.image_union P.U N
  · intro x hx y hy
    have hxS := hU hx
    have hyS := hU hy
    rcases D.pair_cases hx hy with ⟨hxL, hyL⟩ | ⟨hxP, hyP⟩ |
      ⟨hxN, hyP, hay⟩ | ⟨hxP, hax, hyN⟩
    · have hxL' := F.inLow hP (hP D.ha) hxL
      have hyL' := F.inLow hP (hP D.ha) hyL
      have er := e.2.2 _ (D.low_back_mem hxL) _ (D.low_back_mem hyL)
      constructor
      · rw [D.r₁_low hxL hyL, D'.r₁_low hxL' hyL',
          F.back_apply hN g hxS, F.back_apply hN g hyS]
        exact er.1
      · rw [D.r₂_low hxL hyL, D'.r₂_low hxL' hyL',
          F.back_apply hN g hxS, F.back_apply hN g hyS]
        exact er.2
    · constructor
      · rw [D.r₁_PP hxP hyP, D'.r₁_PP (e.mem hxP) (e.mem hyP)]
        exact (e.2.2 x hxP y hyP).1
      · rw [D.r₂_PP hxP hyP, D'.r₂_PP (e.mem hxP) (e.mem hyP)]
        exact (e.2.2 x hxP y hyP).2
    · have hxN' := Finset.mem_image_of_mem F.toFun hxN
      have hay' := (F.le_iff (hP D.ha) hyS).mpr hay
      constructor
      · rw [D.r₁_NH hxN hyP hay, D'.r₁_NH hxN' (e.mem hyP) hay',
          F.conjugate_apply g hxS]
        exact and_congr Iff.rfl (and_congr
          (e.2.2 _ (D.g_props hxN).1 _ D.hb).1 (e.2.2 _ D.ha _ hyP).1)
      · exact iff_of_false (D.not_r₂_NH hxN hyP hay)
          (D'.not_r₂_NH hxN' (e.mem hyP) hay')
    · have hyN' := Finset.mem_image_of_mem F.toFun hyN
      have hax' := (F.le_iff (hP D.ha) hxS).mpr hax
      exact ⟨iff_of_false (D.not_r₁_HN hxP hax hyN)
          (D'.not_r₁_HN (e.mem hxP) hax' hyN'),
        iff_of_false (D.not_r₂_HN hxP hax hyN)
          (D'.not_r₂_HN (e.mem hxP) hax' hyN')⟩

/-- Upward reflection data transport with the earlier rule and the copied block. -/
theorem upwardData {P Q : Str α} {a b : α} {N : Finset α} {g : α → α}
    (hP : P.U ⊆ S) (hQ : Q.U ⊆ S) (hN : N ⊆ S)
    (D : Str.UpData P Q a b N g) :
    Str.UpData (P.map F.toFun) (Q.map F.toFun) (F.toFun a) (F.toFun b)
      (N.image F.toFun) (F.conjugate g) := by
  have eP := F.isIso hP
  have eQ := F.isIso hQ
  refine
    { pat := eQ.isPattern D.pat
      cont := F.continuous hP hQ D.cont
      ext := F.extensionAt hP hQ D.ext
      hb := eP.mem D.hb
      hab := F.mono a (hP D.ha) b (hP D.hb) D.hab
      hrel := (eP.2.2 _ D.ha _ D.hb).2.mp D.hrel
      hNP := ?_
      hNb := ?_
      hNL := ?_
      himage := ?_
      hmono := ?_ }
  · intro x hx hxP
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact D.hNP y hy ((F.mem_image_iff hP (hN hy)).mp hxP)
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact F.mono y (hN hy) b (hP D.hb) (D.hNb y hy)
  · intro x hx q hq hqb
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨p, hp, rfl⟩ := eP.preimage hq
    exact F.mono p (hP hp) y (hN hy)
      (D.hNL y hy p hp ((F.lt_iff (hP hp) (hP D.hb)).mp hqb))
  · rw [F.image_conjugate hN g, D.himage]
    exact F.image_sdiff hQ hP
  · intro x hx y hy hxy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    rw [F.conjugate_apply g (hN hu), F.conjugate_apply g (hN hv)]
    exact F.mono (g u) (hQ (D.g_mem hu).1) (g v) (hQ (D.g_mem hv).1)
      (D.hmono u hu v hv ((F.lt_iff (hN hu) (hN hv)).mp hxy))

/-- The two upward reflections agree on their finite carriers after relabeling. -/
theorem upward_isIso {P Q : Str α} {a b : α} {N : Finset α} {g : α → α}
    (hP : P.U ⊆ S) (hQ : Q.U ⊆ S) (hN : N ⊆ S)
    (D : Str.UpData P Q a b N g) :
    Str.IsIso (P.upward Q a b N g)
      ((P.map F.toFun).upward (Q.map F.toFun) (F.toFun a) (F.toFun b)
        (N.image F.toFun) (F.conjugate g)) F.toFun := by
  have D' := F.upwardData hP hQ hN D
  have eP := F.isIso hP
  have eQ := F.isIso hQ
  have hU : (P.upward Q a b N g).U ⊆ S := Finset.union_subset hP hN
  refine ⟨?_, fun x hx y hy => F.mono x (hU hx) y (hU hy), ?_⟩
  · exact Finset.image_union P.U N
  · intro x hx y hy
    rcases Finset.mem_union.mp hx with hxP | hxN <;>
      rcases Finset.mem_union.mp hy with hyP | hyN
    · constructor
      · rw [D.r₁_PP hxP hyP, D'.r₁_PP (eP.mem hxP) (eP.mem hyP)]
        exact (eP.2.2 _ hxP _ hyP).1
      · rw [D.r₂_PP hxP hyP, D'.r₂_PP (eP.mem hxP) (eP.mem hyP)]
        exact (eP.2.2 _ hxP _ hyP).2
    · have hyN' := Finset.mem_image_of_mem F.toFun hyN
      constructor
      · rw [D.r₁_PN hxP hyN, D'.r₁_PN (eP.mem hxP) hyN']
        exact and_congr (F.lt_iff (hP hxP) (hP D.hb)).symm
          (eP.2.2 _ hxP _ D.hb).1
      · rw [D.r₂_PN hxP hyN, D'.r₂_PN (eP.mem hxP) hyN',
          F.conjugate_apply g (hN hyN)]
        exact and_congr (F.lt_iff (hP hxP) (hP D.ha)).symm
          (eQ.2.2 _ (D.cont.1.1 hxP) _ (D.g_mem hyN).1).2
    · have hxN' := Finset.mem_image_of_mem F.toFun hxN
      exact ⟨iff_of_false (D.not_r₁_NP hxN hyP)
          (D'.not_r₁_NP hxN' (eP.mem hyP)),
        iff_of_false (D.not_r₂_NP hxN hyP)
          (D'.not_r₂_NP hxN' (eP.mem hyP))⟩
    · have hxN' := Finset.mem_image_of_mem F.toFun hxN
      have hyN' := Finset.mem_image_of_mem F.toFun hyN
      constructor
      · rw [D.r₁_NN hxN hyN, D'.r₁_NN hxN' hyN',
          F.conjugate_apply g (hN hxN), F.conjugate_apply g (hN hyN)]
        exact (eQ.2.2 _ (D.g_mem hxN).1 _ (D.g_mem hyN).1).1
      · rw [D.r₂_NN hxN hyN, D'.r₂_NN hxN' hyN',
          F.conjugate_apply g (hN hxN), F.conjugate_apply g (hN hyN)]
        exact (eQ.2.2 _ (D.g_mem hxN).1 _ (D.g_mem hyN).1).2

end FiniteRelabeling
end Alexander313.Carlson
