import Alexander313.Wilken.HereditaryNativeIotaOrder

/-!
# Actual principal words and recursive query domains for iota order induction

Every atom and exposed comparison query retains the original source admission,
weak Normality and restriction. The mapped SOURCE atom word denotes the actual
target transform by its already proved addition law. Low atomization preserves
all word values. The source's final-principal-summand convention is expressed
by real ANF words, including its all-zero exception.

These are supporting lemmas for the simultaneous semantic induction, not
supplied order, Normality or collapse-naturality contracts. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Iota.OrderInduction

open NativePublicBridge (contextCode contextCode_checked)

theorem atoms_checked_normal (q : Nat) (t x : RelativeTerm Nat)
    (ht : check q t = true) (hn : Comparison.Normal q t) (hx : x ∈ Comparison.atoms t) :
    check q x = true ∧ Comparison.Normal q x := by
  have hq := (Bool.and_eq_true.mp ht).1
  have hs := (Comparison.atoms_spec q (SourceOne.PublicCodes.fragment t) hq t
    (checked_admissible q t ht) hn).1 x hx
  exact ⟨Comparison.admitted_checked q _ hq x hs.1, hs.2⟩

theorem atoms_sum_size_lt (t u x : RelativeTerm Nat)
    (hx : x ∈ Comparison.atoms (.sum t u)) : x.size < (.sum t u : RelativeTerm Nat).size := by
  rcases List.mem_append.mp hx with hx | hx
  · exact (Comparison.atoms_size_le t x hx).trans_lt (RelativeTerm.sum_left_size_lt t u)
  · exact (Comparison.atoms_size_le u x hx).trans_lt (RelativeTerm.sum_right_size_lt t u)

theorem restricted_argument (s a k : Nat) (t : RelativeTerm Nat)
    (hr : Restricted s a (.theta k t)) : Restricted s a t := by
  cases k with
  | zero => exact ((restricted_theta_zero s a t).mp hr).2
  | succ k => exact (restricted_theta_succ s a k t).mp hr

theorem restricted_atoms (s a : Nat) (t x : RelativeTerm Nat)
    (hr : Restricted s a t) (hx : x ∈ Comparison.atoms t) : Restricted s a x := by
  revert hr hx
  induction t with
  | parameter p =>
    intro hr hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    simp only [Restricted, fullList, RelativeTerm.PrincipalSupport.principalList,
      List.not_mem_nil, false_implies, implies_true, forall_const]
  | sum t u iht ihu =>
    intro hr hx
    have hs := (restricted_sum s a t u).mp hr
    rcases List.mem_append.mp hx with hx | hx
    · exact iht hs.1 hx
    · exact ihu hs.2 hx
  | theta k t ih =>
    intro hr hx
    have he : x = .theta k t := List.mem_singleton.mp hx
    subst x
    exact hr

theorem restricted_exposed (s a m : Nat) (t x : RelativeTerm Nat)
    (hr : Restricted s a t) (hx : x ∈ exposedThetaList m t) : Restricted s a x := by
  revert hr hx
  induction t with
  | parameter p => intro hr hx; simp only [exposedThetaList, List.not_mem_nil] at hx
  | sum t u iht ihu =>
    intro hr hx
    have hs := (restricted_sum s a t u).mp hr
    rcases List.mem_append.mp hx with hx | hx
    · exact iht hs.1 hx
    · exact ihu hs.2 hx
  | theta k t ih =>
    intro hr hx
    by_cases he : k = m
    · have hx' : x = .theta k t := by
        simpa only [exposedThetaList, if_pos he, List.mem_singleton] using hx
      subst x
      exact hr
    · by_cases hm : m < k
      · exact ih (restricted_argument s a k t hr)
          (by simpa only [exposedThetaList, if_neg he, if_pos hm] using hx)
      · simp only [exposedThetaList, if_neg he, if_neg hm, List.not_mem_nil] at hx

theorem exposed_checked_normal (q m : Nat) (t x : RelativeTerm Nat)
    (ht : check q t = true) (hn : Comparison.Normal q t) (hx : x ∈ exposedThetaList m t) :
    check q x = true ∧ Comparison.Normal q x := by
  have hq := (Bool.and_eq_true.mp ht).1
  exact ⟨Comparison.admitted_checked q _ hq x
    (Comparison.admitted_exposed (checked_admissible q t ht) m hx), hn.exposed m hx⟩

theorem source_atoms_anf (q : Nat) (t : RelativeTerm Nat)
    (ht : check q t = true) (hn : Comparison.Normal q t) :
    (Comparison.atoms t).map (denote q) = canonicalANF (denote q t) :=
  Comparison.atoms_anf q _ (Bool.and_eq_true.mp ht).1 t (checked_admissible q t ht) hn

theorem source_atoms_normal (q : Nat) (t : RelativeTerm Nat)
    (ht : check q t = true) (hn : Comparison.Normal q t) :
    IsAdditiveNormalForm ((Comparison.atoms t).map (denote q)) := by
  rw [source_atoms_anf q t ht hn]
  exact canonicalANF_normal _

theorem source_atoms_value (q : Nat) (t : RelativeTerm Nat)
    (ht : check q t = true) (hn : Comparison.Normal q t) :
    principalSum ((Comparison.atoms t).map (denote q)) = denote q t := by
  rw [source_atoms_anf q t ht hn, principalSum_canonicalANF]

/-- Atomization of a whole low expression preserves every principal WORD
value, not just the value of the whole expression. -/
theorem mapped_atoms_low (s a : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (contextCode s) t = true)
    (hn : Comparison.Normal (contextCode s) t) (hr : Restricted s a t)
    (hl : t.outerSort ≤ 1) :
    (Comparison.atoms t).map (fun x => denote (alphaCode s a) (transform s a x)) =
      (Comparison.atoms t).map (denote (contextCode s)) := by
  apply List.map_congr_left
  intro x hx
  have hxc := (atoms_checked_normal _ t x ht hn hx).1
  have hval : denote (contextCode s) x ≤ denote (contextCode s) t := by
    apply canonicalANF_mem_le
    rw [← source_atoms_anf _ t ht hn]
    exact List.mem_map.mpr ⟨x, hx, rfl⟩
  exact (transform_parameter_value s a ha x hxc
    (hval.trans_lt (restricted_low_below s a ha t ht hr hl))).2

/-- The genuine transformed source atom word evaluates to the target
denotation of the existing transform. No target Normality is assumed. -/
theorem mapped_atoms_value (s a : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (contextCode s) t = true)
    (hn : Comparison.Normal (contextCode s) t) (hr : Restricted s a t) :
    principalSum ((Comparison.atoms t).map
      (fun x => denote (alphaCode s a) (transform s a x))) =
      denote (alphaCode s a) (transform s a t) := by
  revert ht hn hr
  induction t with
  | parameter p =>
    intro ht hn hr
    rw [mapped_atoms_low s a ha (.parameter p) ht hn hr (Nat.zero_le _),
      source_atoms_value _ (.parameter p) ht hn,
      transform_low_value s a ha (.parameter p) ht hr (Nat.zero_le _)]
  | sum t u iht ihu =>
    intro ht hn hr
    have hc := BaseTransformation.sum_checks _ t u ht
    have hs := (restricted_sum s a t u).mp hr
    rw [Comparison.atoms, List.map_append, principalSum_append,
      iht hc.1 hn.1 hs.1, ihu hc.2 hn.2.1 hs.2, transform_add s a ha t u hc.1 hc.2]
  | theta k t ih =>
    intro ht hn hr
    simp only [Comparison.atoms, List.map_cons, List.map_nil, principalSum, add_zero]

theorem checked_theta_pos_principal (q k : Nat) (t : RelativeTerm Nat)
    (ht : check q (.theta k t) = true) :
    0 < denote q (.theta k t) ∧ Ordinal.IsPrincipal (· + ·) (denote q (.theta k t)) := by
  have hq := (Bool.and_eq_true.mp ht).1
  have hs := checked_admissible q (.theta k t) ht
  rw [denote_eq_finite q _ hq _ hs.2]
  exact Comparison.theta_pos_principal q _ k hq t hs

private theorem normal_list_zero_iff {X : Type} (value : X → Ordinal.{0}) (xs : List X)
    (hn : IsAdditiveNormalForm (xs.map value)) :
    principalSum (xs.map value) = 0 ↔ xs = [] := by
  cases xs with
  | nil => simp [principalSum]
  | cons x xs =>
    have hp : 0 < value x := (hn.1 _ List.mem_cons_self).1
    have hs : 0 < principalSum ((x :: xs).map value) := hp.trans_le le_self_add
    simp [ne_of_gt hs]

/-- Exact finite-word form of the source's final-principal convention.
The right word is either empty together with the left word, or a SINGLE
principal atom. Ordinary absorption-free binary addition is insufficient. -/
theorem normalSum_words_iff {X : Type} (value : X → Ordinal.{0}) (xs ys : List X)
    (hxs : IsAdditiveNormalForm (xs.map value)) (hys : IsAdditiveNormalForm (ys.map value)) :
    SourceNormalSum (principalSum (xs.map value) + principalSum (ys.map value))
      (principalSum (xs.map value)) (principalSum (ys.map value)) ↔
      (xs = [] ∧ ys = []) ∨ ∃ y, ys = [y] ∧ ∀ x ∈ xs, value y ≤ value x := by
  constructor
  · intro h
    rcases h with hz | ⟨as, has, he, hv⟩
    · exact Or.inl ⟨(normal_list_zero_iff value xs hxs).mp hz.2.1,
        (normal_list_zero_iff value ys hys).mp hz.2.2⟩
    · have hp := has.1 _ (List.mem_append_right _ (List.mem_singleton_self _))
      have hword : ys.map value = [principalSum (ys.map value)] := by
        calc
          ys.map value = canonicalANF (principalSum (ys.map value)) :=
            (canonicalANF_eq_of_normal hys rfl).symm
          _ = [principalSum (ys.map value)] := canonicalANF_principal hp.1 hp.2
      have hlength : ys.length = 1 := by
        have hl := congrArg List.length hword
        simpa only [List.length_map, List.length_singleton] using hl
      obtain ⟨y, hy⟩ : ∃ y, ys = [y] := by
        cases ys with
        | nil => simp at hlength
        | cons y ys =>
          cases ys with
          | nil => exact ⟨y, rfl⟩
          | cons z zs => simp at hlength
      subst ys
      have hsum : SourceNormalSum
          (principalSum (xs.map value) + principalSum ([y].map value))
          (principalSum (xs.map value)) (principalSum ([y].map value)) :=
        Or.inr ⟨as, has, he, hv⟩
      have hc := sourceNormalSum_canonical_concat hsum
      rw [canonicalANF_eq_of_normal hxs rfl, canonicalANF_eq_of_normal hys rfl] at hc
      refine Or.inr ⟨y, rfl, ?_⟩
      intro x hx
      exact (List.pairwise_append.mp hc.2).2.2 _ (List.mem_map.mpr ⟨x, hx, rfl⟩) _ (by simp)
  · rintro (⟨rfl, rfl⟩ | ⟨y, rfl, hcross⟩)
    · exact Or.inl ⟨by simp [principalSum], rfl, rfl⟩
    · have hc : IsAdditiveNormalForm ((xs.map value) ++ [value y]) := by
        refine ⟨?_, ?_⟩
        · intro p hp
          rcases List.mem_append.mp hp with hp | hp
          · exact hxs.1 p hp
          · have he : p = value y := List.mem_singleton.mp hp
            subst p
            exact hys.1 _ (by simp)
        · apply List.pairwise_append.mpr
          refine ⟨hxs.2, by simp, ?_⟩
          intro p hp q hq
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
          have he : q = value y := List.mem_singleton.mp hq
          subst q
          exact hcross x hx
      refine Or.inr ⟨xs.map value, ?_, rfl, ?_⟩
      · simpa only [List.map_cons, List.map_nil, principalSum, add_zero] using hc
      · rw [principalSum_append]
        simp [principalSum]

/-- A sum's actual final-principal clause transports once its smaller atom
comparisons and its two real target principal words have been established. -/
theorem mapped_normalSum (s a : Nat) (ha : rootCheck s a = true)
    (t u : RelativeTerm Nat) (ht : check (contextCode s) t = true)
    (hu : check (contextCode s) u = true)
    (hnt : Comparison.Normal (contextCode s) t) (hnu : Comparison.Normal (contextCode s) u)
    (hrt : Restricted s a t) (hru : Restricted s a u)
    (hs : SourceNormalSum (denote (contextCode s) t + denote (contextCode s) u)
      (denote (contextCode s) t) (denote (contextCode s) u))
    (htw : IsAdditiveNormalForm ((Comparison.atoms t).map
      (fun x => denote (alphaCode s a) (transform s a x))))
    (huw : IsAdditiveNormalForm ((Comparison.atoms u).map
      (fun x => denote (alphaCode s a) (transform s a x))))
    (hcross : ∀ x ∈ Comparison.atoms t, ∀ y ∈ Comparison.atoms u,
      denote (contextCode s) y ≤ denote (contextCode s) x →
      denote (alphaCode s a) (transform s a y) ≤ denote (alphaCode s a) (transform s a x)) :
    SourceNormalSum
      (denote (alphaCode s a) (transform s a t) + denote (alphaCode s a) (transform s a u))
      (denote (alphaCode s a) (transform s a t))
      (denote (alphaCode s a) (transform s a u)) := by
  have hsource := (normalSum_words_iff (denote (contextCode s))
    (Comparison.atoms t) (Comparison.atoms u) (source_atoms_normal _ t ht hnt)
    (source_atoms_normal _ u hu hnu)).mp (by
      simpa only [source_atoms_value _ t ht hnt, source_atoms_value _ u hu hnu] using hs)
  have hshape : (Comparison.atoms t = [] ∧ Comparison.atoms u = []) ∨
      ∃ y, Comparison.atoms u = [y] ∧ ∀ x ∈ Comparison.atoms t,
        denote (alphaCode s a) (transform s a y) ≤ denote (alphaCode s a) (transform s a x) := by
    rcases hsource with hz | ⟨y, hy, hle⟩
    · exact Or.inl hz
    · refine Or.inr ⟨y, hy, ?_⟩
      intro x hx
      exact hcross x hx y (by rw [hy]; exact List.mem_singleton_self _) (hle x hx)
  have htarget := (normalSum_words_iff
    (fun x => denote (alphaCode s a) (transform s a x))
    (Comparison.atoms t) (Comparison.atoms u) htw huw).mpr hshape
  simpa only [mapped_atoms_value s a ha t ht hnt hrt,
    mapped_atoms_value s a ha u hu hnu hru] using htarget

/-- Compare the same finite source atom words in the two real contexts.
The caller proves both atom directions by a smaller-size induction. -/
theorem mapped_word_lt_iff (s a : Nat) (ha : rootCheck s a = true)
    (t u : RelativeTerm Nat) (ht : check (contextCode s) t = true)
    (hu : check (contextCode s) u = true)
    (hnt : Comparison.Normal (contextCode s) t) (hnu : Comparison.Normal (contextCode s) u)
    (hrt : Restricted s a t) (hru : Restricted s a u)
    (htw : IsAdditiveNormalForm ((Comparison.atoms t).map
      (fun x => denote (alphaCode s a) (transform s a x))))
    (huw : IsAdditiveNormalForm ((Comparison.atoms u).map
      (fun x => denote (alphaCode s a) (transform s a x))))
    (hc : ∀ x ∈ Comparison.atoms t, ∀ y ∈ Comparison.atoms u,
      (denote (alphaCode s a) (transform s a x) < denote (alphaCode s a) (transform s a y) ↔
        denote (contextCode s) x < denote (contextCode s) y) ∧
      (denote (alphaCode s a) (transform s a y) < denote (alphaCode s a) (transform s a x) ↔
        denote (contextCode s) y < denote (contextCode s) x)) :
    denote (alphaCode s a) (transform s a t) < denote (alphaCode s a) (transform s a u) ↔
      denote (contextCode s) t < denote (contextCode s) u := by
  have hsource : ∀ x ∈ Comparison.atoms t, ∀ y ∈ Comparison.atoms u,
      (Comparison.less (contextCode s) x y = true ↔ denote (contextCode s) x < denote (contextCode s) y) ∧
      (Comparison.less (contextCode s) y x = true ↔ denote (contextCode s) y < denote (contextCode s) x) := by
    intro x hx y hy
    have hxc := atoms_checked_normal _ t x ht hnt hx
    have hyc := atoms_checked_normal _ u y hu hnu hy
    exact ⟨Comparison.less_correct _ x y hxc.1 hyc.1 hxc.2 hyc.2,
      Comparison.less_correct _ y x hyc.1 hxc.1 hyc.2 hxc.2⟩
  have htarget : ∀ x ∈ Comparison.atoms t, ∀ y ∈ Comparison.atoms u,
      (Comparison.less (contextCode s) x y = true ↔
        denote (alphaCode s a) (transform s a x) < denote (alphaCode s a) (transform s a y)) ∧
      (Comparison.less (contextCode s) y x = true ↔
        denote (alphaCode s a) (transform s a y) < denote (alphaCode s a) (transform s a x)) := by
    intro x hx y hy
    exact ⟨(hsource x hx y hy).1.trans (hc x hx y hy).1.symm,
      (hsource x hx y hy).2.trans (hc x hx y hy).2.symm⟩
  have hs := Theta.lexLT_correct (Comparison.less (contextCode s)) (denote (contextCode s))
    (Comparison.atoms t) (Comparison.atoms u) (source_atoms_normal _ t ht hnt)
    (source_atoms_normal _ u hu hnu) hsource
  have hv := Theta.lexLT_correct (Comparison.less (contextCode s))
    (fun x => denote (alphaCode s a) (transform s a x))
    (Comparison.atoms t) (Comparison.atoms u) htw huw htarget
  rw [source_atoms_value _ t ht hnt, source_atoms_value _ u hu hnu] at hs
  rw [mapped_atoms_value s a ha t ht hnt hrt, mapped_atoms_value s a ha u hu hnu hru] at hv
  exact hv.symm.trans hs

theorem checked_theta_lt_iff_exposed (q k : Nat) (t u : RelativeTerm Nat)
    (ht : check q (.theta k t) = true) (hu : check q (.theta k u) = true)
    (hnt : Comparison.Normal q t) (hnu : Comparison.Normal q u) :
    denote q (.theta k t) < denote q (.theta k u) ↔
      (denote q t < denote q u ∧ ∀ x ∈ exposedThetaList k t, denote q x < denote q (.theta k u)) ∨
      ∃ x ∈ exposedThetaList k u, denote q (.theta k t) ≤ denote q x := by
  let n := max (SourceOne.PublicCodes.fragment (.theta k t))
    (SourceOne.PublicCodes.fragment (.theta k u))
  have htn := Comparison.checked_admissible q n (.theta k t) ht
    ((SourceOne.PublicCodes.height_le_fragment _).trans (le_max_left _ _))
  have hun := Comparison.checked_admissible q n (.theta k u) hu
    ((SourceOne.PublicCodes.height_le_fragment _).trans (le_max_right _ _))
  exact Comparison.theta_lt_iff_exposed q n k (Bool.and_eq_true.mp ht).1 t u htn hun hnt hnu

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Iota.OrderInduction
