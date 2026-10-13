import Alexander313.Wilken.HereditaryNativeBoundedContextIotaOrderInduction

/-!
# Genuine full beta restriction of the actual SAME-value source return

The original bounded intermediate root and its original restricted Normal
tree derive every hidden return caller. Each returned LOW parameter or
zero-index node has its entire hidden support bounded by its SAME value.
Positive indices retain the recursive return. Actual addition normalizes
the returned sum without introducing new zero-index values. The conclusion
is full original-source restriction below the genuine beta value; no root
representation, restriction-preservation or commutation oracle is assumed.
Uncompiled source candidates. Full iota commutation is a separate step.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.BoundedContextIota.ReturnSupport

open NativePublicBridge (contextCode)

def FullBelow (q : Nat) (β : Ordinal.{0}) (t : RelativeTerm Nat) : Prop :=
  ∀ u ∈ Iota.fullList t, denote q u < β

theorem fullBelow_sum (q : Nat) (β : Ordinal.{0}) (t u : RelativeTerm Nat) :
    FullBelow q β (.sum t u) ↔ FullBelow q β t ∧ FullBelow q β u := by
  constructor
  · intro h
    exact ⟨fun v hv => h v (List.mem_append_left _ hv),
      fun v hv => h v (List.mem_append_right _ hv)⟩
  · rintro ⟨ht, hu⟩ v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact ht v hv
    · exact hu v hv

theorem fullBelow_theta_zero (q : Nat) (β : Ordinal.{0}) (t : RelativeTerm Nat) :
    FullBelow q β (.theta 0 t) ↔ denote q (.theta 0 t) < β ∧ FullBelow q β t := by
  simp only [FullBelow, Iota.fullList, RelativeTerm.PrincipalSupport.principalList_theta_same,
    List.forall_mem_cons]

theorem fullBelow_theta_succ (q : Nat) (β : Ordinal.{0}) (k : Nat) (t : RelativeTerm Nat) :
    FullBelow q β (.theta (k + 1) t) ↔ FullBelow q β t := by
  rw [FullBelow, Iota.fullList,
    RelativeTerm.PrincipalSupport.principalList_theta_higher 0 (k + 1) t (Nat.succ_pos k)]
  rfl

private theorem zero_fullBelow (q : Nat) (β : Ordinal.{0}) : FullBelow q β Normalization.zeroTree := by
  intro u hu
  simp only [Normalization.zeroTree, Iota.fullList,
    RelativeTerm.PrincipalSupport.principalList, List.not_mem_nil] at hu

private theorem atoms_fullBelow (q : Nat) (β : Ordinal.{0}) (t : RelativeTerm Nat)
    (hr : FullBelow q β t) (u : RelativeTerm Nat) (hu : u ∈ Comparison.atoms t) :
    FullBelow q β u := by
  revert hr hu
  induction t with
  | parameter p =>
    intro hr hu
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hu
    intro v hv
    simp only [Iota.fullList, RelativeTerm.PrincipalSupport.principalList, List.not_mem_nil] at hv
  | sum t v iht ihv =>
    intro hr hu
    have hs := (fullBelow_sum q β t v).mp hr
    rcases List.mem_append.mp hu with hu | hu
    · exact iht hs.1 hu
    · exact ihv hs.2 hu
  | theta k t ih =>
    intro hr hu
    exact (List.mem_singleton.mp hu).symm ▸ hr

private theorem buildRev_fullBelow (q : Nat) (β : Ordinal.{0}) (as : List (RelativeTerm Nat))
    (hr : ∀ t ∈ as, FullBelow q β t) : FullBelow q β (Normalization.buildRev as) := by
  revert hr
  induction as with
  | nil => intro _; exact zero_fullBelow q β
  | cons t as ih =>
    intro hr
    exact (fullBelow_sum q β _ _).mpr
      ⟨ih (fun u hu => hr u (List.mem_cons_of_mem _ hu)), hr t List.mem_cons_self⟩

private theorem buildAtoms_fullBelow (q : Nat) (β : Ordinal.{0}) (as : List (RelativeTerm Nat))
    (hr : ∀ t ∈ as, FullBelow q β t) : FullBelow q β (Normalization.buildAtoms as) :=
  buildRev_fullBelow q β as.reverse (fun t ht => hr t (List.mem_reverse.mp ht))

/-- The original native normalizer preserves the entire scalar support cut. -/
theorem normalize_fullBelow (q : Nat) (β : Ordinal.{0}) (t : RelativeTerm Nat)
    (ht : check q t = true) (hr : FullBelow q β t) :
    FullBelow q β (Normalization.normalize q t) := by
  revert ht hr
  induction t with
  | parameter p => intro ht hr; exact hr
  | sum t u iht ihu =>
    intro ht hr
    have hc := BaseTransformation.sum_checks q t u ht
    have hs := (fullBelow_sum q β t u).mp hr
    apply buildAtoms_fullBelow
    intro v hv
    have hm := Normalization.normalizeAtoms_mem q v _ hv
    rcases List.mem_append.mp hm with hm | hm
    · exact atoms_fullBelow q β _ (iht hc.1 hs.1) v hm
    · exact atoms_fullBelow q β _ (ihu hc.2 hs.2) v hm
  | theta k t ih =>
    intro ht hr
    have hc := BaseTransformation.theta_argument_check q k t ht
    cases k with
    | zero =>
      have hs := (fullBelow_theta_zero q β t).mp hr
      apply (fullBelow_theta_zero q β _).mpr
      refine ⟨?_, ih hc hs.2⟩
      have hv := (Normalization.normalize_checked q t hc).2.2
      change globalCollapse (base q) 0 (denote q (Normalization.normalize q t)) < _
      rw [hv]
      exact hs.1
    | succ k =>
      exact (fullBelow_theta_succ q β k _).mpr
        (ih hc ((fullBelow_theta_succ q β k t).mp hr))

/-- The actual admitted-pair addition code preserves both full support cuts. -/
theorem addCode_fullBelow (q c d : Nat) (β : Ordinal.{0})
    (hc : checkCode q c = true) (hd : checkCode q d = true)
    (hrc : FullBelow q β (ThetaCourse.rawTree c))
    (hrd : FullBelow q β (ThetaCourse.rawTree d)) :
    FullBelow q β (ThetaCourse.rawTree (Arithmetic.addCode q c d)) := by
  have hi := (Arithmetic.inputCheck_exact q c d).mpr ⟨hc, hd⟩
  have ht := Iota.Inverse.checked_sum q _ _ (Arithmetic.raw_checked q c hc) (Arithmetic.raw_checked q d hd)
  have h := normalize_fullBelow q β (.sum (ThetaCourse.rawTree c) (ThetaCourse.rawTree d)) ht
    ((fullBelow_sum q β _ _).mpr ⟨hrc, hrd⟩)
  simpa only [Arithmetic.addCode, hi, Bool.cond_true, Arithmetic.addTerm, ThetaCourse.rawTree_code] using h

/-- Actual LOW admission and weak Normality bound every hidden node. -/
theorem lowCode_fullBelow (q c : Nat) (β : Ordinal.{0})
    (hc : lowCheckCode q c = true) (hn : Comparison.acceptedCode q c = true)
    (hb : interpretation q c < β) : FullBelow q β (ThetaCourse.rawTree c) := by
  have ha := (Comparison.acceptedCode_exact q c).mp hn
  have ht := Arithmetic.raw_checked q c ha.1
  obtain ⟨t, he, hl⟩ := (lowCheckCode_exact q c).mp hc
  have hlow : (ThetaCourse.rawTree c).outerSort ≤ 1 := by
    simpa only [← he, ThetaCourse.rawTree_code] using of_decide_eq_true (Bool.and_eq_true.mp hl).2
  intro u hu
  have h := Iota.Inverse.fullList_value_le_low q _ u ht ha.2 hlow hu
  rw [Arithmetic.raw_value q c ha.1] at h
  exact h.trans_lt hb

/-- The original beta restriction derives EVERY internal return caller. -/
theorem sourceTermCode_spec (s a b : Nat) (ha : rootCheck s a b = true)
    (t : RelativeTerm Nat) (ht : check (sourceCode s a) t = true)
    (hn : Comparison.Normal (sourceCode s a) t) (hr : Restricted s a b t) :
    Comparison.acceptedCode (contextCode s) (BoundedPublicReturn.sourceTermCode s a t) = true ∧
      interpretation (contextCode s) (BoundedPublicReturn.sourceTermCode s a t) = denote (sourceCode s a) t := by
  apply BoundedPublicReturn.sourceTermCode_spec s a (outer_root s a b ha) t ht hn
  intro u hu
  exact (hr u hu).trans_lt ((rootCheck_exact s a b).mp ha).2.2

private theorem sourceTermCode_low_fullBelow (s a b : Nat) (ha : rootCheck s a b = true)
    (t : RelativeTerm Nat) (ht : check (sourceCode s a) t = true)
    (hn : Comparison.Normal (sourceCode s a) t) (hl : t.outerSort ≤ 1)
    (hb : denote (sourceCode s a) t < interpretation (sourceCode s a) b) :
    FullBelow (contextCode s) (interpretation (sourceCode s a) b)
      (ThetaCourse.rawTree (BoundedPublicReturn.sourceTermCode s a t)) := by
  have hs := BoundedPublicReturn.sourceTermCode_low_spec s a (outer_root s a b ha) t ht hn hl
    (hb.trans ((rootCheck_exact s a b).mp ha).2.2)
  exact lowCode_fullBelow (contextCode s) _ _ hs.2.1 hs.1 (hs.2.2.trans_lt hb)

/-- The actual SAME-value finite source return preserves the ORIGINAL full
beta cut, including every node hidden inside a zero-index argument. -/
theorem sourceTermCode_restricted (s a b : Nat) (ha : rootCheck s a b = true)
    (t : RelativeTerm Nat) (ht : check (sourceCode s a) t = true)
    (hn : Comparison.Normal (sourceCode s a) t) (hr : Restricted s a b t) :
    FullBelow (contextCode s) (interpretation (sourceCode s a) b)
      (ThetaCourse.rawTree (BoundedPublicReturn.sourceTermCode s a t)) := by
  revert ht hn hr
  induction t with
  | parameter p =>
    intro ht hn hr
    have hp := checked_parameters (sourceCode s a) (.parameter p) ht p (by simp [RelativeTerm.parameters])
    exact sourceTermCode_low_fullBelow s a b ha (.parameter p) ht hn (by simp [RelativeTerm.outerSort])
      (hp.2.trans_le (root_base_le s a b ha))
  | sum t u iht ihu =>
    intro ht hn hr
    have hc := BaseTransformation.sum_checks (sourceCode s a) t u ht
    have hs := (restricted_sum s a b t u).mp hr
    have hst := sourceTermCode_spec s a b ha t hc.1 hn.1 hs.1
    have hsu := sourceTermCode_spec s a b ha u hc.2 hn.2.1 hs.2
    rw [BoundedPublicReturn.sourceTermCode_sum]
    exact addCode_fullBelow (contextCode s) _ _ _
      ((Comparison.acceptedCode_exact _ _).mp hst.1).1
      ((Comparison.acceptedCode_exact _ _).mp hsu.1).1
      (iht hc.1 hn.1 hs.1) (ihu hc.2 hn.2.1 hs.2)
  | theta k t ih =>
    intro ht hn hr
    cases k with
    | zero =>
      exact sourceTermCode_low_fullBelow s a b ha (.theta 0 t) ht hn (by simp [RelativeTerm.outerSort])
        ((restricted_theta_zero s a b t).mp hr).1
    | succ k =>
      have hc := BaseTransformation.theta_argument_check (sourceCode s a) (k + 1) t ht
      have hrt := (restricted_theta_succ s a b k t).mp hr
      have h := ih hc hn hrt
      have hk : (k + 1 == 0) = false := by simp
      rw [BoundedPublicReturn.sourceTermCode_theta]
      simpa only [BoundedPublicReturn.thetaCode, hk, Bool.cond_false,
        BoundedPublicReturn.nodeCode, ThetaCourse.rawTree_code, fullBelow_theta_succ] using h

/-- A genuine SAME-value returned beta code converts the derived scalar
cut to the original source-star restriction. This local equality belongs
to the concrete returned-root construction, not the input domain. -/
theorem sourceTermCode_iota_restricted (s a b returnedRoot : Nat) (ha : rootCheck s a b = true)
    (he : interpretation (contextCode s) returnedRoot = interpretation (sourceCode s a) b)
    (t : RelativeTerm Nat) (ht : check (sourceCode s a) t = true)
    (hn : Comparison.Normal (sourceCode s a) t) (hr : Restricted s a b t) :
    Iota.Restricted s returnedRoot (ThetaCourse.rawTree (BoundedPublicReturn.sourceTermCode s a t)) := by
  intro u hu
  rw [he]
  exact sourceTermCode_restricted s a b ha t ht hn hr u hu

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.BoundedContextIota.ReturnSupport
