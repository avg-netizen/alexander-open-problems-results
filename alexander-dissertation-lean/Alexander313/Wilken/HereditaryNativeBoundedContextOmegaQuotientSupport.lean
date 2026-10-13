import Alexander313.Wilken.HereditaryNativeOmegaQuotient
import Alexander313.Wilken.HereditaryNativeOmegaPowers

/-!
# Genuine generic ANF quotient and finite-unit suffix kernels

Actual native Normal descending principal words retain descending order by
the real positive Omega-one multiplication identity. The finite selector's
unit suffix is derived from the real checker/equality and original ANF.
These are mathematical finite kernels, not supplied quotient/Normal oracles.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.BoundedContextIota.OmegaQuotient.Support

open Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.OmegaQuotient
  (baseTerm thresholdTerm theta_checked baseTerm_spec thresholdTerm_spec theta_principal
   theta_one_high_absorbs wordHeight wordHeight_mem unitTest unitTest_exact selectUnits
   selectUnits_primrec selectUnits_mem selectUnits_filter theta_one_below_threshold
   theta_one_shifted_quotient theta_one_above_threshold principal_above_second_absorbs)

theorem quotient_map_normal (q : Nat) (Ω : Ordinal.{0}) (hΩ : 0 < Ω)
    (f : RelativeTerm Nat → RelativeTerm Nat) (as : List (RelativeTerm Nat))
    (hn : IsAdditiveNormalForm (as.map (denote q)))
    (hs : ∀ t ∈ as, 0 < denote q (f t) ∧ Ordinal.IsPrincipal (· + ·) (denote q (f t)) ∧
      Ω * denote q (f t) = denote q t) :
    IsAdditiveNormalForm ((as.map f).map (denote q)) := by
  revert hn hs
  induction as with
  | nil => intro hn hs; simpa only [List.map_nil] using hn
  | cons t as ih =>
    intro hn hs
    have hp := List.pairwise_cons.mp hn.2
    have htail : IsAdditiveNormalForm (as.map (denote q)) :=
      ⟨fun p hp' => hn.1 p (List.mem_cons_of_mem _ hp'), hp.2⟩
    have ht := hs t List.mem_cons_self
    have htnew := ih htail (fun u hu => hs u (List.mem_cons_of_mem _ hu))
    refine ⟨?_, List.pairwise_cons.mpr ⟨?_, htnew.2⟩⟩
    · intro p hp'
      rcases List.mem_cons.mp hp' with rfl | hp'
      · exact ⟨ht.1, ht.2.1⟩
      · exact htnew.1 p hp'
    · intro p hp'
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hp'
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
      have hvnew := hs v (List.mem_cons_of_mem _ hv)
      apply le_of_not_gt
      intro hbad
      have hb := mul_lt_mul_of_pos_left hbad hΩ
      rw [ht.2.2, hvnew.2.2] at hb
      exact (hp.1 (denote q v) (List.mem_map.mpr ⟨v, hv, rfl⟩)).not_lt hb

theorem mul_principalSum_map (q : Nat) (Ω : Ordinal.{0})
    (f : RelativeTerm Nat → RelativeTerm Nat) (as : List (RelativeTerm Nat))
    (hs : ∀ t ∈ as, Ω * denote q (f t) = denote q t) :
    Ω * principalSum ((as.map f).map (denote q)) = principalSum (as.map (denote q)) := by
  revert hs
  induction as with
  | nil => intro _; simp only [List.map_nil, principalSum, mul_zero]
  | cons t as ih =>
    intro hs
    simp only [List.map_cons, principalSum, mul_add]
    rw [hs t List.mem_cons_self, ih (fun u hu => hs u (List.mem_cons_of_mem _ hu))]

theorem selectUnits_all (q : Nat) (as : List (RelativeTerm Nat))
    (h : ∀ t ∈ as, unitTest q t = true) : selectUnits true q as = as ∧ selectUnits false q as = [] := by
  revert h
  induction as with
  | nil => intro h; exact ⟨rfl, rfl⟩
  | cons t as ih =>
    intro h
    have ht := h t List.mem_cons_self
    have hs := ih (fun u hu => h u (List.mem_cons_of_mem _ hu))
    constructor
    · simp only [selectUnits, ht, Bool.cond_true, Bool.cond_false, Bool.not_true, hs.1]
    · simp only [selectUnits, ht, Bool.cond_true, Bool.cond_false, Bool.not_true, hs.2]

theorem unit_partition (q : Nat) (hq : baseCheck q = true) (as : List (RelativeTerm Nat))
    (hn : IsAdditiveNormalForm (as.map (denote q)))
    (hs : ∀ t ∈ as, check q t = true ∧ Comparison.Normal q t) :
    as = selectUnits false q as ++ selectUnits true q as := by
  revert hn hs
  induction as with
  | nil => intro hn hs; rfl
  | cons t as ih =>
    intro hn hs
    have hp := List.pairwise_cons.mp hn.2
    have htail : IsAdditiveNormalForm (as.map (denote q)) :=
      ⟨fun p hm => hn.1 p (List.mem_cons_of_mem _ hm), hp.2⟩
    have ht := hs t List.mem_cons_self
    cases he : unitTest q t with
    | false =>
      have hi := ih htail (fun u hu => hs u (List.mem_cons_of_mem _ hu))
      simp only [selectUnits, he, Bool.cond_false, Bool.not_false, Bool.cond_true,
        List.cons_append, ← hi]
    | true =>
      have hv := (unitTest_exact q hq t ht.1 ht.2).mp he
      have hall : ∀ u ∈ as, unitTest q u = true := by
        intro u hu
        have hus := hs u (List.mem_cons_of_mem _ hu)
        apply (unitTest_exact q hq u hus.1 hus.2).mpr
        have hupos := (hn.1 _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨u, hu, rfl⟩))).1
        have hule : denote q u ≤ 1 := by
          rw [← hv]
          exact hp.1 _ (List.mem_map.mpr ⟨u, hu, rfl⟩)
        exact le_antisymm hule (Order.one_le_iff_pos.mpr hupos)
      have hall' := selectUnits_all q as hall
      simp only [selectUnits, he, Bool.cond_true, Bool.not_true, Bool.cond_false,
        hall'.1, hall'.2, List.nil_append]

theorem selected_normal (q : Nat) (units : Bool) (as : List (RelativeTerm Nat))
    (hn : IsAdditiveNormalForm (as.map (denote q))) :
    IsAdditiveNormalForm ((selectUnits units q as).map (denote q)) := by
  rw [selectUnits_filter]
  have hbase : (as.filter (fun t => cond units (unitTest q t) (!unitTest q t))).Sublist as :=
    List.filter_sublist
  have hsub := hbase.map (denote q)
  exact ⟨fun p hp => hn.1 p (hsub.subset hp), hn.2.sublist hsub⟩

theorem unit_sum (q : Nat) (hq : baseCheck q = true) (as : List (RelativeTerm Nat))
    (hs : ∀ t ∈ as, check q t = true ∧ Comparison.Normal q t) :
    principalSum ((selectUnits true q as).map (denote q)) =
      ((selectUnits true q as).length : Ordinal.{0}) := by
  have hv : ∀ t ∈ selectUnits true q as, denote q t = 1 := by
    intro t ht
    have hm := (selectUnits_mem true q as t).mp ht
    exact (unitTest_exact q hq t (hs t hm.1).1 (hs t hm.1).2).mp hm.2
  generalize he : selectUnits true q as = bs at hv ⊢
  clear he
  revert hv
  induction bs with
  | nil => intro hv; simp only [List.map_nil, principalSum, List.length_nil, Nat.cast_zero]
  | cons t bs ih =>
    intro hv
    simp only [List.map_cons, principalSum, List.length_cons]
    rw [hv t List.mem_cons_self, ih (fun u hu => hv u (List.mem_cons_of_mem _ hu)),
      ← Nat.cast_one, ← Nat.cast_add]
    exact congrArg (fun n : Nat => (n : Ordinal.{0})) (Nat.add_comm 1 bs.length)

theorem principalSum_limit_zero (as : List Ordinal.{0})
    (hs : ∀ p ∈ as, 1 < p ∧ Ordinal.IsPrincipal (· + ·) p) :
    principalSum as = 0 ∨ IsSuccLimit (principalSum as) := by
  revert hs
  induction as with
  | nil => intro hs; exact Or.inl rfl
  | cons p as ih =>
    intro hs
    have hp := hs p List.mem_cons_self
    have ht := ih (fun q hq => hs q (List.mem_cons_of_mem _ hq))
    apply Or.inr
    rcases ht with hz | hl
    · simpa only [principalSum, hz, add_zero] using Ordinal.isSuccLimit_of_isPrincipal_add hp.1 hp.2
    · exact Ordinal.isSuccLimit_add _ hl

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.BoundedContextIota.OmegaQuotient.Support
