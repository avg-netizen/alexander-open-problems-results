import Alexander313.Wilken.SourceOneNativeIotaAddition
import Alexander313.Wilken.SourceOneOmegaQuotient
import Alexander313.Wilken.PublicEpsilonNativeMappedOmegaQuotientSupport

/-!
# Genuine original source-one mapped quotient callers

Only the original check0/Theta.Normal/source-one restriction controls the
source. The actual alpha epsilon supplies the target scalar formulas.
Original normalized addition and order reflection identify the genuine
Difference.tree left quotient. No Native base-one source parser or mapped
subtraction oracle occurs. Source-only and uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.MappedOmegaQuotient

open OrderSupport OmegaQuotient
open NativeContext.PublicEpsilonIota.MappedOmegaQuotient
  (theta_zero_unit zero_threshold_lt_first theta_zero_below_threshold
   theta_zero_shifted_quotient theta_zero_above_threshold principal_above_first_absorbs)

theorem baseTerm_restricted (a : Nat) : Restricted a baseTerm :=
  (restricted_theta_succ a 0 _).mpr (zero_restricted a)

theorem unitTerm_restricted (a : Nat) (ha : rootCheck a = true) : Restricted a unitTerm := by
  apply (restricted_theta_zero a _).mpr
  refine ⟨?_, zero_restricted a⟩
  change denote 0 unitTerm < interpretation 0 a
  rw [unitTerm_spec.2.2]
  exact EpsilonOffsets.epsilon_one_lt (root_epsilon a ha)

theorem thresholdTerm_restricted (a : Nat) (ha : rootCheck a = true) : Restricted a thresholdTerm :=
  (restricted_theta_succ a 0 _).mpr (unitTerm_restricted a ha)

theorem mapped_baseTerm (a : Nat) (ha : rootCheck a = true) :
    NativeContext.denote (alphaCode a) (transform a baseTerm) = NativeContext.base (alphaCode a) := by
  rw [baseTerm, transform_theta_succ a 0 ha _ baseTerm_spec.1 (baseTerm_restricted a)]
  change globalCollapse (NativeContext.base (alphaCode a)) 0
    (NativeContext.denote (alphaCode a) (transform a (zeroTree 0))) = _
  rw [transform_low_value a ha _ (Bool.and_eq_true.mp (zeroTree_lowCheck 0)).1
    (zero_restricted a) (Nat.zero_le _), zeroTree_denote]
  simpa only [omegaSequence_zero] using globalCollapse_zero (NativeContext.base (alphaCode a))
    (NativeContext.base_pos _ (alphaCode_baseCheck a ha))
    (NativeContext.BaseTransformation.base_additive _ (alphaCode_baseCheck a ha)) 0

theorem mapped_thresholdTerm (a : Nat) (ha : rootCheck a = true) :
    NativeContext.denote (alphaCode a) (transform a thresholdTerm) =
      NativeContext.base (alphaCode a) * Ordinal.omega0 := by
  rw [thresholdTerm, transform_theta_succ a 0 ha _ thresholdTerm_spec.1
    (thresholdTerm_restricted a ha)]
  change globalCollapse (NativeContext.base (alphaCode a)) 0
    (NativeContext.denote (alphaCode a) (transform a unitTerm)) = _
  rw [transform_low_value a ha _ unitTerm_spec.1 (unitTerm_restricted a ha) (by
    simp only [unitTerm, RelativeTerm.outerSort]; omega), unitTerm_spec.2.2]
  exact theta_zero_unit _ ((NativeContext.baseCheck_exact _).mp (alphaCode_baseCheck a ha)).2

/-- Actual original source normalization supplies the subtraction caller
and preserves the full original restriction; iota reflects the resulting
ordinary addition equation. -/
theorem mapped_subtract_base (a : Nat) (ha : rootCheck a = true)
    (t : RelativeTerm Nat) (ht : check 0 t = true) (hn : Theta.Normal 0 t)
    (hr : Restricted a t) (hle : omegaSequence (finiteBase 0) 1 ≤ denote 0 t) :
    NativeContext.denote (alphaCode a) (transform a (Difference.tree 0 baseTerm.code t.code)) =
      NativeContext.denote (alphaCode a) (transform a t) - NativeContext.base (alphaCode a) := by
  have hbc : checkCode 0 baseTerm.code = true := by simpa only [checkCode_code] using baseTerm_spec.1
  have htc : checkCode 0 t.code = true := by simpa only [checkCode_code] using ht
  have hs := Difference.tree_spec 0 baseTerm.code t.code hbc htc (by
    simpa only [interpretation_code, baseTerm_spec.2.2] using hle)
  have hsr := subtract_restricted a baseTerm.code t.code htc
    (by simpa only [ThetaCourse.rawTree_code] using hr)
  have hv : denote 0 (Difference.tree 0 baseTerm.code t.code) =
      denote 0 t - omegaSequence (finiteBase 0) 1 := by
    simpa only [interpretation_code, baseTerm_spec.2.2] using hs.2.2.2
  have hadd := Addition.sourceSum_spec a ha baseTerm _ baseTerm_spec.1 hs.1
    baseTerm_spec.2.1 hs.2.1 (baseTerm_restricted a) hsr
  have he : denote 0 (Addition.sourceSum baseTerm (Difference.tree 0 baseTerm.code t.code)) = denote 0 t := by
    rw [hadd.2.2.2.1, baseTerm_spec.2.2, hv, Ordinal.add_sub_cancel_of_le hle]
  have hm := (transform_eq_iff a ha _ t hadd.1 ht hadd.2.1 hn hadd.2.2.1 hr).mpr he
  have hsum : NativeContext.base (alphaCode a) +
      NativeContext.denote (alphaCode a) (transform a (Difference.tree 0 baseTerm.code t.code)) =
        NativeContext.denote (alphaCode a) (transform a t) := by
    rw [← mapped_baseTerm a ha, ← hadd.2.2.2.2]
    exact hm
  calc
    NativeContext.denote (alphaCode a) (transform a (Difference.tree 0 baseTerm.code t.code)) =
        (NativeContext.base (alphaCode a) +
          NativeContext.denote (alphaCode a) (transform a (Difference.tree 0 baseTerm.code t.code))) -
          NativeContext.base (alphaCode a) := (Ordinal.add_sub_cancel _ _).symm
    _ = NativeContext.denote (alphaCode a) (transform a t) - NativeContext.base (alphaCode a) := by rw [hsum]

private theorem selectUnits_all (as : List (RelativeTerm Nat))
    (h : ∀ t ∈ as, unitTest t = true) : selectUnits true as = as ∧ selectUnits false as = [] := by
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

theorem unit_partition (as : List (RelativeTerm Nat))
    (hn : IsAdditiveNormalForm (as.map (denote 0)))
    (hs : ∀ t ∈ as, check 0 t = true ∧ Theta.Normal 0 t) :
    as = selectUnits false as ++ selectUnits true as := by
  revert hn hs
  induction as with
  | nil => intro hn hs; rfl
  | cons t as ih =>
    intro hn hs
    have hp := List.pairwise_cons.mp hn.2
    have htail : IsAdditiveNormalForm (as.map (denote 0)) :=
      ⟨fun p hm => hn.1 p (List.mem_cons_of_mem _ hm), hp.2⟩
    have ht := hs t List.mem_cons_self
    cases he : unitTest t with
    | false =>
      have hi := ih htail (fun u hu => hs u (List.mem_cons_of_mem _ hu))
      simp only [selectUnits, he, Bool.cond_false, Bool.not_false, Bool.cond_true,
        List.cons_append, ← hi]
    | true =>
      have hv := (unitTest_exact t ht.1 ht.2).mp he
      have hall : ∀ u ∈ as, unitTest u = true := by
        intro u hu
        have hus := hs u (List.mem_cons_of_mem _ hu)
        apply (unitTest_exact u hus.1 hus.2).mpr
        have hupos := (hn.1 _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨u, hu, rfl⟩))).1
        have hule : denote 0 u ≤ 1 := by
          rw [← hv]
          exact hp.1 _ (List.mem_map.mpr ⟨u, hu, rfl⟩)
        exact le_antisymm hule (Order.one_le_iff_pos.mpr hupos)
      have hall' := selectUnits_all as hall
      simp only [selectUnits, he, Bool.cond_true, Bool.not_true, Bool.cond_false,
        hall'.1, hall'.2, List.nil_append]


end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.MappedOmegaQuotient
