import Alexander313.Wilken.PublicEpsilonNativeUnboundedOmegaQuotientSupport
import Alexander313.Wilken.PublicEpsilonNativeUnboundedIotaOrderInduction

/-!
# Actual full Omega-one coefficient on the full original high-root domain

The original admitted Normal high root supplies the complete descending
ANF quotient. Positive Omega-one multiplication reflects its order; the
actual unit test partitions its finite suffix and yields lambda zero or a
proper limit. Every original restriction, source admission and target iota
LOW Normal caller is derived. The literal admitted source q is retained throughout, including noncanonical
spellings. The genuine original RootLow guard supplies the callers, with no
selected endpoint. No base-change or mu invariance oracle is assumed.
Source-only and uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.OmegaQuotient

open Support
open PublicEpsilonUnboundedIota (Restricted fullList)
open BoundedContextIota.OmegaQuotient
  (atomTerm quotientWord quotientWord_primrec quotientTerm quotientTerm_primrec
   limitWord finiteOffset limitTerm limitTerm_primrec finiteOffset_primrec)
open BoundedContextIota.OmegaQuotient.Support
  (quotient_map_normal mul_principalSum_map selected_normal unit_sum unit_partition principalSum_limit_zero)
open Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.OmegaQuotient
  (wordHeight wordHeight_mem unitTest unitTest_exact selectUnits selectUnits_mem)

abbrev argumentCode := Localization.argumentCode

def deltaCode (root : Nat) : Nat := Decomposition.highCode 0 (argumentCode root)

theorem argumentCode_primrec : Primrec argumentCode :=
  BoundedContextIota.OmegaQuotient.argumentCode_primrec

theorem deltaCode_primrec : Primrec deltaCode :=
  BoundedContextIota.OmegaQuotient.deltaCode_primrec

theorem high_atom_spec (q root c : Nat) (ha : PublicEpsilonUnboundedIota.rootCheck q root = true)
    (hc : Decomposition.inputCheck q c = true)
    (hr : Restricted q root (ThetaCourse.rawTree c)) (t : RelativeTerm Nat)
    (ht : t ∈ Decomposition.highWord 0 c) :
    check q (atomTerm q t) = true ∧
      Comparison.Normal q (atomTerm q t) ∧ Restricted q root (atomTerm q t) ∧
      0 < denote q (atomTerm q t) ∧
      Ordinal.IsPrincipal (· + ·) (denote q (atomTerm q t)) ∧
      omegaSequence (base q) 1 * denote q (atomTerm q t) =
        denote q t := by
  have hm := (Decomposition.highWord_mem 0 c t).mp ht
  have hs := (Decomposition.word_spec q c hc).1 t hm.1
  have htRest := atoms_restricted q root (ThetaCourse.rawTree c) hr t hm.1
  rcases Comparison.atoms_shape (ThetaCourse.rawTree c) t hm.1 with ⟨p, rfl⟩ | ⟨k, u, rfl⟩
  · have hb := hm.2
    simp only [Decomposition.above, RelativeTerm.outerSort, Nat.zero_add,
      decide_false, Bool.false_eq_true] at hb
  · cases k with
    | zero =>
      have hb := hm.2
      simp only [Decomposition.above, RelativeTerm.outerSort, Nat.zero_add,
        Nat.lt_irrefl, decide_false, Bool.false_eq_true] at hb
    | succ k => exact atom_spec q root k ha u hs.1 hs.2.1 htRest

theorem quotientWord_normal (q root c : Nat) (ha : PublicEpsilonUnboundedIota.rootCheck q root = true)
    (hc : Decomposition.inputCheck q c = true)
    (hr : Restricted q root (ThetaCourse.rawTree c)) :
    IsAdditiveNormalForm ((quotientWord q c).map (denote q)) := by
  apply quotient_map_normal q (omegaSequence (base q) 1)
    (omegaSequence_isSuccLimit (base q) 0).bot_lt (atomTerm q)
    (Decomposition.highWord 0 c) (Decomposition.words_normal q 0 c hc).1
  intro t ht
  have hs := high_atom_spec q root c ha hc hr t ht
  exact ⟨hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2⟩

theorem quotientWord_good (q root c : Nat) (ha : PublicEpsilonUnboundedIota.rootCheck q root = true)
    (hc : Decomposition.inputCheck q c = true)
    (hr : Restricted q root (ThetaCourse.rawTree c)) :
    Normalization.GoodAtoms q (wordHeight (quotientWord q c)) (quotientWord q c) := by
  intro t ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  have hs := high_atom_spec q root c ha hc hr u hu
  exact ⟨Comparison.checked_admissible _ _ _ hs.1 (wordHeight_mem _ _ ht),
    hs.2.1, hs.2.2.2.1, hs.2.2.2.2.1⟩

theorem quotientTerm_spec (q root c : Nat) (ha : PublicEpsilonUnboundedIota.rootCheck q root = true)
    (hc : Decomposition.inputCheck q c = true)
    (hr : Restricted q root (ThetaCourse.rawTree c)) :
    check q (quotientTerm q c) = true ∧
      Comparison.Normal q (quotientTerm q c) ∧ Restricted q root (quotientTerm q c) ∧
      omegaSequence (base q) 1 * denote q (quotientTerm q c) =
        interpretation q (Decomposition.highCode 0 c) := by
  have hg := quotientWord_good q root c ha hc hr
  have had := Normalization.buildAtoms_admissible q _ (source_checked q root ha) _ hg
  refine ⟨Comparison.admitted_checked _ _ (source_checked q root ha) _ had,
    Normalization.buildAtoms_normal _ _ _ hg (quotientWord_normal q root c ha hc hr), ?_, ?_⟩
  · apply buildAtoms_restricted
    intro t ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
    exact (high_atom_spec q root c ha hc hr u hu).2.2.1
  · rw [quotientTerm, Normalization.buildAtoms_denote]
    have hv := mul_principalSum_map q (omegaSequence (base q) 1)
      (atomTerm q) (Decomposition.highWord 0 c) (fun t ht =>
        (high_atom_spec q root c ha hc hr t ht).2.2.2.2.2)
    exact hv.trans (by
      simpa only [Decomposition.highCode, interpretation_code] using
        (Decomposition.parts_word_values q 0 c).1.symm)

theorem limitTerm_spec (q root c : Nat) (ha : PublicEpsilonUnboundedIota.rootCheck q root = true)
    (hc : Decomposition.inputCheck q c = true)
    (hr : Restricted q root (ThetaCourse.rawTree c)) :
    check q (limitTerm q c) = true ∧
      Comparison.Normal q (limitTerm q c) ∧ Restricted q root (limitTerm q c) ∧
      (denote q (limitTerm q c) = 0 ∨ IsSuccLimit (denote q (limitTerm q c))) ∧
      omegaSequence (base q) 1 *
          (denote q (limitTerm q c) + (finiteOffset q c : Ordinal.{0})) =
        interpretation q (Decomposition.highCode 0 c) := by
  have hq := source_checked q root ha
  have hn := quotientWord_normal q root c ha hc hr
  have hs : ∀ t ∈ quotientWord q c, check q t = true ∧ Comparison.Normal q t := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
    have h := high_atom_spec q root c ha hc hr u hu
    exact ⟨h.1, h.2.1⟩
  have hg := quotientWord_good q root c ha hc hr
  have hmem : ∀ t ∈ limitWord q c, t ∈ quotientWord q c := fun t ht =>
    ((selectUnits_mem false q _ t).mp ht).1
  have hgood : Normalization.GoodAtoms q (wordHeight (quotientWord q c)) (limitWord q c) :=
    fun t ht => hg t (hmem t ht)
  have had := Normalization.buildAtoms_admissible q _ hq _ hgood
  refine ⟨Comparison.admitted_checked q _ hq _ had,
    Normalization.buildAtoms_normal q _ _ hgood (selected_normal q false _ hn), ?_, ?_, ?_⟩
  · apply buildAtoms_restricted
    intro t ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp (hmem t ht)
    exact (high_atom_spec q root c ha hc hr u hu).2.2.1
  · rw [limitTerm, Normalization.buildAtoms_denote]
    apply principalSum_limit_zero
    intro p hp
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hp
    have hm := (selectUnits_mem false q _ t).mp ht
    have hp' := hn.1 _ (List.mem_map.mpr ⟨t, hm.1, rfl⟩)
    refine ⟨lt_of_le_of_ne (Order.one_le_iff_pos.mpr hp'.1) ?_, hp'.2⟩
    intro he
    have hut := (unitTest_exact q hq t (hs t hm.1).1 (hs t hm.1).2).mpr he.symm
    have hnot := hm.2
    simp only [Bool.cond_false, hut, Bool.not_true, Bool.false_eq_true] at hnot
  · have hv : denote q (quotientTerm q c) = denote q (limitTerm q c) +
        (finiteOffset q c : Ordinal.{0}) := by
      rw [quotientTerm, Normalization.buildAtoms_denote,
        unit_partition q hq (quotientWord q c) hn hs, List.map_append, principalSum_append,
        unit_sum q hq _ hs]
      rw [limitTerm, Normalization.buildAtoms_denote]
      rfl
    rw [← hv]
    exact (quotientTerm_spec q root c ha hc hr).2.2.2

theorem root_coefficient_spec (q root : Nat) (ha : PublicEpsilonUnboundedIota.rootCheck q root = true) :
    check q (limitTerm q (argumentCode root)) = true ∧
      Comparison.Normal q (limitTerm q (argumentCode root)) ∧
      Restricted q root (limitTerm q (argumentCode root)) ∧
      (denote q (limitTerm q (argumentCode root)) = 0 ∨
        IsSuccLimit (denote q (limitTerm q (argumentCode root)))) ∧
      omegaSequence (base q) 1 *
          (denote q (limitTerm q (argumentCode root)) +
            (finiteOffset q (argumentCode root) : Ordinal.{0})) =
        interpretation q (deltaCode root) :=
  limitTerm_spec q root _ ha (argument_accepted q root ha) (PublicEpsilonUnboundedIota.argument_restricted q root ha)

def coefficientCode (q root : Nat) : Nat :=
  cond (rootCheck q root) (limitTerm q (argumentCode root)).code 0

def coefficientOffset (q root : Nat) : Nat :=
  cond (rootCheck q root) (finiteOffset q (argumentCode root)) 0

theorem coefficientCode_primrec : Primrec₂ coefficientCode :=
  (rootCheck_primrec.cond (code_primrec.comp (limitTerm_primrec.comp Primrec.fst
    (argumentCode_primrec.comp Primrec.snd))) (Primrec.const 0)).to₂

theorem coefficientOffset_primrec : Primrec₂ coefficientOffset :=
  (rootCheck_primrec.cond (finiteOffset_primrec.comp Primrec.fst
    (argumentCode_primrec.comp Primrec.snd)) (Primrec.const 0)).to₂

theorem coefficientCode_literal (q root : Nat) (ha : PublicEpsilonUnboundedIota.rootCheck q root = true) :
    coefficientCode q root = (limitTerm q (argumentCode root)).code := by
  simp only [coefficientCode, ha, Bool.cond_true]

theorem coefficientOffset_literal (q root : Nat) (ha : PublicEpsilonUnboundedIota.rootCheck q root = true) :
    coefficientOffset q root = finiteOffset q (argumentCode root) := by
  simp only [coefficientOffset, ha, Bool.cond_true]

theorem coefficientCode_accepted (q root : Nat) (ha : PublicEpsilonUnboundedIota.rootCheck q root = true) :
    Comparison.acceptedCode q (coefficientCode q root) = true := by
  have hs := root_coefficient_spec q root ha
  rw [coefficientCode_literal q root ha]
  exact (Comparison.acceptedCode_exact _ _).mpr
    ⟨by simpa only [checkCode_code] using hs.1,
      by simpa only [ThetaCourse.rawTree_code] using hs.2.1⟩

theorem coefficient_iota_input (q root : Nat) (ha : PublicEpsilonUnboundedIota.rootCheck q root = true) :
    PublicEpsilonUnboundedIota.inputCheck q root (coefficientCode q root) = true := by
  have hs := root_coefficient_spec q root ha
  apply (PublicEpsilonUnboundedIota.inputCheck_exact q root _).mpr
  refine ⟨ha, limitTerm q (argumentCode root), coefficientCode_literal q root ha,
    hs.1, hs.2.1, ?_⟩
  exact (PublicEpsilonUnboundedIota.restricted_iff_sourceStar q root ha _ hs.1 hs.2.1).mp hs.2.2.1

theorem coefficientCode_spec (q root : Nat) (ha : PublicEpsilonUnboundedIota.rootCheck q root = true) :
    Comparison.acceptedCode q (coefficientCode q root) = true ∧
      PublicEpsilonUnboundedIota.inputCheck q root (coefficientCode q root) = true ∧
      (interpretation q (coefficientCode q root) = 0 ∨
        IsSuccLimit (interpretation q (coefficientCode q root))) ∧
      omegaSequence (base q) 1 *
          (interpretation q (coefficientCode q root) + (coefficientOffset q root : Ordinal.{0})) =
        interpretation q (deltaCode root) := by
  have hs := root_coefficient_spec q root ha
  refine ⟨coefficientCode_accepted q root ha, coefficient_iota_input q root ha, ?_, ?_⟩
  · simpa only [coefficientCode_literal q root ha, interpretation_code] using hs.2.2.2.1
  · simpa only [coefficientCode_literal q root ha, coefficientOffset_literal q root ha,
      interpretation_code] using hs.2.2.2.2

theorem coefficientCode_rejected (q root : Nat) (ha : PublicEpsilonUnboundedIota.rootCheck q root = false) :
    coefficientCode q root = 0 ∧ coefficientOffset q root = 0 := by
  constructor
  · simp only [coefficientCode, ha, Bool.cond_false]
  · simp only [coefficientOffset, ha, Bool.cond_false]

theorem coefficient_below_second (q root : Nat) (ha : PublicEpsilonUnboundedIota.rootCheck q root = true) :
    interpretation q (coefficientCode q root) <
      omegaSequence (base q) 2 := by
  have hs := coefficientCode_spec q root ha
  have hΩ : 1 ≤ omegaSequence (base q) 1 :=
    Order.one_le_iff_pos.mpr (omegaSequence_isSuccLimit (base q) 0).bot_lt
  have hle : interpretation q (coefficientCode q root) ≤
      interpretation q (deltaCode root) := by
    calc
      interpretation q (coefficientCode q root) ≤
          interpretation q (coefficientCode q root) + (coefficientOffset q root : Ordinal.{0}) :=
        le_self_add
      _ = 1 * (interpretation q (coefficientCode q root) +
          (coefficientOffset q root : Ordinal.{0})) := (one_mul _).symm
      _ ≤ omegaSequence (base q) 1 *
          (interpretation q (coefficientCode q root) + (coefficientOffset q root : Ordinal.{0})) :=
        mul_le_mul' hΩ le_rfl
      _ = interpretation q (deltaCode root) := hs.2.2.2
  have hd : interpretation q (deltaCode root) ≤
      interpretation q (argumentCode root) := by
    rw [deltaCode,
      (Decomposition.parts_code_value q 0 (argumentCode root)
        (argument_accepted q root ha)).1]
    exact Ordinal.mul_div_le _ _
  obtain ⟨t, he, ht, hn, hhigh⟩ := (PublicEpsilonUnboundedIota.rootCheck_exact q root).mp ha
  have hsort : interpretation q (argumentCode root) <
      omegaSequence (base q) 2 := by
    simpa only [argumentCode, he, Localization.argumentCode_theta, interpretation_code] using
      FixedPoint.checked_theta_sort q 0 t ht
  exact (hle.trans hd).trans_lt hsort

theorem coefficient_iota_low (q root : Nat) (ha : PublicEpsilonUnboundedIota.rootCheck q root = true) :
    lowCheckCode (PublicEpsilonUnboundedIota.betaCode q root) (PublicEpsilonUnboundedIota.literalCode q root (coefficientCode q root)) = true ∧
      Comparison.acceptedCode (PublicEpsilonUnboundedIota.betaCode q root) (PublicEpsilonUnboundedIota.literalCode q root (coefficientCode q root)) = true := by
  let t := limitTerm q (argumentCode root)
  have hs := root_coefficient_spec q root ha
  have hi := coefficient_iota_input q root ha
  have hsort : t.outerSort ≤ 2 :=
    (denote_lt_iff_outerSort_le q t hs.1 2 (by omega)).mp (by
      simpa only [coefficientCode_literal q root ha, interpretation_code] using coefficient_below_second q root ha)
  have htransform := PublicEpsilonUnboundedIota.transform_checked q root ha t hs.1 hs.2.2.1
  have hnormal := PublicEpsilonUnboundedIota.transform_normal q root ha t hs.1 hs.2.1 hs.2.2.1
  have houter : (PublicEpsilonUnboundedIota.transform q root t).outerSort ≤ 1 := by
    have h := PublicEpsilonUnboundedIota.transform_outerSort q root ha t hs.1 hs.2.2.1
    omega
  have he : PublicEpsilonUnboundedIota.literalCode q root (coefficientCode q root) = (PublicEpsilonUnboundedIota.transform q root t).code := by
    simp only [PublicEpsilonUnboundedIota.literalCode, hi, Bool.cond_true, coefficientCode_literal q root ha, PublicEpsilonUnboundedIota.stateCode_code]
  rw [he]
  refine ⟨?_, (Comparison.acceptedCode_exact _ _).mpr
    ⟨by simpa only [checkCode_code] using htransform,
      by simpa only [ThetaCourse.rawTree_code] using hnormal⟩⟩
  simp only [lowCheckCode_code, lowCheck, htransform, houter, decide_true, Bool.true_and]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.OmegaQuotient
