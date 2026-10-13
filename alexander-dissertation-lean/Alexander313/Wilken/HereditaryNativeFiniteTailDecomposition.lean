import Alexander313.Wilken.HereditaryNativeOmegaQuotient
import Alexander313.Wilken.PublicEpsilonNativePowerBaseChangeSupport
import Alexander313.Wilken.LimitFiniteDecomposition

/-!
# Actual finite-tail decomposition at every native epsilon base

The original checked word is normalized by the real finite normalizer. Its
complete additive normal form has all unit atoms at the right. The actual
unit comparator selects those atoms and counts them; the remaining word
is built into an admitted normal zero-or-limit expression. The finite tail
and its numerical code are computed from the original input, with no
public-return or decomposition witness supplied. Source-only uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.FiniteTailDecomposition

open OmegaQuotient (unitTest unitTest_exact selectUnits selectUnits_primrec
  selectUnits_filter selectUnits_mem)

private theorem selectUnits_all (q : Nat) (as : List (RelativeTerm Nat))
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

private theorem unit_partition (q : Nat) (hq : baseCheck q = true) (as : List (RelativeTerm Nat))
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

private theorem selected_normal (q : Nat) (units : Bool) (as : List (RelativeTerm Nat))
    (hn : IsAdditiveNormalForm (as.map (denote q))) :
    IsAdditiveNormalForm ((selectUnits units q as).map (denote q)) := by
  rw [selectUnits_filter]
  have hbase : (as.filter (fun t => cond units (unitTest q t) (!unitTest q t))).Sublist as :=
    List.filter_sublist
  have hsub := hbase.map (denote q)
  exact ⟨fun p hp => hn.1 p (hsub.subset hp), hn.2.sublist hsub⟩

private theorem unit_sum (q : Nat) (hq : baseCheck q = true) (as : List (RelativeTerm Nat))
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

private theorem principalSum_limit_zero (as : List Ordinal.{0})
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

def limitWord (q c : Nat) : List (RelativeTerm Nat) :=
  selectUnits false q (Arithmetic.normalizedWord q c)

def offset (q c : Nat) : Nat :=
  (selectUnits true q (Arithmetic.normalizedWord q c)).length

def limitTerm (q c : Nat) : RelativeTerm Nat := Normalization.buildAtoms (limitWord q c)

def lambdaCode (q c : Nat) : Nat := (limitTerm q c).code

theorem limitWord_primrec : Primrec₂ limitWord :=
  (selectUnits_primrec.comp (((Primrec.const false).pair Primrec.fst).pair
    Arithmetic.normalizedWord_primrec)).to₂

theorem offset_primrec : Primrec₂ offset :=
  (Primrec.list_length.comp (selectUnits_primrec.comp
    (((Primrec.const true).pair Primrec.fst).pair Arithmetic.normalizedWord_primrec))).to₂

theorem lambdaCode_primrec : Primrec₂ lambdaCode :=
  (code_primrec.comp (Normalization.Effective.buildAtoms_primrec.comp limitWord_primrec)).to₂

/-- Actual input admission alone supplies a normal lambda, its genuine
zero-or-proper-limit status, and the entire original finite-tail equation. -/
theorem lambdaCode_spec (q c : Nat) (hc : checkCode q c = true) :
    Comparison.acceptedCode q (lambdaCode q c) = true ∧
      (interpretation q (lambdaCode q c) = 0 ∨ IsSuccLimit (interpretation q (lambdaCode q c))) ∧
      interpretation q c = interpretation q (lambdaCode q c) + (offset q c : Ordinal.{0}) := by
  have hq := (Bool.and_eq_true.mp (Arithmetic.raw_checked q c hc)).1
  have hn := Arithmetic.normalizedWord_normal q c hc
  have hs := (Arithmetic.normalizedWord_spec q c hc).1
  have hmem : ∀ t ∈ limitWord q c, t ∈ Arithmetic.normalizedWord q c :=
    fun t ht => ((selectUnits_mem false q _ t).mp ht).1
  have hg : Normalization.GoodAtoms q (heightCode c) (limitWord q c) :=
    fun t ht => Arithmetic.normalizedWord_good q (heightCode c) c hc le_rfl t (hmem t ht)
  have had := Normalization.buildAtoms_admissible q _ hq _ hg
  have hnormal := Normalization.buildAtoms_normal q _ _ hg (selected_normal q false _ hn)
  have hchecked := Comparison.admitted_checked q _ hq _ had
  have haccepted : Comparison.acceptedCode q (lambdaCode q c) = true := by
    apply (Comparison.acceptedCode_exact q _).mpr
    exact ⟨by simpa only [lambdaCode, limitTerm, checkCode_code] using hchecked,
      by simpa only [lambdaCode, limitTerm, ThetaCourse.rawTree_code] using hnormal⟩
  refine ⟨haccepted, ?_, ?_⟩
  · simp only [lambdaCode, interpretation_code, limitTerm, Normalization.buildAtoms_denote]
    apply principalSum_limit_zero
    intro p hp
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hp
    have hm := (selectUnits_mem false q _ t).mp ht
    have hps := hn.1 _ (List.mem_map.mpr ⟨t, hm.1, rfl⟩)
    refine ⟨lt_of_le_of_ne (Order.one_le_iff_pos.mpr hps.1) ?_, hps.2⟩
    intro he
    have hu := (unitTest_exact q hq t (hs t hm.1).1 (hs t hm.1).2.1).mpr he.symm
    have hnot := hm.2
    simp only [Bool.cond_false, hu, Bool.not_true, Bool.false_eq_true] at hnot
  · have hv : interpretation q c =
        principalSum ((Arithmetic.normalizedWord q c).map (denote q)) := by
      rw [(Arithmetic.normalizedWord_spec q c hc).2, principalSum_canonicalANF]
    rw [hv, unit_partition q hq _ hn (fun t ht => ⟨(hs t ht).1, (hs t ht).2.1⟩),
      List.map_append, principalSum_append,
      unit_sum q hq _ (fun t ht => ⟨(hs t ht).1, (hs t ht).2.1⟩)]
    simp only [lambdaCode, interpretation_code, limitTerm, Normalization.buildAtoms_denote,
      limitWord, offset]

theorem lambdaCode_le (q c : Nat) (hc : checkCode q c = true) :
    interpretation q (lambdaCode q c) ≤ interpretation q c := by
  rw [(lambdaCode_spec q c hc).2.2]
  exact le_self_add

theorem lambdaCode_low (q c : Nat) (hc : lowCheckCode q c = true) :
    lowCheckCode q (lambdaCode q c) = true := by
  have hi := HeightBoundary.input_spec q c hc
  exact OmegaPowers.low_of_bound q _
    ((Comparison.acceptedCode_exact q _).mp (lambdaCode_spec q c hi.1).1).1
    ((lambdaCode_le q c hi.1).trans_lt hi.2.2)

private theorem selectUnits_context (q v : Nat) (units : Bool) (as : List (RelativeTerm Nat)) :
    selectUnits units q as = selectUnits units v as := by
  have he : unitTest q = unitTest v := funext fun t =>
    BaseTransformation.equal_context q v t (ThetaCourse.rawTree LogEndZero.unitCode)
  simp only [selectUnits_filter, he]

theorem lambdaCode_context (q v c : Nat) (hcq : checkCode q c = true)
    (hcv : checkCode v c = true) : lambdaCode q c = lambdaCode v c := by
  simp only [lambdaCode, limitTerm, limitWord,
    OmegaPowers.BaseChange.normalizedWord_context q v c hcq hcv, selectUnits_context q v false]

theorem offset_context (q v c : Nat) (hcq : checkCode q c = true)
    (hcv : checkCode v c = true) : offset q c = offset v c := by
  simp only [offset, OmegaPowers.BaseChange.normalizedWord_context q v c hcq hcv,
    selectUnits_context q v true]

/-- The computed finite decomposition is value invariant at the same
actual base because zero-or-limit plus a finite tail is unique. -/
theorem decomposition_value_invariant (q c d : Nat) (hc : checkCode q c = true)
    (hd : checkCode q d = true) (he : interpretation q c = interpretation q d) :
    interpretation q (lambdaCode q c) = interpretation q (lambdaCode q d) ∧
      offset q c = offset q d := by
  have hs := lambdaCode_spec q c hc
  have ht := lambdaCode_spec q d hd
  exact LimitFiniteDecomposition.coefficient_unique _ _ _ _ hs.2.1 ht.2.1
    (hs.2.2.symm.trans (he.trans ht.2.2))

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.FiniteTailDecomposition
