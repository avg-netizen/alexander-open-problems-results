import Alexander313.Wilken.PublicEpsilonNativeLocalization
import Alexander313.Wilken.HereditaryFinePredecessor
import Alexander313.Wilken.HereditaryNativeRelativeZetaSupport

/-!
# Genuine fine-predecessor ANF prefix at the literal original coded epsilon

The original native weak Normal word is cut at Omega1. Removing its final
positive LOW atom preserves the same source fragment and derives a checked
Normal theta-zero prefix. The actual unit and STRICT recognizers implement
the two printed first cases; the remaining branch uses the genuine computed
ordinary localization. No predecessor, cutoff or gap is supplied. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceFinePredecessor

open ThetaCourse SourceLocalization
open Normalization (buildAtoms buildAtoms_denote buildAtoms_normal buildAtoms_admissible GoodAtoms zeroTree)

open Hereditary.FinePredecessor (stripLast stripLast_primrec stripLast_split stripLast_mem)

private theorem stripLast_nil {α : Type} : stripLast ([] : List α) = [] := rfl

private theorem anf_prefix {α : Type} (f : α → Ordinal.{0}) (as bs : List α)
    (hn : IsAdditiveNormalForm ((as ++ bs).map f)) : IsAdditiveNormalForm (as.map f) := by
  rw [List.map_append] at hn
  exact ⟨fun p hp => hn.1 p (List.mem_append_left _ hp), (List.pairwise_append.mp hn.2).1⟩

def lowWord (q c : Nat) : List (RelativeTerm Nat) :=
  Decomposition.lowWord 0 (SourceLocalization.argumentCode c)

def highWord (q c : Nat) : List (RelativeTerm Nat) :=
  Decomposition.highWord 0 (SourceLocalization.argumentCode c)

def prefixWord (q c : Nat) : List (RelativeTerm Nat) := highWord q c ++ stripLast (lowWord q c)

def prefixArgument (q c : Nat) : RelativeTerm Nat := buildAtoms (prefixWord q c)

def prefixCode (q c : Nat) : Nat := (prefixArgument q c).code

def prefixNode (q c : Nat) : Nat := (.theta 0 (prefixArgument q c) : RelativeTerm Nat).code

def lastAtom (q c : Nat) : RelativeTerm Nat := (lowWord q c).reverse.head?.getD (zeroTree)

def unitCode (q : Nat) : Nat := OmegaPowerHeight.numeralCode 1

theorem unitCode_primrec : Primrec unitCode := Primrec.const _

theorem unitCode_spec (q : Nat) (hq : baseCheck q = true) :
    Comparison.acceptedCode q (unitCode q) = true ∧ interpretation q (unitCode q) = 1 := by
  have hs := OmegaPowerHeight.numeralCode_spec q 1 hq
  exact ⟨hs.2.1, by simpa only [unitCode, Nat.cast_one] using hs.2.2.1⟩

theorem argument_accepted (q c : Nat) (hc : SourceLocalization.Node q c) :
    Decomposition.inputCheck q (SourceLocalization.argumentCode c) = true :=
  SourceLocalization.node_argument q c hc

noncomputable def delta (q c : Nat) : Ordinal.{0} :=
  interpretation q (Decomposition.highCode 0 (SourceLocalization.argumentCode c))

noncomputable def residual (q c : Nat) : Ordinal.{0} :=
  interpretation q (Decomposition.lowCode 0 (SourceLocalization.argumentCode c))

noncomputable def prefixResidual (q c : Nat) : Ordinal.{0} :=
  principalSum ((stripLast (lowWord q c)).map (denote q))

theorem argument_parts (q c : Nat) (hc : SourceLocalization.Node q c) :
    delta q c + residual q c = SourceLocalization.argumentValue q c ∧
      residual q c < omegaSequence (base q) 1 ∧
      omegaSequence (base q) 1 ∣ delta q c := by
  have ha := argument_accepted q c hc
  exact ⟨Decomposition.parts_reconstruct q 0 _ ha,
    Decomposition.lowPart_bound q 0 _ ha, Decomposition.highPart_dvd q 0 _ ha⟩

theorem prefixCode_value (q c : Nat) :
    interpretation q (prefixCode q c) = delta q c + prefixResidual q c := by
  rw [prefixCode, interpretation_code, prefixArgument, buildAtoms_denote, prefixWord,
    List.map_append, principalSum_append]
  rw [delta, Decomposition.highCode, interpretation_code, Decomposition.highPartTerm,
    buildAtoms_denote]
  rfl

theorem low_split (q c : Nat) (hc : SourceLocalization.Node q c) (he : lowWord q c ≠ []) :
    lowWord q c = stripLast (lowWord q c) ++ [lastAtom q c] ∧
      check q (lastAtom q c) = true ∧ Comparison.Normal q (lastAtom q c) ∧
      0 < denote q (lastAtom q c) ∧ Ordinal.IsPrincipal (· + ·) (denote q (lastAtom q c)) ∧
      residual q c = prefixResidual q c + denote q (lastAtom q c) := by
  obtain ⟨a, hs, hl⟩ := stripLast_split (lowWord q c) he
  have heq : lastAtom q c = a := by simp only [lastAtom, hl, Option.getD_some]
  have ham : a ∈ lowWord q c := by rw [hs]; simp
  have haw := (Decomposition.lowWord_mem 0 _ a).mp ham
  have ha := (Decomposition.word_spec q _ (argument_accepted q c hc)).1 a haw.1
  refine ⟨by simpa only [heq] using hs, by simpa only [heq] using ha.1,
    by simpa only [heq] using ha.2.1, by simpa only [heq] using ha.2.2.1,
    by simpa only [heq] using ha.2.2.2, ?_⟩
  rw [residual, Decomposition.lowCode, interpretation_code,
    (Decomposition.parts_word_values q 0 _).2]
  change principalSum ((lowWord q c).map (denote q)) = _
  rw [hs, List.map_append, principalSum_append]
  simp only [List.map_cons, List.map_nil, principalSum, add_zero, heq, prefixResidual]

theorem prefix_residual_lt (q c : Nat) (hc : SourceLocalization.Node q c) (he : lowWord q c ≠ []) :
    prefixResidual q c < residual q c := by
  have hs := low_split q c hc he
  rw [hs.2.2.2.2.2]
  exact lt_add_of_pos_right _ hs.2.2.2.1

theorem low_split_normal (q c : Nat) (hc : SourceLocalization.Node q c) (he : lowWord q c ≠ []) :
    SourceNormalSum (residual q c) (prefixResidual q c) (denote q (lastAtom q c)) := by
  have hs := low_split q c hc he
  have hn := (Decomposition.words_normal q 0 _ (argument_accepted q c hc)).2
  change IsAdditiveNormalForm ((lowWord q c).map (denote q)) at hn
  rw [hs.1, List.map_append, List.map_cons, List.map_nil] at hn
  refine Or.inr ⟨(stripLast (lowWord q c)).map (denote q), hn, rfl, ?_⟩
  rw [principalSum_append]
  simpa only [principalSum, add_zero, prefixResidual] using hs.2.2.2.2.2.symm

theorem prefix_normal (q c : Nat) (hc : SourceLocalization.Node q c) :
    Comparison.Normal q (prefixArgument q c) := by
  have ha := argument_accepted q c hc
  let n := SourceOne.PublicCodes.fragment (ThetaCourse.rawTree (SourceLocalization.argumentCode c))
  have hg := Decomposition.word_good q n _ ha (SourceOne.PublicCodes.height_le_fragment _)
  have hp : ∀ a ∈ prefixWord q c, a ∈ Decomposition.word (SourceLocalization.argumentCode c) := by
    intro a ham
    rcases List.mem_append.mp ham with ham | ham
    · exact (Decomposition.highWord_mem 0 _ a).mp ham |>.1
    · exact (Decomposition.lowWord_mem 0 _ a).mp (stripLast_mem _ _ ham) |>.1
  have hgood : GoodAtoms q n (prefixWord q c) := fun a ham => hg a (hp a ham)
  have hn : IsAdditiveNormalForm ((prefixWord q c).map (denote q)) := by
    by_cases he : lowWord q c = []
    · simpa only [prefixWord, he, stripLast_nil, List.append_nil, highWord] using
        (Decomposition.words_normal q 0 _ ha).1
    · obtain ⟨a, hs, _⟩ := stripLast_split (lowWord q c) he
      have hw : Decomposition.word (SourceLocalization.argumentCode c) = prefixWord q c ++ [a] := by
        rw [Decomposition.word_partition q 0 _ ha]
        change highWord q c ++ lowWord q c = _
        rw [hs, ← List.append_assoc]; rfl
      have hn := Decomposition.word_normal q _ ha
      rw [hw] at hn
      exact anf_prefix (denote q) _ _ hn
  exact buildAtoms_normal q n _ hgood hn

/-- Rebuilding a prefix retains the original finite fragment, not just a
larger direct-limit presentation. -/
theorem prefix_admissible (q n c : Nat) (hc : SourceLocalization.Node q c)
    (hh : (ThetaCourse.rawTree (SourceLocalization.argumentCode c)).height ≤ n) :
    admissible q n (prefixArgument q c) := by
  have hg := Decomposition.words_good q n 0 _ (argument_accepted q c hc) hh
  apply buildAtoms_admissible q n (node_baseCheck q c hc)
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact hg.1 a ha
  · exact hg.2 a (stripLast_mem _ _ ha)

theorem prefix_checked (q c : Nat) (hc : SourceLocalization.Node q c) :
    checkCode q (prefixCode q c) = true ∧ Comparison.Normal q (ThetaCourse.rawTree (prefixCode q c)) := by
  let n := SourceOne.PublicCodes.fragment (ThetaCourse.rawTree (SourceLocalization.argumentCode c))
  have ha := prefix_admissible q n c hc (SourceOne.PublicCodes.height_le_fragment _)
  simpa only [prefixCode, checkCode_code, ThetaCourse.rawTree_code] using
    And.intro (Comparison.admitted_checked q n (node_baseCheck q c hc) _ ha) (prefix_normal q c hc)

theorem prefix_sort (q c : Nat) (hc : SourceLocalization.Node q c) (he : lowWord q c ≠ []) :
    interpretation q (prefixCode q c) < omegaSequence (base q) 2 := by
  have hs := argument_parts q c hc
  have hp := add_lt_add_right (prefix_residual_lt q c hc he) (delta q c)
  rw [← prefixCode_value q c, hs.1] at hp
  obtain ⟨a, heq, hcheck, hn⟩ := hc
  have hb : SourceLocalization.argumentValue q c < omegaSequence (base q) 2 := by
    simpa only [heq, SourceLocalization.argumentValue, SourceLocalization.argumentCode_theta, interpretation_code] using
      FixedPoint.checked_theta_sort q 0 a hcheck
  exact hp.trans hb

theorem prefix_node (q c : Nat) (hc : SourceLocalization.Node q c) (he : lowWord q c ≠ []) :
    SourceLocalization.Node q (prefixNode q c) := by
  have hp := prefix_checked q c hc
  have hcheck : check q (prefixArgument q c) = true := by
    simpa only [prefixCode, checkCode_code] using hp.1
  exact ⟨prefixArgument q c, rfl, SourceChi.Powers.checked_theta_zero q _ hcheck
    (by simpa only [prefixCode, interpretation_code] using prefix_sort q c hc he),
    prefix_normal q c hc⟩

private theorem global_same_high_strict (tau : Ordinal.{0}) (htau : 0 < tau)
    (d : GlobalNotationOrdinal tau 1) (hds : d.val < omegaSequence tau 2)
    (hdd : omegaSequence tau 1 ∣ d.val) (eta rho : Ordinal.{0})
    (her : eta < rho) (hr : rho < omegaSequence tau 1) :
    globalCollapse tau 0 (d.val + eta) < globalCollapse tau 0 (d.val + rho) := by
  obtain ⟨n, h1n, hd⟩ := globalNotation_finite_witness tau htau 1 d.property
  have hn : 0 < n := (Nat.zero_le 1).trans_lt h1n
  let dn : SourceNotationOrdinal tau n 1 := ⟨d.val, hd⟩
  let a := SourceHighPartComparison.residualArgument tau n 0 hn dn eta (her.trans hr)
  let b := SourceHighPartComparison.residualArgument tau n 0 hn dn rho hr
  have ha : a.val < omegaSequence tau 2 :=
    SourceFixedPointLimits.shiftArgument_sort tau n 0 hn dn hds eta (her.trans hr)
  have hb : b.val < omegaSequence tau 2 :=
    SourceFixedPointLimits.shiftArgument_sort tau n 0 hn dn hds rho hr
  have hab := SourceHighPartComparison.same_high_part_strict tau htau n 0 hn dn hds hdd eta rho her hr
  have had := source_finite_notation_sorted_lt_boundary tau htau n 1 1 le_rfl h1n a.property ha
  have hbd := source_finite_notation_sorted_lt_boundary tau htau n 1 1 le_rfl h1n b.property hb
  rw [globalCollapse_finite_agreement tau htau n 0 hn _ had,
    globalCollapse_finite_agreement tau htau n 0 hn _ hbd]
  exact hab

theorem prefix_strict (q c : Nat) (hc : SourceLocalization.Node q c) (he : lowWord q c ≠ []) :
    SourceLocalization.value q (prefixNode q c) < SourceLocalization.value q c := by
  have ha := argument_accepted q c hc
  have hparts := argument_parts q c hc
  have hdcheck := (Decomposition.parts_checked q 0 _ ha).1
  let d := FixedPoint.sourceOrdinal q 0 (Decomposition.highPartTerm 0
    (SourceLocalization.argumentCode c)) hdcheck
  have hdv : d.val = delta q c := by simp only [d, FixedPoint.sourceOrdinal,
    delta, Decomposition.highCode, interpretation_code]
  have hds : d.val < omegaSequence (base q) 2 := by
    rw [hdv]
    obtain ⟨a, heq, hcheck, _⟩ := hc
    have hab : SourceLocalization.argumentValue q c < omegaSequence (base q) 2 := by
      simpa only [heq, SourceLocalization.argumentValue, SourceLocalization.argumentCode_theta, interpretation_code] using
        FixedPoint.checked_theta_sort q 0 a hcheck
    exact (Decomposition.parts_le q 0 _ ha).1.trans_lt hab
  have hp := global_same_high_strict (base q) (base_pos q (node_baseCheck q c hc)) d hds
    (by simpa only [hdv] using hparts.2.2) _ _ (prefix_residual_lt q c hc he) hparts.2.1
  rw [hdv, ← prefixCode_value q c, hparts.1] at hp
  obtain ⟨a, heq, _, _⟩ := hc
  simpa only [SourceLocalization.value, prefixNode, interpretation_code, denote, eval,
    prefixCode, heq, SourceLocalization.argumentValue, SourceLocalization.argumentCode_theta] using hp

def penultimate (xs : List Nat) : Nat := (xs.reverse[1]?).getD 0

theorem penultimate_primrec : Primrec penultimate :=
  Primrec.option_getD.comp (Primrec.list_getElem?.comp (Primrec.list_reverse.comp Primrec.id)
    (Primrec.const 1)) (Primrec.const 0)

private theorem last_two (xs : List Nat) (h : 2 ≤ xs.length) :
    ∃ pre a b, xs = pre ++ [a, b] := by
  cases he : xs.reverse with
  | nil => have hl := congrArg List.length he; simp at hl; omega
  | cons b bs =>
    cases hs : bs with
    | nil => have hl := congrArg List.length he; simp only [List.length_reverse, hs,
        List.length_cons, List.length_nil] at hl; omega
    | cons a pre =>
      refine ⟨pre.reverse, a, b, ?_⟩
      have hr := congrArg List.reverse he
      simpa only [List.reverse_reverse, hs, List.reverse_cons, List.reverse_nil,
        List.append_assoc, List.singleton_append] using hr

private theorem endpoint_append_last (xs : List Nat) (a : Nat) : SourceLocalization.endpoint (xs ++ [a]) = a := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    cases bs with
    | nil => rfl
    | cons d ds => exact ih

theorem localization_length (q c : Nat) (hc : SourceLocalization.Node q c)
    (hb : base q < SourceLocalization.value q c) : 2 ≤ (SourceLocalization.nativePath q c).length := by
  have hi := (SourceLocalization.inputCheck_exact q c).mpr hc
  obtain ⟨tail, ht⟩ := SourceLocalization.nativePath_head q c
  cases tail with
  | nil =>
    have he := SourceLocalization.nativePath_end q c hi
    rw [ht] at he
    change SourceLocalization.value q (SourceLocalization.baseRaw q) = SourceLocalization.value q c at he
    rw [SourceLocalization.baseRaw_value q (node_baseCheck q c hc)] at he
    exact False.elim ((ne_of_lt hb) he)
  | cons d ds => simp only [ht, List.length_cons]; omega

def fallback (q c : Nat) : Nat := penultimate (SourceLocalization.nativePath q c)

theorem fallback_spec (q c : Nat) (hc : SourceLocalization.Node q c)
    (hb : base q < SourceLocalization.value q c) :
    SourceLocalization.Node q (fallback q c) ∧ base q ≤ SourceLocalization.value q (fallback q c) ∧
      SourceLocalization.value q (fallback q c) < SourceLocalization.value q c := by
  have hi := (SourceLocalization.inputCheck_exact q c).mpr hc
  obtain ⟨pre, a, b, hs⟩ := last_two _ (localization_length q c hc hb)
  have hf : fallback q c = a := by simp only [fallback, penultimate, hs,
    List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
  have han := SourceLocalization.nativePath_nodes q c hi a (by rw [hs]; simp)
  have he : SourceLocalization.value q b = SourceLocalization.value q c := by
    have ht := SourceLocalization.nativePath_end q c hi
    have heq : pre ++ [a, b] = (pre ++ [a]) ++ [b] := by simp only [List.append_assoc, List.singleton_append]
    rwa [hs, heq, endpoint_append_last] at ht
  have hp := SourceLocalization.nativePath_strict q c hi
  rw [hs, List.map_append] at hp
  have hpab := (List.pairwise_append.mp hp).2.1
  have hab : SourceLocalization.value q a < SourceLocalization.value q b :=
    (List.pairwise_cons.mp hpab).1 _ (by simp)
  rw [hf]
  exact ⟨han, by simpa only [SourceLocalization.baseRaw_value q (node_baseCheck q a han)] using SourceLocalization.baseRaw_le q a han,
    hab.trans_eq he⟩

def inputCheck (q c : Nat) : Bool :=
  SourceLocalization.inputCheck q c && Normalization.lessRawCode q (SourceLocalization.baseRaw q) c

theorem inputCheck_exact (q c : Nat) : inputCheck q c = true ↔
    SourceLocalization.Node q c ∧ base q < SourceLocalization.value q c := by
  rw [inputCheck, Bool.and_eq_true, SourceLocalization.inputCheck_exact]
  apply and_congr_right
  intro hc
  simpa only [SourceLocalization.baseRaw_value q (node_baseCheck q c hc)] using
    SourceLocalization.value_less_exact q _ c
      (SourceLocalization.baseRaw_node q (node_baseCheck q c hc)) hc

def firstBranch (q c : Nat) : Bool :=
  !(lowWord q c).isEmpty && (Normalization.equalRawCode q (lastAtom q c).code (unitCode q) ||
    FixedPoint.strictRawCode q 0 (prefixCode q c))

noncomputable def FirstCase (q c : Nat) : Prop := lowWord q c ≠ [] ∧
  (denote q (lastAtom q c) = 1 ∨ prefixResidual q c <
    SourceFixedPointLimits.globalResidualImageSup (base q) 0 (delta q c) (prefixResidual q c))

theorem prefix_divmod (q c : Nat) (hc : SourceLocalization.Node q c) (he : lowWord q c ≠ []) :
    FixedPoint.delta q 0 (prefixCode q c) = delta q c ∧
      FixedPoint.residual q 0 (prefixCode q c) = prefixResidual q c := by
  have hp := (prefix_residual_lt q c hc he).trans (argument_parts q c hc).2.1
  obtain ⟨d, hd⟩ := (argument_parts q c hc).2.2
  rw [FixedPoint.delta, FixedPoint.residual, prefixCode_value q c, hd,
    Ordinal.mul_add_div _ (omegaSequence_isSuccLimit (base q) 0).bot_lt.ne',
    Ordinal.div_eq_zero_of_lt hp, add_zero, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hp]
  exact ⟨rfl, rfl⟩

theorem firstBranch_exact (q c : Nat) (hc : SourceLocalization.Node q c) :
    firstBranch q c = true ↔ FirstCase q c := by
  by_cases he : lowWord q c = []
  · simp only [firstBranch, he, List.isEmpty_nil, Bool.not_true, Bool.false_and,
      Bool.false_eq_true, FirstCase, ne_self_iff_false, false_and]
  · have hs := low_split q c hc he
    have hu := unitCode_spec q (node_baseCheck q c hc)
    have hunit : Normalization.equalRawCode q (lastAtom q c).code (unitCode q) = true ↔
        denote q (lastAtom q c) = 1 := by
      have hl := Normalization.equalRawCode_exact q (lastAtom q c).code (unitCode q)
      have hlast : checkCode q (lastAtom q c).code = true := by
        simpa only [checkCode_code] using hs.2.1
      have hucheck := ((Comparison.acceptedCode_exact q _).mp hu.1).1
      simpa only [hlast, hucheck, true_and, interpretation_code, hu.2] using hl
    have hp := prefix_checked q c hc
    have hsort := prefix_sort q c hc he
    have hdiv := prefix_divmod q c hc he
    have hstrict : FixedPoint.strictRawCode q 0 (prefixCode q c) = true ↔
        prefixResidual q c < SourceFixedPointLimits.globalResidualImageSup (base q) 0
          (delta q c) (prefixResidual q c) := by
      rw [FixedPoint.strictRawCode_exact, FixedPoint.SourceStrict, hdiv.1, hdiv.2]
      simp only [hp.1, hsort, true_and]
    have hi : (lowWord q c).isEmpty = false := by
      cases hl : lowWord q c with
      | nil => exact False.elim (he hl)
      | cons a as => rfl
    simp only [firstBranch, hi, Bool.not_false, Bool.true_and,
      Bool.or_eq_true, hunit, hstrict, FirstCase, he, true_and]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceFinePredecessor
