import Alexander313.Wilken.HereditarySourceFixedPoint
import Alexander313.Wilken.HereditaryThetaEmbeddings
import Alexander313.Wilken.RelativeTermWeakPrincipalSupport

/-!
# Actual finite-base fine predecessor

The actual public ANF cut supplies the low word; its final positive principal
atom is removed literally. The unit test and the repaired STRICT ordinary
supremum test implement the two distinct first branches of Definition 2.34.
The remaining branch is the penultimate node of the frozen computed literal
support localization. Admission and strict ordinal decrease are derived.

The fallback refers to the actual SourcePath recurrence. The fresh weak-normal
support theorem identifies its principal VALUE set with Definition 2.23 P_0,
including zero-leading sums. No literal parameter-support invariance or native
spelling uniqueness is asserted. All public levels, including base one, remain.
These source proof candidates are uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.FinePredecessor

open Theta.Normalization
open scoped Classical

noncomputable def sourcePrincipalValues (r c : Nat) : Finset Ordinal.{0} :=
  (((ThetaCourse.rawTree c).subtermsAt 0).image (denote r)).filter (fun p =>
    0 < p ∧ Ordinal.IsPrincipal (· + ·) p ∧ finiteBase r ≤ p ∧ p < omegaSequence (finiteBase r) 1)

theorem support_value_set (r c : Nat) (hc : Localization.Node r c) :
    sourcePrincipalValues r c = ((Localization.support c).map (Localization.value r)).toFinset := by
  obtain ⟨a, rfl, ha, hn⟩ := hc
  simpa only [sourcePrincipalValues, ThetaCourse.rawTree_code, omegaSequence_zero,
    Localization.support, Localization.value] using
      PrincipalSupport.listCode_sourcePrincipalValueSupport r 0 (.theta 0 a) ha hn

theorem source_candidate_coverage (r c : Nat) (hc : Localization.Node r c) (beta : Ordinal.{0}) :
    beta ∈ sourcePrincipalValues r c ↔ ∃ d ∈ Localization.support c,
      Localization.Node r d ∧ Localization.value r d = beta := by
  rw [support_value_set r c hc]
  constructor
  · intro hb
    obtain ⟨d, hd, hv⟩ := List.mem_map.mp (List.mem_toFinset.mp hb)
    exact ⟨d, hd, Localization.support_node r c d hc hd, hv⟩
  · rintro ⟨d, hd, hn, hv⟩
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨d, hd, hv⟩)

def stripLast {α : Type} (as : List α) : List α := as.reverse.tail.reverse

theorem stripLast_primrec {α : Type} [Primcodable α] : Primrec (@stripLast α) :=
  Primrec.list_reverse.comp (Primrec.list_tail.comp Primrec.list_reverse)

private theorem stripLast_nil {α : Type} : stripLast ([] : List α) = [] := rfl

theorem stripLast_split {α : Type} (as : List α) (ha : as ≠ []) :
    ∃ a, as = stripLast as ++ [a] ∧ as.reverse.head? = some a := by
  cases hr : as.reverse with
  | nil => exact False.elim (ha (by simpa using congrArg List.reverse hr))
  | cons a bs =>
    refine ⟨a, ?_, rfl⟩
    have he := congrArg List.reverse hr
    simpa only [List.reverse_reverse, List.reverse_cons, stripLast, hr, List.tail_cons] using he

theorem stripLast_mem {α : Type} (as : List α) (a : α) (ha : a ∈ stripLast as) : a ∈ as := by
  by_cases hn : as = []
  · subst as; simp only [stripLast_nil, List.not_mem_nil] at ha
  · obtain ⟨b, hb, _⟩ := stripLast_split as hn
    rw [hb]; exact List.mem_append_left _ ha

private theorem anf_prefix {α : Type} (f : α → Ordinal.{0}) (as bs : List α)
    (hn : IsAdditiveNormalForm ((as ++ bs).map f)) : IsAdditiveNormalForm (as.map f) := by
  rw [List.map_append] at hn
  exact ⟨fun p hp => hn.1 p (List.mem_append_left _ hp), (List.pairwise_append.mp hn.2).1⟩

def lowWord (r c : Nat) : List (RelativeTerm Nat) :=
  SourceDecomposition.lowWord r 0 (Localization.argumentCode c)

def highWord (r c : Nat) : List (RelativeTerm Nat) :=
  SourceDecomposition.highWord r 0 (Localization.argumentCode c)

def prefixWord (r c : Nat) : List (RelativeTerm Nat) := highWord r c ++ stripLast (lowWord r c)

def prefixArgument (r c : Nat) : RelativeTerm Nat := buildAtoms r (prefixWord r c)

def prefixCode (r c : Nat) : Nat := (prefixArgument r c).code

def prefixNode (r c : Nat) : Nat := (.theta 0 (prefixArgument r c) : RelativeTerm Nat).code

def lastAtom (r c : Nat) : RelativeTerm Nat := (lowWord r c).reverse.head?.getD (zeroTree r)

def unitCode (r : Nat) : Nat := BaseArithmetic.embedCode r (Localization.baseRaw 0)

theorem unitCode_primrec : Primrec unitCode :=
  BaseArithmetic.embedCode_primrec.comp Primrec.id (Primrec.const (Localization.baseRaw 0))

theorem unitCode_spec (r : Nat) : Theta.acceptedCode r (unitCode r) = true ∧
    interpretation r (unitCode r) = 1 := by
  have h0 := Localization.baseRaw_node 0
  have hc := Theta.embed_old_checked 0 r _ (Localization.node_low 0 _ h0)
  have hn := Theta.embed_normal 0 r _ (Localization.node_normal 0 _ h0)
  have hclow : lowCheckCode r (unitCode r) = true := by
    simpa only [Nat.zero_add, unitCode] using hc
  have hf : checkCode r (unitCode r) = true := by
    exact (Bool.and_eq_true.mp (by simpa only [lowCheckCode_eq] using hclow)).1
  refine ⟨(Theta.acceptedCode_iff r _).mpr ⟨hf, ?_⟩, ?_⟩
  · simpa only [Nat.zero_add, unitCode, ThetaCourse.rawTree] using hn
  · simpa only [Nat.zero_add, unitCode, Localization.value, finiteBase_zero] using
      (Theta.embed_original_value 0 r (Localization.baseRaw 0)).trans (Localization.baseRaw_value 0)

theorem argument_accepted (r c : Nat) (hc : Localization.Node r c) :
    SourceDecomposition.inputCheck r (Localization.argumentCode c) = true :=
  (SourceDecomposition.inputCheck_exact r _).mpr (Localization.node_argument r c hc)

noncomputable def delta (r c : Nat) : Ordinal.{0} :=
  interpretation r (SourceDecomposition.highCode r 0 (Localization.argumentCode c))

noncomputable def residual (r c : Nat) : Ordinal.{0} :=
  interpretation r (SourceDecomposition.lowCode r 0 (Localization.argumentCode c))

noncomputable def prefixResidual (r c : Nat) : Ordinal.{0} :=
  principalSum ((stripLast (lowWord r c)).map (denote r))

theorem argument_parts (r c : Nat) (hc : Localization.Node r c) :
    delta r c + residual r c = Localization.argumentValue r c ∧
      residual r c < omegaSequence (finiteBase r) 1 ∧
      omegaSequence (finiteBase r) 1 ∣ delta r c := by
  have ha := argument_accepted r c hc
  exact ⟨SourceDecomposition.parts_reconstruct r 0 _ ha,
    SourceDecomposition.lowPart_bound r 0 _ ha, SourceDecomposition.highPart_dvd r 0 _ ha⟩

theorem prefixCode_value (r c : Nat) :
    interpretation r (prefixCode r c) = delta r c + prefixResidual r c := by
  rw [prefixCode, interpretation_code, prefixArgument, buildAtoms_denote, prefixWord,
    List.map_append, principalSum_append]
  rw [delta, SourceDecomposition.highCode, interpretation_code, SourceDecomposition.highPartTerm,
    buildAtoms_denote]
  rfl

theorem low_split (r c : Nat) (hc : Localization.Node r c) (he : lowWord r c ≠ []) :
    lowWord r c = stripLast (lowWord r c) ++ [lastAtom r c] ∧
      check r (lastAtom r c) = true ∧ Theta.Normal r (lastAtom r c) ∧
      0 < denote r (lastAtom r c) ∧ Ordinal.IsPrincipal (· + ·) (denote r (lastAtom r c)) ∧
      residual r c = prefixResidual r c + denote r (lastAtom r c) := by
  obtain ⟨a, hs, hl⟩ := stripLast_split (lowWord r c) he
  have heq : lastAtom r c = a := by simp only [lastAtom, hl, Option.getD_some]
  have ham : a ∈ lowWord r c := by rw [hs]; simp
  have haw := (SourceDecomposition.lowWord_mem r 0 _ a).mp ham
  have ha := (SourceDecomposition.word_spec r _ (argument_accepted r c hc)).1 a haw.1
  refine ⟨by simpa only [heq] using hs, by simpa only [heq] using ha.1,
    by simpa only [heq] using ha.2.1, by simpa only [heq] using ha.2.2.1,
    by simpa only [heq] using ha.2.2.2, ?_⟩
  rw [residual, SourceDecomposition.lowCode, interpretation_code,
    (SourceDecomposition.parts_word_values r 0 _).2]
  change principalSum ((lowWord r c).map (denote r)) = _
  rw [hs, List.map_append, principalSum_append]
  simp only [List.map_cons, List.map_nil, principalSum, add_zero, heq, prefixResidual]

theorem prefix_residual_lt (r c : Nat) (hc : Localization.Node r c) (he : lowWord r c ≠ []) :
    prefixResidual r c < residual r c := by
  have hs := low_split r c hc he
  rw [hs.2.2.2.2.2]
  exact lt_add_of_pos_right _ hs.2.2.2.1

theorem low_split_normal (r c : Nat) (hc : Localization.Node r c) (he : lowWord r c ≠ []) :
    SourceNormalSum (residual r c) (prefixResidual r c) (denote r (lastAtom r c)) := by
  have hs := low_split r c hc he
  have hn := (SourceDecomposition.words_normal r 0 _ (argument_accepted r c hc)).2
  change IsAdditiveNormalForm ((lowWord r c).map (denote r)) at hn
  rw [hs.1, List.map_append, List.map_cons, List.map_nil] at hn
  refine Or.inr ⟨(stripLast (lowWord r c)).map (denote r), hn, rfl, ?_⟩
  rw [principalSum_append]
  simpa only [principalSum, add_zero, prefixResidual] using hs.2.2.2.2.2.symm

theorem prefix_normal (r c : Nat) (hc : Localization.Node r c) :
    Theta.Normal r (prefixArgument r c) := by
  have ha := argument_accepted r c hc
  let n := SourceOne.PublicCodes.fragment (ThetaCourse.rawTree (Localization.argumentCode c))
  have hg := SourceDecomposition.word_good r n _ ha (SourceOne.PublicCodes.height_le_fragment _)
  have hp : ∀ a ∈ prefixWord r c, a ∈ SourceDecomposition.word r (Localization.argumentCode c) := by
    intro a ham
    rcases List.mem_append.mp ham with ham | ham
    · exact (SourceDecomposition.highWord_mem r 0 _ a).mp ham |>.1
    · exact (SourceDecomposition.lowWord_mem r 0 _ a).mp (stripLast_mem _ _ ham) |>.1
  have hgood : GoodAtoms r n (prefixWord r c) := fun a ham => hg a (hp a ham)
  have hn : IsAdditiveNormalForm ((prefixWord r c).map (denote r)) := by
    by_cases he : lowWord r c = []
    · simpa only [prefixWord, he, stripLast_nil, List.append_nil, highWord] using
        (SourceDecomposition.words_normal r 0 _ ha).1
    · obtain ⟨a, hs, _⟩ := stripLast_split (lowWord r c) he
      have hw : SourceDecomposition.word r (Localization.argumentCode c) = prefixWord r c ++ [a] := by
        rw [SourceDecomposition.word_partition r 0 _ ha]
        change highWord r c ++ lowWord r c = _
        rw [hs, ← List.append_assoc]; rfl
      have hn := SourceDecomposition.word_normal r _ ha
      rw [hw] at hn
      exact anf_prefix (denote r) _ _ hn
  exact buildAtoms_normal r n _ hgood hn

/-- Rebuilding a prefix retains the original finite fragment, not just a
larger direct-limit presentation. -/
theorem prefix_admissible (r n c : Nat) (hc : Localization.Node r c)
    (hh : (ThetaCourse.rawTree (Localization.argumentCode c)).height ≤ n) :
    admissible r n (prefixArgument r c) := by
  have hg := SourceDecomposition.words_good r n 0 _ (argument_accepted r c hc) hh
  apply buildAtoms_admissible
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact hg.1 a ha
  · exact hg.2 a (stripLast_mem _ _ ha)

theorem prefix_checked (r c : Nat) (hc : Localization.Node r c) :
    checkCode r (prefixCode r c) = true ∧ Theta.Normal r (ThetaCourse.rawTree (prefixCode r c)) := by
  let n := SourceOne.PublicCodes.fragment (ThetaCourse.rawTree (Localization.argumentCode c))
  have ha := prefix_admissible r n c hc (SourceOne.PublicCodes.height_le_fragment _)
  simpa only [prefixCode, checkCode_code, ThetaCourse.rawTree_code] using
    And.intro (Theta.admitted_checked ha) (prefix_normal r c hc)

theorem prefix_sort (r c : Nat) (hc : Localization.Node r c) (he : lowWord r c ≠ []) :
    interpretation r (prefixCode r c) < omegaSequence (finiteBase r) 2 := by
  have hs := argument_parts r c hc
  have hp := add_lt_add_right (prefix_residual_lt r c hc he) (delta r c)
  rw [← prefixCode_value r c, hs.1] at hp
  obtain ⟨a, heq, hcheck, hn⟩ := hc
  have hb : Localization.argumentValue r c < omegaSequence (finiteBase r) 2 := by
    simpa only [heq, Localization.argumentValue, Localization.argumentCode_theta, interpretation_code] using
      SourceFixedPoint.checked_theta_sort r 0 a hcheck
  exact hp.trans hb

theorem prefix_node (r c : Nat) (hc : Localization.Node r c) (he : lowWord r c ≠ []) :
    Localization.Node r (prefixNode r c) := by
  obtain ⟨a, heq, hcheck, hn⟩ := hc
  let n := SourceOne.PublicCodes.fragment (.theta 0 a)
  have hh : a.height ≤ n := (le_max_right (0 + 1) a.height).trans (SourceOne.PublicCodes.height_le_fragment _)
  have hp := prefix_admissible r n c hc (by simpa only [heq, Localization.argumentCode_theta,
    ThetaCourse.rawTree_code] using hh)
  have ht := Theta.checked_admissible r n (.theta 0 a) hcheck (SourceOne.PublicCodes.height_le_fragment _)
  have hkn : 0 < n := by cases ht.2 with | theta h0k hkn hsort ha => exact hkn
  have hsort : finiteDenote r n (prefixArgument r c) < omegaSequence (finiteBase r) (0 + 2) := by
    rw [← denote_eq_finite r n _ hp.2]
    simpa only [prefixCode, interpretation_code] using prefix_sort r c hc he
  have hpnode : admissible r n (.theta 0 (prefixArgument r c)) :=
    ⟨hp.1, .theta (Nat.zero_le 0) hkn hsort hp.2⟩
  exact ⟨prefixArgument r c, rfl, Theta.admitted_checked hpnode,
    (Theta.normal_theta r 0 _).mpr (prefix_normal r c hc)⟩

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

theorem prefix_strict (r c : Nat) (hc : Localization.Node r c) (he : lowWord r c ≠ []) :
    Localization.value r (prefixNode r c) < Localization.value r c := by
  have ha := argument_accepted r c hc
  have hparts := argument_parts r c hc
  have hdcheck := (SourceDecomposition.parts_checked r 0 _ ha).1
  let d := SourceFixedPoint.sourceOrdinal r 0 (SourceDecomposition.highPartTerm r 0
    (Localization.argumentCode c)) hdcheck
  have hdv : d.val = delta r c := by simp only [d, SourceFixedPoint.sourceOrdinal,
    delta, SourceDecomposition.highCode, interpretation_code]
  have hds : d.val < omegaSequence (finiteBase r) 2 := by
    rw [hdv]
    obtain ⟨a, heq, hcheck, _⟩ := hc
    have hab : Localization.argumentValue r c < omegaSequence (finiteBase r) 2 := by
      simpa only [heq, Localization.argumentValue, Localization.argumentCode_theta, interpretation_code] using
        SourceFixedPoint.checked_theta_sort r 0 a hcheck
    exact (SourceDecomposition.parts_le r 0 _ ha).1.trans_lt hab
  have hp := global_same_high_strict (finiteBase r) (finiteBase_pos r) d hds
    (by simpa only [hdv] using hparts.2.2) _ _ (prefix_residual_lt r c hc he) hparts.2.1
  rw [hdv, ← prefixCode_value r c, hparts.1] at hp
  obtain ⟨a, heq, _, _⟩ := hc
  simpa only [Localization.value, prefixNode, interpretation_code, denote, eval,
    prefixCode, heq, Localization.argumentValue, Localization.argumentCode_theta] using hp

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

private theorem endpoint_append_last (xs : List Nat) (a : Nat) : Localization.endpoint (xs ++ [a]) = a := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    cases bs with
    | nil => rfl
    | cons d ds => exact ih

theorem localization_length (r c : Nat) (hc : Localization.Node r c)
    (hb : finiteBase r < Localization.value r c) : 2 ≤ (Localization.nativePath r c).length := by
  have hi := (Localization.inputCheck_exact r c).mpr hc
  obtain ⟨tail, ht⟩ := Localization.nativePath_head r c
  cases tail with
  | nil =>
    have he := Localization.nativePath_end r c hi
    rw [ht] at he
    change Localization.value r (Localization.baseRaw r) = Localization.value r c at he
    rw [Localization.baseRaw_value] at he
    exact False.elim ((ne_of_lt hb) he)
  | cons d ds => simp only [ht, List.length_cons]; omega

def fallback (r c : Nat) : Nat := penultimate (Localization.nativePath r c)

theorem fallback_spec (r c : Nat) (hc : Localization.Node r c)
    (hb : finiteBase r < Localization.value r c) :
    Localization.Node r (fallback r c) ∧ finiteBase r ≤ Localization.value r (fallback r c) ∧
      Localization.value r (fallback r c) < Localization.value r c := by
  have hi := (Localization.inputCheck_exact r c).mpr hc
  obtain ⟨pre, a, b, hs⟩ := last_two _ (localization_length r c hc hb)
  have hf : fallback r c = a := by simp only [fallback, penultimate, hs,
    List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
  have han := Localization.nativePath_nodes r c hi a (by rw [hs]; simp)
  have he : Localization.value r b = Localization.value r c := by
    have ht := Localization.nativePath_end r c hi
    have heq : pre ++ [a, b] = (pre ++ [a]) ++ [b] := by simp only [List.append_assoc, List.singleton_append]
    rwa [hs, heq, endpoint_append_last] at ht
  have hp := Localization.nativePath_strict r c hi
  rw [hs, List.map_append] at hp
  have hpab := (List.pairwise_append.mp hp).2.1
  have hab : Localization.value r a < Localization.value r b :=
    (List.pairwise_cons.mp hpab).1 _ (by simp)
  rw [hf]
  exact ⟨han, by simpa only [Localization.baseRaw_value] using Localization.baseRaw_le r a han,
    hab.trans_eq he⟩

def inputCheck (r c : Nat) : Bool :=
  Localization.inputCheck r c && Theta.lessCode r (Localization.baseRaw r) c

theorem inputCheck_exact (r c : Nat) : inputCheck r c = true ↔
    Localization.Node r c ∧ finiteBase r < Localization.value r c := by
  rw [inputCheck, Bool.and_eq_true, Localization.inputCheck_exact]
  apply and_congr_right
  intro hc
  simpa only [Localization.baseRaw_value] using
    Localization.value_less_exact r _ c (Localization.baseRaw_node r) hc

def firstBranch (r c : Nat) : Bool :=
  !(lowWord r c).isEmpty && (Theta.equalCode r (lastAtom r c).code (unitCode r) ||
    SourceFixedPoint.strictRawCode r 0 (prefixCode r c))

noncomputable def FirstCase (r c : Nat) : Prop := lowWord r c ≠ [] ∧
  (denote r (lastAtom r c) = 1 ∨ prefixResidual r c <
    SourceFixedPointLimits.globalResidualImageSup (finiteBase r) 0 (delta r c) (prefixResidual r c))

theorem prefix_divmod (r c : Nat) (hc : Localization.Node r c) (he : lowWord r c ≠ []) :
    SourceFixedPoint.delta r 0 (prefixCode r c) = delta r c ∧
      SourceFixedPoint.residual r 0 (prefixCode r c) = prefixResidual r c := by
  have hp := (prefix_residual_lt r c hc he).trans (argument_parts r c hc).2.1
  obtain ⟨d, hd⟩ := (argument_parts r c hc).2.2
  rw [SourceFixedPoint.delta, SourceFixedPoint.residual, prefixCode_value r c, hd,
    Ordinal.mul_add_div _ (omegaSequence_isSuccLimit (finiteBase r) 0).bot_lt.ne',
    Ordinal.div_eq_zero_of_lt hp, add_zero, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hp]
  exact ⟨rfl, rfl⟩

theorem firstBranch_exact (r c : Nat) (hc : Localization.Node r c) :
    firstBranch r c = true ↔ FirstCase r c := by
  by_cases he : lowWord r c = []
  · simp only [firstBranch, he, List.isEmpty_nil, Bool.not_true, Bool.false_and,
      Bool.false_eq_true, FirstCase, ne_self_iff_false, false_and]
  · have hs := low_split r c hc he
    have hu := unitCode_spec r
    have hlu : SourceDecomposition.inputCheck r (lastAtom r c).code = true :=
      (SourceDecomposition.inputCheck_exact r _).mpr
        ⟨by simpa only [checkCode_code] using hs.2.1,
          by simpa only [ThetaCourse.rawTree_code] using hs.2.2.1⟩
    have hue : SourceDecomposition.inputCheck r (unitCode r) = true := hu.1
    have hunit : Theta.equalCode r (lastAtom r c).code (unitCode r) = true ↔ denote r (lastAtom r c) = 1 := by
      have hl := (SourceFixedPoint.equalCode_exact r (lastAtom r c).code (unitCode r))
      simp only [SourceFixedPoint.equalCode, hlu, hue, Bool.true_and] at hl
      have hls := (SourceDecomposition.inputCheck_exact r _).mp hlu
      have hus := (SourceDecomposition.inputCheck_exact r _).mp hue
      simpa only [hls.1, hls.2, hus.1, hus.2, true_and, interpretation_code, hu.2] using hl
    have hp := prefix_checked r c hc
    have hsort := prefix_sort r c hc he
    have hdiv := prefix_divmod r c hc he
    have hstrict : SourceFixedPoint.strictRawCode r 0 (prefixCode r c) = true ↔
        prefixResidual r c < SourceFixedPointLimits.globalResidualImageSup (finiteBase r) 0
          (delta r c) (prefixResidual r c) := by
      rw [SourceFixedPoint.strictRawCode_exact, SourceFixedPoint.SourceStrict, hdiv.1, hdiv.2]
      simp only [hp.1, hsort, true_and]
    have hi : (lowWord r c).isEmpty = false := by
      cases hl : lowWord r c with
      | nil => exact False.elim (he hl)
      | cons a as => rfl
    simp only [firstBranch, hi, Bool.not_false, Bool.true_and,
      Bool.or_eq_true, hunit, hstrict, FirstCase, he, true_and]

def nativeCode (r c : Nat) : Nat := cond (firstBranch r c) (prefixNode r c) (fallback r c)

def predecessorCode (r c : Nat) : Nat := cond (inputCheck r c) (nativeCode r c) 0

theorem predecessor_spec (r c : Nat) (hc : inputCheck r c = true) :
    Localization.Node r (predecessorCode r c) ∧
      finiteBase r ≤ Localization.value r (predecessorCode r c) ∧
      Localization.value r (predecessorCode r c) < Localization.value r c := by
  obtain ⟨hn, hb⟩ := (inputCheck_exact r c).mp hc
  simp only [predecessorCode, hc, Bool.cond_true, nativeCode]
  cases hbcase : firstBranch r c with
  | false => exact fallback_spec r c hn hb
  | true =>
    have he := ((firstBranch_exact r c hn).mp hbcase).1
    have hp := prefix_node r c hn he
    exact ⟨hp, by simpa only [Localization.baseRaw_value] using Localization.baseRaw_le r _ hp,
      prefix_strict r c hn he⟩

theorem predecessor_branches (r c : Nat) (hc : inputCheck r c = true) :
    (FirstCase r c ∧ predecessorCode r c = prefixNode r c) ∨
      (¬FirstCase r c ∧ predecessorCode r c = fallback r c) := by
  have hn := ((inputCheck_exact r c).mp hc).1
  cases h : firstBranch r c with
  | false =>
    refine Or.inr ⟨?_, by simp only [predecessorCode, hc, nativeCode, h, Bool.cond_true, Bool.cond_false]⟩
    intro hf
    have ht := (firstBranch_exact r c hn).mpr hf
    simp only [h, Bool.false_eq_true] at ht
  | true => exact Or.inl ⟨(firstBranch_exact r c hn).mp h,
      by simp only [predecessorCode, hc, nativeCode, h, Bool.cond_true]⟩

theorem lowWord_primrec : Primrec₂ lowWord :=
  (SourceDecomposition.lowWord_primrec.comp (Primrec.fst.pair ((Primrec.const 0).pair
    (Localization.argumentCode_primrec.comp Primrec.snd)))).to₂

theorem highWord_primrec : Primrec₂ highWord :=
  (SourceDecomposition.highWord_primrec.comp (Primrec.fst.pair ((Primrec.const 0).pair
    (Localization.argumentCode_primrec.comp Primrec.snd)))).to₂

theorem prefixWord_primrec : Primrec₂ prefixWord :=
  (Primrec.list_append.comp highWord_primrec (stripLast_primrec.comp lowWord_primrec)).to₂

theorem prefixArgument_primrec : Primrec₂ prefixArgument :=
  (Theta.Normalization.Effective.buildAtoms_primrec.comp Primrec.fst prefixWord_primrec).to₂

theorem prefixCode_primrec : Primrec₂ prefixCode := code_primrec.comp₂ prefixArgument_primrec

theorem prefixNode_primrec : Primrec₂ prefixNode :=
  (code_primrec.comp (theta_primrec.comp (Primrec.const 0) prefixArgument_primrec)).to₂

theorem lastAtom_primrec : Primrec₂ lastAtom :=
  (Primrec.option_getD.comp (Primrec.list_head?.comp (Primrec.list_reverse.comp lowWord_primrec))
    (Theta.Normalization.Effective.zeroTree_primrec.comp Primrec.fst)).to₂

theorem fallback_primrec : Primrec₂ fallback := penultimate_primrec.comp₂ Localization.nativePath_primrec

theorem inputCheck_primrec : Primrec₂ inputCheck :=
  (Primrec.and.comp Localization.inputCheck_primrec (Theta.Effective.lessCode_primrec.comp
    (Primrec.fst.pair ((Localization.baseRaw_primrec.comp Primrec.fst).pair Primrec.snd)))).to₂

theorem firstBranch_primrec : Primrec₂ firstBranch := by
  have hempty := Primrec.beq.comp (Primrec.list_length.comp lowWord_primrec) (Primrec.const 0)
  have hunit := Theta.Effective.equalCode_primrec.comp
    (Primrec.fst.pair ((code_primrec.comp lastAtom_primrec).pair (unitCode_primrec.comp Primrec.fst)))
  have hstrict := SourceFixedPoint.strictRawCode_primrec.comp
    (Primrec.fst.pair ((Primrec.const 0).pair prefixCode_primrec))
  have hnonempty : Primrec (fun p : Nat × Nat => !(lowWord p.1 p.2).isEmpty) :=
    (Primrec.not.comp hempty).of_eq (fun p => by cases lowWord p.1 p.2 <;> simp)
  exact (Primrec.and.comp hnonempty (Primrec.or.comp hunit hstrict)).to₂

theorem nativeCode_primrec : Primrec₂ nativeCode :=
  (firstBranch_primrec.cond prefixNode_primrec fallback_primrec).to₂

theorem predecessorCode_primrec : Primrec₂ predecessorCode :=
  (inputCheck_primrec.cond nativeCode_primrec (Primrec.const 0)).to₂

def predecessor (r c : Nat) : Part Nat := cond (inputCheck r c) (Part.some (predecessorCode r c)) Part.none

theorem predecessor_partrec : Partrec₂ predecessor :=
  (Partrec.cond inputCheck_primrec.to_comp predecessorCode_primrec.to_comp.partrec Partrec.none).to₂

theorem predecessor_domain (r c : Nat) : (predecessor r c).Dom ↔
    Localization.Node r c ∧ finiteBase r < Localization.value r c := by
  cases h : inputCheck r c <;> simp [predecessor, h, ← inputCheck_exact]

theorem predecessor_graph (r c d : Nat) : d ∈ predecessor r c ↔
    inputCheck r c = true ∧ d = predecessorCode r c := by
  cases h : inputCheck r c <;> simp [predecessor, h]

theorem predecessor_unique (r c : Nat) (hc : inputCheck r c = true) :
    ∃! d, d ∈ predecessor r c := by
  refine ⟨predecessorCode r c, (predecessor_graph r c _).mpr ⟨hc, rfl⟩, ?_⟩
  intro d hd
  exact ((predecessor_graph r c d).mp hd).2

def graphCheck (r c d : Nat) : Bool := inputCheck r c && (d == predecessorCode r c)

theorem graphCheck_primrec : Primrec (fun p : (Nat × Nat) × Nat => graphCheck p.1.1 p.1.2 p.2) :=
  Primrec.and.comp (inputCheck_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst))
    (Primrec.beq.comp Primrec.snd (predecessorCode_primrec.comp
      (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)))

theorem graphCheck_exact (r c d : Nat) : graphCheck r c d = true ↔ d ∈ predecessor r c := by
  simp only [graphCheck, Bool.and_eq_true, beq_iff_eq, predecessor_graph]

def canonicalCode (r c : Nat) : Nat := cond (inputCheck r c) (Localization.emit r (predecessorCode r c)) 0

theorem canonicalCode_primrec : Primrec₂ canonicalCode :=
  (inputCheck_primrec.cond (Localization.emit_primrec.comp Primrec.fst predecessorCode_primrec)
    (Primrec.const 0)).to₂

theorem canonicalCode_spec (r c : Nat) (hc : inputCheck r c = true) :
    Canonical.check (canonicalCode r c) = true ∧
      unionInterpretation (canonicalCode r c) = Localization.value r (predecessorCode r c) := by
  simpa only [canonicalCode, hc, Bool.cond_true] using
    Localization.emit_spec r _ (predecessor_spec r c hc).1

/-- The raw adapter computes on the constructed normalized spelling. It
does not assert support preservation or equality of fine predecessors across
arbitrary original spellings. -/
def rawInputCheck (r c : Nat) : Bool := (checkCode r c && Localization.rootShape c) &&
  Theta.Normalization.lessRawCode r (Localization.baseRaw r) c

theorem rawInputCheck_primrec : Primrec₂ rawInputCheck :=
  (Primrec.and.comp (Primrec.and.comp Uniform.hereditaryCheckCode_primrec
    (Localization.rootShape_primrec.comp Primrec.snd))
      (Theta.Normalization.Effective.lessRawCode_primrec.comp
        (Primrec.fst.pair ((Localization.baseRaw_primrec.comp Primrec.fst).pair Primrec.snd)))).to₂

theorem rawInputCheck_exact (r c : Nat) : rawInputCheck r c = true ↔
    (∃ a : RelativeTerm Nat, c = (.theta 0 a).code ∧ check r (.theta 0 a) = true) ∧
      finiteBase r < interpretation r c := by
  constructor
  · intro h
    obtain ⟨hi, hb⟩ := Bool.and_eq_true.mp h
    obtain ⟨hc, hs⟩ := Bool.and_eq_true.mp hi
    obtain ⟨t, ht, hct⟩ := (checkCode_iff r c).mp hc
    obtain ⟨a, ha⟩ := (Localization.rootShape_code t).mp (by simpa only [← ht] using hs)
    subst t
    have hbase : checkCode r (Localization.baseRaw r) = true :=
      (Bool.and_eq_true.mp (by simpa only [lowCheckCode_eq] using Localization.node_low r _ (Localization.baseRaw_node r))).1
    have hv := (Theta.Normalization.lessRawCode_correct r _ c hbase hc).mp hb
    exact ⟨⟨a, ht.symm, hct⟩, by simpa only [← Localization.baseRaw_value r, Localization.value] using hv⟩
  · rintro ⟨⟨a, rfl, ha⟩, hb⟩
    have hbase : checkCode r (Localization.baseRaw r) = true :=
      (Bool.and_eq_true.mp (by simpa only [lowCheckCode_eq] using Localization.node_low r _ (Localization.baseRaw_node r))).1
    apply Bool.and_eq_true.mpr
    refine ⟨Bool.and_eq_true.mpr ⟨by simpa only [checkCode_code] using ha,
      (Localization.rootShape_code _).mpr ⟨a, rfl⟩⟩, ?_⟩
    apply (Theta.Normalization.lessRawCode_correct r _ _ hbase (by simpa only [checkCode_code] using ha)).mpr
    simpa only [← Localization.baseRaw_value r, Localization.value] using hb

theorem raw_normalized_input (r c : Nat) (hc : rawInputCheck r c = true) :
    inputCheck r (Theta.Normalization.normalizeCode r c) = true := by
  obtain ⟨⟨a, rfl, ha⟩, hb⟩ := (rawInputCheck_exact r c).mp hc
  have hs := Theta.Normalization.normalizeCode_checked r (.theta 0 a).code
    (by simpa only [checkCode_code] using ha)
  have hn : Localization.Node r (Theta.Normalization.normalizeCode r (.theta 0 a).code) := by
    refine ⟨Theta.Normalization.normalize r a, ?_, ?_, ?_⟩
    · simp only [Theta.Normalization.normalizeCode_code, Theta.Normalization.normalize_theta]
    · simpa only [Theta.Normalization.normalizeCode_code, Theta.Normalization.normalize_theta, checkCode_code] using hs.1
    · simpa only [Theta.Normalization.normalizeCode_code, Theta.Normalization.normalize_theta, ThetaCourse.rawTree_code] using hs.2.1
  exact (inputCheck_exact r _).mpr ⟨hn, by simpa only [Localization.value, hs.2.2] using hb⟩

def rawPredecessorCode (r c : Nat) : Nat := cond (rawInputCheck r c)
  (predecessorCode r (Theta.Normalization.normalizeCode r c)) 0

theorem rawPredecessorCode_primrec : Primrec₂ rawPredecessorCode :=
  (rawInputCheck_primrec.cond (predecessorCode_primrec.comp Primrec.fst
    Theta.Normalization.Effective.normalizeCode_primrec) (Primrec.const 0)).to₂

theorem rawPredecessor_spec (r c : Nat) (hc : rawInputCheck r c = true) :
    Localization.Node r (rawPredecessorCode r c) ∧
      finiteBase r ≤ Localization.value r (rawPredecessorCode r c) ∧
      Localization.value r (rawPredecessorCode r c) < interpretation r c := by
  have hn := raw_normalized_input r c hc
  have hs := predecessor_spec r _ hn
  have hcheck := (Bool.and_eq_true.mp (Bool.and_eq_true.mp hc).1).1
  have hv := (Theta.Normalization.normalizeCode_checked r c hcheck).2.2
  simpa only [rawPredecessorCode, hc, Bool.cond_true, Localization.value, hv] using hs

end Alexander313.Wilken.RelativeTerm.Hereditary.FinePredecessor
