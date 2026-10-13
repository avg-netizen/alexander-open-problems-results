import Alexander313.Wilken.SourceOneNativeBoundedPublicReturn
import Alexander313.Wilken.PublicEpsilonNativeRootPositiveCollapseSupport
import Alexander313.Wilken.DirectLimitComparison

/-!
# Actual original source-one scalar callers and comparison

Every original check and Normal predicate is hereditary source level zero.
Positive collapse indices agree through the real cardinal suffix and BOTH
finite minimum recursions. Original theta comparison and written support
follow from the original admitted grammar. No native base-one parser, output
representative, localization cutoff or relative scalar oracle. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.RootScalar

open ThetaCourse

abbrev argumentCheck := SourceDecomposition.inputCheck 0
abbrev nodeCode := BoundedPublicReturn.nodeCode

theorem argumentCheck_primrec : Primrec argumentCheck :=
  SourceDecomposition.inputCheck_primrec.comp (Primrec.const 0) Primrec.id

theorem raw_code (c : Nat) (hc : argumentCheck c = true) : (rawTree c).code = c := by
  obtain ⟨t, ht, hct⟩ := (checkCode_iff 0 c).mp
    ((SourceDecomposition.inputCheck_exact 0 c).mp hc).1
  rw [← ht, rawTree_code]

theorem raw_checked (c : Nat) (hc : argumentCheck c = true) : check 0 (rawTree c) = true :=
  (SourceDecomposition.input_tree 0 c hc).1

theorem raw_value (c : Nat) (hc : argumentCheck c = true) :
    denote 0 (rawTree c) = interpretation 0 c := (SourceDecomposition.input_value 0 c hc).symm

theorem root_accepted (b : Nat) (hb : rootCheck b = true) : argumentCheck b = true := by
  obtain ⟨a, rfl, ha, hna, hh⟩ := (rootCheck_exact b).mp hb
  exact (Theta.acceptedCode_iff 0 _).mpr
    ⟨by simpa only [checkCode_code] using ha, by simpa only [rawTree_code] using hna⟩

theorem root_base_le (b : Nat) (hb : rootCheck b = true) : 1 ≤ interpretation 0 b :=
  (EpsilonOffsets.epsilon_one_lt (root_epsilon b hb)).le

theorem root_omegaSequence_pos (b k : Nat) (hb : rootCheck b = true) (hk : 0 < k) :
    omegaSequence 1 k = omegaSequence (interpretation 0 b) k := by
  have hz := NativeContext.Iota.HeightSupport.levelCardinal_zero_eq_of_interval 1
    (interpretation 0 b) (root_base_le b hb) (root_lt_first b hb)
  cases k with
  | zero => omega
  | succ k => exact congrArg Cardinal.ord
      (NativeContext.Iota.HeightSupport.levelCardinal_eq_of_zero_eq _ _ hz (k + 1))

theorem positive_finiteCollapse_eq (b n k : Nat) (hb : rootCheck b = true)
    (hk : 0 < k) (hkn : k < n) (ξ : Ordinal.{0}) :
    sourceFiniteCollapse 1 n k ξ = sourceFiniteCollapse (interpretation 0 b) n k ξ := by
  apply NativeContext.Iota.HeightSupport.finiteCollapse_suffix_congr _ _ n 1 k _
    (by omega) hkn ξ
  intro j hj
  exact root_omegaSequence_pos b j hb (by omega)

theorem positive_notation_iff (b n m : Nat) (hb : rootCheck b = true)
    (hm : 0 < m) (ξ : Ordinal.{0}) :
    sourceNotation 1 n m ξ ↔ sourceNotation (interpretation 0 b) n m ξ := by
  by_cases hmn : m < n
  · rw [sourceNotation_iff_hull 1 n m hmn ξ,
      sourceNotation_iff_hull (interpretation 0 b) n m hmn ξ,
      ← root_omegaSequence_pos b (m + 2) hb (by omega)]
    exact NativeContext.Iota.HeightSupport.hull_suffix_congr _ _ _ _ n m _ 0 ξ
      (fun k hk => root_omegaSequence_pos b k hb (hm.trans_le hk))
      (fun k hmk hkn η => positive_finiteCollapse_eq b n k hb (hm.trans hmk) hkn η)
      (fun η _ => positive_finiteCollapse_eq b n m hb hm hmn η)
  · simp only [sourceNotation, if_neg hmn, root_omegaSequence_pos b m hb hm]

/-- Every global caller is derived from the ORIGINAL checked argument. -/
theorem positive_collapse_eq (b k c : Nat) (hb : rootCheck b = true) (hk : 0 < k)
    (hc : argumentCheck c = true) (hs : (rawTree c).outerSort ≤ k + 2) :
    globalCollapse 1 k (interpretation 0 c) =
      globalCollapse (interpretation 0 b) k (interpretation 0 c) := by
  have hτ : (0 : Ordinal.{0}) < 1 := zero_lt_one
  have hβ := root_pos b hb
  have hn : GlobalNotation 1 (k + 1) (interpretation 0 c) := by
    simpa only [finiteBase_zero, raw_value c hc] using
      SourceFixedPoint.checked_notation_at 0 (rawTree c) (raw_checked c hc) (k + 1)
  obtain ⟨n, hkn, hnt⟩ := globalNotation_finite_witness 1 hτ (k + 1) hn
  have hnb := (positive_notation_iff b n (k + 1) hb (by omega) _).mp hnt
  have hsort : interpretation 0 c < omegaSequence 1 (k + 2) := by
    rw [← raw_value c hc, ← finiteBase_zero]
    exact (denote_lt_iff_outerSort_le 0 _ (raw_checked c hc) (k + 2) (by omega)).mpr hs
  have hsortβ : interpretation 0 c < omegaSequence (interpretation 0 b) (k + 2) := by
    rw [← root_omegaSequence_pos b (k + 2) hb (by omega)]
    exact hsort
  have hbτ := source_finite_notation_sorted_lt_boundary 1 hτ n (k + 1) (k + 1)
    le_rfl hkn hnt hsort
  have hbβ := source_finite_notation_sorted_lt_boundary (interpretation 0 b) hβ n
    (k + 1) (k + 1) le_rfl hkn hnb hsortβ
  rw [globalCollapse_finite_agreement 1 hτ n k (by omega) _ hbτ,
    globalCollapse_finite_agreement (interpretation 0 b) hβ n k (by omega) _ hbβ]
  exact positive_finiteCollapse_eq b n k hb hk (by omega) _

theorem nodeCode_sorted_spec (k c : Nat) (hc : argumentCheck c = true)
    (hs : (rawTree c).outerSort ≤ k + 2) :
    argumentCheck (nodeCode k c) = true ∧
      interpretation 0 (nodeCode k c) = globalCollapse 1 k (interpretation 0 c) := by
  apply BoundedPublicReturn.nodeCode_spec k c hc
  rw [← raw_value c hc]
  exact (denote_lt_iff_outerSort_le 0 _ (raw_checked c hc) (k + 2) (by omega)).mpr hs

theorem positive_nodeCode_spec (b k c : Nat) (hb : rootCheck b = true) (hk : 0 < k)
    (hc : argumentCheck c = true) (hs : (rawTree c).outerSort ≤ k + 2) :
    argumentCheck (nodeCode k c) = true ∧
      interpretation 0 (nodeCode k c) = globalCollapse (interpretation 0 b) k (interpretation 0 c) :=
  ⟨(nodeCode_sorted_spec k c hc hs).1,
    (nodeCode_sorted_spec k c hc hs).2.trans (positive_collapse_eq b k c hb hk hc hs)⟩

/-- The real original-source comparison has no native source parser. -/
theorem checked_theta_lt_iff_exposed (k : Nat) (a u : RelativeTerm Nat)
    (ha : check 0 (.theta k a) = true) (hu : check 0 (.theta k u) = true)
    (hna : Theta.Normal 0 a) (hnu : Theta.Normal 0 u) :
    denote 0 (.theta k a) < denote 0 (.theta k u) ↔
      (denote 0 a < denote 0 u ∧
        ∀ s ∈ exposedThetaList k a, denote 0 s < denote 0 (.theta k u)) ∨
      ∃ s ∈ exposedThetaList k u, denote 0 (.theta k a) ≤ denote 0 s := by
  let n := max (SourceOne.PublicCodes.fragment (.theta k a))
    (SourceOne.PublicCodes.fragment (.theta k u))
  have haa := Theta.checked_admissible 0 n (.theta k a) ha
    ((SourceOne.PublicCodes.height_le_fragment _).trans (le_max_left _ _))
  have huu := Theta.checked_admissible 0 n (.theta k u) hu
    ((SourceOne.PublicCodes.height_le_fragment _).trans (le_max_right _ _))
  exact Theta.theta_global_lt_iff_exposed 0 n k a u haa huu hna hnu

theorem source_exposed_lt_root (k : Nat) (a s : RelativeTerm Nat)
    (ha : check 0 (.theta k a) = true) (hna : Theta.Normal 0 a)
    (hs : s ∈ exposedThetaList k a) : denote 0 s < denote 0 (.theta k a) :=
  PrincipalSupport.principalList_argument_lt 0 k a s ha hna
    (RelativeTerm.PrincipalSupport.exposed_mem_principalList k a s hs)

theorem above_argument_le_iff_support (k : Nat) (a u : RelativeTerm Nat)
    (ha : check 0 (.theta k a) = true) (hu : check 0 (.theta k u) = true)
    (hna : Theta.Normal 0 a) (hnu : Theta.Normal 0 u) (harg : denote 0 a < denote 0 u) :
    denote 0 (.theta k u) ≤ denote 0 (.theta k a) ↔
      ∃ s ∈ exposedThetaList k a, denote 0 (.theta k u) ≤ denote 0 s := by
  constructor
  · intro hle
    have hlt : denote 0 (.theta k u) < denote 0 (.theta k a) := by
      by_contra hn
      have he := le_antisymm hle (le_of_not_gt hn)
      have hr := (checked_theta_lt_iff_exposed k a u ha hu hna hnu).mpr
        (Or.inl ⟨harg, fun s hs => (source_exposed_lt_root k a s ha hna hs).trans_le he.symm.le⟩)
      exact hr.not_ge hle
    rcases (checked_theta_lt_iff_exposed k u a hu ha hnu hna).mp hlt with hf | hs
    · exact False.elim (hf.1.not_gt harg)
    · exact hs
  · intro hs
    exact ((checked_theta_lt_iff_exposed k u a hu ha hnu hna).mpr (Or.inr hs)).le

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.RootScalar
