import Alexander313.Wilken.HereditaryFineLocalization
import Alexander313.Wilken.SourceHighPartComparison

/-!
# Actual support stability of the fine-predecessor prefix

Opening a public parameter into principal comparison representatives creates
only parameter leaves at the present level. Consequently taking those atoms
and rebuilding a written sum preserves the full current-level theta support.
Removing the last low atom retains a literal subset of argument support.
The unit/STRICT first branch bounds every removed support value by the new
theta value. These facts use the original weak-normal domain at every public
level, including base one; no parameter-support or spelling invariance is
asserted. All proof candidates are uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.FineLocalization.Refinements

open Theta Theta.Normalization Localization Localization.Refinements FinePredecessor

theorem atoms_principal_support (r m : Nat) (t s : RelativeTerm Nat) :
    s ∈ RelativeTerm.PrincipalSupport.principalList m t ↔
      ∃ a ∈ Theta.atoms r t, s ∈ RelativeTerm.PrincipalSupport.principalList m a := by
  induction t with
  | parameter p =>
    cases r with
    | zero => simp only [RelativeTerm.PrincipalSupport.principalList, atoms_parameter_zero,
        List.not_mem_nil, false_and, exists_false]
    | succ r =>
      rw [Theta.Effective.atoms_parameter_succ]
      cases hd : decode p with
      | none => simp [hd, RelativeTerm.PrincipalSupport.principalList]
      | some u =>
        simp only [hd, Option.map_some, Option.getD_some,
          RelativeTerm.PrincipalSupport.principalList, List.not_mem_nil]
        constructor
        · intro h; exact False.elim h
        · rintro ⟨a, ha, hs⟩
          obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
          exact List.not_mem_nil hs
  | sum a b iha ihb =>
    simp only [RelativeTerm.PrincipalSupport.principalList, atoms_sum, List.mem_append]
    constructor
    · rintro (h | h)
      · obtain ⟨a, ha, hs⟩ := iha.mp h
        exact ⟨a, Or.inl ha, hs⟩
      · obtain ⟨a, ha, hs⟩ := ihb.mp h
        exact ⟨a, Or.inr ha, hs⟩
    · rintro ⟨a, ha | ha, hs⟩
      · exact Or.inl (iha.mpr ⟨a, ha, hs⟩)
      · exact Or.inr (ihb.mpr ⟨a, ha, hs⟩)
  | theta k a => simp only [atoms_theta, List.mem_singleton, exists_eq_left]

private theorem buildRev_principal_support (r m : Nat) (as : List (RelativeTerm Nat))
    (s : RelativeTerm Nat) :
    s ∈ RelativeTerm.PrincipalSupport.principalList m (buildRev r as) ↔
      ∃ a ∈ as, s ∈ RelativeTerm.PrincipalSupport.principalList m a := by
  induction as with
  | nil =>
    cases r <;> simp only [buildRev, zeroTree, RelativeTerm.PrincipalSupport.principalList,
      List.not_mem_nil, false_and, exists_false]
  | cons a as ih =>
    simp only [buildRev, RelativeTerm.PrincipalSupport.principalList, List.mem_append, ih,
      List.mem_cons]
    constructor
    · rintro (⟨b, hb, hs⟩ | hs)
      · exact ⟨b, Or.inr hb, hs⟩
      · exact ⟨a, Or.inl rfl, hs⟩
    · rintro ⟨b, rfl | hb, hs⟩
      · exact Or.inr hs
      · exact Or.inl ⟨b, hb, hs⟩

theorem buildAtoms_principal_support (r m : Nat) (as : List (RelativeTerm Nat))
    (s : RelativeTerm Nat) :
    s ∈ RelativeTerm.PrincipalSupport.principalList m (buildAtoms r as) ↔
      ∃ a ∈ as, s ∈ RelativeTerm.PrincipalSupport.principalList m a := by
  simpa only [buildAtoms, List.mem_reverse] using buildRev_principal_support r m as.reverse s

theorem prefix_argument_support_subset (r c : Nat) (hc : Node r c) (s : RelativeTerm Nat)
    (hs : s ∈ RelativeTerm.PrincipalSupport.principalList 0 (prefixArgument r c)) :
    s ∈ RelativeTerm.PrincipalSupport.principalList 0 (ThetaCourse.rawTree (argumentCode c)) := by
  obtain ⟨a, ha, hs⟩ := (buildAtoms_principal_support r 0 (prefixWord r c) s).mp hs
  have haw : a ∈ SourceDecomposition.word r (argumentCode c) := by
    rcases List.mem_append.mp ha with ha | ha
    · exact ((SourceDecomposition.highWord_mem r 0 _ a).mp ha).1
    · exact ((SourceDecomposition.lowWord_mem r 0 _ a).mp (stripLast_mem _ _ ha)).1
  exact (atoms_principal_support r 0 _ s).mpr ⟨a, haw, hs⟩

theorem argument_support_split (r c : Nat) (hc : Node r c) (he : lowWord r c ≠ [])
    (s : RelativeTerm Nat) :
    s ∈ RelativeTerm.PrincipalSupport.principalList 0 (ThetaCourse.rawTree (argumentCode c)) ↔
      s ∈ RelativeTerm.PrincipalSupport.principalList 0 (prefixArgument r c) ∨
      s ∈ RelativeTerm.PrincipalSupport.principalList 0 (lastAtom r c) := by
  have hw : SourceDecomposition.word r (argumentCode c) = prefixWord r c ++ [lastAtom r c] := by
    rw [SourceDecomposition.word_partition r 0 _ (argument_accepted r c hc)]
    change highWord r c ++ lowWord r c = _
    rw [(low_split r c hc he).1, ← List.append_assoc]
    rfl
  rw [atoms_principal_support r 0, ← SourceDecomposition.word, hw,
    buildAtoms_principal_support]
  constructor
  · rintro ⟨a, ha, hs⟩
    rcases List.mem_append.mp ha with ha | ha
    · exact Or.inl ⟨a, ha, hs⟩
    · rw [List.mem_singleton.mp ha] at hs
      exact Or.inr hs
  · rintro (⟨a, ha, hs⟩ | hs)
    · exact ⟨a, List.mem_append_left _ ha, hs⟩
    · exact ⟨lastAtom r c, List.mem_append_right _ List.mem_cons_self, hs⟩

theorem prefix_argument_lt (r c : Nat) (hc : Node r c) (he : lowWord r c ≠ []) :
    argumentValue r (prefixNode r c) < argumentValue r c := by
  have h := add_lt_add_right (prefix_residual_lt r c hc he) (delta r c)
  rw [← prefixCode_value r c, (argument_parts r c hc).1] at h
  simpa only [prefixNode, argumentValue, argumentCode_theta, prefixCode] using h

theorem prefix_level_eq (r c : Nat) (hc : Node r c) (he : lowWord r c ≠ []) :
    SourceHighPartComparison.localizationLevel r (prefixNode r c) =
      SourceHighPartComparison.localizationLevel r c := by
  have ha := argument_accepted r c hc
  have hd := (SourceDecomposition.parts_code_value r 0 _ ha).1
  have hp := (prefix_divmod r c hc he).1
  change SourceHighPartComparison.highPart (omegaSequence (finiteBase r) 1)
      (interpretation r (prefixCode r c)) = _
  change SourceFixedPoint.delta r 0 (prefixCode r c) = _
  rw [hp]
  exact hd

/-- The genuine divisible-high residual bound transported to the direct limit. -/
theorem global_tail_lt (tau : Ordinal.{0}) (htau : 0 < tau)
    (d : GlobalNotationOrdinal tau 1) (hd : d.val < omegaSequence tau 2)
    (hdiv : omegaSequence tau 1 ∣ d.val) (eta : Ordinal.{0})
    (heta : eta < omegaSequence tau 1) : eta < globalCollapse tau 0 (d.val + eta) := by
  obtain ⟨n, hn, hdn⟩ := globalNotation_finite_witness tau htau 1 d.property
  have hn0 : 0 < n := (Nat.zero_le 1).trans_lt hn
  let dn : SourceNotationOrdinal tau n 1 := ⟨d.val, hdn⟩
  let a := SourceFixedPointLimits.shiftArgument tau n 0 hn0 dn eta heta
  have has := SourceFixedPointLimits.shiftArgument_sort tau n 0 hn0 dn hd eta heta
  have had := source_finite_notation_sorted_lt_boundary tau htau n 1 1 le_rfl hn a.property has
  rw [globalCollapse_finite_agreement tau htau n 0 hn0 _ had]
  exact SourceFixedPointLimits.tail_lt_collapse tau htau n 0 hn0 dn hd hdiv eta heta

theorem prefix_residual_lt_node (r c : Nat) (hc : Node r c) (he : lowWord r c ≠ []) :
    prefixResidual r c < value r (prefixNode r c) := by
  have ha := argument_accepted r c hc
  have hdcheck := (SourceDecomposition.parts_checked r 0 _ ha).1
  let d := SourceFixedPoint.sourceOrdinal r 0 (SourceDecomposition.highPartTerm r 0
    (argumentCode c)) hdcheck
  have hdv : d.val = delta r c := by
    simp only [d, SourceFixedPoint.sourceOrdinal, delta, SourceDecomposition.highCode,
      interpretation_code]
  have hd : d.val < omegaSequence (finiteBase r) 2 := by
    rw [hdv]
    exact (SourceDecomposition.parts_le r 0 _ ha).1.trans_lt (by
      obtain ⟨a, heq, hcheck, _⟩ := hc
      simpa only [heq, argumentValue, argumentCode_theta, interpretation_code] using
        SourceFixedPoint.checked_theta_sort r 0 a hcheck)
  have ht := global_tail_lt (finiteBase r) (finiteBase_pos r) d hd
    (by simpa only [hdv] using (argument_parts r c hc).2.2) (prefixResidual r c)
    ((prefix_residual_lt r c hc he).trans (argument_parts r c hc).2.1)
  rw [hdv, ← prefixCode_value r c] at ht
  simpa only [prefixNode, value, interpretation_code, denote, eval, prefixCode,
    interpretation_code] using ht

theorem last_support_le (r c : Nat) (hc : Node r c) (he : lowWord r c ≠ [])
    (s : RelativeTerm Nat) (hs : s ∈ RelativeTerm.PrincipalSupport.principalList 0 (lastAtom r c)) :
    denote r s ≤ denote r (lastAtom r c) := by
  have hsplit := low_split r c hc he
  have ham : lastAtom r c ∈ lowWord r c := by rw [hsplit.1]; simp
  have haw := (SourceDecomposition.lowWord_mem r 0 _ _).mp ham
  rcases SourceDecomposition.word_shape r _ _ haw.1 with ⟨p, hp⟩ | ⟨k, a, hka⟩
  · rw [hp] at hs
    exact False.elim (List.not_mem_nil hs)
  · have hk : k = 0 := by
      have h := haw.2
      rw [hka] at h
      have hn : ¬1 < k + 1 := by simpa only [SourceDecomposition.above,
        RelativeTerm.outerSort, Nat.zero_add, decide_eq_false_iff_not] using h
      omega
    subst k
    rw [hka] at hs ⊢
    exact PrincipalSupport.principalList_theta_value_le r a s
      (by simpa only [hka] using hsplit.2.1)
      (by simpa only [hka] using hsplit.2.2.1) hs

theorem first_last_le_node (r c : Nat) (hc : Node r c) (hf : FirstCase r c) :
    denote r (lastAtom r c) ≤ value r (prefixNode r c) := by
  have hn := (SourceDecomposition.words_normal r 0 _ (argument_accepted r c hc)).2
  have hs := low_split r c hc hf.1
  change IsAdditiveNormalForm ((lowWord r c).map (denote r)) at hn
  rw [hs.1, List.map_append, List.map_cons, List.map_nil] at hn
  cases hp : stripLast (lowWord r c) with
  | nil =>
    have hz : prefixResidual r c = 0 := by simp only [prefixResidual, hp, List.map_nil, principalSum]
    have hu : denote r (lastAtom r c) = 1 := by
      rcases hf.2 with h | h
      · exact h
      · rw [hz] at h
        simp only [SourceFixedPointLimits.globalResidualImageSup, Ordinal.bsup_zero,
          lt_self_iff_false] at h
    rw [hu]
    exact (Order.one_le_iff_pos.mpr (finiteBase_pos r)).trans
      (by simpa only [baseRaw_value] using baseRaw_le r _ (prefix_node r c hc hf.1))
  | cons a as =>
    have ham : denote r a ∈ (stripLast (lowWord r c)).map (denote r) := by
      rw [hp]; exact List.mem_cons_self
    have hlast : denote r (lastAtom r c) ≤ denote r a := by
      rw [hp, List.map_cons] at hn
      exact additiveNormalForm_head_ge hn (List.mem_append_right _ List.mem_cons_self)
    exact (hlast.trans (principalSum_mem_le ham)).trans
      (prefix_residual_lt_node r c hc hf.1).le

/-- Every old argument support value lies below or at the actual first-branch
predecessor. The non-strict endpoint is necessary for the base-one unit. -/
theorem first_argument_support_bound (r c : Nat) (hc : Node r c) (hf : FirstCase r c)
    (s : RelativeTerm Nat)
    (hs : s ∈ RelativeTerm.PrincipalSupport.principalList 0 (ThetaCourse.rawTree (argumentCode c))) :
    denote r s ≤ value r (prefixNode r c) := by
  rcases (argument_support_split r c hc hf.1 s).mp hs with hs | hs
  · have hlow := node_low r _ (prefix_node r c hc hf.1)
    have hcheck : checkCode r (prefixNode r c) = true :=
      (Bool.and_eq_true.mp (by simpa only [lowCheckCode_eq] using hlow)).1
    have ht : check r (.theta 0 (prefixArgument r c)) = true := by
      simpa only [prefixNode, checkCode_code] using hcheck
    exact (PrincipalSupport.principalList_argument_lt r 0 (prefixArgument r c) s
      ht (prefix_normal r c hc) hs).le
  · exact (last_support_le r c hc hf.1 s hs).trans (first_last_le_node r c hc hf)

theorem prefix_support_cases (r c d : Nat) (hc : Node r c) (he : lowWord r c ≠ [])
    (hd : d ∈ support (prefixNode r c)) :
    d = prefixNode r c ∨ d ∈ support c := by
  rw [prefixNode, support, PrincipalSupport.listCode_code,
    RelativeTerm.PrincipalSupport.principalList_theta_same] at hd
  obtain ⟨s, hs, hsd⟩ := List.mem_map.mp hd
  rcases List.mem_cons.mp hs with hs | hs
  · exact Or.inl (by rw [← hsd, hs]; rfl)
  · have hsold := prefix_argument_support_subset r c hc s hs
    obtain ⟨a, heq, ha, hna⟩ := hc
    have hsa : s ∈ RelativeTerm.PrincipalSupport.principalList 0 a := by
      simpa only [heq, argumentCode_theta, ThetaCourse.rawTree_code] using hsold
    right
    rw [heq, support, PrincipalSupport.listCode_code]
    exact List.mem_map.mpr ⟨s, RelativeTerm.PrincipalSupport.principalList_nested 0 a s hsa, hsd⟩

theorem first_support_below_root (r c d : Nat) (hc : Node r c) (hf : FirstCase r c)
    (hd : d ∈ support c) (hlt : value r d < value r c) :
    value r d ≤ value r (prefixNode r c) := by
  obtain ⟨a, heq, ha, hn⟩ := hc
  rw [heq, support, PrincipalSupport.listCode_code,
    RelativeTerm.PrincipalSupport.principalList_theta_same] at hd
  obtain ⟨s, hs, hsd⟩ := List.mem_map.mp hd
  rcases List.mem_cons.mp hs with hs | hs
  · have hdc : d = c := by rw [← hsd, hs, heq]
    exact False.elim (by simpa only [hdc, lt_self_iff_false] using hlt)
  · have hsa : s ∈ RelativeTerm.PrincipalSupport.principalList 0
        (ThetaCourse.rawTree (argumentCode c)) := by
      simpa only [heq, argumentCode_theta, ThetaCourse.rawTree_code] using hs
    simpa only [← hsd, value, interpretation_code] using
      first_argument_support_bound r c ⟨a, heq, ha, hn⟩ hf s hsa

end Alexander313.Wilken.RelativeTerm.Hereditary.FineLocalization.Refinements
