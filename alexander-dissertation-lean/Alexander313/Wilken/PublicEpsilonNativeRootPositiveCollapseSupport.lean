import Alexander313.Wilken.PublicEpsilonNativeRootLowCollapse

/-!
# Actual positive-index relative collapse at the original coded context

The original checked Normal high root supplies beta and the identical
positive cardinal suffix. Actual finite hull/minimum recursion proves all
positive finite collapse values equal. Genuine notation and sorted-bound
theorems derive one legitimate fragment for both global callers.

The finite producer retains the SAME positive theta index at the ORIGINAL
q and derives admission from the original argument checker and sort. It
needs no public beta representation or selected-return endpoint. The
zero-index HIGH return and the full iota/Par construction remain separate.
All candidates are source-only and uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RootPositiveCollapse

open ThetaCourse

abbrev Query := Nat × (Nat × (Nat × Nat))

theorem root_omegaSequence_pos (q b k : Nat) (ha : RootLowCollapse.rootCheck q b = true)
    (hk : 0 < k) :
    omegaSequence (base q) k = omegaSequence (interpretation q b) k := by
  have hz := Iota.HeightSupport.levelCardinal_zero_eq_of_interval (base q)
    (interpretation q b) (RootLowCollapse.root_base_le q b ha)
    (RootLowCollapse.root_lt_first q b ha)
  cases k with
  | zero => omega
  | succ k => exact congrArg Cardinal.ord
      (Iota.HeightSupport.levelCardinal_eq_of_zero_eq _ _ hz (k + 1))

/-- Both genuine finite minimum recursions agree at every positive index,
for every ordinal argument, including their total fallback values. -/
theorem positive_finiteCollapse_eq (q b n k : Nat)
    (ha : RootLowCollapse.rootCheck q b = true) (hk : 0 < k) (hkn : k < n)
    (ξ : Ordinal.{0}) :
    sourceFiniteCollapse (base q) n k ξ =
      sourceFiniteCollapse (interpretation q b) n k ξ := by
  apply Iota.HeightSupport.finiteCollapse_suffix_congr _ _ n 1 k _ (by omega) hkn ξ
  intro j hj
  exact root_omegaSequence_pos q b j ha (by omega)

/-- This is actual notation transport at every positive parameter level.
All higher and local calls agree by the finite recursion just proved. -/
theorem positive_notation_iff (q b n m : Nat)
    (ha : RootLowCollapse.rootCheck q b = true) (hm : 0 < m) (ξ : Ordinal.{0}) :
    sourceNotation (base q) n m ξ ↔ sourceNotation (interpretation q b) n m ξ := by
  by_cases hmn : m < n
  · rw [sourceNotation_iff_hull (base q) n m hmn ξ,
      sourceNotation_iff_hull (interpretation q b) n m hmn ξ,
      ← root_omegaSequence_pos q b (m + 2) ha (by omega)]
    exact Iota.HeightSupport.hull_suffix_congr _ _ _ _ n m _ 0 ξ
      (fun k hk => root_omegaSequence_pos q b k ha (hm.trans_le hk))
      (fun k hmk hkn η => positive_finiteCollapse_eq q b n k ha (hm.trans hmk) hkn η)
      (fun η _ => positive_finiteCollapse_eq q b n m ha hm hmn η)
  · simp only [sourceNotation, if_neg hmn, root_omegaSequence_pos q b m ha hm]

/-- Actual original native admission supplies notation at k+1. The real
sorted finite-coverage theorem derives BOTH global input boundaries. -/
theorem positive_collapse_eq (q b k : Nat)
    (ha : RootLowCollapse.rootCheck q b = true) (hk : 0 < k)
    (t : RelativeTerm Nat) (ht : check q t = true) (hs : t.outerSort ≤ k + 2) :
    globalCollapse (base q) k (denote q t) =
      globalCollapse (interpretation q b) k (denote q t) := by
  have hq := RootLowCollapse.source_checked q b ha
  have hτ := base_pos q hq
  have hβ : 0 < interpretation q b := hτ.trans_le (RootLowCollapse.root_base_le q b ha)
  have hn := FixedPoint.checked_notation_at q t ht (k + 1)
  obtain ⟨n, hkn, hnt⟩ := globalNotation_finite_witness (base q) hτ (k + 1) hn
  have hnb := (positive_notation_iff q b n (k + 1) ha (by omega) (denote q t)).mp hnt
  have hsort : denote q t < omegaSequence (base q) (k + 2) :=
    (denote_lt_iff_outerSort_le q t ht (k + 2) (by omega)).mpr hs
  have hsortβ : denote q t < omegaSequence (interpretation q b) (k + 2) := by
    rw [← root_omegaSequence_pos q b (k + 2) ha (by omega)]
    exact hsort
  have hbτ := source_finite_notation_sorted_lt_boundary (base q) hτ n (k + 1) (k + 1)
    le_rfl hkn hnt hsort
  have hbβ := source_finite_notation_sorted_lt_boundary (interpretation q b) hβ n
    (k + 1) (k + 1) le_rfl hkn hnb hsortβ
  rw [globalCollapse_finite_agreement (base q) hτ n k (by omega) _ hbτ,
    globalCollapse_finite_agreement (interpretation q b) hβ n k (by omega) _ hbβ]
  exact positive_finiteCollapse_eq q b n k ha hk (by omega) _

/-- The actual native finite checker derives the positive node admission
from the ORIGINAL argument checker and its literal sort bound. -/
theorem theta_checked (q k : Nat) (t : RelativeTerm Nat)
    (ht : check q t = true) (hs : t.outerSort ≤ k + 2) : check q (.theta k t) = true := by
  have hq := (Bool.and_eq_true.mp ht).1
  let n := SourceOne.PublicCodes.fragment (.theta k t)
  have hn : t.height ≤ n := (le_max_right (k + 1) t.height).trans
    (SourceOne.PublicCodes.height_le_fragment (.theta k t))
  have had := Comparison.checked_admissible q n t ht hn
  have hkn : k < n := by
    have h := (le_max_left (k + 1) t.height).trans
      (SourceOne.PublicCodes.height_le_fragment (.theta k t))
    omega
  exact Comparison.admitted_checked q n hq _
    ⟨had.1, .theta (Nat.zero_le k) hkn
      ((source_eval_lt_iff_outerSort_le (base q) parameters n t had.2 (k + 2)
        (by omega)).mpr hs) had.2⟩

def nodeCode (k c : Nat) : Nat := (.theta k (rawTree c) : RelativeTerm Nat).code

theorem nodeCode_primrec : Primrec₂ nodeCode :=
  (code_primrec.comp (theta_primrec.comp Primrec.fst (rawTree_primrec.comp Primrec.snd))).to₂

def inputCheck (q b k c : Nat) : Bool := RootLowCollapse.rootCheck q b &&
  (Comparison.acceptedCode q c &&
    (decide (0 < k) && decide ((rawTree c).outerSort ≤ k + 2)))

theorem inputCheck_primrec : Primrec (fun p : Query => inputCheck p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hq : Primrec (fun p : Query => p.1) := Primrec.fst
  have hb : Primrec (fun p : Query => p.2.1) := Primrec.fst.comp Primrec.snd
  have hk : Primrec (fun p : Query => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hc : Primrec (fun p : Query => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hpos := (Primrec.nat_lt.comp (Primrec.const 0) hk).decide
  have hsort := (Primrec.nat_le.comp (outerSort_primrec.comp (rawTree_primrec.comp hc))
    (Primrec.nat_add.comp hk (Primrec.const 2))).decide
  exact Primrec.and.comp (RootLowCollapse.rootCheck_primrec.comp hq hb)
    (Primrec.and.comp (Comparison.acceptedCode_primrec.comp hq hc)
      (Primrec.and.comp hpos hsort))

theorem inputCheck_exact (q b k c : Nat) : inputCheck q b k c = true ↔
    RootLowCollapse.rootCheck q b = true ∧ Comparison.acceptedCode q c = true ∧
      0 < k ∧ (rawTree c).outerSort ≤ k + 2 := by
  simp only [inputCheck, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

def collapseCode (q b k c : Nat) : Nat := cond (inputCheck q b k c) (nodeCode k c) 0

theorem collapseCode_primrec : Primrec (fun p : Query => collapseCode p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  inputCheck_primrec.cond
    (nodeCode_primrec.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))) (Primrec.const 0)

/-- The executing output is accepted Normal at ORIGINAL q and has the
actual positive-index beta-collapse value on every original guarded input. -/
theorem collapseCode_spec (q b k c : Nat) (hi : inputCheck q b k c = true) :
    Comparison.acceptedCode q (collapseCode q b k c) = true ∧
      interpretation q (collapseCode q b k c) =
        globalCollapse (interpretation q b) k (interpretation q c) := by
  have hs := (inputCheck_exact q b k c).mp hi
  have hc := (Comparison.acceptedCode_exact q c).mp hs.2.1
  have ht := Arithmetic.raw_checked q c hc.1
  have hn := theta_checked q k (rawTree c) ht hs.2.2.2
  simp only [collapseCode, hi, Bool.cond_true, nodeCode]
  refine ⟨(Comparison.acceptedCode_exact _ _).mpr
    ⟨by simpa only [checkCode_code] using hn,
      by simpa only [rawTree_code, Comparison.Normal] using hc.2⟩, ?_⟩
  simp only [interpretation_code]
  change globalCollapse (base q) k (denote q (rawTree c)) = _
  rw [positive_collapse_eq q b k hs.1 hs.2.2.1 (rawTree c) ht hs.2.2.2,
    Arithmetic.raw_value q c hc.1]

theorem collapseCode_eq (q b k c : Nat) (hi : inputCheck q b k c = true) :
    collapseCode q b k c = nodeCode k c := by simp only [collapseCode, hi, Bool.cond_true]

theorem collapseCode_rejected (q b k c : Nat) (hi : inputCheck q b k c = false) :
    collapseCode q b k c = 0 := by simp only [collapseCode, hi, Bool.cond_false]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RootPositiveCollapse
