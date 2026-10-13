import Alexander313.Wilken.HereditaryNativeIotaInverse
import Alexander313.Wilken.HereditaryNativeHeightBoundary

/-!
# Genuine same-alpha height support and source inverse parameter bounds

Positive cardinal levels of the actual source and alpha contexts agree,
derived from source base <= alpha < source Omega1. The actual hull/minimum
recursion then agrees at every positive index, without any collapse-naturality
premise. This supports an unshifted SAME-VALUE alpha presentation.

The genuine LOW inverse parameter return has source height at most alpha's
source height, by the already constructed endpoint minimum theorem.
All proof candidates are uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Iota.HeightSupport

open NativePublicBridge (contextCode contextCode_checked)

theorem accepted_of_checked_normal (q : Nat) (t : RelativeTerm Nat)
    (ht : check q t = true) (hn : Comparison.Normal q t) :
    Comparison.acceptedCode q t.code = true :=
  (Comparison.acceptedCode_exact q _).mpr
    ⟨by simpa only [checkCode_code] using ht, by simpa only [ThetaCourse.rawTree_code] using hn⟩

theorem canonical_height_normal (q : Nat) (t : RelativeTerm Nat)
    (ht : check q t = true) (hn : Comparison.Normal q t) :
    CanonicalHeight.canonicalHeightCode q t.code = t.height := by
  rw [CanonicalHeight.canonicalHeightCode_normal q t.code (accepted_of_checked_normal q t ht hn),
    heightCode_code]

theorem root_accepted (s a : Nat) (ha : rootCheck s a = true) :
    Comparison.acceptedCode (contextCode s) a = true :=
  (Bool.and_eq_true.mp (Bool.and_eq_true.mp ha).1).1

theorem source_low_height_le_root (s a : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (contextCode s) t = true)
    (hn : Comparison.Normal (contextCode s) t) (hl : t.outerSort ≤ 1)
    (hb : denote (contextCode s) t < interpretation (contextCode s) a) :
    t.height ≤ CanonicalHeight.canonicalHeightCode (contextCode s) a := by
  have hc : lowCheckCode (contextCode s) t.code = true := by
    simp only [lowCheckCode_code, lowCheck, ht, hl, decide_true, Bool.true_and]
  have hr := (HeightBoundary.canonicalHeightCode_le_iff_endpoint (contextCode s)
    (CanonicalHeight.canonicalHeightCode (contextCode s) a) a (root_low s a ha)).mp le_rfl
  have hh := (HeightBoundary.canonicalHeightCode_le_iff_endpoint (contextCode s)
    (CanonicalHeight.canonicalHeightCode (contextCode s) a) t.code hc).mpr
    (by simpa only [interpretation_code] using hb.trans hr)
  simpa only [canonical_height_normal _ t ht hn] using hh

/-- All actual target parameters, with no supplied source representation,
have a genuine LOW source return whose height is bounded by the root. -/
theorem inverse_atom_height (s a p : Nat) (ha : rootCheck s a = true)
    (hp : parameterCheck (alphaCode s a) p = true) :
    (Inverse.atomTerm s p).height ≤ CanonicalHeight.canonicalHeightCode (contextCode s) a := by
  have hs := Inverse.atom_spec s a p ha hp
  apply source_low_height_le_root s a ha _ hs.1 hs.2.1 hs.2.2.1
  rw [hs.2.2.2]
  simpa only [alpha_base s a ha] using parameter_sound _ p hp

theorem levelCardinal_zero_eq_of_interval (τ σ : Ordinal.{0})
    (hle : τ ≤ σ) (hlt : σ < omegaSequence τ 1) : levelCardinal τ 0 = levelCardinal σ 0 := by
  have hs : σ.card ≤ max Cardinal.aleph0 τ.card := by
    apply Order.lt_succ_iff.mp
    have h := Cardinal.lt_ord.mp hlt
    simpa only [omegaSequence, levelCardinal] using h
  change max Cardinal.aleph0 τ.card = max Cardinal.aleph0 σ.card
  exact le_antisymm (max_le_max le_rfl (Ordinal.card_le_card hle))
    (max_le (le_max_left _ _) hs)

theorem levelCardinal_eq_of_zero_eq (τ σ : Ordinal.{0})
    (hzero : levelCardinal τ 0 = levelCardinal σ 0) (k : Nat) :
    levelCardinal τ k = levelCardinal σ k := by
  induction k with
  | zero => exact hzero
  | succ k ih => exact congrArg Order.succ ih

theorem root_omegaSequence_succ (s a k : Nat) (ha : rootCheck s a = true) :
    omegaSequence (base (contextCode s)) (k + 1) = omegaSequence (base (alphaCode s a)) (k + 1) := by
  have hzero := levelCardinal_zero_eq_of_interval (base (contextCode s))
    (interpretation (contextCode s) a) (root_base_le s a ha) (root_below_first_cardinal s a ha)
  rw [← alpha_base s a ha] at hzero
  exact congrArg Cardinal.ord (levelCardinal_eq_of_zero_eq _ _ hzero (k + 1))

/-- Genuine closure rules see only the cardinal suffix starting at m and
already defined higher/local theta calls. This helper has explicit recursion
inputs; the next theorem proves them for the actual finite collapse. -/
theorem hull_suffix_congr (omega omega' : Nat → Ordinal.{0})
    (theta theta' : Nat → Ordinal.{0} → Ordinal.{0}) (n m : Nat) (α β ξ : Ordinal.{0})
    (homega : ∀ k, m ≤ k → omega k = omega' k)
    (higher : ∀ k, m < k → k < n → ∀ η, theta k η = theta' k η)
    (localEq : ∀ η, η < α → theta m η = theta' m η) :
    Hull omega theta n m α β ξ ↔ Hull omega' theta' n m α β ξ := by
  have forward (first second : Nat → Ordinal.{0})
      (f g : Nat → Ordinal.{0} → Ordinal.{0})
      (hω : ∀ k, m ≤ k → first k = second k)
      (hh : ∀ k, m < k → k < n → ∀ η, f k η = g k η)
      (hl : ∀ η, η < α → f m η = g m η)
      (h : Hull first f n m α β ξ) : Hull second g n m α β ξ := by
    induction h with
    | below_base h => exact .below_base (by simpa only [← hω m le_rfl] using h)
    | below_parameter h => exact .below_parameter h
    | add _ _ ihξ ihη => exact .add ihξ ihη
    | higher hmk hkn hsort _ ih =>
      rw [hh _ hmk hkn _]
      exact .higher hmk hkn (by simpa only [← hω _ (by omega)] using hsort) ih
    | «local» hη _ ih =>
      rw [hl _ hη]
      exact .«local» hη ih
  exact ⟨forward omega omega' theta theta' homega higher localEq,
    forward omega' omega theta' theta (fun k hk => (homega k hk).symm)
      (fun k hmk hkn η => (higher k hmk hkn η).symm) (fun η hη => (localEq η hη).symm)⟩

/-- The actual descending-level/ordinal recursion proves suffix agreement
for every ordinal argument, including fallback values. -/
theorem finiteCollapse_suffix_congr (omega omega' : Nat → Ordinal.{0}) (n l m : Nat)
    (homega : ∀ k, l ≤ k → omega k = omega' k) (hlm : l ≤ m) (hmn : m < n)
    (α : Ordinal.{0}) : finiteCollapse omega n m α = finiteCollapse omega' n m α := by
  have all : ∀ j : Fin n, l ≤ j.val → ∀ η : Ordinal.{0},
      finiteCollapse omega n j.val η = finiteCollapse omega' n j.val η := by
    intro j
    refine (InvImage.wf (fun k : Fin n => n - k.val) Nat.lt_wfRel.wf).induction j ?_
    intro j ih hj η
    refine Ordinal.induction η ?_
    intro η localIH
    have higher : ∀ k, j.val < k → k < n → ∀ γ,
        finiteCollapse omega n k γ = finiteCollapse omega' n k γ := by
      intro k hjk hkn γ
      exact ih ⟨k, hkn⟩ (by change n - k < n - j.val; have h := j.isLt; omega)
        (by omega) γ
    have localEq : ∀ γ, γ < η → finiteCollapse omega n j.val γ = finiteCollapse omega' n j.val γ :=
      fun γ hγ => localIH γ hγ
    have hh (β ξ : Ordinal.{0}) := hull_suffix_congr omega omega'
      (finiteCollapse omega n) (finiteCollapse omega' n) n j.val η β ξ
      (fun k hk => homega k (hj.trans hk)) higher localEq
    have hc : collapseCandidates omega (finiteCollapse omega n) n j.val η =
        collapseCandidates omega' (finiteCollapse omega' n) n j.val η := by
      ext β
      simp only [collapseCandidates, Set.mem_setOf_eq, CollapseCandidate]
      rw [homega (j.val + 1) (by omega)]
      simp_rw [hh]
    rw [finiteCollapse_eq omega n j.val j.isLt η, finiteCollapse_eq omega' n j.val j.isLt η]
    exact congrArg sInf hc
  exact all ⟨m, hmn⟩ hlm α

theorem root_positive_finiteCollapse (s a n k : Nat) (ha : rootCheck s a = true)
    (hk : 0 < k) (hkn : k < n) (ξ : Ordinal.{0}) :
    sourceFiniteCollapse (base (contextCode s)) n k ξ =
      sourceFiniteCollapse (base (alphaCode s a)) n k ξ := by
  apply finiteCollapse_suffix_congr _ _ n 1 k _ (by omega) hkn ξ
  intro j hj
  cases j with
  | zero => omega
  | succ j => exact root_omegaSequence_succ s a j ha

/-- Real checked positive-index theta nodes at the two contexts have equal
values whenever their actual argument values agree. Equality of the collapse
families is a conclusion of the hull recursion above, not a hypothesis. -/
theorem root_positive_theta_value (s a k : Nat) (ha : rootCheck s a = true)
    (t u : RelativeTerm Nat) (hk : 0 < k)
    (ht : check (contextCode s) (.theta k t) = true)
    (hu : check (alphaCode s a) (.theta k u) = true)
    (hv : denote (alphaCode s a) u = denote (contextCode s) t) :
    denote (alphaCode s a) (.theta k u) = denote (contextCode s) (.theta k t) := by
  let n := max (SourceOne.PublicCodes.fragment (.theta k t))
    (SourceOne.PublicCodes.fragment (.theta k u))
  have htn := Comparison.checked_admissible _ n (.theta k t) ht
    ((SourceOne.PublicCodes.height_le_fragment _).trans (le_max_left _ _))
  have hun := Comparison.checked_admissible _ n (.theta k u) hu
    ((SourceOne.PublicCodes.height_le_fragment _).trans (le_max_right _ _))
  have hkn : k < n := by
    cases htn.2 with
    | theta h0k hkn hsort ht => exact hkn
  have hta := Comparison.admitted_argument htn
  have hua := Comparison.admitted_argument hun
  rw [denote_eq_finite _ n (alphaCode_baseCheck s a ha) _ hun.2,
    denote_eq_finite _ n (contextCode_checked s) _ htn.2]
  change sourceFiniteCollapse (base (alphaCode s a)) n k (finiteDenote _ n u) =
    sourceFiniteCollapse (base (contextCode s)) n k (finiteDenote _ n t)
  rw [← denote_eq_finite _ n (alphaCode_baseCheck s a ha) u hua.2,
    ← denote_eq_finite _ n (contextCode_checked s) t hta.2, hv,
    root_positive_finiteCollapse s a n k ha hk hkn]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Iota.HeightSupport
