import Alexander313.Wilken.HereditaryNativeIotaOrderSupport

/-!
# Genuine semantic addition and partial order transport for Definition 2.45

The actual existing Iota.transform preserves addition on EVERY checked
original restricted input, including raw written sums and absorbed summands.
It preserves and reflects order/equality on the complete low outer-sort part
of that domain, separates that part from its complement, preserves all
different shifted theta levels, and preserves same-level theta comparison
when their actual arguments have low outer sort. Actual weak Normality is
proved on the low part and on these shifted principal terms.

No naturality, value-invariance, order oracle, inverse, coverage, or Normal
correspondence is an input. These are substantive sublemmas of Lemma 2.46(a),
not its full isomorphism: recursive same-level comparisons with high arguments,
general weak Normal transport and image/inverse coverage remain unproved.
These source-only proof candidates have not been compiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Iota

open NativePublicBridge (contextCode contextCode_checked)

/-- Semantic addition is preserved even when the whole source sum is
atomized. Its two summands are then genuinely below alpha as well. -/
theorem transform_add (s a : Nat) (ha : rootCheck s a = true)
    (t u : RelativeTerm Nat) (ht : check (contextCode s) t = true)
    (hu : check (contextCode s) u = true) :
    denote (alphaCode s a) (transform s a (.sum t u)) =
      denote (alphaCode s a) (transform s a t) + denote (alphaCode s a) (transform s a u) := by
  have hc : check (contextCode s) (.sum t u) = true := by
    apply (check_exact _ _).mpr
    let n := max (SourceOne.PublicCodes.fragment t) (SourceOne.PublicCodes.fragment u)
    have htn := Comparison.checked_admissible _ n t ht
      ((SourceOne.PublicCodes.height_le_fragment t).trans (le_max_left _ _))
    have hun := Comparison.checked_admissible _ n u hu
      ((SourceOne.PublicCodes.height_le_fragment u).trans (le_max_right _ _))
    exact ⟨contextCode_checked s, n, ⟨⟨htn.1, hun.1⟩, .sum htn.2 hun.2⟩⟩
  cases h : small s a (.sum t u) with
  | false => simp only [transform, h, Bool.cond_false]; rfl
  | true =>
    have hs := (small_exact s a ha (.sum t u) hc).mp h
    have hst : denote (contextCode s) t < interpretation (contextCode s) a :=
      le_self_add.trans_lt hs
    have hsu : denote (contextCode s) u < interpretation (contextCode s) a :=
      le_add_self.trans_lt hs
    rw [(transform_parameter_value s a ha (.sum t u) hc hs).2,
      (transform_parameter_value s a ha t ht hst).2,
      (transform_parameter_value s a ha u hu hsu).2]
    rfl

/-- The low restriction is a theorem-consequence of the ORIGINAL domain.
All admitted hidden theta arguments and arbitrary written height remain. -/
theorem transform_low_lt_iff (s a : Nat) (ha : rootCheck s a = true)
    (t u : RelativeTerm Nat) (ht : check (contextCode s) t = true)
    (hu : check (contextCode s) u = true) (hrt : Restricted s a t)
    (hru : Restricted s a u) (hlt : t.outerSort ≤ 1) (hlu : u.outerSort ≤ 1) :
    denote (alphaCode s a) (transform s a t) < denote (alphaCode s a) (transform s a u) ↔
      denote (contextCode s) t < denote (contextCode s) u := by
  rw [transform_low_value s a ha t ht hrt hlt, transform_low_value s a ha u hu hru hlu]

theorem transform_low_eq_iff (s a : Nat) (ha : rootCheck s a = true)
    (t u : RelativeTerm Nat) (ht : check (contextCode s) t = true)
    (hu : check (contextCode s) u = true) (hrt : Restricted s a t)
    (hru : Restricted s a u) (hlt : t.outerSort ≤ 1) (hlu : u.outerSort ≤ 1) :
    denote (alphaCode s a) (transform s a t) = denote (alphaCode s a) (transform s a u) ↔
      denote (contextCode s) t = denote (contextCode s) u := by
  rw [transform_low_value s a ha t ht hrt hlt, transform_low_value s a ha u hu hru hlu]

theorem transform_low_high_lt (s a : Nat) (ha : rootCheck s a = true)
    (t u : RelativeTerm Nat) (ht : check (contextCode s) t = true)
    (hu : check (contextCode s) u = true) (hrt : Restricted s a t)
    (hru : Restricted s a u) (hlt : t.outerSort ≤ 1) (hhu : 1 < u.outerSort) :
    denote (contextCode s) t < denote (contextCode s) u ∧
      denote (alphaCode s a) (transform s a t) < denote (alphaCode s a) (transform s a u) := by
  have hts := restricted_low_below s a ha t ht hrt hlt
  have hus : interpretation (contextCode s) a ≤ denote (contextCode s) u := by
    apply le_of_not_gt
    intro h
    have hl := (restricted_below_iff_outerSort s a ha u hu hru).mp h
    omega
  exact ⟨hts.trans_le hus, ((transform_below_base_iff s a ha t ht hrt).mpr hts).trans_le
    (transform_ge_base s a ha u hu hru hus)⟩

theorem transform_shifted_normal_low_argument (s a k : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (contextCode s) (.theta (k + 1) t) = true)
    (hr : Restricted s a (.theta (k + 1) t)) (hl : t.outerSort ≤ 1) :
    Comparison.Normal (alphaCode s a) (transform s a (.theta (k + 1) t)) := by
  rw [transform_theta_succ s a k ha t ht hr]
  exact transform_low_normal s a ha t
    (BaseTransformation.theta_argument_check _ (k + 1) t ht)
    ((restricted_theta_succ s a k t).mp hr) hl

/-- Distinct retained levels compare strictly in both actual collapsing
families, using their derived genuine cardinal intervals. -/
theorem transform_shifted_level_lt (s a k l : Nat) (ha : rootCheck s a = true)
    (t u : RelativeTerm Nat) (ht : check (contextCode s) (.theta (k + 1) t) = true)
    (hu : check (contextCode s) (.theta (l + 1) u) = true)
    (hrt : Restricted s a (.theta (k + 1) t))
    (hru : Restricted s a (.theta (l + 1) u)) (hkl : k < l) :
    denote (contextCode s) (.theta (k + 1) t) < denote (contextCode s) (.theta (l + 1) u) ∧
      denote (alphaCode s a) (transform s a (.theta (k + 1) t)) <
        denote (alphaCode s a) (transform s a (.theta (l + 1) u)) := by
  have source_lt (q i j : Nat) (x y : RelativeTerm Nat)
      (hx : check q (.theta i x) = true) (hy : check q (.theta j y) = true)
      (hij : i < j) : denote q (.theta i x) < denote q (.theta j y) := by
    let n := max (SourceOne.PublicCodes.fragment (.theta i x))
      (SourceOne.PublicCodes.fragment (.theta j y))
    have hxn := Comparison.checked_admissible q n (.theta i x) hx
      ((SourceOne.PublicCodes.height_le_fragment _).trans (le_max_left _ _))
    have hyn := Comparison.checked_admissible q n (.theta j y) hy
      ((SourceOne.PublicCodes.height_le_fragment _).trans (le_max_right _ _))
    rw [denote_eq_finite q n (Bool.and_eq_true.mp hx).1 _ hxn.2,
      denote_eq_finite q n (Bool.and_eq_true.mp hx).1 _ hyn.2]
    exact Comparison.theta_lt_of_level_lt q n i j x y hxn hyn hij
  have hct := transform_checked s a ha (.theta (k + 1) t) ht hrt
  have hcu := transform_checked s a ha (.theta (l + 1) u) hu hru
  rw [transform_theta_succ s a k ha t ht hrt] at hct
  rw [transform_theta_succ s a l ha u hu hru] at hcu
  refine ⟨source_lt _ (k + 1) (l + 1) t u ht hu (by omega), ?_⟩
  rw [transform_theta_succ s a k ha t ht hrt, transform_theta_succ s a l ha u hu hru]
  exact source_lt _ k l _ _ hct hcu hkl

/-- Actual same-level comparison with low arguments has empty exposed
support on BOTH sides. This proves a genuine shifted collapse order law,
without postulating any equation between the two collapse families. -/
theorem transform_shifted_theta_lt_iff_low_arguments (s a k : Nat)
    (ha : rootCheck s a = true) (t u : RelativeTerm Nat)
    (ht : check (contextCode s) (.theta (k + 1) t) = true)
    (hu : check (contextCode s) (.theta (k + 1) u) = true)
    (hrt : Restricted s a (.theta (k + 1) t))
    (hru : Restricted s a (.theta (k + 1) u))
    (hnt : Comparison.Normal (contextCode s) t)
    (hnu : Comparison.Normal (contextCode s) u)
    (hlt : t.outerSort ≤ 1) (hlu : u.outerSort ≤ 1) :
    denote (alphaCode s a) (transform s a (.theta (k + 1) t)) <
        denote (alphaCode s a) (transform s a (.theta (k + 1) u)) ↔
      denote (contextCode s) (.theta (k + 1) t) < denote (contextCode s) (.theta (k + 1) u) := by
  have htc := BaseTransformation.theta_argument_check _ (k + 1) t ht
  have huc := BaseTransformation.theta_argument_check _ (k + 1) u hu
  have htr := (restricted_theta_succ s a k t).mp hrt
  have hur := (restricted_theta_succ s a k u).mp hru
  have hct := transform_checked s a ha (.theta (k + 1) t) ht hrt
  have hcu := transform_checked s a ha (.theta (k + 1) u) hu hru
  rw [transform_theta_succ s a k ha t ht hrt] at hct
  rw [transform_theta_succ s a k ha u hu hru] at hcu
  have source_compare (q i : Nat) (x y : RelativeTerm Nat)
      (hx : check q (.theta i x) = true) (hy : check q (.theta i y) = true)
      (hnx : Comparison.Normal q x) (hny : Comparison.Normal q y)
      (hex : exposedThetaList i x = []) (hey : exposedThetaList i y = []) :
      denote q (.theta i x) < denote q (.theta i y) ↔ denote q x < denote q y := by
    let n := max (SourceOne.PublicCodes.fragment (.theta i x))
      (SourceOne.PublicCodes.fragment (.theta i y))
    have hxn := Comparison.checked_admissible q n (.theta i x) hx
      ((SourceOne.PublicCodes.height_le_fragment _).trans (le_max_left _ _))
    have hyn := Comparison.checked_admissible q n (.theta i y) hy
      ((SourceOne.PublicCodes.height_le_fragment _).trans (le_max_right _ _))
    rw [Comparison.theta_lt_iff_exposed q n i (Bool.and_eq_true.mp hx).1 x y hxn hyn hnx hny,
      hex, hey]
    simp
  have hs := source_compare (contextCode s) (k + 1) t u ht hu hnt hnu
    (exposedThetaList_low (k + 1) (by omega) t hlt)
    (exposedThetaList_low (k + 1) (by omega) u hlu)
  have htt : Comparison.Normal (alphaCode s a) (transform s a t) :=
    transform_low_normal s a ha t htc htr hlt
  have hut : Comparison.Normal (alphaCode s a) (transform s a u) :=
    transform_low_normal s a ha u huc hur hlu
  have hte : exposedThetaList k (transform s a t) = [] := by
    rw [transform_low s a ha t htc htr hlt]; rfl
  have hue : exposedThetaList k (transform s a u) = [] := by
    rw [transform_low s a ha u huc hur hlu]; rfl
  rw [transform_theta_succ s a k ha t ht hrt, transform_theta_succ s a k ha u hu hru,
    source_compare (alphaCode s a) k _ _ hct hcu htt hut hte hue,
    transform_low_value s a ha t htc htr hlt, transform_low_value s a ha u huc hur hlu, hs]

theorem transform_shifted_theta_eq_iff_low_arguments (s a k : Nat)
    (ha : rootCheck s a = true) (t u : RelativeTerm Nat)
    (ht : check (contextCode s) (.theta (k + 1) t) = true)
    (hu : check (contextCode s) (.theta (k + 1) u) = true)
    (hrt : Restricted s a (.theta (k + 1) t))
    (hru : Restricted s a (.theta (k + 1) u))
    (hnt : Comparison.Normal (contextCode s) t)
    (hnu : Comparison.Normal (contextCode s) u)
    (hlt : t.outerSort ≤ 1) (hlu : u.outerSort ≤ 1) :
    denote (alphaCode s a) (transform s a (.theta (k + 1) t)) =
        denote (alphaCode s a) (transform s a (.theta (k + 1) u)) ↔
      denote (contextCode s) (.theta (k + 1) t) = denote (contextCode s) (.theta (k + 1) u) := by
  have htu := transform_shifted_theta_lt_iff_low_arguments s a k ha t u ht hu hrt hru hnt hnu hlt hlu
  have hut := transform_shifted_theta_lt_iff_low_arguments s a k ha u t hu ht hru hrt hnu hnt hlu hlt
  constructor
  · intro h
    exact le_antisymm (le_of_not_gt (fun hv => (hut.mpr hv).ne h.symm))
      (le_of_not_gt (fun hv => (htu.mpr hv).ne h))
  · intro h
    exact le_antisymm (le_of_not_gt (fun hv => (hut.mp hv).ne h.symm))
      (le_of_not_gt (fun hv => (htu.mp hv).ne h))

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Iota
