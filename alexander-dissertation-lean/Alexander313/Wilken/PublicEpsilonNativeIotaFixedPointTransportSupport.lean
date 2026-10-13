import Alexander313.Wilken.PublicEpsilonNativeOmegaQuotientSupport
import Alexander313.Wilken.PublicEpsilonNativeReturnedIotaSupport
import Alexander313.Wilken.HereditaryNativeFixedPoint

/-!
# Actual shifted principal-word cuts under generic iota

Original small subtrees become parameters, whose entire comparison word is
LOW. Every positive source atom lowers its literal index by one. The genuine
original checked restricted domain therefore identifies the WHOLE transformed
high word with the mapped original word at the shifted cardinal cut. No
parameter payload equality, supplied ANF transport or target cutoff is used.
This is a fixed-point transport dependency, not a beta/q chi identification.
Source-only and uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonIota.FixedPointTransport

open ThetaCourse

private theorem select_append (m : Nat) (as bs : List (RelativeTerm Nat)) :
    Decomposition.select true m (as ++ bs) =
      Decomposition.select true m as ++ Decomposition.select true m bs := by
  simp only [Decomposition.select_filter, List.filter_append]

private theorem select_parameters (m : Nat) (ps : List Nat) :
    Decomposition.select true m (ps.map RelativeTerm.parameter) = [] := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, Decomposition.select, Bool.cond_true,
      Decomposition.above, outerSort, Nat.not_lt_zero, decide_false,
      Bool.cond_false, ih]

theorem selected_atoms_parameter (m p : Nat) :
    Decomposition.select true m (Comparison.atoms (.parameter p)) = [] :=
  select_parameters m (CanonicalCoefficients.word p)

theorem selected_atoms_low (m : Nat) (t : RelativeTerm Nat)
    (hs : t.outerSort ≤ m + 1) :
    Decomposition.select true m (Comparison.atoms t) = [] := by
  revert hs
  induction t with
  | parameter p => intro hs; exact selected_atoms_parameter m p
  | sum t u iht ihu =>
    intro hs
    have ht : t.outerSort ≤ m + 1 := (le_max_left _ _).trans hs
    have hu : u.outerSort ≤ m + 1 := (le_max_right _ _).trans hs
    simpa only [Comparison.atoms, select_append, iht ht, ihu hu, List.nil_append]
  | theta k t ih =>
    intro hs
    have hn : ¬m + 1 < (.theta k t : RelativeTerm Nat).outerSort := not_lt_of_ge hs
    simp only [Comparison.atoms, Decomposition.select, Decomposition.above,
      decide_eq_false hn, Bool.cond_true, Bool.cond_false]

private theorem above_theta_shift (m k : Nat) (t u : RelativeTerm Nat) :
    Decomposition.above m (.theta k u) = Decomposition.above (m + 1) (.theta (k + 1) t) := by
  simp only [Decomposition.above, outerSort, Nat.add_lt_add_iff_right]

/-- The complete actual high comparison word shifts by one. Small
parameter expansions are discarded by both genuine cardinal cuts. -/
theorem selected_atoms_transform (q b m : Nat) (ha : rootCheck q b = true)
    (t : RelativeTerm Nat) (ht : check q t = true) (hr : Restricted q b t) :
    Decomposition.select true m (Comparison.atoms (transform q b t)) =
      (Decomposition.select true (m + 1) (Comparison.atoms t)).map (transform q b) := by
  revert ht hr
  induction t with
  | parameter p =>
    intro ht hr
    simp only [transform, selected_atoms_parameter, List.map_nil]
  | sum t u iht ihu =>
    intro ht hr
    have hc := BaseTransformation.sum_checks q t u ht
    have hrs := (restricted_sum q b t u).mp hr
    cases he : small q b (.sum t u) with
    | true =>
      have hs := (OrderSupport.small_iff_outerSort q b ha _ ht hr).mp he
      simp only [transform, he, Bool.cond_true, selected_atoms_parameter,
        selected_atoms_low (m + 1) (.sum t u) (by omega), List.map_nil]
    | false =>
      simp only [transform, he, Bool.cond_false, Comparison.atoms, select_append,
        iht hc.1 hrs.1, ihu hc.2 hrs.2, List.map_append]
  | theta k t ih =>
    intro ht hr
    cases k with
    | zero =>
      simp only [OrderSupport.transform_low q b ha (.theta 0 t) ht hr le_rfl,
        selected_atoms_parameter, selected_atoms_low (m + 1) (.theta 0 t) (by
          simp only [outerSort]; omega), List.map_nil]
    | succ k =>
      rw [OrderSupport.transform_theta_succ q b k ha t ht hr]
      simp only [Comparison.atoms, Decomposition.select, Bool.cond_true,
        above_theta_shift m k t (transform q b t)]
      cases he : Decomposition.above (m + 1) (.theta (k + 1) t) <;>
        simp only [he, Bool.cond_true, Bool.cond_false, List.map_cons, List.map_nil,
          OrderSupport.transform_theta_succ q b k ha t ht hr]

theorem highWord_transform (q b m : Nat) (ha : rootCheck q b = true)
    (t : RelativeTerm Nat) (ht : check q t = true) (hr : Restricted q b t) :
    Decomposition.highWord m (transform q b t).code =
      (Decomposition.highWord (m + 1) t.code).map (transform q b) := by
  simpa only [Decomposition.highWord, Decomposition.word, rawTree_code] using
    selected_atoms_transform q b m ha t ht hr

/-- Every literal cardinal sort drops exactly once, including complete
small stops and weak-normal sums with zero prefixes. -/
theorem transform_outerSort_eq (q b : Nat) (ha : rootCheck q b = true)
    (t : RelativeTerm Nat) (ht : check q t = true) (hr : Restricted q b t) :
    (transform q b t).outerSort = t.outerSort - 1 := by
  revert ht hr
  induction t with
  | parameter p => intro ht hr; rfl
  | sum t u iht ihu =>
    intro ht hr
    have hc := BaseTransformation.sum_checks q t u ht
    have hrs := (restricted_sum q b t u).mp hr
    cases he : small q b (.sum t u) with
    | true =>
      have hs := (OrderSupport.small_iff_outerSort q b ha _ ht hr).mp he
      simp only [transform, he, Bool.cond_true, outerSort]
      simp only [outerSort] at hs
      omega
    | false =>
      simp only [transform, he, Bool.cond_false, outerSort,
        iht hc.1 hrs.1, ihu hc.2 hrs.2]
      omega
  | theta k t ih =>
    intro ht hr
    cases k with
    | zero =>
      rw [OrderSupport.transform_low q b ha (.theta 0 t) ht hr le_rfl]
      rfl
    | succ k =>
      rw [OrderSupport.transform_theta_succ q b k ha t ht hr]
      simp only [outerSort, Nat.add_sub_cancel]

theorem less_transform (q b : Nat) (ha : rootCheck q b = true)
    (t u : RelativeTerm Nat) (ht : check q t = true) (hu : check q u = true)
    (hnt : Comparison.Normal q t) (hnu : Comparison.Normal q u)
    (hrt : Restricted q b t) (hru : Restricted q b u) :
    Comparison.less (betaCode q b) (transform q b t) (transform q b u) =
      Comparison.less q t u := by
  apply Bool.eq_iff_iff.mpr
  rw [Comparison.less_correct (betaCode q b) _ _
    (transform_checked q b ha t ht hrt) (transform_checked q b ha u hu hru)
    (transform_normal q b ha t ht hnt hrt) (transform_normal q b ha u hu hnu hru),
    Comparison.less_correct q t u ht hu hnt hnu]
  exact transform_lt_iff q b ha t u ht hu hnt hnu hrt hru

/-- The actual exposed-list star TEST agrees at the shifted level.
Every smaller exposed comparison caller is derived from original syntax. -/
theorem starLess_transform (q b m : Nat) (ha : rootCheck q b = true)
    (t u : RelativeTerm Nat) (ht : check q t = true) (hu : check q u = true)
    (hnt : Comparison.Normal q t) (hnu : Comparison.Normal q u)
    (hrt : Restricted q b t) (hru : Restricted q b u) :
    FixedPoint.starLess (betaCode q b) m (transform q b t) (transform q b u) =
      FixedPoint.starLess q (m + 1) t u := by
  rw [FixedPoint.starLess, FixedPoint.starLess,
    OrderSupport.transform_exposedThetaList q b m ha t ht hrt, List.all_map]
  apply Bool.eq_iff_iff.mpr
  rw [List.all_eq_true, List.all_eq_true]
  have he (x : RelativeTerm Nat) (hx : x ∈ exposedThetaList (m + 1) t) :
      Comparison.less (betaCode q b) (transform q b x) (transform q b u) =
        Comparison.less q x u := by
    have hs := Iota.OrderInduction.exposed_checked_normal q (m + 1) t x ht hnt hx
    exact less_transform q b ha x u hs.1 hu hs.2 hnu
      (OrderSupport.restricted_exposed q b (m + 1) t x hrt hx) hru
  constructor
  · intro h x hx
    have hh := h x hx
    simpa only [Function.comp_apply, he x hx] using hh
  · intro h x hx
    simpa only [Function.comp_apply, he x hx] using h x hx

private theorem mapped_buildRev_value (q b n : Nat) (ha : rootCheck q b = true)
    (as : List (RelativeTerm Nat)) (hg : Normalization.GoodAtoms q n as) :
    denote (betaCode q b) (transform q b (Normalization.buildRev as)) =
      principalSum (as.reverse.map (fun t => denote (betaCode q b) (transform q b t))) := by
  revert hg
  induction as with
  | nil =>
    intro hg
    have hz := OrderSupport.transform_low_value q b ha Normalization.zeroTree
      (Normalization.zeroTree_checked q (source_checked q b ha))
      (OmegaQuotient.Support.zero_restricted q b) (Nat.zero_le 1)
    simpa only [Normalization.buildRev, Normalization.zeroTree_denote,
      List.reverse_nil, List.map_nil, principalSum] using hz
  | cons t as ih =>
    intro hg
    have htail : Normalization.GoodAtoms q n as :=
      fun u hu => hg u (List.mem_cons_of_mem _ hu)
    have hhead := (hg t List.mem_cons_self).1
    have hq := source_checked q b ha
    have ht := Comparison.admitted_checked q n hq t hhead
    have hs := Comparison.admitted_checked q n hq (Normalization.buildRev as)
      (Normalization.buildRev_admissible q n hq as htail)
    rw [Normalization.buildRev,
      OrderSupport.transform_add q b ha (Normalization.buildRev as) t hs ht,
      ih htail, List.reverse_cons, List.map_append, principalSum_append]
    simp only [List.map_cons, List.map_nil, principalSum, add_zero]

theorem mapped_buildAtoms_value (q b n : Nat) (ha : rootCheck q b = true)
    (as : List (RelativeTerm Nat)) (hg : Normalization.GoodAtoms q n as) :
    denote (betaCode q b) (transform q b (Normalization.buildAtoms as)) =
      principalSum (as.map (fun t => denote (betaCode q b) (transform q b t))) := by
  simpa only [Normalization.buildAtoms, List.reverse_reverse] using
    mapped_buildRev_value q b n ha as.reverse (fun t ht => hg t (List.mem_reverse.mp ht))

theorem parts_restricted (q b m : Nat) (t : RelativeTerm Nat) (hr : Restricted q b t) :
    Restricted q b (Decomposition.highPartTerm m t.code) ∧
      Restricted q b (Decomposition.lowPartTerm m t.code) := by
  have hword (x : RelativeTerm Nat) (hx : x ∈ Decomposition.word t.code) : Restricted q b x := by
    apply OrderSupport.restricted_atoms q b t x hr
    simpa only [Decomposition.word, rawTree_code] using hx
  constructor
  · apply OmegaQuotient.Support.buildAtoms_restricted
    intro x hx
    exact hword x ((Decomposition.highWord_mem m t.code x).mp hx).1
  · apply OmegaQuotient.Support.buildAtoms_restricted
    intro x hx
    exact hword x ((Decomposition.lowWord_mem m t.code x).mp hx).1

/-- Actual target and original shifted HIGH parts denote the same mapped
value, with all genuine checked Normal part callers constructed. -/
theorem highPart_transform_value (q b m : Nat) (ha : rootCheck q b = true)
    (t : RelativeTerm Nat) (ht : check q t = true) (hn : Comparison.Normal q t)
    (hr : Restricted q b t) :
    denote (betaCode q b) (Decomposition.highPartTerm m (transform q b t).code) =
      denote (betaCode q b) (transform q b (Decomposition.highPartTerm (m + 1) t.code)) := by
  have hi : Decomposition.inputCheck q t.code = true := ReturnedIota.original_accepted q t ht hn
  have hg := (Decomposition.words_good q t.height (m + 1) t.code hi
    (by simp only [rawTree_code, le_refl])).1
  rw [(Decomposition.parts_word_values (betaCode q b) m (transform q b t).code).1,
    highWord_transform q b m ha t ht hr, List.map_map]
  exact (mapped_buildAtoms_value q b t.height ha _ hg).symm

/-- The genuine original ANF partition maps additively at the shifted
cut. This includes whole small sums that are stopped into one parameter. -/
theorem mapped_parts_add (q b m : Nat) (ha : rootCheck q b = true)
    (t : RelativeTerm Nat) (ht : check q t = true) (hn : Comparison.Normal q t)
    (hr : Restricted q b t) :
    denote (betaCode q b) (transform q b t) =
      denote (betaCode q b) (transform q b (Decomposition.highPartTerm (m + 1) t.code)) +
      denote (betaCode q b) (transform q b (Decomposition.lowPartTerm (m + 1) t.code)) := by
  have hi : Decomposition.inputCheck q t.code = true := ReturnedIota.original_accepted q t ht hn
  have hg := Decomposition.words_good q t.height (m + 1) t.code hi
    (by simp only [rawTree_code, le_refl])
  rw [mapped_buildAtoms_value q b t.height ha _ hg.1,
    mapped_buildAtoms_value q b t.height ha _ hg.2]
  have hm := (OrderSupport.mapped_atoms_value q b ha t ht hn hr).symm
  change denote (betaCode q b) (transform q b t) = _ at hm
  rw [← show Decomposition.word t.code = Comparison.atoms t from by
    simp only [Decomposition.word, rawTree_code],
    Decomposition.word_partition q (m + 1) t.code hi,
    List.map_append, principalSum_append] at hm
  exact hm

/-- Ordinary ordinal prefix cancellation identifies the actual LOW
part with the mapped original shifted LOW part. No residual oracle. -/
theorem lowPart_transform_value (q b m : Nat) (ha : rootCheck q b = true)
    (t : RelativeTerm Nat) (ht : check q t = true) (hn : Comparison.Normal q t)
    (hr : Restricted q b t) :
    denote (betaCode q b) (Decomposition.lowPartTerm m (transform q b t).code) =
      denote (betaCode q b) (transform q b (Decomposition.lowPartTerm (m + 1) t.code)) := by
  have hi : Decomposition.inputCheck (betaCode q b) (transform q b t).code = true :=
    ReturnedIota.original_accepted _ _ (transform_checked q b ha t ht hr)
      (transform_normal q b ha t ht hn hr)
  apply add_left_cancel (a :=
    denote (betaCode q b) (transform q b (Decomposition.highPartTerm (m + 1) t.code)))
  rw [← highPart_transform_value q b m ha t ht hn hr]
  exact (by
    simpa only [Decomposition.highCode, Decomposition.lowCode, interpretation_code] using
      Decomposition.parts_reconstruct (betaCode q b) m (transform q b t).code hi).trans
    (by simpa only [interpretation_code] using mapped_parts_add q b m ha t ht hn hr)

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonIota.FixedPointTransport
