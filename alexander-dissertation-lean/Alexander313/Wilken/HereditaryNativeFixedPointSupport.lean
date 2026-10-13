import Alexander313.Wilken.HereditaryNativeComparison
import Alexander313.Wilken.SourceFixedPointLimits

/-!
# Genuine source callers and star tests in native epsilon contexts

Native leaves remain atomic original public payloads. The same-level source
membership and theta sorts below are consequences of original native
admission. The star test uses the actual exposed native theta list and the
proved source-star maximum identity. No ordinal evaluator, source admission
or support test is supplied. Native epsilon bases explicitly exclude the
base-1 exception of the repaired source fixed-point criterion. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.FixedPoint

theorem base_ne_one (q : Nat) (hq : baseCheck q = true) : base q ≠ 1 := by
  intro hb
  have he := ((baseCheck_exact q).mp hq).2
  rw [hb, Ordinal.opow_one] at he
  exact Ordinal.one_lt_omega0.ne' he

theorem checked_notation_at (q : Nat) (t : RelativeTerm Nat) (ht : check q t = true)
    (m : Nat) : GlobalNotation (base q) m (denote q t) := by
  induction m with
  | zero => exact checked_globalNotation q t ht
  | succ m ih => exact globalNotation_embeds_next (base q) (base_pos q (Bool.and_eq_true_iff.mp ht).1) m ih

noncomputable def sourceOrdinal (q m : Nat) (t : RelativeTerm Nat) (ht : check q t = true) :
    GlobalNotationOrdinal (base q) (m + 1) := ⟨denote q t, checked_notation_at q t ht (m + 1)⟩

theorem checked_theta_argument (q k : Nat) (a : RelativeTerm Nat)
    (ht : check q (.theta k a) = true) : check q a = true := by
  have hq := (Bool.and_eq_true_iff.mp ht).1
  have ha := Comparison.admitted_argument (NativeContext.checked_admissible q (.theta k a) ht)
  exact Comparison.admitted_checked q _ hq a ha

theorem checked_theta_sort (q k : Nat) (a : RelativeTerm Nat)
    (ht : check q (.theta k a) = true) : denote q a < omegaSequence (base q) (k + 2) := by
  have hq := (Bool.and_eq_true_iff.mp ht).1
  have ha := NativeContext.checked_admissible q (.theta k a) ht
  cases ha.2 with
  | theta h0k hkn hsort hab =>
    rw [denote_eq_finite q _ hq a hab]
    exact hsort

theorem checked_theta_range (q k : Nat) (a : RelativeTerm Nat)
    (ht : check q (.theta k a) = true) :
    omegaSequence (base q) k ≤ denote q (.theta k a) ∧
      denote q (.theta k a) < omegaSequence (base q) (k + 1) := by
  have hq := (Bool.and_eq_true_iff.mp ht).1
  have ha := NativeContext.checked_admissible q (.theta k a) ht
  rw [denote_eq_finite q _ hq (.theta k a) ha.2]
  cases ha.2 with
  | theta h0k hkn hsort hab => exact source_theta_range (base q) parameters _ k a hkn hab hsort

theorem checked_parameter_lt_base (q p : Nat) (ht : check q (.parameter p) = true) :
    denote q (.parameter p) < base q :=
  parameter_sound q p (NativeContext.checked_admissible q (.parameter p) ht).1

/-- The global star of a checked weak-normal native argument is bounded
exactly by its literal exposed native theta values. Public payloads are not
traversed by this support list. -/
theorem sourceStar_lt_iff_exposed (q m : Nat) (t : RelativeTerm Nat)
    (ht : check q t = true) (hn : Comparison.Normal q t) (η : Ordinal.{0}) (hη : 0 < η) :
    globalStar (base q) (base_pos q (Bool.and_eq_true_iff.mp ht).1) m (sourceOrdinal q m t ht) < η ↔
      ∀ s ∈ exposedThetaList m t, denote q s < η := by
  classical
  have hq := (Bool.and_eq_true_iff.mp ht).1
  let n := max (SourceOne.PublicCodes.fragment t) (m + 2)
  have hm : m < n := (show m < m + 2 by omega).trans_le (le_max_right _ _)
  have had := Comparison.checked_admissible q n t ht
    ((SourceOne.PublicCodes.height_le_fragment t).trans (le_max_left _ _))
  let tn := sourceAdmittedOrdinal (base q) parameters n m hm t had.2
  have hv : (sourceOrdinal q m t ht).val = tn.val := denote_eq_finite q n hq t had.2
  rw [globalStar_finite_agreement (base q) (base_pos q hq) m (sourceOrdinal q m t ht) n hm tn hv,
    sourceStar_eq_exposedTheta (base q) (base_pos q hq) parameters n m hm t had.2
      ((Comparison.normal_finite_iff q n hq t had.2).mpr hn), Finset.sup_lt_iff hη]
  constructor
  · intro h s hs
    have hv := h _ (Finset.mem_image.mpr ⟨s, (mem_exposedThetaList_iff m t s).mp hs, rfl⟩)
    change finiteDenote q n s < η at hv
    rw [← denote_eq_finite q n hq s (had.2.exposedThetaList m hs)] at hv
    exact hv
  · intro h p hp
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hp
    have hsl := (mem_exposedThetaList_iff m t s).mpr hs
    change finiteDenote q n s < η
    rw [← denote_eq_finite q n hq s (had.2.exposedThetaList m hsl)]
    exact h s hsl

def starLess (q m : Nat) (d e : RelativeTerm Nat) : Bool :=
  (exposedThetaList m d).all (fun s => Comparison.less q s e)

theorem starLess_primrec : Primrec (fun p : Nat × (Nat × (RelativeTerm Nat × RelativeTerm Nat)) =>
    starLess p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hlist : Primrec (fun p : Nat × (Nat × (RelativeTerm Nat × RelativeTerm Nat)) =>
      exposedThetaList p.2.1 p.2.2.1) := exposedThetaList_primrec.comp
    (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have htest : Primrec₂ (fun p : Nat × (Nat × (RelativeTerm Nat × RelativeTerm Nat)) =>
      fun s : RelativeTerm Nat => Comparison.less p.1 s p.2.2.2) :=
    (Comparison.Effective.less_primrec.comp ((Primrec.fst.comp Primrec.fst).pair
      (Primrec.snd.pair (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))))).to₂
  exact (SourceOne.Comparison.Effective.listAll_primrec _ htest).comp Primrec.id hlist

theorem starLess_exact (q m : Nat) (d e : RelativeTerm Nat)
    (hd : check q d = true) (he : check q e = true)
    (hnd : Comparison.Normal q d) (hne : Comparison.Normal q e) (hepos : 0 < denote q e) :
    starLess q m d e = true ↔
      globalStar (base q) (base_pos q (Bool.and_eq_true_iff.mp hd).1) m (sourceOrdinal q m d hd) < denote q e := by
  rw [sourceStar_lt_iff_exposed q m d hd hnd (denote q e) hepos, starLess, List.all_eq_true]
  apply forall_congr'
  intro s
  apply imp_congr_right
  intro hs
  have hq := (Bool.and_eq_true_iff.mp hd).1
  have had := Comparison.admitted_exposed (NativeContext.checked_admissible q d hd) m hs
  exact Comparison.less_correct q s e (Comparison.admitted_checked q _ hq s had) he
    (hnd.exposed m hs) hne

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.FixedPoint
