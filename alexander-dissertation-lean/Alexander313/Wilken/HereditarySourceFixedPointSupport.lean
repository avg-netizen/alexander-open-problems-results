import Alexander313.Wilken.HereditaryThetaNormalizationPrimitive
import Alexander313.Wilken.HereditaryLocalization
import Alexander313.Wilken.HereditaryBaseAtoms
import Alexander313.Wilken.SourceFixedPointLimits

/-!
# Genuine fixed-point callers at every original public level

The original public grammar includes level zero with base one. Actual source
admission, theta range, and exposed-star fidelity are derived from its checker.
The literal level-zero base code supplies the exceptional residual-one test.
Parameters stay atomic for source star; their principal comparison words do
not redefine support. All proof candidates remain uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceFixedPoint

theorem finiteBase_eq_one_iff (r : Nat) : finiteBase r = 1 ↔ r = 0 := by
  constructor
  · intro h
    exact BaseAtoms.bases_strictMono.injective (h.trans finiteBase_zero.symm)
  · rintro rfl
    exact finiteBase_zero

theorem checked_notation_at (r : Nat) (t : RelativeTerm Nat) (ht : check r t = true)
    (m : Nat) : GlobalNotation (finiteBase r) m (denote r t) := by
  induction m with
  | zero => exact checked_globalNotation r t ht
  | succ m ih => exact globalNotation_embeds_next (finiteBase r) (finiteBase_pos r) m ih

noncomputable def sourceOrdinal (r m : Nat) (t : RelativeTerm Nat) (ht : check r t = true) :
    GlobalNotationOrdinal (finiteBase r) (m + 1) := ⟨denote r t, checked_notation_at r t ht (m + 1)⟩

theorem checked_theta_argument (r k : Nat) (a : RelativeTerm Nat)
    (ht : check r (.theta k a) = true) : check r a = true := by
  have ha := Theta.admitted_theta_argument
    (Theta.checked_admissible r _ (.theta k a) ht (SourceOne.PublicCodes.height_le_fragment _))
  exact Theta.admitted_checked ha

theorem checked_theta_sort (r k : Nat) (a : RelativeTerm Nat)
    (ht : check r (.theta k a) = true) : denote r a < omegaSequence (finiteBase r) (k + 2) := by
  have ha := Theta.checked_admissible r _ (.theta k a) ht (SourceOne.PublicCodes.height_le_fragment _)
  cases ha.2 with
  | theta h0k hkn hsort hab =>
    rw [denote_eq_finite r _ a hab]
    exact hsort

theorem checked_theta_range (r k : Nat) (a : RelativeTerm Nat)
    (ht : check r (.theta k a) = true) :
    omegaSequence (finiteBase r) k ≤ denote r (.theta k a) ∧
      denote r (.theta k a) < omegaSequence (finiteBase r) (k + 1) := by
  have ha := Theta.checked_admissible r _ (.theta k a) ht (SourceOne.PublicCodes.height_le_fragment _)
  rw [denote_eq_finite r _ (.theta k a) ha.2]
  cases ha.2 with
  | theta h0k hkn hsort hab => exact source_theta_range (finiteBase r) (parameters r) _ k a hkn hab hsort

theorem checked_parameter_lt_base (r p : Nat) (ht : check r (.parameter p) = true) :
    denote r (.parameter p) < finiteBase r := by
  have ha := Theta.checked_admissible r _ (.parameter p) ht (SourceOne.PublicCodes.height_le_fragment _)
  exact parameter_sound r p ha.1

theorem sourceStar_lt_iff_exposed (r m : Nat) (t : RelativeTerm Nat)
    (ht : check r t = true) (hn : Theta.Normal r t) (η : Ordinal.{0}) (hη : 0 < η) :
    globalStar (finiteBase r) (finiteBase_pos r) m (sourceOrdinal r m t ht) < η ↔
      ∀ s ∈ exposedThetaList m t, denote r s < η := by
  classical
  let n := max (SourceOne.PublicCodes.fragment t) (m + 2)
  have hm : m < n := (show m < m + 2 by omega).trans_le (le_max_right _ _)
  have had := Theta.checked_admissible r n t ht
    ((SourceOne.PublicCodes.height_le_fragment t).trans (le_max_left _ _))
  let tn := sourceAdmittedOrdinal (finiteBase r) (parameters r) n m hm t had.2
  have hv : (sourceOrdinal r m t ht).val = tn.val := denote_eq_finite r n t had.2
  rw [globalStar_finite_agreement (finiteBase r) (finiteBase_pos r) m (sourceOrdinal r m t ht) n hm tn hv,
    sourceStar_eq_exposedTheta (finiteBase r) (finiteBase_pos r) (parameters r) n m hm t had.2
      (hn.finite had), Finset.sup_lt_iff hη]
  constructor
  · intro h s hs
    have hv := h _ (Finset.mem_image.mpr ⟨s, (mem_exposedThetaList_iff m t s).mp hs, rfl⟩)
    change finiteDenote r n s < η at hv
    rw [← denote_eq_finite r n s (had.2.exposedThetaList m hs)] at hv
    exact hv
  · intro h p hp
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hp
    have hsl := (mem_exposedThetaList_iff m t s).mpr hs
    change finiteDenote r n s < η
    rw [← denote_eq_finite r n s (had.2.exposedThetaList m hsl)]
    exact h s hsl

def starLess (r m : Nat) (d e : RelativeTerm Nat) : Bool :=
  (exposedThetaList m d).all (fun s => Theta.less r s e)

theorem starLess_primrec : Primrec (fun p : Nat × (Nat × (RelativeTerm Nat × RelativeTerm Nat)) =>
    starLess p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hlist : Primrec (fun p : Nat × (Nat × (RelativeTerm Nat × RelativeTerm Nat)) =>
      exposedThetaList p.2.1 p.2.2.1) := exposedThetaList_primrec.comp
    (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have htest : Primrec₂ (fun p : Nat × (Nat × (RelativeTerm Nat × RelativeTerm Nat)) =>
      fun s : RelativeTerm Nat => Theta.less p.1 s p.2.2.2) :=
    (Theta.Effective.less_primrec.comp ((Primrec.fst.comp Primrec.fst).pair
      (Primrec.snd.pair (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))))).to₂
  exact (SourceOne.Comparison.Effective.listAll_primrec _ htest).comp Primrec.id hlist

theorem starLess_exact (r m : Nat) (d e : RelativeTerm Nat)
    (hd : check r d = true) (he : check r e = true)
    (hnd : Theta.Normal r d) (hne : Theta.Normal r e) (hepos : 0 < denote r e) :
    starLess r m d e = true ↔
      globalStar (finiteBase r) (finiteBase_pos r) m (sourceOrdinal r m d hd) < denote r e := by
  rw [sourceStar_lt_iff_exposed r m d hd hnd (denote r e) hepos, starLess, List.all_eq_true]
  apply forall_congr'
  intro s
  apply imp_congr_right
  intro hs
  have had := Theta.admitted_exposedThetaList
    (Theta.checked_admissible r _ d hd (SourceOne.PublicCodes.height_le_fragment _)) m hs
  exact Theta.less_correct r s e (Theta.admitted_checked had) he
    (hnd.exposedThetaList m hs) hne

def oneCode : Nat := Localization.baseRaw 0

theorem oneCode_accepted : Theta.acceptedCode 0 oneCode = true := by
  obtain ⟨a, he, hc, hn⟩ := Localization.baseRaw_node 0
  apply (Theta.acceptedCode_iff 0 oneCode).mpr
  exact ⟨by simpa only [oneCode, he, checkCode_code] using hc,
    by simpa only [oneCode, he, ThetaCourse.rawTree_code] using hn⟩

theorem oneCode_value : interpretation 0 oneCode = 1 := by
  simpa only [oneCode, Localization.value, finiteBase_zero] using Localization.baseRaw_value 0

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceFixedPoint
