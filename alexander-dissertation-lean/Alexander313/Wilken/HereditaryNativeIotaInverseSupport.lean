import Alexander313.Wilken.HereditaryNativeIotaOrder
import Alexander313.Wilken.HereditaryNativeLowArithmetic

/-!
# A genuine finite inverse operation for the actual iota transform

Every target parameter is an originally admitted public union code below the
actual alpha. Canonicalization and the proved bounded finite return put its
value back into the SAME positive public source context. No target-payload
coverage or source-admission hypothesis is supplied. Nonparameter theta
indices increase by one; written sums are retained. The original full
source restriction is derived even for hidden arguments of returned atoms.

These source proof candidates have not been compiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Iota.Inverse

open NativePublicBridge (contextCode contextCode_checked)

def atomCode (s p : Nat) : Nat :=
  LowArithmetic.returnCode s (Canonical.canonicalize p)

def atomTerm (s p : Nat) : RelativeTerm Nat := ThetaCourse.rawTree (atomCode s p)

theorem atomCode_primrec : Primrec₂ atomCode :=
  (LowArithmetic.returnCode_primrec.comp Primrec.fst
    (Canonical.Effective.canonicalize_primrec.comp Primrec.snd)).to₂

theorem atomTerm_primrec : Primrec₂ atomTerm :=
  (ThetaCourse.rawTree_primrec.comp atomCode_primrec).to₂

theorem atom_spec (s a p : Nat) (ha : rootCheck s a = true)
    (hp : parameterCheck (alphaCode s a) p = true) :
    check (contextCode s) (atomTerm s p) = true ∧
      Comparison.Normal (contextCode s) (atomTerm s p) ∧
      (atomTerm s p).outerSort ≤ 1 ∧
      denote (contextCode s) (atomTerm s p) = parameters p := by
  have hpc := (parameterCheck_exact _ p).mp hp
  have hv := Canonical.canonicalize_value p hpc.1
  have hpalpha : parameters p < interpretation (contextCode s) a := by
    simpa only [alpha_base s a ha] using hpc.2.2
  have hb : unionInterpretation (Canonical.canonicalize p) < finiteBase ((s + 1) + 1) := by
    rw [hv]
    exact hpalpha.trans (LowArithmetic.lowInput_bound s a (root_low s a ha))
  have hs := LowArithmetic.returnCode_spec s (Canonical.canonicalize p)
    (Canonical.canonicalize_check p hpc.1) hb
  obtain ⟨t, he, ht⟩ := (lowCheckCode_exact _ _).mp hs.1
  have htree : atomTerm s p = t := by
    simp only [atomTerm, atomCode, ← he, ThetaCourse.rawTree_code]
  have hn := ((Comparison.acceptedCode_exact _ _).mp hs.2.1).2
  have hs' := Bool.and_eq_true.mp ht
  refine ⟨htree.symm ▸ hs'.1, ?_, htree.symm ▸ of_decide_eq_true hs'.2, ?_⟩
  · simpa only [atomTerm, atomCode] using hn
  · rw [htree]
    have heval : denote (contextCode s) t = unionInterpretation (Canonical.canonicalize p) := by
      simpa only [← he, interpretation_code] using hs.2.2
    exact heval.trans hv

/-- The real finite principal-support theorem bounds every full theta-zero
node of a low normal return, including nodes in its hidden high arguments. -/
theorem fullList_value_le_low (q : Nat) (t u : RelativeTerm Nat)
    (ht : check q t = true) (hn : Comparison.Normal q t)
    (hl : t.outerSort ≤ 1) (hu : u ∈ fullList t) : denote q u ≤ denote q t := by
  revert ht hn hl hu
  induction t with
  | parameter p =>
    intro ht hn hl hu
    simp only [fullList, RelativeTerm.PrincipalSupport.principalList, List.not_mem_nil] at hu
  | sum t v iht ihv =>
    intro ht hn hl hu
    have hc := BaseTransformation.sum_checks q t v ht
    rcases List.mem_append.mp hu with hu | hu
    · exact (iht hc.1 hn.1 ((le_max_left _ _).trans hl) hu).trans le_self_add
    · exact (ihv hc.2 hn.2.1 ((le_max_right _ _).trans hl) hu).trans le_add_self
  | theta k t ih =>
    intro ht hn hl hu
    have hk : k = 0 := by simp only [outerSort] at hl; omega
    subst k
    let n := SourceOne.PublicCodes.fragment (.theta 0 t)
    have hq := (Bool.and_eq_true.mp ht).1
    have had := NativeContext.checked_admissible q (.theta 0 t) ht
    have haa := Comparison.admitted_argument had
    have hua := RelativeTerm.PrincipalSupport.principalList_admissible had.2 0 hu
    have h := RelativeTerm.PrincipalSupport.principalList_theta_value_le
      (base q) (base_pos q hq) parameters n 0 t u had.2
      ((Comparison.normal_finite_iff q n hq t haa.2).mpr hn) hu
    rw [← denote_eq_finite q n hq u hua,
      ← denote_eq_finite q n hq (.theta 0 t) had.2] at h
    exact h

theorem atom_restricted (s a p : Nat) (ha : rootCheck s a = true)
    (hp : parameterCheck (alphaCode s a) p = true) : Restricted s a (atomTerm s p) := by
  have hs := atom_spec s a p ha hp
  intro u hu
  have hle := fullList_value_le_low _ _ u hs.1 hs.2.1 hs.2.2.1 hu
  rw [hs.2.2.2] at hle
  exact hle.trans_lt (by simpa only [alpha_base s a ha] using parameter_sound _ p hp)

def lift (s : Nat) : RelativeTerm Nat → RelativeTerm Nat
  | .parameter p => atomTerm s p
  | .sum t u => .sum (lift s t) (lift s u)
  | .theta k t => .theta (k + 1) (lift s t)

theorem lift_primrec : Primrec₂ lift := by
  have ht : Primrec (fun p : Nat × (Nat × RelativeTerm Nat) =>
      (.theta (p.2.1 + 1) p.2.2 : RelativeTerm Nat)) :=
    theta_primrec.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  have hf := ValueFold.term_primrec atomTerm RelativeTerm.sum
    (fun (_ : Nat) k t => .theta (k + 1) t) (.parameter 0)
    atomTerm_primrec sum_primrec ht
  have he : ValueFold.term atomTerm RelativeTerm.sum
      (fun (_ : Nat) k t => .theta (k + 1) t) = lift := by
    funext s t
    induction t <;> simp_all [ValueFold.term, lift]
  rw [he] at hf
  exact hf

theorem lift_outerSort (s a : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (alphaCode s a) t = true) :
    (lift s t).outerSort ≤ t.outerSort + 1 := by
  revert ht
  induction t with
  | parameter p =>
    intro ht
    exact (atom_spec s a p ha (NativeContext.checked_admissible _ _ ht).1).2.2.1
  | sum t u iht ihu =>
    intro ht
    have hc := BaseTransformation.sum_checks _ t u ht
    have hlt := iht hc.1
    have hlu := ihu hc.2
    simp only [lift, outerSort]
    omega
  | theta k t ih => intro ht; simp only [lift, outerSort]; omega

theorem checked_sum (q : Nat) (t u : RelativeTerm Nat)
    (ht : check q t = true) (hu : check q u = true) : check q (.sum t u) = true := by
  let n := max (SourceOne.PublicCodes.fragment t) (SourceOne.PublicCodes.fragment u)
  have htn := Comparison.checked_admissible q n t ht
    ((SourceOne.PublicCodes.height_le_fragment t).trans (le_max_left _ _))
  have hun := Comparison.checked_admissible q n u hu
    ((SourceOne.PublicCodes.height_le_fragment u).trans (le_max_right _ _))
  exact Comparison.admitted_checked q n (Bool.and_eq_true.mp ht).1 (.sum t u)
    ⟨⟨htn.1, hun.1⟩, .sum htn.2 hun.2⟩

theorem checked_theta (q k : Nat) (t : RelativeTerm Nat)
    (ht : check q t = true) (hs : t.outerSort ≤ k + 2) : check q (.theta k t) = true := by
  let n := max (SourceOne.PublicCodes.fragment t) (k + 1)
  have htn := Comparison.checked_admissible q n t ht
    ((SourceOne.PublicCodes.height_le_fragment t).trans (le_max_left _ _))
  have hkn : k < n := by have h := le_max_right (SourceOne.PublicCodes.fragment t) (k + 1); omega
  have hf : finiteCheck q n (.theta k t) = true := by
    simp only [finiteCheck_theta, (finiteCheck_exact q n t).mpr htn,
      hkn, hs, decide_true, Bool.true_and]
  exact Comparison.admitted_checked q n (Bool.and_eq_true.mp ht).1 _
    ((finiteCheck_exact q n _).mp hf)

theorem lift_checked (s a : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (alphaCode s a) t = true) :
    check (contextCode s) (lift s t) = true := by
  revert ht
  induction t with
  | parameter p => intro ht; exact (atom_spec s a p ha (NativeContext.checked_admissible _ _ ht).1).1
  | sum t u iht ihu =>
    intro ht
    have hc := BaseTransformation.sum_checks _ t u ht
    exact checked_sum _ _ _ (iht hc.1) (ihu hc.2)
  | theta k t ih =>
    intro ht
    have hc := BaseTransformation.theta_argument_check _ k t ht
    have hf := (Bool.and_eq_true.mp ht).2
    have hs : finiteCheck (alphaCode s a) (SourceOne.PublicCodes.fragment (.theta k t)) t = true ∧
        k < SourceOne.PublicCodes.fragment (.theta k t) ∧ t.outerSort ≤ k + 2 := by
      simpa only [finiteCheck_theta, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using hf
    apply checked_theta _ (k + 1) _ (ih hc)
    have hl := lift_outerSort s a ha t hc
    have hsort := hs.2.2
    omega

theorem lift_restricted (s a : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (alphaCode s a) t = true) : Restricted s a (lift s t) := by
  revert ht
  induction t with
  | parameter p => intro ht; exact atom_restricted s a p ha (NativeContext.checked_admissible _ _ ht).1
  | sum t u iht ihu =>
    intro ht
    have hc := BaseTransformation.sum_checks _ t u ht
    exact (restricted_sum s a _ _).mpr ⟨iht hc.1, ihu hc.2⟩
  | theta k t ih =>
    intro ht
    exact (restricted_theta_succ s a k _).mpr
      (ih (BaseTransformation.theta_argument_check _ k t ht))

/-- Actual target value recovery already holds on every originally admitted
target expression; no target Normality is required. -/
theorem lift_right_inverse (s a : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (alphaCode s a) t = true) :
    denote (alphaCode s a) (transform s a (lift s t)) = denote (alphaCode s a) t := by
  revert ht
  induction t with
  | parameter p =>
    intro ht
    have hp := (NativeContext.checked_admissible _ _ ht).1
    have hs := atom_spec s a p ha hp
    have hb : denote (contextCode s) (atomTerm s p) < interpretation (contextCode s) a := by
      rw [hs.2.2.2]
      simpa only [alpha_base s a ha] using parameter_sound _ p hp
    exact ((transform_parameter_value s a ha _ hs.1 hb).2).trans hs.2.2.2
  | sum t u iht ihu =>
    intro ht
    have hc := BaseTransformation.sum_checks _ t u ht
    rw [lift, transform_add s a ha _ _ (lift_checked s a ha t hc.1)
      (lift_checked s a ha u hc.2), iht hc.1, ihu hc.2]
    rfl
  | theta k t ih =>
    intro ht
    have hc := BaseTransformation.theta_argument_check _ k t ht
    have hs := lift_checked s a ha (.theta k t) ht
    have hr := lift_restricted s a ha (.theta k t) ht
    rw [lift, transform_theta_succ s a k ha _ hs hr]
    change globalCollapse (base (alphaCode s a)) k
      (denote (alphaCode s a) (transform s a (lift s t))) =
      globalCollapse (base (alphaCode s a)) k (denote (alphaCode s a) t)
    rw [ih hc]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Iota.Inverse
