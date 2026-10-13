import Alexander313.Wilken.SourceOneNativeIotaOrder
import Alexander313.Wilken.HereditarySourceZetaTransport
import Alexander313.Wilken.HereditaryNativeNormalizationPrimitive

/-!
# Executing inverse atoms at the ORIGINAL source base one

An actual target public parameter is below the original root, and the root
is below the actual first public base endpoint. The genuine finite bounded
return therefore produces an original admitted Normal LOW source-one tree.
Every hidden principal node is bounded by this actual returned value.
Target theta indices shift up by one, with every ORIGINAL caller derived.
No source representation, coverage or return oracle occurs. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.Inverse

open OrderSupport

def atomCode (p : Nat) : Nat := SourceZeta.Transport.returnCode 0 (Canonical.canonicalize p)

def atomTerm (p : Nat) : RelativeTerm Nat := ThetaCourse.rawTree (atomCode p)

theorem atomCode_primrec : Primrec atomCode :=
  SourceZeta.Transport.returnCode_primrec.comp (Primrec.const 0)
    Canonical.Effective.canonicalize_primrec

theorem atomTerm_primrec : Primrec atomTerm := ThetaCourse.rawTree_primrec.comp atomCode_primrec

theorem atom_spec (a p : Nat) (ha : rootCheck a = true)
    (hp : NativeContext.parameterCheck (alphaCode a) p = true) :
    check 0 (atomTerm p) = true ∧ Theta.Normal 0 (atomTerm p) ∧
      (atomTerm p).outerSort ≤ 1 ∧ denote 0 (atomTerm p) = NativeContext.parameters p := by
  have hpc := (NativeContext.parameterCheck_exact _ p).mp hp
  have hv := Canonical.canonicalize_value p hpc.1
  have hpalpha : NativeContext.parameters p < interpretation 0 a := by
    simpa only [alpha_base a ha] using hpc.2.2
  have hb : unionInterpretation (Canonical.canonicalize p) < finiteBase (0 + 1) := by
    rw [hv]
    exact hpalpha.trans ((lt_nextBase_iff_code 0 _).mpr ⟨a, root_low a ha, rfl⟩)
  have hs := SourceZeta.Transport.returnCode_spec 0 (Canonical.canonicalize p)
    (Canonical.canonicalize_check p hpc.1) hb
  have hlow := (Theta.acceptedLowCode_iff 0 _).mp hs.1
  obtain ⟨t, he, ht⟩ := (lowCheckCode_iff 0 _).mp hlow.1
  have htree : atomTerm p = t := by
    simp only [atomTerm, atomCode, ← he, ThetaCourse.rawTree_code]
  have ht' := Bool.and_eq_true.mp ht
  refine ⟨htree.symm ▸ ht'.1, ?_, htree.symm ▸ of_decide_eq_true ht'.2, ?_⟩
  · simpa only [atomTerm, atomCode] using hlow.2
  · rw [htree]
    have heval : denote 0 t = unionInterpretation (Canonical.canonicalize p) := by
      simpa only [← he, interpretation_code] using hs.2
    exact heval.trans hv

/-- The genuine full principal bound at source level zero traverses every
hidden theta argument of the actual returned LOW original tree. -/
theorem fullList_value_le_low (t u : RelativeTerm Nat) (ht : check 0 t = true)
    (hn : Theta.Normal 0 t) (hl : t.outerSort ≤ 1) (hu : u ∈ fullList t) :
    denote 0 u ≤ denote 0 t := by
  revert ht hn hl hu
  induction t with
  | parameter p =>
    intro ht hn hl hu
    simp only [fullList, RelativeTerm.PrincipalSupport.principalList, List.not_mem_nil] at hu
  | sum t v iht ihv =>
    intro ht hn hl hu
    have hc := sum_checks t v ht
    rcases List.mem_append.mp hu with hu | hu
    · exact (iht hc.1 hn.1 ((le_max_left _ _).trans hl) hu).trans le_self_add
    · exact (ihv hc.2 hn.2.1 ((le_max_right _ _).trans hl) hu).trans le_add_self
  | theta k t ih =>
    intro ht hn hl hu
    have hk : k = 0 := by simp only [RelativeTerm.outerSort] at hl; omega
    subst k
    exact PrincipalSupport.principalList_theta_value_le 0 t u ht hn hu

theorem atom_restricted (a p : Nat) (ha : rootCheck a = true)
    (hp : NativeContext.parameterCheck (alphaCode a) p = true) : Restricted a (atomTerm p) := by
  have hs := atom_spec a p ha hp
  intro u hu
  have hle := fullList_value_le_low _ u hs.1 hs.2.1 hs.2.2.1 hu
  rw [hs.2.2.2] at hle
  exact hle.trans_lt (by
    simpa only [alpha_base a ha] using NativeContext.parameter_sound _ p hp)

def lift : RelativeTerm Nat → RelativeTerm Nat
  | .parameter p => atomTerm p
  | .sum t u => .sum (lift t) (lift u)
  | .theta k t => .theta (k + 1) (lift t)

theorem lift_primrec : Primrec lift := by
  have ht : Primrec (fun p : Unit × (Nat × RelativeTerm Nat) =>
      (.theta (p.2.1 + 1) p.2.2 : RelativeTerm Nat)) :=
    theta_primrec.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  have hf := ValueFold.term_primrec (fun (_ : Unit) p => atomTerm p) RelativeTerm.sum
    (fun (_ : Unit) k t => .theta (k + 1) t) (.parameter 0)
    (atomTerm_primrec.comp Primrec.snd) sum_primrec ht
  have he : ValueFold.term (fun (_ : Unit) p => atomTerm p) RelativeTerm.sum
      (fun (_ : Unit) k t => .theta (k + 1) t) = fun (_ : Unit) t => lift t := by
    funext v t
    induction t <;> simp_all [ValueFold.term, lift]
  rw [he] at hf
  exact hf.comp (Primrec.const ()) Primrec.id

theorem lift_outerSort (a : Nat) (ha : rootCheck a = true) (t : RelativeTerm Nat)
    (ht : NativeContext.check (alphaCode a) t = true) : (lift t).outerSort ≤ t.outerSort + 1 := by
  revert ht
  induction t with
  | parameter p =>
    intro ht
    exact (atom_spec a p ha (NativeContext.checked_admissible _ _ ht).1).2.2.1
  | sum t u iht ihu =>
    intro ht
    have hc := NativeContext.BaseTransformation.sum_checks _ t u ht
    have hlt := iht hc.1
    have hlu := ihu hc.2
    simp only [lift, RelativeTerm.outerSort]
    omega
  | theta k t ih => intro ht; simp only [lift, RelativeTerm.outerSort]; omega

theorem checked_sum (t u : RelativeTerm Nat) (ht : check 0 t = true) (hu : check 0 u = true) :
    check 0 (.sum t u) = true := by
  let n := max (SourceOne.PublicCodes.fragment t) (SourceOne.PublicCodes.fragment u)
  have htn := Theta.checked_admissible 0 n t ht
    ((SourceOne.PublicCodes.height_le_fragment t).trans (le_max_left _ _))
  have hun := Theta.checked_admissible 0 n u hu
    ((SourceOne.PublicCodes.height_le_fragment u).trans (le_max_right _ _))
  exact Theta.admitted_checked ⟨⟨htn.1, hun.1⟩, .sum htn.2 hun.2⟩

theorem checked_theta (k : Nat) (t : RelativeTerm Nat)
    (ht : check 0 t = true) (hs : t.outerSort ≤ k + 2) : check 0 (.theta k t) = true := by
  let n := max (SourceOne.PublicCodes.fragment t) (k + 1)
  have htn := Theta.checked_admissible 0 n t ht
    ((SourceOne.PublicCodes.height_le_fragment t).trans (le_max_left _ _))
  have hkn : k < n := by have h := le_max_right (SourceOne.PublicCodes.fragment t) (k + 1); omega
  have hf : finiteCheck 0 n (.theta k t) = true := by
    simp only [finiteCheck_theta, (finiteCheck_iff 0 n t).mpr htn,
      hkn, hs, decide_true, Bool.true_and]
  exact Theta.admitted_checked ((finiteCheck_iff 0 n _).mp hf)

theorem lift_checked (a : Nat) (ha : rootCheck a = true) (t : RelativeTerm Nat)
    (ht : NativeContext.check (alphaCode a) t = true) : check 0 (lift t) = true := by
  revert ht
  induction t with
  | parameter p =>
    intro ht
    exact (atom_spec a p ha (NativeContext.checked_admissible _ _ ht).1).1
  | sum t u iht ihu =>
    intro ht
    have hc := NativeContext.BaseTransformation.sum_checks _ t u ht
    exact checked_sum _ _ (iht hc.1) (ihu hc.2)
  | theta k t ih =>
    intro ht
    have hc := NativeContext.BaseTransformation.theta_argument_check _ k t ht
    have hf := (Bool.and_eq_true.mp ht).2
    have hs : NativeContext.finiteCheck (alphaCode a) (SourceOne.PublicCodes.fragment (.theta k t)) t = true ∧
        k < SourceOne.PublicCodes.fragment (.theta k t) ∧ t.outerSort ≤ k + 2 := by
      simpa only [NativeContext.finiteCheck_theta, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using hf
    apply checked_theta (k + 1) _ (ih hc)
    have hl := lift_outerSort a ha t hc
    have hsort := hs.2.2
    omega

theorem lift_restricted (a : Nat) (ha : rootCheck a = true) (t : RelativeTerm Nat)
    (ht : NativeContext.check (alphaCode a) t = true) : Restricted a (lift t) := by
  revert ht
  induction t with
  | parameter p =>
    intro ht
    exact atom_restricted a p ha (NativeContext.checked_admissible _ _ ht).1
  | sum t u iht ihu =>
    intro ht
    have hc := NativeContext.BaseTransformation.sum_checks _ t u ht
    exact (restricted_sum a _ _).mpr ⟨iht hc.1, ihu hc.2⟩
  | theta k t ih =>
    intro ht
    exact (restricted_theta_succ a k _).mpr
      (ih (NativeContext.BaseTransformation.theta_argument_check _ k t ht))

theorem lift_right_inverse (a : Nat) (ha : rootCheck a = true) (t : RelativeTerm Nat)
    (ht : NativeContext.check (alphaCode a) t = true) :
    NativeContext.denote (alphaCode a) (transform a (lift t)) = NativeContext.denote (alphaCode a) t := by
  revert ht
  induction t with
  | parameter p =>
    intro ht
    have hp := (NativeContext.checked_admissible _ _ ht).1
    have hs := atom_spec a p ha hp
    have hb : denote 0 (atomTerm p) < interpretation 0 a := by
      rw [hs.2.2.2]
      simpa only [alpha_base a ha] using NativeContext.parameter_sound _ p hp
    exact (transform_below_value a ha _ hs.1 hb).trans hs.2.2.2
  | sum t u iht ihu =>
    intro ht
    have hc := NativeContext.BaseTransformation.sum_checks _ t u ht
    rw [lift, transform_add a ha _ _ (lift_checked a ha t hc.1)
      (lift_checked a ha u hc.2), iht hc.1, ihu hc.2]
    rfl
  | theta k t ih =>
    intro ht
    have hc := NativeContext.BaseTransformation.theta_argument_check _ k t ht
    have hs := lift_checked a ha (.theta k t) ht
    have hr := lift_restricted a ha (.theta k t) ht
    rw [lift, transform_theta_succ a k ha _ hs hr]
    change globalCollapse (NativeContext.base (alphaCode a)) k
      (NativeContext.denote (alphaCode a) (transform a (lift t))) =
      globalCollapse (NativeContext.base (alphaCode a)) k (NativeContext.denote (alphaCode a) t)
    rw [ih hc]

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.Inverse
