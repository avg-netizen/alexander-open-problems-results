import Alexander313.Wilken.HereditaryNativeNormalizationPrimitive

/-!
# Actual dependencies for changing a native epsilon base

The finite native comparison algorithm threads its context code but never
tests it: public atomic values are compared by the original union comparator,
and theta comparisons use the proved relative exposed-support criterion.
This gives actual different-base ordinal comparisons once admission is proved
at both bases. It is not a hypothesis about collapse naturality.

Parameter support below uses the priority in Definition 2.23: a whole value
below the base is atomic, even when its written native syntax is a sum. Thus
it is not the set of all below-base written nodes. Its exact bound is derived
from original admission, real theta lower bounds and epsilon sum closure.
This is extraction from the chosen presentation, not equality with a unique
printed Par set on arbitrary weak-normal or raw spellings. In particular,
zero-prefix syntax can contribute an extra zero without affecting the bound.
All candidates are uncompiled; no iota or temporary translation is assumed.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.BaseTransformation

theorem lessFuel_context (fuel q v : Nat) (t u : RelativeTerm Nat) :
    Comparison.lessFuel fuel q t u = Comparison.lessFuel fuel v t u := by
  induction fuel generalizing t u with
  | zero => cases t <;> cases u <;> rfl
  | succ fuel ih =>
    have he : Comparison.lessFuel fuel q = Comparison.lessFuel fuel v :=
      funext fun a => funext fun b => ih a b
    cases t <;> cases u <;> simp only [Comparison.lessFuel, he]

theorem less_context (q v : Nat) (t u : RelativeTerm Nat) :
    Comparison.less q t u = Comparison.less v t u :=
  lessFuel_context (t.size + u.size) q v t u

theorem equal_context (q v : Nat) (t u : RelativeTerm Nat) :
    Comparison.equal q t u = Comparison.equal v t u := by
  simp only [Comparison.equal, less_context q v]

theorem normalAppend_context (q v : Nat) (as bs : List (RelativeTerm Nat)) :
    Comparison.normalAppend q as bs = Comparison.normalAppend v as bs := by
  cases bs with
  | nil => rfl
  | cons b bs => cases bs <;> simp only [Comparison.normalAppend, less_context q v]

theorem normalCheck_context (q v : Nat) (t : RelativeTerm Nat) :
    Comparison.normalCheck q t = Comparison.normalCheck v t := by
  induction t <;> simp_all only [Comparison.normalCheck, normalAppend_context q v]

theorem normal_context (q v : Nat) (t : RelativeTerm Nat)
    (hq : check q t = true) (hv : check v t = true) :
    Comparison.Normal q t ↔ Comparison.Normal v t := by
  rw [← Comparison.normalCheck_correct q t hq,
    ← Comparison.normalCheck_correct v t hv, normalCheck_context q v]

theorem prependAtom_context (q v : Nat) (a : RelativeTerm Nat)
    (as : List (RelativeTerm Nat)) :
    Normalization.prependAtom q a as = Normalization.prependAtom v a as := by
  cases as <;> simp only [Normalization.prependAtom, less_context q v]

theorem normalizeAtoms_context (q v : Nat) (as : List (RelativeTerm Nat)) :
    Normalization.normalizeAtoms q as = Normalization.normalizeAtoms v as := by
  induction as <;> simp_all only [Normalization.normalizeAtoms, prependAtom_context q v]

theorem normalize_context (q v : Nat) (t : RelativeTerm Nat) :
    Normalization.normalize q t = Normalization.normalize v t := by
  induction t <;> simp_all only [Normalization.normalize, normalizeAtoms_context q v]

theorem normalizeCode_context (q v c : Nat)
    (hq : checkCode q c = true) (hv : checkCode v c = true) :
    Normalization.normalizeCode q c = Normalization.normalizeCode v c := by
  simp only [Normalization.normalizeCode, hq, hv, Bool.cond_true, normalize_context q v]

theorem finiteCheck_change (q v n : Nat) (t : RelativeTerm Nat)
    (ht : finiteCheck q n t = true) (hp : Payloads v t) : finiteCheck v n t = true := by
  revert ht hp
  induction t with
  | parameter p => intro ht hp; exact hp
  | sum a b iha ihb =>
    intro ht hp
    have hs := Bool.and_eq_true_iff.mp ht
    simp only [finiteCheck_sum, iha hs.1 hp.1, ihb hs.2 hp.2, Bool.true_and]
  | theta k a ih =>
    intro ht hp
    have hs : finiteCheck q n a = true ∧ k < n ∧ a.outerSort ≤ k + 2 := by
      simpa only [finiteCheck_theta, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using ht
    simp only [finiteCheck_theta, ih hs.1 hp, hs.2.1, hs.2.2, decide_true, Bool.true_and]

theorem admissible_change (q v n : Nat) (t : RelativeTerm Nat)
    (ht : admissible q n t) (hp : Payloads v t) : admissible v n t :=
  (finiteCheck_exact v n t).mp
    (finiteCheck_change q v n t ((finiteCheck_exact q n t).mpr ht) hp)

theorem check_change (q v : Nat) (t : RelativeTerm Nat)
    (ht : check q t = true) (hv : baseCheck v = true) (hp : Payloads v t) :
    check v t = true := by
  have hc := finiteCheck_change q v (SourceOne.PublicCodes.fragment t) t
    (Bool.and_eq_true_iff.mp ht).2 hp
  simp only [check, hv, hc, Bool.true_and]

theorem sum_checks (q : Nat) (a b : RelativeTerm Nat) (ht : check q (.sum a b) = true) :
    check q a = true ∧ check q b = true := by
  have hq := (Bool.and_eq_true_iff.mp ht).1
  have hs := checked_admissible q (.sum a b) ht
  cases hs.2 with
  | sum ha hb =>
    exact ⟨Comparison.admitted_checked q _ hq a ⟨hs.1.1, ha⟩,
      Comparison.admitted_checked q _ hq b ⟨hs.1.2, hb⟩⟩

theorem theta_argument_check (q k : Nat) (a : RelativeTerm Nat)
    (ht : check q (.theta k a) = true) : check q a = true := by
  have hs := checked_admissible q (.theta k a) ht
  exact Comparison.admitted_checked q _ (Bool.and_eq_true_iff.mp ht).1 a
    (Comparison.admitted_argument hs)

theorem theta_base_le (q k : Nat) (a : RelativeTerm Nat)
    (ht : check q (.theta k a) = true) : base q ≤ denote q (.theta k a) := by
  have hq := (Bool.and_eq_true_iff.mp ht).1
  have hs := checked_admissible q (.theta k a) ht
  rw [denote_eq_finite q _ hq (.theta k a) hs.2]
  cases hs.2 with
  | theta h0k hkn hsort ha =>
    have hr := (source_theta_range (base q) parameters _ k a hkn ha hsort).1
    have hb : base q ≤ omegaSequence (base q) k := by
      simpa only [omegaSequence_zero] using
        (omegaSequence_strictMono (base q)).monotone (Nat.zero_le k)
    exact hb.trans hr

def Pure : RelativeTerm Nat → Prop
  | .parameter _ => True
  | .sum a b => Pure a ∧ Pure b
  | .theta _ _ => False

private theorem pure_eval (f g : Nat → Ordinal.{0} → Ordinal.{0})
    (t : RelativeTerm Nat) (ht : Pure t) : t.eval parameters f = t.eval parameters g := by
  revert ht
  induction t with
  | parameter p => intro _; rfl
  | sum a b iha ihb =>
    intro ht
    exact congrArg₂ (fun x y : Ordinal.{0} => x + y) (iha ht.1) (ihb ht.2)
  | theta k a => intro ht; exact False.elim ht

theorem pure_value (q v : Nat) (t : RelativeTerm Nat) (ht : Pure t) : denote q t = denote v t :=
  pure_eval (globalCollapse (base q)) (globalCollapse (base v)) t ht

theorem pure_parameter_le (q : Nat) (t : RelativeTerm Nat) (ht : Pure t)
    (p : Nat) (hp : p ∈ t.parameters) : parameters p ≤ denote q t := by
  revert ht p
  induction t with
  | parameter v =>
    intro ht p hp
    have he : p = v := by simpa only [RelativeTerm.parameters, Finset.mem_singleton] using hp
    subst p; exact le_rfl
  | sum a b iha ihb =>
    intro ht p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (iha ht.1 p hp).trans le_self_add
    · exact (ihb ht.2 p hp).trans le_add_self
  | theta k a => intro ht p hp; exact False.elim ht

theorem base_additive (v : Nat) (hv : baseCheck v = true) : Ordinal.IsPrincipal (· + ·) (base v) := by
  rw [← ((baseCheck_exact v).mp hv).2]
  exact Ordinal.isPrincipal_add_omega0_opow _

theorem pure_below (q v : Nat) (t : RelativeTerm Nat) (ht : Pure t)
    (hv : baseCheck v = true) (hp : Payloads v t) : denote q t < base v := by
  revert ht hp
  induction t with
  | parameter p => intro ht hp; exact parameter_sound v p hp
  | sum a b iha ihb =>
    intro ht hp
    exact base_additive v hv (iha ht.1 hp.1) (ihb ht.2 hp.2)
  | theta k a => intro ht hp; exact False.elim ht

theorem below_base_pure (q : Nat) (t : RelativeTerm Nat) (ht : check q t = true)
    (hl : denote q t < base q) : Pure t := by
  revert ht hl
  induction t with
  | parameter p => intro ht hl; trivial
  | sum a b iha ihb =>
    intro ht hl
    have hs := sum_checks q a b ht
    exact ⟨iha hs.1 (lt_of_le_of_lt le_self_add hl),
      ihb hs.2 (lt_of_le_of_lt le_add_self hl)⟩
  | theta k a =>
    intro ht hl
    exact False.elim ((not_lt_of_ge (theta_base_le q k a ht)) hl)

theorem below_base_iff_pure (q : Nat) (t : RelativeTerm Nat) (ht : check q t = true) :
    denote q t < base q ↔ Pure t :=
  ⟨below_base_pure q t ht, fun hp => pure_below q q t hp
    (Bool.and_eq_true_iff.mp ht).1 (checked_admissible q t ht).1⟩

open scoped Classical

/-- Atomic-below-base priority on the chosen admitted presentation. The sum
case stops before either child when its whole value is below the base. This
does not assert invariance under different equal-valued presentations. -/
noncomputable def parameterSupport (q : Nat) : RelativeTerm Nat → Finset Ordinal.{0}
  | .parameter p => {parameters p}
  | .sum a b => if denote q (.sum a b) < base q then {denote q (.sum a b)}
      else parameterSupport q a ∪ parameterSupport q b
  | .theta k a => if denote q (.theta k a) < base q then {denote q (.theta k a)}
      else parameterSupport q a

theorem parameterSupport_atomic (q : Nat) (t : RelativeTerm Nat) (hl : denote q t < base q) :
    parameterSupport q t = {denote q t} := by
  cases t <;> simp only [parameterSupport, if_pos hl] <;> rfl

theorem parameterSupport_sum (q : Nat) (a b : RelativeTerm Nat)
    (hl : ¬ denote q (.sum a b) < base q) :
    parameterSupport q (.sum a b) = parameterSupport q a ∪ parameterSupport q b :=
  if_neg hl

theorem parameterSupport_theta (q k : Nat) (a : RelativeTerm Nat)
    (ht : check q (.theta k a) = true) :
    parameterSupport q (.theta k a) = parameterSupport q a :=
  if_neg (not_lt_of_ge (theta_base_le q k a ht))

def ParBounded (q v : Nat) (t : RelativeTerm Nat) : Prop :=
  ∀ ξ ∈ parameterSupport q t, ξ < base v

theorem parBounded_iff_payloads (q v : Nat) (t : RelativeTerm Nat)
    (ht : check q t = true) (hv : baseCheck v = true) : ParBounded q v t ↔ Payloads v t := by
  revert ht
  induction t with
  | parameter p =>
    intro ht
    have hp := checked_parameters q (.parameter p) ht p (by simp [RelativeTerm.parameters])
    simp only [ParBounded, parameterSupport, Finset.mem_singleton, forall_eq, Payloads,
      parameterCheck_exact, hp.1, ((baseCheck_exact v).mp hv).1, true_and]
  | sum a b iha ihb =>
    intro ht
    by_cases hl : denote q (.sum a b) < base q
    · rw [ParBounded, parameterSupport_atomic q (.sum a b) hl]
      simp only [Finset.mem_singleton, forall_eq]
      have hpure := below_base_pure q (.sum a b) ht hl
      constructor
      · intro hs
        apply (payloads_iff_parameters v (.sum a b)).mpr
        intro p hp
        exact (parameterCheck_exact v p).mpr ⟨(checked_parameters q _ ht p hp).1,
          ((baseCheck_exact v).mp hv).1, (pure_parameter_le q _ hpure p hp).trans_lt hs⟩
      · exact fun hp => pure_below q v _ hpure hv hp
    · have hs := sum_checks q a b ht
      simp only [ParBounded, parameterSupport_sum q a b hl, Finset.mem_union]
      change (∀ ξ, ξ ∈ parameterSupport q a ∨ ξ ∈ parameterSupport q b → ξ < base v) ↔
        Payloads v a ∧ Payloads v b
      rw [← iha hs.1, ← ihb hs.2]
      exact ⟨fun h => ⟨fun ξ hx => h ξ (Or.inl hx), fun ξ hx => h ξ (Or.inr hx)⟩,
        fun h ξ hx => hx.elim (h.1 ξ) (h.2 ξ)⟩
  | theta k a ih =>
    intro ht
    simpa only [ParBounded, parameterSupport_theta q k a ht, Payloads] using
      ih (theta_argument_check q k a ht)

theorem parameterSupport_context (q v : Nat) (t : RelativeTerm Nat)
    (hq : check q t = true) (hv : check v t = true) : parameterSupport q t = parameterSupport v t := by
  revert hq hv
  induction t with
  | parameter p => intro hq hv; rfl
  | sum a b iha ihb =>
    intro hq hv
    by_cases hp : Pure (.sum a b)
    · rw [parameterSupport_atomic q _ ((below_base_iff_pure q _ hq).mpr hp),
        parameterSupport_atomic v _ ((below_base_iff_pure v _ hv).mpr hp), pure_value q v _ hp]
    · have hqnot : ¬ denote q (.sum a b) < base q := fun h => hp ((below_base_iff_pure q _ hq).mp h)
      have hvnot : ¬ denote v (.sum a b) < base v := fun h => hp ((below_base_iff_pure v _ hv).mp h)
      have hqs := sum_checks q a b hq
      have hvs := sum_checks v a b hv
      rw [parameterSupport_sum q a b hqnot, parameterSupport_sum v a b hvnot,
        iha hqs.1 hvs.1, ihb hqs.2 hvs.2]
  | theta k a ih =>
    intro hq hv
    rw [parameterSupport_theta q k a hq, parameterSupport_theta v k a hv,
      ih (theta_argument_check q k a hq) (theta_argument_check v k a hv)]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.BaseTransformation
