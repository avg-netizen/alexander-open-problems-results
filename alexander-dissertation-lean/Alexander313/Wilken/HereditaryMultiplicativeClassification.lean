import Alexander313.Wilken.MultiplicativePrincipalArithmetic
import Alexander313.Wilken.HereditaryPrincipalLogarithm

/-!
# Executing classification of Wilken's multiplicative principals

Original positive additive-principal admission is tested first. On that domain,
the genuine principal logarithm search returns a canonical omega exponent. The
real exponent is zero or positive additive principal exactly when the input is
closed under actual ordinal multiplication. This makes the guarded decision
total, without asserting that its unbounded search is primitive recursive.

The source class includes 1 and excludes 0 and 2; both actual additive and
multiplicative closure remain in its meaning. Canonical class admission is an
additional literal canonical-code check. No semantic classifier, logarithm
oracle or termination premise is supplied. Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.Multiplicative

open MultiplicativePrincipalArithmetic

def exponentCheck (c : Nat) : Bool :=
  Canonical.graph c (CanonicalArithmetic.numeralCode 0) || Principal.unionPrincipalCheck c

theorem exponentCheck_primrec : Primrec exponentCheck :=
  Primrec.or.comp
    (Canonical.Effective.graph_primrec.comp Primrec.id
      (Primrec.const (CanonicalArithmetic.numeralCode 0)))
    Principal.unionPrincipalCheck_primrec

theorem exponentCheck_exact (c : Nat) (hc : Canonical.check c = true) :
    exponentCheck c = true ↔ unionInterpretation c = 0 ∨
      (0 < unionInterpretation c ∧ Ordinal.IsPrincipal (· + ·) (unionInterpretation c)) := by
  simp only [exponentCheck, Bool.or_eq_true, Canonical.graph_exact,
    CanonicalArithmetic.numeralCode_checked, CanonicalArithmetic.numeralCode_value,
    Nat.cast_zero, Principal.unionPrincipalCheck_exact, Canonical.check_original hc,
    true_and]

theorem logarithm_test_exact (q c : Nat) (hc : c ∈ PrincipalLogarithm.logarithm q) :
    exponentCheck c = true ↔ IsMultiplicativePrincipal (unionInterpretation q) := by
  have hs := PrincipalLogarithm.logarithm_value q c hc
  rw [exponentCheck_exact c hs.2.2.2.1]
  constructor
  · intro he
    refine ⟨hs.2.1, hs.2.2.1, ?_⟩
    rw [← hs.2.2.2.2]
    exact (omegaPower_multiplicative_iff _).mpr he
  · intro hm
    apply (omegaPower_multiplicative_iff _).mp
    rw [hs.2.2.2.2]
    exact hm.2.2

/-- The only unbounded computation is the previously constructed real
logarithm; its branch guard is precisely the proved terminating domain. -/
def decision (q : Nat) : Part Bool :=
  cond (Principal.unionPrincipalCheck q)
    ((PrincipalLogarithm.logarithm q).map exponentCheck) (Part.some false)

theorem decision_partrec : Partrec decision := by
  have hm := Partrec.map PrincipalLogarithm.logarithm_partrec
    (exponentCheck_primrec.comp Primrec.snd).to_comp.to₂
  exact Partrec.cond Principal.unionPrincipalCheck_computable hm (Computable.const false).partrec

theorem decision_total (q : Nat) : (decision q).Dom := by
  cases hq : Principal.unionPrincipalCheck q with
  | false => simpa only [decision, hq, Bool.cond_false] using Part.some_dom false
  | true =>
    rw [decision, hq]
    change (PrincipalLogarithm.logarithm q).Dom
    exact (PrincipalLogarithm.logarithm_domain q).mpr hq

theorem decision_true_iff (q : Nat) : true ∈ decision q ↔
    unionCheck q = true ∧ IsMultiplicativePrincipal (unionInterpretation q) := by
  cases hq : Principal.unionPrincipalCheck q with
  | false =>
    constructor
    · intro h
      have hfalse : true = false := by simpa only [decision, hq, Bool.cond_false,
        Part.mem_some_iff] using h
      cases hfalse
    · rintro ⟨hu, hp, ha, _⟩
      have ht := (Principal.unionPrincipalCheck_exact q).mpr ⟨hu, hp, ha⟩
      rw [hq] at ht
      cases ht
  | true =>
    have hu := ((Principal.unionPrincipalCheck_exact q).mp hq).1
    constructor
    · intro h
      have hm : true ∈ (PrincipalLogarithm.logarithm q).map exponentCheck := by
        simpa only [decision, hq, Bool.cond_true] using h
      obtain ⟨c, hc, ht⟩ := (Part.mem_map_iff exponentCheck).mp hm
      exact ⟨hu, (logarithm_test_exact q c hc).mp ht⟩
    · rintro ⟨_, hp⟩
      obtain ⟨c, hc, _, _⟩ := PrincipalLogarithm.logarithm_returns q hq
      have ht := (logarithm_test_exact q c hc).mpr hp
      have hm := Part.mem_map exponentCheck hc
      rw [ht] at hm
      simpa only [decision, hq, Bool.cond_true] using hm

/-- This total function is obtained from the actual terminating Part program,
not from a classical decision of its ordinal specification. -/
def check (q : Nat) : Bool := (decision q).get (decision_total q)

theorem check_mem (q : Nat) : check q ∈ decision q := ⟨decision_total q, rfl⟩

theorem decision_eq_some (q : Nat) : decision q = Part.some (check q) :=
  Part.eq_some_iff.mpr (check_mem q)

theorem check_computable : Computable check := decision_partrec.of_eq_tot check_mem

theorem check_exact (q : Nat) : check q = true ↔
    unionCheck q = true ∧ IsMultiplicativePrincipal (unionInterpretation q) := by
  simpa only [decision_eq_some, Part.mem_some_iff, eq_comm] using decision_true_iff q

theorem check_closure_exact (q : Nat) : check q = true ↔
    unionCheck q = true ∧ 0 < unionInterpretation q ∧
      Ordinal.IsPrincipal (· + ·) (unionInterpretation q) ∧
      Ordinal.IsPrincipal (· * ·) (unionInterpretation q) := check_exact q

theorem check_class_exact (q : Nat) : check q = true ↔
    unionCheck q = true ∧ (unionInterpretation q = 1 ∨
      ∃ ρ : Ordinal.{0}, unionInterpretation q = Ordinal.omega0 ^ (Ordinal.omega0 ^ ρ)) := by
  rw [check_exact, multiplicativePrincipal_iff]

theorem check_rejected (q : Nat) (hq : unionCheck q = false) : check q = false := by
  cases hc : check q with
  | false => rfl
  | true =>
    have ht := ((check_exact q).mp hc).1
    rw [hq] at ht
    cases ht

theorem check_invariant (q v : Nat) (hq : unionCheck q = true) (hv : unionCheck v = true)
    (he : unionInterpretation q = unionInterpretation v) : check q = check v := by
  apply Bool.eq_iff_iff.mpr
  simp only [check_exact, hq, hv, true_and, he]

theorem check_one (q : Nat) (hq : unionCheck q = true) (hv : unionInterpretation q = 1) :
    check q = true :=
  (check_class_exact q).mpr ⟨hq, Or.inl hv⟩

theorem check_zero (q : Nat) (hv : unionInterpretation q = 0) : check q = false := by
  cases hc : check q with
  | false => rfl
  | true =>
    have ht := ((check_exact q).mp hc).2
    rw [hv] at ht
    exact False.elim (not_multiplicativePrincipal_zero ht)

theorem check_two (q : Nat) (hv : unionInterpretation q = 2) : check q = false := by
  cases hc : check q with
  | false => rfl
  | true =>
    have ht := ((check_exact q).mp hc).2
    rw [hv] at ht
    exact False.elim (not_multiplicativePrincipal_two ht)

theorem check_double_power (q : Nat) (hq : unionCheck q = true) :
    check (OmegaPowers.powerCode (OmegaPowers.powerCode q)) = true := by
  have hw := OmegaPowers.powerCode_original q hq
  apply (check_class_exact _).mpr
  refine ⟨OmegaPowers.powerCode_original _ hw, Or.inr ⟨unionInterpretation q, ?_⟩⟩
  rw [OmegaPowers.powerCode_value _ hw, OmegaPowers.powerCode_value q hq]

def canonicalCheck (q : Nat) : Bool := Canonical.check q && check q

theorem canonicalCheck_computable : Computable canonicalCheck :=
  Primrec.and.to_comp.comp Canonical.Effective.check_primrec.to_comp check_computable

theorem canonicalCheck_exact (q : Nat) : canonicalCheck q = true ↔
    Canonical.check q = true ∧ IsMultiplicativePrincipal (unionInterpretation q) := by
  simp only [canonicalCheck, Bool.and_eq_true, check_exact]
  constructor
  · rintro ⟨hc, _, hp⟩; exact ⟨hc, hp⟩
  · rintro ⟨hc, hp⟩; exact ⟨hc, Canonical.check_original hc, hp⟩

theorem canonicalCheck_class_exact (q : Nat) : canonicalCheck q = true ↔
    Canonical.check q = true ∧ (unionInterpretation q = 1 ∨
      ∃ ρ : Ordinal.{0}, unionInterpretation q = Ordinal.omega0 ^ (Ordinal.omega0 ^ ρ)) := by
  rw [canonicalCheck_exact, multiplicativePrincipal_iff]

theorem canonicalize_checked (q : Nat) (hq : check q = true) :
    canonicalCheck (Canonical.canonicalize q) = true := by
  have hs := (check_exact q).mp hq
  apply (canonicalCheck_exact _).mpr
  refine ⟨Canonical.canonicalize_check q hs.1, ?_⟩
  rw [Canonical.canonicalize_value q hs.1]
  exact hs.2

end Alexander313.Wilken.RelativeTerm.Hereditary.Multiplicative
