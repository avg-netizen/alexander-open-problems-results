import Alexander313.Wilken.HereditaryNativeLowArithmetic
import Alexander313.Wilken.HereditaryExactDivision

/-!
# Executing exact left division in the same public epsilon context

Both ORIGINAL native inputs are low at contextCode s. The factor is genuinely
positive. The source domain additionally requires an actual ordinal quotient;
the finite caller check alone does not decide divisibility. Actual public
exact division searches real multiplication certificates and returns its
unique canonical quotient. Its bound quotient <= dividend, together with the
original low dividend bound, licenses the genuine finite native return.

The native answer is originally low and weak Normal. Every ordinal solution
equals its value, so it is the least solution in the source preliminary
definition. Zero dividend, unit factor and equal factors execute actual chosen
returns. Zero factors and nonexistent quotients do not acquire a source clause.
The producer is Partrec; finite callers/conversions and compiler operations
are separately PR. Positive principal factor <= positive principal dividend
genuinely supplies quotient existence, through actual omega-power divisibility.
No arbitrary epsilon/full-sort division, source chi division law, height bound
or recoding oracle is assumed.
All proof terms remain uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.ExactDivision

open NativePublicBridge (contextCode)
open LowArithmetic (lowInput publicCode returnCode)

/-- This finite caller only checks the two original low inputs and positivity. -/
def callerCheck (s c d : Nat) : Bool := (lowInput s c && lowInput s d) &&
  Hereditary.ExactDivision.callerCheck (publicCode s c) (publicCode s d)

theorem callerCheck_primrec : Primrec
    (fun p : Nat × (Nat × Nat) => callerCheck p.1 p.2.1 p.2.2) := by
  have hs := Primrec.fst
  have hc := Primrec.fst.comp Primrec.snd
  have hd := Primrec.snd.comp Primrec.snd
  exact Primrec.and.comp
    (Primrec.and.comp (LowArithmetic.lowInput_primrec.comp hs hc)
      (LowArithmetic.lowInput_primrec.comp hs hd))
    (Hereditary.ExactDivision.callerCheck_primrec.comp
      (LowArithmetic.publicCode_primrec.comp hs hc)
      (LowArithmetic.publicCode_primrec.comp hs hd))

theorem callerCheck_exact (s c d : Nat) : callerCheck s c d = true ↔
    lowInput s c = true ∧ lowInput s d = true ∧ 0 < interpretation (contextCode s) c := by
  constructor
  · intro h
    obtain ⟨hl, hp⟩ := Bool.and_eq_true.mp h
    obtain ⟨hc, hd⟩ := Bool.and_eq_true.mp hl
    have hv := LowArithmetic.publicCode_spec s c hc
    have he := (Hereditary.ExactDivision.callerCheck_exact _ _).mp hp
    exact ⟨hc, hd, hv.2 ▸ he.2.2⟩
  · rintro ⟨hc, hd, hp⟩
    have hpc := LowArithmetic.publicCode_spec s c hc
    have hpd := LowArithmetic.publicCode_spec s d hd
    exact Bool.and_eq_true.mpr ⟨Bool.and_eq_true.mpr ⟨hc, hd⟩,
      (Hereditary.ExactDivision.callerCheck_exact _ _).mpr
        ⟨hpc.1, hpd.1, hpc.2.symm ▸ hp⟩⟩

/-- Literal quotient existence is not a supplied operation or termination input. -/
def SourceDomain (s c d : Nat) : Prop := lowInput s c = true ∧ lowInput s d = true ∧
  0 < interpretation (contextCode s) c ∧
    ∃ δ : Ordinal.{0}, interpretation (contextCode s) c * δ = interpretation (contextCode s) d

theorem sourceDomain_caller (s c d : Nat) (h : SourceDomain s c d) : callerCheck s c d = true :=
  (callerCheck_exact s c d).mpr ⟨h.1, h.2.1, h.2.2.1⟩

theorem sourceDomain_public (s c d : Nat) (h : SourceDomain s c d) :
    Hereditary.ExactDivision.SourceDomain (publicCode s c) (publicCode s d) := by
  have hc := LowArithmetic.publicCode_spec s c h.1
  have hd := LowArithmetic.publicCode_spec s d h.2.1
  refine ⟨hc.1, hd.1, hc.2.symm ▸ h.2.2.1, ?_⟩
  simpa only [hc.2, hd.2] using h.2.2.2

def divide (s c d : Nat) : Part Nat := cond (callerCheck s c d)
  ((Hereditary.ExactDivision.divide (publicCode s c) (publicCode s d)).map (returnCode s)) Part.none

theorem divide_partrec : Partrec
    (fun p : Nat × (Nat × Nat) => divide p.1 p.2.1 p.2.2) := by
  have hs := Computable.fst
  have hc := Computable.fst.comp Computable.snd
  have hd := Computable.snd.comp Computable.snd
  have hp := Hereditary.ExactDivision.divide_partrec.comp
    (LowArithmetic.publicCode_primrec.to_comp.comp hs hc)
    (LowArithmetic.publicCode_primrec.to_comp.comp hs hd)
  have hm := Partrec.map hp
    (LowArithmetic.returnCode_primrec.to_comp.comp (hs.comp Computable.fst) Computable.snd).to₂
  exact Partrec.cond callerCheck_primrec.to_comp hm Partrec.none

theorem divide_rejected (s c d : Nat) (h : callerCheck s c d = false) : divide s c d = Part.none := by
  simp only [divide, h, Bool.cond_false]

theorem divide_witness (s c d out : Nat) (ho : out ∈ divide s c d) :
    callerCheck s c d = true ∧ ∃ w,
      w ∈ Hereditary.ExactDivision.divide (publicCode s c) (publicCode s d) ∧ out = returnCode s w := by
  cases hi : callerCheck s c d with
  | false => simp only [divide, hi, Bool.cond_false, Part.notMem_none] at ho
  | true =>
    obtain ⟨w, hw, he⟩ := (Part.mem_map_iff (returnCode s)).mp
      (by simpa only [divide, hi, Bool.cond_true] using ho)
    exact ⟨hi, w, hw, he.symm⟩

/-- Every native return caller is derived from the genuine quotient bound. -/
theorem publicDivision_spec (s c d w : Nat) (hi : callerCheck s c d = true)
    (hw : w ∈ Hereditary.ExactDivision.divide (publicCode s c) (publicCode s d)) :
    Canonical.check w = true ∧ unionInterpretation w < finiteBase ((s + 1) + 1) ∧
      interpretation (contextCode s) c * unionInterpretation w = interpretation (contextCode s) d ∧
      unionInterpretation w ≤ interpretation (contextCode s) d := by
  have hc := (callerCheck_exact s c d).mp hi
  have hpc := LowArithmetic.publicCode_spec s c hc.1
  have hpd := LowArithmetic.publicCode_spec s d hc.2.1
  have hv := Hereditary.ExactDivision.divide_value _ _ w hw
  have hb : unionInterpretation w ≤ interpretation (contextCode s) d := by
    simpa only [hpd.2] using Hereditary.ExactDivision.divide_bound _ _ w hw
  exact ⟨hv.2.2.2.1, hb.trans_lt (LowArithmetic.lowInput_bound s d hc.2.1),
    by simpa only [hpc.2, hpd.2] using hv.2.2.2.2, hb⟩

theorem divide_domain (s c d : Nat) : (divide s c d).Dom ↔ SourceDomain s c d := by
  constructor
  · intro h
    obtain ⟨out, ho⟩ := Part.dom_iff_mem.mp h
    obtain ⟨hi, w, hw, _⟩ := divide_witness s c d out ho
    have hc := (callerCheck_exact s c d).mp hi
    have hs := publicDivision_spec s c d w hi hw
    exact ⟨hc.1, hc.2.1, hc.2.2, unionInterpretation w, hs.2.2.1⟩
  · intro h
    obtain ⟨w, hw⟩ := Part.dom_iff_mem.mp
      ((Hereditary.ExactDivision.divide_domain _ _).mpr (sourceDomain_public s c d h))
    have hm : returnCode s w ∈ divide s c d := by
      simp only [divide, sourceDomain_caller s c d h, Bool.cond_true]
      exact (Part.mem_map_iff (returnCode s)).mpr ⟨w, hw, rfl⟩
    exact Part.dom_iff_mem.mpr ⟨_, hm⟩

theorem divide_spec (s c d out : Nat) (ho : out ∈ divide s c d) :
    SourceDomain s c d ∧ lowInput s out = true ∧ Comparison.acceptedCode (contextCode s) out = true ∧
      interpretation (contextCode s) c * interpretation (contextCode s) out = interpretation (contextCode s) d ∧
      interpretation (contextCode s) out ≤ interpretation (contextCode s) d := by
  have hdom := (divide_domain s c d).mp (Part.dom_iff_mem.mpr ⟨out, ho⟩)
  obtain ⟨hi, w, hw, rfl⟩ := divide_witness s c d out ho
  have hs := publicDivision_spec s c d w hi hw
  have hr := LowArithmetic.returnCode_spec s w hs.1 hs.2.1
  exact ⟨hdom, hr.1, hr.2.1, by rw [hr.2.2]; exact hs.2.2.1,
    hr.2.2.symm ▸ hs.2.2.2⟩

theorem divide_bound (s c d out : Nat) (ho : out ∈ divide s c d) :
    interpretation (contextCode s) out < finiteBase ((s + 1) + 1) :=
  (divide_spec s c d out ho).2.2.2.2.trans_lt
    (LowArithmetic.lowInput_bound s d (divide_spec s c d out ho).1.2.1)

theorem divide_returns (s c d : Nat) (h : SourceDomain s c d) :
    ∃ out, out ∈ divide s c d ∧ lowInput s out = true ∧ Comparison.acceptedCode (contextCode s) out = true := by
  obtain ⟨out, ho⟩ := Part.dom_iff_mem.mp ((divide_domain s c d).mpr h)
  have hs := divide_spec s c d out ho
  exact ⟨out, ho, hs.2.1, hs.2.2.1⟩

/-- Every ordinal solution, without a code or grammar restriction, is this quotient. -/
theorem divide_eq_every_solution (s c d out : Nat) (ho : out ∈ divide s c d)
    (δ : Ordinal.{0}) (hδ : interpretation (contextCode s) c * δ = interpretation (contextCode s) d) :
    interpretation (contextCode s) out = δ := by
  have hs := divide_spec s c d out ho
  exact MultiplicativePrincipalArithmetic.positive_mul_injective hs.1.2.2.1
    (hs.2.2.2.1.trans hδ.symm)

theorem divide_least (s c d out : Nat) (ho : out ∈ divide s c d) :
    interpretation (contextCode s) c * interpretation (contextCode s) out = interpretation (contextCode s) d ∧
      ∀ δ : Ordinal.{0}, interpretation (contextCode s) c * δ = interpretation (contextCode s) d →
        interpretation (contextCode s) out ≤ δ :=
  ⟨(divide_spec s c d out ho).2.2.2.1,
    fun δ hδ => (divide_eq_every_solution s c d out ho δ hδ).le⟩

theorem divide_unique (s c d : Nat) (h : SourceDomain s c d) : ∃! out, out ∈ divide s c d := by
  obtain ⟨out, ho, _⟩ := divide_returns s c d h
  exact ⟨out, ho, fun z hz => Part.mem_unique hz ho⟩

theorem quotient_exists_unique (s c d : Nat) (h : SourceDomain s c d) :
    ∃! δ : Ordinal.{0}, interpretation (contextCode s) c * δ = interpretation (contextCode s) d := by
  obtain ⟨out, ho, _⟩ := divide_returns s c d h
  refine ⟨interpretation (contextCode s) out, (divide_spec s c d out ho).2.2.2.1, ?_⟩
  intro δ hδ
  exact (divide_eq_every_solution s c d out ho δ hδ).symm

theorem divide_no_quotient (s c d : Nat)
    (h : ∀ δ : Ordinal.{0}, interpretation (contextCode s) c * δ ≠ interpretation (contextCode s) d) :
    divide s c d = Part.none := by
  apply Part.eq_none_iff'.mpr
  intro hd
  obtain ⟨δ, hδ⟩ := ((divide_domain s c d).mp hd).2.2.2
  exact h δ hδ

theorem divide_zero_factor (s c d : Nat) (h : interpretation (contextCode s) c = 0) :
    divide s c d = Part.none := by
  apply Part.eq_none_iff'.mpr
  intro hd
  have hp := ((divide_domain s c d).mp hd).2.2.1
  rw [h] at hp
  exact lt_irrefl _ hp

/-- Equal actual input values give the same literal selected native return.
Canonical intermediate injection, rather than native spelling uniqueness, proves this. -/
theorem divide_invariant (s c d c' d' out out' : Nat)
    (ho : out ∈ divide s c d) (ho' : out' ∈ divide s c' d')
    (hc : interpretation (contextCode s) c = interpretation (contextCode s) c')
    (hd : interpretation (contextCode s) d = interpretation (contextCode s) d') : out = out' := by
  obtain ⟨hi, w, hw, he⟩ := divide_witness s c d out ho
  obtain ⟨hi', w', hw', he'⟩ := divide_witness s c' d' out' ho'
  have hl := (callerCheck_exact s c d).mp hi
  have hl' := (callerCheck_exact s c' d').mp hi'
  have hpc := LowArithmetic.publicCode_spec s c hl.1
  have hpd := LowArithmetic.publicCode_spec s d hl.2.1
  have hpc' := LowArithmetic.publicCode_spec s c' hl'.1
  have hpd' := LowArithmetic.publicCode_spec s d' hl'.2.1
  have hww := Hereditary.ExactDivision.divide_output_invariant _ _ _ _ w w' hw hw'
    (hpc.2.trans (hc.trans hpc'.2.symm)) (hpd.2.trans (hd.trans hpd'.2.symm))
  exact he.trans ((congrArg (returnCode s) hww).trans he'.symm)

/-- A proved canonical solution identifies the actual executed answer;
the producer itself never accepts such a solution as an input. -/
theorem divide_eq_return (s c d w : Nat) (hc : lowInput s c = true) (hd : lowInput s d = true)
    (hp : 0 < interpretation (contextCode s) c) (hw : Canonical.check w = true)
    (he : interpretation (contextCode s) c * unionInterpretation w = interpretation (contextCode s) d) :
    divide s c d = Part.some (returnCode s w) := by
  have hdom : SourceDomain s c d := ⟨hc, hd, hp, unionInterpretation w, he⟩
  obtain ⟨out, ho, _⟩ := divide_returns s c d hdom
  obtain ⟨hi, v, hv, hout⟩ := divide_witness s c d out ho
  have hs := publicDivision_spec s c d v hi hv
  have hvalue := MultiplicativePrincipalArithmetic.positive_mul_injective hp
    (hs.2.2.1.trans he.symm)
  have hcode := Canonical.check_value_injective v w hs.1 hw hvalue
  rw [hcode] at hout
  apply Part.eq_some_iff.mpr
  rw [← hout]
  exact ho

theorem divide_zero_dividend (s c d : Nat) (hc : lowInput s c = true) (hd : lowInput s d = true)
    (hp : 0 < interpretation (contextCode s) c) (hz : interpretation (contextCode s) d = 0) :
    divide s c d = Part.some (returnCode s (CanonicalArithmetic.numeralCode 0)) := by
  apply divide_eq_return s c d _ hc hd hp (CanonicalArithmetic.numeralCode_checked 0)
  rw [CanonicalArithmetic.numeralCode_value, Nat.cast_zero, mul_zero, hz]

theorem divide_unit_factor (s c d : Nat) (hc : lowInput s c = true) (hd : lowInput s d = true)
    (h1 : interpretation (contextCode s) c = 1) :
    divide s c d = Part.some (returnCode s (Canonical.canonicalize (publicCode s d))) := by
  have hv := LowArithmetic.publicCode_spec s d hd
  apply divide_eq_return s c d _ hc hd (by rw [h1]; exact zero_lt_one)
    (Canonical.canonicalize_check _ hv.1)
  rw [h1, one_mul, Canonical.canonicalize_value _ hv.1, hv.2]

theorem divide_equal_factors (s c d : Nat) (hc : lowInput s c = true) (hd : lowInput s d = true)
    (hp : 0 < interpretation (contextCode s) c)
    (he : interpretation (contextCode s) c = interpretation (contextCode s) d) :
    divide s c d = Part.some (returnCode s (CanonicalArithmetic.numeralCode 1)) := by
  apply divide_eq_return s c d _ hc hd hp (CanonicalArithmetic.numeralCode_checked 1)
  rw [CanonicalArithmetic.numeralCode_value, Nat.cast_one, mul_one, he]

theorem divide_zero_iff (s c d out : Nat) (ho : out ∈ divide s c d) :
    interpretation (contextCode s) out = 0 ↔ interpretation (contextCode s) d = 0 := by
  constructor
  · intro hz
    have he := (divide_spec s c d out ho).2.2.2.1
    rw [hz, mul_zero] at he
    exact he.symm
  · intro hz
    exact divide_eq_every_solution s c d out ho 0 (by rw [mul_zero, hz])

/-- Actual principal powers derive divisibility, rather than requiring a
quotient or a divisibility oracle as a caller premise. -/
theorem principal_quotient_exists {a b : Ordinal.{0}} (ha : 0 < a) (hb : 0 < b)
    (hpa : Ordinal.IsPrincipal (· + ·) a) (hpb : Ordinal.IsPrincipal (· + ·) b)
    (hab : a ≤ b) : ∃ δ : Ordinal.{0}, a * δ = b := by
  rcases Ordinal.isPrincipal_add_iff_zero_or_omega0_opow.mp hpa with ha0 | ⟨γ, hγ⟩
  · exact False.elim ((ne_of_gt ha) ha0)
  rcases Ordinal.isPrincipal_add_iff_zero_or_omega0_opow.mp hpb with hb0 | ⟨η, hη⟩
  · exact False.elim ((ne_of_gt hb) hb0)
  have hγη : γ ≤ η := omegaPower_strictMono.le_iff_le.mp (by rw [hγ, hη]; exact hab)
  have hdvd : a ∣ b := by
    rw [← hγ, ← hη]
    exact Ordinal.opow_dvd_opow Ordinal.omega0 hγη
  obtain ⟨δ, hδ⟩ := hdvd
  exact ⟨δ, hδ.symm⟩

def principalCaller (s c d : Nat) : Bool :=
  (LowArithmetic.principalInput s c && LowArithmetic.principalInput s d) &&
    Arithmetic.leCode (contextCode s) c d

theorem principalCaller_primrec : Primrec
    (fun p : Nat × (Nat × Nat) => principalCaller p.1 p.2.1 p.2.2) := by
  have hs := Primrec.fst
  have hc := Primrec.fst.comp Primrec.snd
  have hd := Primrec.snd.comp Primrec.snd
  exact Primrec.and.comp
    (Primrec.and.comp (LowArithmetic.principalInput_primrec.comp hs hc)
      (LowArithmetic.principalInput_primrec.comp hs hd))
    (Arithmetic.leCode_primrec.comp
      ((NativePublicBridge.contextCode_primrec.comp hs).pair (hc.pair hd)))

theorem principalCaller_exact (s c d : Nat) : principalCaller s c d = true ↔
    lowInput s c = true ∧ lowInput s d = true ∧
      0 < interpretation (contextCode s) c ∧ 0 < interpretation (contextCode s) d ∧
      Ordinal.IsPrincipal (· + ·) (interpretation (contextCode s) c) ∧
      Ordinal.IsPrincipal (· + ·) (interpretation (contextCode s) d) ∧
        interpretation (contextCode s) c ≤ interpretation (contextCode s) d := by
  constructor
  · intro h
    obtain ⟨hl, he⟩ := Bool.and_eq_true.mp h
    obtain ⟨hc, hd⟩ := Bool.and_eq_true.mp hl
    have hs := (LowArithmetic.principalInput_exact s c).mp hc
    have ht := (LowArithmetic.principalInput_exact s d).mp hd
    have hcc := (Bool.and_eq_true.mp hs.1).1
    have hdd := (Bool.and_eq_true.mp ht.1).1
    exact ⟨hs.1, ht.1, hs.2.1, ht.2.1, hs.2.2, ht.2.2,
      (Arithmetic.leCode_exact _ c d hcc hdd).mp he⟩
  · rintro ⟨hc, hd, hp, hq, hpc, hpd, he⟩
    have hcc := (Bool.and_eq_true.mp hc).1
    have hdd := (Bool.and_eq_true.mp hd).1
    exact Bool.and_eq_true.mpr ⟨Bool.and_eq_true.mpr
      ⟨(LowArithmetic.principalInput_exact s c).mpr ⟨hc, hp, hpc⟩,
        (LowArithmetic.principalInput_exact s d).mpr ⟨hd, hq, hpd⟩⟩,
      (Arithmetic.leCode_exact _ c d hcc hdd).mpr he⟩

/-- This includes the actual source 3.5 principal-factor existence caller;
it asserts no chi preservation law for the returned quotient. -/
theorem principalCaller_sourceDomain (s c d : Nat) (h : principalCaller s c d = true) :
    SourceDomain s c d := by
  have hs := (principalCaller_exact s c d).mp h
  exact ⟨hs.1, hs.2.1, hs.2.2.1,
    principal_quotient_exists hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.1 hs.2.2.2.2.2.1 hs.2.2.2.2.2.2⟩

theorem principalCaller_returns (s c d : Nat) (h : principalCaller s c d = true) :
    ∃ out, out ∈ divide s c d ∧ lowInput s out = true ∧ Comparison.acceptedCode (contextCode s) out = true :=
  divide_returns s c d (principalCaller_sourceDomain s c d h)

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.ExactDivision
