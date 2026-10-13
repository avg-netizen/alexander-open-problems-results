import Alexander313.Wilken.HereditaryMultiplication
import Alexander313.Wilken.HereditaryNaturalCodes

/-!
# Actual powers of arbitrary original bases with finite exponents

A genuine natural recursion starts at canonical one and executes the actual
general multiplier at each successor. Original base admission guards the
whole computation, including exponent zero. Induction derives termination
and the literal ordinal exponentiation equation; the searched multiplication
is partial recursive, so no primitive-recursive power claim is made.

A second entry point accepts a finite original ordinal exponent code and
executes the genuine finite checker/extractor. Both operations return unique
canonical original codes. No power, graph, termination or effectivity oracle
is an input. All proof terms remain uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.FinitePowers

def oneCode : Nat := CanonicalArithmetic.numeralCode 1

theorem oneCode_checked : Canonical.check oneCode = true :=
  CanonicalArithmetic.numeralCode_checked 1

theorem oneCode_value : unionInterpretation oneCode = 1 := by
  simpa only [oneCode, Nat.cast_one] using CanonicalArithmetic.numeralCode_value 1

def rawPower (q : Nat) : Nat → Part Nat
  | 0 => Part.some oneCode
  | n + 1 => (rawPower q n).bind (fun c => Multiplication.multiply c q)

theorem rawPower_partrec : Partrec₂ rawPower := by
  have hstep : Partrec₂ (fun (p : Nat × Nat) (s : Nat × Nat) =>
      Multiplication.multiply s.2 p.1) :=
    (Multiplication.multiply_partrec.comp (Computable.snd.comp Computable.snd)
      (Computable.fst.comp Computable.fst)).to₂
  have h := Partrec.nat_rec Computable.snd (Computable.const oneCode).partrec hstep
  have he : (fun p : Nat × Nat => p.2.rec (Part.some oneCode)
      (fun n ih => ih.bind (fun c => Multiplication.multiply c p.1))) =
      (fun p => rawPower p.1 p.2) := by
    funext p
    induction p.2 with
    | zero => rfl
    | succ n ih =>
      simpa only [rawPower] using congrArg
        (fun t : Part Nat => t.bind (fun c => Multiplication.multiply c p.1)) ih
  rw [he] at h
  exact h.to₂

theorem rawPower_value (q n c : Nat) (hq : unionCheck q = true)
    (hc : c ∈ rawPower q n) :
    Canonical.check c = true ∧ unionInterpretation c = unionInterpretation q ^ (n : Ordinal.{0}) := by
  induction n generalizing c with
  | zero =>
    have he : c = oneCode := by simpa only [rawPower, Part.mem_some_iff] using hc
    subst c
    exact ⟨oneCode_checked, by simp only [Nat.cast_zero, Ordinal.opow_zero, oneCode_value]⟩
  | succ n ih =>
    obtain ⟨d, hd, hm⟩ := Part.mem_bind_iff.mp hc
    have hs := Multiplication.multiply_value d q c hm
    have ht := ih d hd
    refine ⟨hs.2.2.1, ?_⟩
    rw [hs.2.2.2, ht.2, Nat.cast_succ, Ordinal.opow_add_one]

theorem rawPower_terminates (q n : Nat) (hq : unionCheck q = true) : (rawPower q n).Dom := by
  induction n with
  | zero => trivial
  | succ n ih =>
    let d := (rawPower q n).get ih
    have hd : d ∈ rawPower q n := ⟨ih, rfl⟩
    have hc := (rawPower_value q n d hq hd).1
    have hm := Multiplication.multiply_terminates d q (Canonical.check_original hc) hq
    have hout : (Multiplication.multiply d q).get hm ∈ Multiplication.multiply d q := ⟨hm, rfl⟩
    exact Part.dom_iff_mem.mpr ⟨_, Part.mem_bind hd hout⟩

def power (q n : Nat) : Part Nat := cond (unionCheck q) (rawPower q n) Part.none

theorem power_partrec : Partrec₂ power :=
  (Partrec.cond (Uniform.unionCheck_primrec.comp Primrec.fst).to_comp
    rawPower_partrec Partrec.none).to₂

theorem power_domain (q n : Nat) : (power q n).Dom ↔ unionCheck q = true := by
  cases hq : unionCheck q with
  | false => simp [power, hq]
  | true =>
    simp only [power, hq, Bool.cond_true, iff_true]
    exact rawPower_terminates q n hq

theorem power_value (q n c : Nat) (hc : c ∈ power q n) :
    unionCheck q = true ∧ Canonical.check c = true ∧
      unionInterpretation c = unionInterpretation q ^ (n : Ordinal.{0}) := by
  have hdom : (power q n).Dom := by obtain ⟨hd, _⟩ := hc; exact hd
  have hq := (power_domain q n).mp hdom
  have hr : c ∈ rawPower q n := by simpa only [power, hq, Bool.cond_true] using hc
  exact ⟨hq, rawPower_value q n c hq hr⟩

theorem power_original (q n c : Nat) (hc : c ∈ power q n) :
    unionCheck c = true ∧ Theta.Normal c.unpair.1 (ThetaCourse.rawTree c.unpair.2) := by
  have hs := (power_value q n c hc).2.1
  exact ⟨Canonical.check_original hs, Canonical.check_normal hs⟩

theorem power_returns (q n : Nat) (hq : unionCheck q = true) :
    ∃ c : Nat, c ∈ power q n ∧ Canonical.check c = true ∧
      unionInterpretation c = unionInterpretation q ^ (n : Ordinal.{0}) := by
  have hd := (power_domain q n).mpr hq
  have hm : (power q n).get hd ∈ power q n := ⟨hd, rfl⟩
  exact ⟨_, hm, (power_value q n _ hm).2⟩

theorem power_graph_iff (q n c : Nat) : c ∈ power q n ↔
    unionCheck q = true ∧ Canonical.check c = true ∧
      unionInterpretation c = unionInterpretation q ^ (n : Ordinal.{0}) := by
  constructor
  · exact power_value q n c
  · rintro ⟨hq, hc, he⟩
    obtain ⟨d, hd, hdc, hdv⟩ := power_returns q n hq
    have hcd := Canonical.check_value_injective c d hc hdc (he.trans hdv.symm)
    rw [hcd]
    exact hd

theorem power_output_unique (q n c d : Nat) (hc : c ∈ power q n) (hd : d ∈ power q n) : c = d := by
  have hs := power_value q n c hc
  have ht := power_value q n d hd
  exact Canonical.check_value_injective c d hs.2.1 ht.2.1 (hs.2.2.trans ht.2.2.symm)

theorem power_invariant (q v n c d : Nat) (hc : c ∈ power q n) (hd : d ∈ power v n)
    (he : unionInterpretation q = unionInterpretation v) : c = d := by
  have hs := power_value q n c hc
  have ht := power_value v n d hd
  apply Canonical.check_value_injective c d hs.2.1 ht.2.1
  exact hs.2.2.trans (by rw [he]; exact ht.2.2.symm)

theorem power_zero (q : Nat) (hq : unionCheck q = true) : power q 0 = Part.some oneCode := by
  simp only [power, hq, Bool.cond_true, rawPower]

theorem power_one (q : Nat) (hq : unionCheck q = true) :
    Canonical.canonicalize q ∈ power q 1 := by
  apply (power_graph_iff q 1 _).mpr
  exact ⟨hq, Canonical.canonicalize_check q hq, by
    rw [Canonical.canonicalize_value q hq, Nat.cast_one, Ordinal.opow_one]⟩

theorem power_below_limit (q n : Nat) (hq : unionCheck q = true) :
    unionInterpretation q ^ (n : Ordinal.{0}) < finiteBaseLimit := by
  obtain ⟨c, _, hc, he⟩ := power_returns q n hq
  exact (Hereditary.lt_finiteBaseLimit_iff_code _).mpr ⟨c, Canonical.check_original hc, he⟩

/-- The exponent is itself an original code, with the real finite checker. -/
def codedPower (q v : Nat) : Part Nat :=
  cond (NaturalCodes.check v) (power q (NaturalCodes.extract v)) Part.none

theorem codedPower_partrec : Partrec₂ codedPower :=
  (Partrec.cond (NaturalCodes.check_primrec.comp Primrec.snd).to_comp
    (power_partrec.comp Computable.fst (NaturalCodes.extract_primrec.comp Primrec.snd).to_comp)
    Partrec.none).to₂

theorem codedPower_domain (q v : Nat) : (codedPower q v).Dom ↔
    unionCheck q = true ∧ unionCheck v = true ∧ unionInterpretation v < Ordinal.omega0 := by
  cases hv : NaturalCodes.check v with
  | false =>
    have hn : ¬ (unionCheck v = true ∧ unionInterpretation v < Ordinal.omega0) := by
      intro h
      have ht := (NaturalCodes.check_below_omega v).mpr h
      rw [hv] at ht
      contradiction
    simp [codedPower, hv, hn]
  | true =>
    have hs := (NaturalCodes.check_below_omega v).mp hv
    simp only [codedPower, hv, Bool.cond_true, power_domain, hs.1, hs.2, and_true]

theorem codedPower_value (q v c : Nat) (hc : c ∈ codedPower q v) :
    unionCheck q = true ∧ unionCheck v = true ∧ unionInterpretation v < Ordinal.omega0 ∧
      Canonical.check c = true ∧ unionInterpretation c = unionInterpretation q ^ unionInterpretation v := by
  have hdom : (codedPower q v).Dom := by obtain ⟨hd, _⟩ := hc; exact hd
  have hs := (codedPower_domain q v).mp hdom
  have hv := (NaturalCodes.check_below_omega v).mpr hs.2
  have hp : c ∈ power q (NaturalCodes.extract v) :=
    by simpa only [codedPower, hv, Bool.cond_true] using hc
  have ht := power_value q _ c hp
  exact ⟨hs.1, hs.2.1, hs.2.2, ht.2.1, by rw [NaturalCodes.extract_value v hv]; exact ht.2.2⟩

theorem codedPower_returns (q v : Nat) (hq : unionCheck q = true)
    (hv : NaturalCodes.check v = true) :
    ∃ c : Nat, c ∈ codedPower q v ∧ Canonical.check c = true ∧
      unionInterpretation c = unionInterpretation q ^ unionInterpretation v := by
  obtain ⟨c, hc, hcanonical, hvalue⟩ := power_returns q (NaturalCodes.extract v) hq
  refine ⟨c, ?_, hcanonical, ?_⟩
  · simpa only [codedPower, hv, Bool.cond_true] using hc
  · rw [NaturalCodes.extract_value v hv]
    exact hvalue

theorem codedPower_graph_iff (q v c : Nat) : c ∈ codedPower q v ↔
    unionCheck q = true ∧ unionCheck v = true ∧ unionInterpretation v < Ordinal.omega0 ∧
      Canonical.check c = true ∧ unionInterpretation c = unionInterpretation q ^ unionInterpretation v := by
  constructor
  · exact codedPower_value q v c
  · rintro ⟨hq, hv, hfinite, hc, he⟩
    obtain ⟨d, hd, hdc, hdv⟩ := codedPower_returns q v hq
      ((NaturalCodes.check_below_omega v).mpr ⟨hv, hfinite⟩)
    have hcd := Canonical.check_value_injective c d hc hdc (he.trans hdv.symm)
    rw [hcd]
    exact hd

end Alexander313.Wilken.RelativeTerm.Hereditary.FinitePowers
